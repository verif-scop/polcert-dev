type requirement =
  | RequireKey of string
  | RequireValue of string * string

type registry_case = {
  name : string;
  group : string;
  witness_kind : string;
  requirements : requirement list;
  semantic_rules : string list;
}

type cert = {
  path : string;
  fields : (string * string list) list;
}

let trim s =
  let len = String.length s in
  let left = ref 0 in
  while !left < len && (s.[!left] = ' ' || s.[!left] = '\t' || s.[!left] = '\r') do
    incr left
  done;
  let right = ref (len - 1) in
  while !right >= !left && (s.[!right] = ' ' || s.[!right] = '\t' || s.[!right] = '\r') do
    decr right
  done;
  if !right < !left then "" else String.sub s !left (!right - !left + 1)

let split_once ch s =
  match String.index_opt s ch with
  | None -> None
  | Some idx ->
      let left = String.sub s 0 idx |> trim in
      let right = String.sub s (idx + 1) (String.length s - idx - 1) |> trim in
      Some (left, right)

let add_field key value fields =
  let rec loop acc = function
    | [] -> List.rev ((key, [ value ]) :: acc)
    | (k, values) :: rest when k = key -> List.rev_append acc ((k, values @ [ value ]) :: rest)
    | item :: rest -> loop (item :: acc) rest
  in
  loop [] fields

let values key fields =
  match List.assoc_opt key fields with
  | None -> []
  | Some values -> values

let has_key key fields = values key fields <> []

let has_value key value fields = List.exists (( = ) value) (values key fields)

let sorted_unique xs =
  xs |> List.sort_uniq String.compare

let find_assignment key cell fields =
  values key fields
  |> List.filter_map (fun item ->
         match split_once '=' item with
         | Some (lhs, rhs) when lhs = cell -> Some rhs
         | _ -> None)
  |> function
  | value :: _ -> Some value
  | [] -> None

let assignments key fields =
  values key fields
  |> List.filter_map (fun item ->
         match split_once '=' item with
         | Some (lhs, rhs) -> Some (lhs, rhs)
         | None -> None)

let target_observable_value cell fields =
  match find_assignment "target_final" cell fields with
  | Some value -> Some value
  | None ->
      values "representation" fields
      |> List.filter_map (fun item ->
             match split_once '-' item with
             | Some (phys, rest) when String.length rest >= 1 && rest.[0] = '>' ->
                 let logical = String.sub rest 1 (String.length rest - 1) |> trim in
                 if logical = cell then find_assignment "target_repr_final" phys fields else None
             | _ -> None)
      |> function
      | value :: _ -> Some value
      | [] -> None

let parse_field_line line =
  let line = trim line in
  if line = "" || line.[0] = '#' then None else split_once ':' line

let parse_cert path =
  let input = open_in path in
  let rec loop fields =
    match input_line input with
    | line -> (
        match parse_field_line line with
        | None -> loop fields
        | Some (key, value) -> loop (add_field key value fields))
    | exception End_of_file ->
        close_in input;
        { path; fields }
  in
  loop []

let requirement_of_string raw =
  match split_once '=' raw with
  | None -> RequireKey raw
  | Some (key, value) -> RequireValue (key, value)

let parse_registry path =
  let input = open_in path in
  let finish_block fields cases =
    match values "case" fields with
    | [] -> cases
    | name :: _ ->
        let group = match values "group" fields with [] -> "unknown" | x :: _ -> x in
        let witness_kind = match values "witness_kind" fields with [] -> "" | x :: _ -> x in
        let requirements = List.map requirement_of_string (values "required" fields) in
        let semantic_rules = values "semantic" fields in
        { name; group; witness_kind; requirements; semantic_rules } :: cases
  in
  let rec loop fields cases =
    match input_line input with
    | line ->
        let line = trim line in
        if line = "---" then loop [] (finish_block fields cases)
        else (
          match parse_field_line line with
          | None -> loop fields cases
          | Some (key, value) -> loop (add_field key value fields) cases)
    | exception End_of_file ->
        close_in input;
        List.rev (finish_block fields cases)
  in
  loop [] []

let rec collect_cert_files root =
  let entries = Sys.readdir root |> Array.to_list |> List.sort String.compare in
  List.concat_map
    (fun name ->
      let path = Filename.concat root name in
      if Sys.is_directory path then collect_cert_files path
      else if Filename.check_suffix path ".cert" then [ path ]
      else [])
    entries

let validate_structure registry cert =
  let errors = ref [] in
  let add_error msg = errors := msg :: !errors in
  let case_name =
    match values "case" cert.fields with
    | [] ->
        add_error "missing case";
        None
    | name :: _ -> Some name
  in
  let registry_case =
    match case_name with
    | None -> None
    | Some name -> (
        match List.find_opt (fun item -> item.name = name) registry with
        | None ->
            add_error ("unknown case " ^ name);
            None
        | Some item -> Some item)
  in
  (match registry_case with
  | None -> ()
  | Some item ->
      List.iter
        (function
          | RequireKey key ->
              if not (has_key key cert.fields) then add_error ("missing required key " ^ key)
          | RequireValue (key, value) ->
              if not (has_value key value cert.fields) then
                add_error ("missing required value " ^ key ^ "=" ^ value))
        item.requirements);
  List.rev !errors

let check_public_output_eq fields =
  let errors = ref [] in
  List.iter
    (fun cell ->
      match (find_assignment "source_final" cell fields, target_observable_value cell fields) with
      | Some src, Some tgt when src = tgt -> ()
      | Some src, Some tgt ->
          errors := ("public output mismatch " ^ cell ^ ": source=" ^ src ^ " target=" ^ tgt) :: !errors
      | None, _ -> errors := ("missing source_final for public cell " ^ cell) :: !errors
      | _, None -> errors := ("missing target observable value for public cell " ^ cell) :: !errors)
    (values "public_cell" fields);
  if values "public_cell" fields = [] then errors := "missing public_cell facts" :: !errors;
  List.rev !errors

let check_set_equal rule_name left_key right_key fields =
  let left = sorted_unique (values left_key fields) in
  let right = sorted_unique (values right_key fields) in
  if left = right then []
  else [ rule_name ^ " mismatch: " ^ left_key ^ "={" ^ String.concat "," left ^ "} " ^ right_key ^ "={" ^ String.concat "," right ^ "}" ]

let check_unique_commit fields =
  let commits = values "commit" fields in
  let uniques = sorted_unique commits in
  if List.length commits = List.length uniques then []
  else [ "duplicate public commit" ]

type interval = { owner : string; phys : string; start_pos : int; end_pos : int }

let parse_interval item =
  match split_once '@' item with
  | None -> None
  | Some (owner, rest) -> (
      match split_once ':' rest with
      | None -> None
      | Some (phys, range) -> (
          match split_once '.' range with
          | Some (start_raw, dot_end) when String.length dot_end >= 1 && dot_end.[0] = '.' -> (
              let end_raw = String.sub dot_end 1 (String.length dot_end - 1) |> trim in
              try Some { owner; phys; start_pos = int_of_string start_raw; end_pos = int_of_string end_raw }
              with Failure _ -> None)
          | _ -> None))

let intervals_overlap a b =
  a.phys = b.phys && a.owner <> b.owner && a.start_pos < b.end_pos && b.start_pos < a.end_pos

let check_live_interval_nonoverlap fields =
  let intervals = values "live_interval" fields |> List.filter_map parse_interval in
  let errors = ref [] in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          if intervals_overlap a b then
            errors := ("overlapping live intervals on " ^ a.phys ^ ": " ^ a.owner ^ " and " ^ b.owner) :: !errors)
        intervals)
    intervals;
  sorted_unique !errors

let check_reduction_laws fields =
  let laws = values "operator_law" fields |> sorted_unique in
  let missing =
    [ "associative"; "identity" ]
    |> List.filter (fun law -> not (List.exists (( = ) law) laws))
  in
  List.map (fun law -> "missing reduction law " ^ law) missing

let check_view_composition_bridge fields =
  let left = assignments "source_mid_final" fields |> List.sort compare in
  let right = assignments "mid_target_final" fields |> List.sort compare in
  if left = right then [] else [ "source-mid and mid-target bridge mismatch" ]

let check_frame_preserved fields =
  let before = assignments "frame_before" fields |> List.sort compare in
  let after = assignments "frame_after" fields |> List.sort compare in
  if before = after then [] else [ "protected frame changed" ]

let validate_semantics item cert =
  List.concat_map
    (function
      | "public_output_eq" -> check_public_output_eq cert.fields
      | "domain_exact_cover" -> check_set_equal "domain_exact_cover" "source_instance" "target_instance" cert.fields
      | "access_identity" -> check_set_equal "access_identity" "source_access" "target_access" cert.fields
      | "unique_commit" -> check_unique_commit cert.fields
      | "live_interval_nonoverlap" -> check_live_interval_nonoverlap cert.fields
      | "reduction_laws" -> check_reduction_laws cert.fields
      | "view_composition_bridge" -> check_view_composition_bridge cert.fields
      | "frame_preserved" -> check_frame_preserved cert.fields
      | rule -> [ "unknown semantic rule " ^ rule ])
    item.semantic_rules

let validate_cert registry cert =
  let structural_errors = validate_structure registry cert in
  let semantic_errors =
    match values "case" cert.fields with
    | name :: _ -> (
        match List.find_opt (fun item -> item.name = name) registry with
        | Some item -> validate_semantics item cert
        | None -> [])
    | [] -> []
  in
  structural_errors @ semantic_errors

let expected cert =
  match values "expect" cert.fields with
  | [ "pass" ] -> Some true
  | [ "fail" ] -> Some false
  | [] -> None
  | other ->
      let joined = String.concat "," other in
      failwith ("invalid expect field in " ^ cert.path ^ ": " ^ joined)

let main () =
  let root =
    if Array.length Sys.argv >= 2 then Sys.argv.(1)
    else "cases"
  in
  let verbose =
    Array.exists (( = ) "--verbose") Sys.argv
  in
  let registry_path = Filename.concat root "registry.txt" in
  let registry = parse_registry registry_path in
  let cert_paths = collect_cert_files root in
  let checked = ref 0 in
  let positives = ref 0 in
  let negatives = ref 0 in
  let unexpected = ref [] in
  List.iter
    (fun path ->
      let cert = parse_cert path in
      let errors = validate_cert registry cert in
      let actual_pass = errors = [] in
      let expect_pass =
        match expected cert with
        | Some value -> value
        | None ->
            unexpected := (path, [ "missing expect" ]) :: !unexpected;
            actual_pass
      in
      incr checked;
      if expect_pass then incr positives else incr negatives;
      if actual_pass <> expect_pass then unexpected := (path, errors) :: !unexpected
      else if verbose then
        Printf.printf "ok %s (%s)\n" path (if actual_pass then "accepted" else "rejected"))
    cert_paths;
  Printf.printf "storage-validator: registry=%d checked=%d positives=%d negatives=%d unexpected=%d\n"
    (List.length registry) !checked !positives !negatives (List.length !unexpected);
  List.iter
    (fun (path, errors) ->
      Printf.printf "unexpected %s\n" path;
      List.iter (fun err -> Printf.printf "  - %s\n" err) errors)
    (List.rev !unexpected);
  if !unexpected = [] then 0 else 1

let () = exit (main ())
