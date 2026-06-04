type requirement =
  | RequireKey of string
  | RequireValue of string * string

type registry_case = {
  name : string;
  group : string;
  witness_kind : string;
  requirements : requirement list;
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
        { name; group; witness_kind; requirements } :: cases
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

let validate_cert registry cert =
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
