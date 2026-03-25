open Tiling_core

type second_level_case = {
  name : string;
  original_iterators : string list;
  raw_added_iterators : string list;
  raw_links : tile_link list;
  raw_schedule_rows : int list list;
  canonical_schedule_rows : int list list;
}

type hyperplane = {
  hp_name : string;
  hp_expr : affine_expr;
}

type diamond_case = {
  name : string;
  before_iterators : string list;
  midpoint_hyperplanes : hyperplane list option;
  links : tile_link list;
}

type scenario =
  | Second_level of second_level_case
  | Diamond of diamond_case

type report = {
  name : string;
  kind : string;
  ok : bool;
  notes : string list;
  canonical_added_iterators : string list;
  reordered_schedule_rows : int list list;
  matched_hyperplanes : (string * string) list;
}

let json_field_string json name =
  match Yojson.Safe.Util.member name json with
  | `String s -> s
  | _ -> raise (Validation_error ("missing string field " ^ name))

let json_field_string_list json name =
  match Yojson.Safe.Util.member name json with
  | `List xs -> List.map Yojson.Safe.Util.to_string xs
  | _ -> raise (Validation_error ("missing string-list field " ^ name))

let json_field_int_rows json name =
  match Yojson.Safe.Util.member name json with
  | `List rows ->
      List.map
        (function
          | `List xs -> List.map Yojson.Safe.Util.to_int xs
          | _ -> raise (Validation_error ("bad row in " ^ name)))
        rows
  | _ -> raise (Validation_error ("missing int-row field " ^ name))

let tile_links_field json name =
  match Yojson.Safe.Util.member name json with
  | `List xs -> List.map tile_link_of_yojson xs
  | _ -> raise (Validation_error ("missing link list field " ^ name))

let hyperplanes_field json name =
  match Yojson.Safe.Util.member name json with
  | `Null -> None
  | `List xs ->
      Some
        (List.map
           (fun item ->
             {
               hp_name = json_field_string item "name";
               hp_expr = affine_expr_of_yojson Yojson.Safe.Util.(item |> member "expr");
             })
           xs)
  | _ -> raise (Validation_error ("bad hyperplane field " ^ name))

let scenario_of_yojson json =
  match json_field_string json "kind" with
  | "second_level" ->
      Second_level
        {
          name = json_field_string json "name";
          original_iterators = json_field_string_list json "original_iterators";
          raw_added_iterators = json_field_string_list json "raw_added_iterators";
          raw_links = tile_links_field json "raw_links";
          raw_schedule_rows = json_field_int_rows json "raw_schedule_rows";
          canonical_schedule_rows = json_field_int_rows json "canonical_schedule_rows";
        }
  | "diamond" ->
      Diamond
        {
          name = json_field_string json "name";
          before_iterators = json_field_string_list json "before_iterators";
          midpoint_hyperplanes = hyperplanes_field json "midpoint_hyperplanes";
          links = tile_links_field json "links";
        }
  | kind -> raise (Validation_error ("unknown scenario kind " ^ kind))

let rec index_of x = function
  | [] -> raise Not_found
  | y :: ys -> if x = y then 0 else 1 + index_of x ys

let sorted_strings xs = List.sort String.compare xs

let reorder_row raw_names canonical_names row =
  if List.length raw_names <> List.length row then
    raise
      (Validation_error
         (Printf.sprintf
            "schedule row width mismatch: expected %d coefficients for [%s], got %d"
            (List.length raw_names)
            (String.concat ", " raw_names)
            (List.length row)));
  let coeff_by_name = List.combine raw_names row in
  List.map (fun name -> List.assoc name coeff_by_name) canonical_names

let reorder_schedule raw_names canonical_names rows =
  List.map (reorder_row raw_names canonical_names) rows

let affine_core expr = (sorted_links [ { parent = ""; tile_size = 1; expr } ] |> List.hd).expr

let same_affine_shape_up_to_const lhs rhs =
  let norm expr =
    let sort_pairs = List.sort (fun (n1, c1) (n2, c2) -> compare_pairs String.compare Int.compare (n1, c1) (n2, c2)) in
    (sort_pairs expr.var_coeffs, sort_pairs expr.param_coeffs)
  in
  norm lhs = norm rhs

let validate_second_level (case_ : second_level_case) =
  let canonical_links =
    canonicalize_links case_.original_iterators case_.raw_added_iterators case_.raw_links
  in
  let canonical_added_iterators = List.map (fun link -> link.parent) canonical_links in
  let raw_set = sorted_strings case_.raw_added_iterators in
  let canonical_set = sorted_strings canonical_added_iterators in
  if raw_set <> canonical_set then
    raise
      (Validation_error
         (Printf.sprintf
            "raw added iterators [%s] do not match canonicalized parents [%s]"
            (String.concat ", " raw_set)
            (String.concat ", " canonical_set)));
  let raw_names = case_.raw_added_iterators @ case_.original_iterators in
  let canonical_names = canonical_added_iterators @ case_.original_iterators in
  let reordered_schedule_rows =
    reorder_schedule raw_names canonical_names case_.raw_schedule_rows
  in
  let ok = reordered_schedule_rows = case_.canonical_schedule_rows in
  let permutation_notes =
    List.map
      (fun name ->
        let raw_idx = index_of name case_.raw_added_iterators in
        let canonical_idx = index_of name canonical_added_iterators in
        Printf.sprintf "added dim %s: raw position %d -> canonical position %d" name raw_idx canonical_idx)
      case_.raw_added_iterators
  in
  let notes =
    [
      Printf.sprintf "canonical added iterators: [%s]" (String.concat ", " canonical_added_iterators);
      "ordered links:";
    ]
    @ List.map
        (fun link ->
          Printf.sprintf "  %s = floor((%s) / %d)" link.parent (expr_render link.expr) link.tile_size)
        canonical_links
    @ permutation_notes
    @
    if ok then
      [ "raw-order to canonical-order schedule bridge reconstructed the expected canonical schedule" ]
    else
      [ "reordered raw schedule does not match the expected canonical schedule" ]
  in
  {
    name = case_.name;
    kind = "second_level";
    ok;
    notes;
    canonical_added_iterators;
    reordered_schedule_rows;
    matched_hyperplanes = [];
  }

let validate_diamond (case_ : diamond_case) =
  let midpoint =
    match case_.midpoint_hyperplanes with
    | Some hs -> hs
    | None -> raise (Validation_error "diamond validation requires an explicit midpoint hyperplane set")
  in
  List.iter
    (fun hp ->
      let unknown =
        List.filter (fun dep -> not (List.mem dep case_.before_iterators)) (expr_dependencies hp.hp_expr)
      in
      if unknown <> [] then
        raise
          (Validation_error
             (Printf.sprintf
                "midpoint hyperplane %s depends on variables outside before-iterators [%s]"
                hp.hp_name
                (String.concat ", " unknown))))
    midpoint;
  let matched_hyperplanes =
    List.map
      (fun link ->
        if link.tile_size <= 0 then
          raise (Validation_error (Printf.sprintf "tile size for %s is not positive" link.parent));
        match List.find_opt (fun hp -> same_affine_shape_up_to_const hp.hp_expr link.expr) midpoint with
        | Some hp -> (link.parent, hp.hp_name)
        | None ->
            raise
              (Validation_error
                 (Printf.sprintf
                    "tile link %s = floor((%s) / %d) does not match any midpoint hyperplane"
                    link.parent
                    (expr_render link.expr)
                    link.tile_size)))
      case_.links
  in
  {
    name = case_.name;
    kind = "diamond";
    ok = true;
    notes =
      [ Printf.sprintf "midpoint hyperplanes: %d" (List.length midpoint) ]
      @ List.map
          (fun (parent, hp_name) ->
            Printf.sprintf "tile link %s is justified by midpoint hyperplane %s" parent hp_name)
          matched_hyperplanes
      @
      [
        "diamond case accepted as: checked affine midpoint + ordinary affine floor-link tiling";
      ];
    canonical_added_iterators = [];
    reordered_schedule_rows = [];
    matched_hyperplanes;
  }

let validate_scenario = function
  | Second_level case_ -> validate_second_level case_
  | Diamond case_ -> validate_diamond case_

let report_to_yojson report =
  `Assoc
    [
      ("name", `String report.name);
      ("kind", `String report.kind);
      ("ok", `Bool report.ok);
      ("notes", `List (List.map (fun note -> `String note) report.notes));
      ( "canonical_added_iterators",
        `List (List.map (fun name -> `String name) report.canonical_added_iterators) );
      ( "reordered_schedule_rows",
        `List
          (List.map
             (fun row -> `List (List.map (fun coeff -> `Int coeff) row))
             report.reordered_schedule_rows) );
      ( "matched_hyperplanes",
        `List
          (List.map
             (fun (parent, hp_name) -> `Assoc [ ("parent", `String parent); ("hyperplane", `String hp_name) ])
             report.matched_hyperplanes) );
    ]

let render_report report =
  let header =
    [
      Printf.sprintf "case:   %s" report.name;
      Printf.sprintf "kind:   %s" report.kind;
      Printf.sprintf "result: %s" (if report.ok then "PASS" else "FAIL");
    ]
  in
  let extras =
    if report.canonical_added_iterators = [] then []
    else
      [
        Printf.sprintf
          "canonical added iterators: [%s]"
          (String.concat ", " report.canonical_added_iterators);
      ]
  in
  String.concat "\n" (header @ extras @ ("" :: List.map (fun note -> "note: " ^ note) report.notes))
