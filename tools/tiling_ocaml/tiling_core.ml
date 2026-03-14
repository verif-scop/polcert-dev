type relation_meta = {
  nrows : int;
  ncols : int;
  output_dims : int;
  input_dims : int;
  local_dims : int;
  param_dims : int;
}

type relation = {
  kind : string;
  meta : relation_meta;
  rows : int list list;
  output_names : string list;
  input_names : string list;
  param_names : string list;
}

type access_relation = {
  kind : string;
  relation : relation;
}

type statement = {
  index : int;
  domain : relation option;
  scattering : relation option;
  accesses : access_relation list;
  iterators : string list;
  body : string;
}

type scop = {
  path : string;
  params : string list;
  statements : statement list;
}

type affine_expr = {
  var_coeffs : (string * int) list;
  param_coeffs : (string * int) list;
  const : int;
}

type tile_link = {
  parent : string;
  expr : affine_expr;
  tile_size : int;
}

type statement_tiling_witness = {
  statement : int;
  original_iterators : string list;
  tiled_iterators : string list;
  added_iterators : string list;
  links : tile_link list;
}

type tiling_witness = {
  before : string;
  after : string;
  params : string list;
  statements : statement_tiling_witness list;
}

type statement_validation = {
  statement : int;
  original_iterators : string list;
  tiled_iterators : string list;
  added_iterators : string list;
  links : tile_link list;
  shape_ok : bool;
  transformation_contract_ok : bool;
  witness_match_ok : bool;
  base_domain_ok : bool;
  link_rows_ok : bool;
  access_ok : bool;
  compiled_relation_ok : bool;
  schedule_sanity_ok : bool;
  bounded_coverage_ok : bool option;
  notes : string list;
}

type validation_report = {
  before : string;
  after : string;
  params : (string * int) list;
  ok : bool;
  witness_source : string;
  statements : statement_validation list;
  limitations : string list;
}

exception Validation_error of string

module StringMap = Map.Make (String)

let split_words s =
  let flush acc buf =
    if Buffer.length buf = 0 then acc
    else
      let word = Buffer.contents buf in
      Buffer.clear buf;
      word :: acc
  in
  let buf = Buffer.create 16 in
  let rec loop i acc =
    if i = String.length s then List.rev (flush acc buf)
    else
      match s.[i] with
      | ' ' | '\t' | '\n' | '\r' -> loop (i + 1) (flush acc buf)
      | c ->
          Buffer.add_char buf c;
          loop (i + 1) acc
  in
  loop 0 []

let starts_with ~prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix

let trim = String.trim

let next_nonempty lines start =
  let rec loop i =
    if i >= Array.length lines then i
    else if trim lines.(i) = "" then loop (i + 1)
    else i
  in
  loop start

let int_list_of_line line =
  split_words line |> List.map int_of_string

let parse_relation_names kind comment_line =
  let text =
    let text = trim comment_line in
    if starts_with ~prefix:"#" text then trim (String.sub text 1 (String.length text - 1))
    else text
  in
  let segments = String.split_on_char '|' text |> List.map trim in
  let take_groups acc = function
    | [] | [ _ ] -> List.rev acc
    | _ :: mid ->
        let mid =
          match List.rev mid with
          | _ :: rev_rest -> List.rev rev_rest
          | [] -> []
        in
        List.rev_append acc (List.filter (fun seg -> seg <> "") mid)
  in
  let groups = take_groups [] segments in
  let words seg = split_words seg in
  match kind with
  | "DOMAIN" ->
      let output_names =
        match groups with
        | g :: _ -> words g
        | [] -> []
      in
      let param_names =
        match groups with
        | _ :: g :: _ -> words g
        | _ -> []
      in
      (output_names, [], param_names)
  | _ ->
      let output_names =
        match groups with
        | g :: _ -> words g
        | [] -> []
      in
      let input_names =
        match groups with
        | _ :: g :: _ -> words g
        | _ -> []
      in
      let param_names =
        match groups with
        | _ :: _ :: g :: _ -> words g
        | _ -> []
      in
      (output_names, input_names, param_names)

let parse_relation lines start kind =
  let i = next_nonempty lines start in
  if i >= Array.length lines then raise (Validation_error ("missing relation header after " ^ kind));
  let meta_vals = int_list_of_line (trim lines.(i)) in
  let meta =
    match meta_vals with
    | [ nrows; ncols; output_dims; input_dims; local_dims; param_dims ] ->
        { nrows; ncols; output_dims; input_dims; local_dims; param_dims }
    | _ -> raise (Validation_error ("bad relation header after " ^ kind ^ ": " ^ lines.(i)))
  in
  let i = next_nonempty lines (i + 1) in
  if i >= Array.length lines then raise (Validation_error ("missing relation names comment for " ^ kind));
  let comment_line = trim lines.(i) in
  if not (starts_with ~prefix:"#" comment_line) then
    raise (Validation_error ("missing relation names comment for " ^ kind));
  let output_names, input_names, param_names = parse_relation_names kind comment_line in
  let rec collect_rows j acc =
    if List.length acc = meta.nrows then
      ({ kind; meta; rows = List.rev acc; output_names; input_names; param_names }, j)
    else
      let j = next_nonempty lines j in
      if j >= Array.length lines then raise (Validation_error ("missing rows for " ^ kind));
      let raw = lines.(j) in
      let body =
        match String.split_on_char '#' raw with
        | [] -> ""
        | piece :: _ -> trim piece
      in
      let row = int_list_of_line body in
      if List.length row <> meta.ncols then
        raise
          (Validation_error
             (Printf.sprintf "row width mismatch for %s: expected %d got %d in %s"
                kind meta.ncols (List.length row) raw));
      collect_rows (j + 1) (row :: acc)
  in
  collect_rows (i + 1) []

let read_lines path =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
  loop []

let parse_scop path =
  let lines = Array.of_list (read_lines path) in
  let params = ref [] in
  let statements = ref [] in
  let current = ref None in
  let flush_current () =
    match !current with
    | None -> ()
    | Some stmt ->
        statements := stmt :: !statements;
        current := None
  in
  let update_current f =
    match !current with
    | None -> raise (Validation_error ("relation outside statement in " ^ path))
    | Some stmt -> current := Some (f stmt)
  in
  let rec skip_until closing i =
    if i >= Array.length lines then i
    else if trim lines.(i) = closing then i
    else skip_until closing (i + 1)
  in
  let rec loop i =
    if i >= Array.length lines then ()
    else
      let line = trim lines.(i) in
      if line = "<strings>" && !params = [] then
        let rec collect_strings j acc =
          if j >= Array.length lines then raise (Validation_error ("unterminated <strings> in " ^ path))
          else if trim lines.(j) = "</strings>" then (params := List.rev acc; loop (j + 1))
          else collect_strings (j + 1) (List.rev_append (split_words lines.(j)) acc)
        in
        collect_strings (i + 1) []
      else if starts_with ~prefix:"# =============================================== Statement" line then (
        flush_current ();
        current :=
          Some
            {
              index = List.length !statements + 1;
              domain = None;
              scattering = None;
              accesses = [];
              iterators = [];
              body = "";
            };
        loop (i + 1))
      else if List.mem line [ "DOMAIN"; "SCATTERING"; "READ"; "WRITE" ] then
        let relation, j = parse_relation lines (i + 1) line in
        update_current (fun stmt ->
            match line with
            | "DOMAIN" -> { stmt with domain = Some relation }
            | "SCATTERING" -> { stmt with scattering = Some relation }
            | "READ" | "WRITE" -> { stmt with accesses = stmt.accesses @ [ { kind = line; relation } ] }
            | _ -> stmt);
        loop j
      else if line = "<body>" then
        let rec collect_body j iterators body =
          if j >= Array.length lines then raise (Validation_error ("unterminated <body> in " ^ path))
          else
            let line = trim lines.(j) in
            if line = "</body>" then (
              update_current (fun stmt -> { stmt with iterators; body });
              loop (j + 1))
            else if line = "# List of original iterators" then
              collect_body (j + 2) (split_words lines.(j + 1)) body
            else if line = "# Statement body expression" then
              collect_body (j + 2) iterators (trim lines.(j + 1))
            else collect_body (j + 1) iterators body
        in
        collect_body (i + 1) [] ""
      else if line = "<loop>" then loop (skip_until "</loop>" (i + 1) + 1)
      else loop (i + 1)
  in
  loop 0;
  flush_current ();
  { path; params = !params; statements = List.rev !statements }

let counter_add map key =
  let count = match StringMap.find_opt key map with Some n -> n | None -> 0 in
  StringMap.add key (count + 1) map

let row_key row = String.concat "," (List.map string_of_int row)

let counter_of_rows rows = List.fold_left (fun acc row -> counter_add acc (row_key row)) StringMap.empty rows

let compare_counters a b = StringMap.equal Int.equal a b

let assoc_default name pairs =
  match List.assoc_opt name pairs with
  | Some v -> v
  | None -> raise (Validation_error ("missing value for " ^ name))

let make_affine_expr coeffs var_names param_coeffs param_names const =
  let var_coeffs =
    List.filter_map
      (fun (name, coeff) -> if coeff = 0 then None else Some (name, coeff))
      (List.combine var_names coeffs)
  in
  let param_coeffs =
    List.filter_map
      (fun (name, coeff) -> if coeff = 0 then None else Some (name, coeff))
      (List.combine param_names param_coeffs)
  in
  { var_coeffs; param_coeffs; const }

let expr_dependencies expr = List.map fst expr.var_coeffs

let rec list_take n xs =
  if n <= 0 then []
  else
    match xs with
    | [] -> []
    | x :: xs' -> x :: list_take (n - 1) xs'

let rec list_drop n xs =
  if n <= 0 then xs
  else
    match xs with
    | [] -> []
    | _ :: xs' -> list_drop (n - 1) xs'

let rec list_map3 f xs ys zs =
  match (xs, ys, zs) with
  | [], [], [] -> []
  | x :: xs', y :: ys', z :: zs' -> f x y z :: list_map3 f xs' ys' zs'
  | _ -> invalid_arg "list_map3"

let delete_domain_added_coeffs row added_count after_var_count param_count =
  let flag = List.hd row in
  let vars_after = list_take after_var_count (list_drop 1 row) in
  let params = list_take param_count (list_drop (1 + after_var_count) row) in
  let const = List.hd (List.rev row) in
  [ flag ] @ list_drop added_count vars_after @ params @ [ const ]

let delete_access_added_coeffs row output_dims input_dims_after added_count param_dims =
  let flag = List.hd row in
  let outs = list_take output_dims (list_drop 1 row) in
  let ins = list_take input_dims_after (list_drop (1 + output_dims) row) in
  let params = list_take param_dims (list_drop (1 + output_dims + input_dims_after) row) in
  let const = List.hd (List.rev row) in
  ([ flag ] @ outs @ list_drop added_count ins @ params @ [ const ], list_take added_count ins)

let classify_tile_link_row row var_names added_names param_names =
  match row with
  | flag :: rest when flag = 1 ->
      let coeffs = list_take (List.length var_names) rest in
      let params = list_take (List.length param_names) (list_drop (List.length var_names) rest) in
      let const = List.hd (List.rev row) in
      let parent_positions =
        List.filter_map
          (fun (idx, (name, coeff)) ->
            if List.mem name added_names && abs coeff >= 2 then Some idx else None)
          (List.mapi (fun idx pair -> (idx, pair)) (List.combine var_names coeffs))
      in
      begin
        match parent_positions with
        | [ parent_idx ] ->
            let parent_name = List.nth var_names parent_idx in
            let parent_coeff = List.nth coeffs parent_idx in
            let tile_size = abs parent_coeff in
            let residual_coeffs =
              List.mapi (fun idx coeff -> if idx = parent_idx then 0 else coeff) coeffs
            in
            if parent_coeff < 0 then
              Some
                ( (parent_name, tile_size, make_affine_expr residual_coeffs var_names params param_names const),
                  "lb" )
            else
              let neg xs = List.map (fun x -> -x) xs in
              Some
                ( ( parent_name,
                    tile_size,
                    make_affine_expr (neg residual_coeffs) var_names (neg params) param_names
                      (tile_size - 1 - const) ),
                  "ub" )
        | _ -> None
      end
  | _ -> None

let compare_pairs compare_a compare_b (a1, b1) (a2, b2) =
  let c = compare_a a1 a2 in
  if c <> 0 then c else compare_b b1 b2

let compare_affine_expr a b =
  compare_pairs Stdlib.compare
    (compare_pairs Stdlib.compare Stdlib.compare)
    (a.var_coeffs, (a.param_coeffs, a.const))
    (b.var_coeffs, (b.param_coeffs, b.const))

let compare_tile_link a b =
  compare_pairs String.compare
    (compare_pairs Int.compare compare_affine_expr)
    (a.parent, (a.tile_size, a.expr))
    (b.parent, (b.tile_size, b.expr))

let sorted_links links = List.sort compare_tile_link links

let canonicalize_links original_iterators added_iterators links =
  let rec loop available pending acc =
    match pending with
    | [] ->
        let ordered = List.rev acc in
        let parents = List.sort String.compare (List.map (fun link -> link.parent) ordered) in
        let expected = List.sort String.compare added_iterators in
        if parents <> expected then
          raise (Validation_error "ordered tile-link parents do not cover added iterators");
        ordered
    | _ ->
        let ready, _blocked =
          List.partition
            (fun link ->
              List.for_all (fun dep -> List.mem dep available) (expr_dependencies link.expr))
            pending
        in
        if ready = [] then
          let unresolved =
            String.concat ", "
              (List.map
                 (fun link -> Printf.sprintf "%s/?/%d" link.parent link.tile_size)
                 (sorted_links pending))
          in
          raise (Validation_error ("cannot topologically order tile links: " ^ unresolved))
        else
          let chosen = List.hd (sorted_links ready) in
          loop (available @ [ chosen.parent ]) (List.filter (( <> ) chosen) pending) (chosen :: acc)
  in
  loop original_iterators links []

let canonical_statement_links original_iterators added_iterators links =
  canonicalize_links original_iterators added_iterators links

let expr_render expr =
  let render_term (name, coeff) =
    if coeff = 1 then name
    else if coeff = -1 then "-" ^ name
    else Printf.sprintf "%d*%s" coeff name
  in
  let parts =
    List.filter_map
      (fun term ->
        let text = render_term term in
        if text = "0*" then None else Some text)
      (expr.var_coeffs @ expr.param_coeffs)
  in
  let parts = if expr.const <> 0 then parts @ [ string_of_int expr.const ] else parts in
  match parts with
  | [] -> "0"
  | first :: rest ->
      List.fold_left
        (fun acc item ->
          if starts_with ~prefix:"-" item then acc ^ " - " ^ String.sub item 1 (String.length item - 1)
          else acc ^ " + " ^ item)
        first rest

let check_statement_shape (before : statement) (after : statement) =
  let before_domain = match before.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let after_domain = match after.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  let notes = ref [] in
  let ok = ref true in
  if List.length after_vars < List.length before_vars then (
    ok := false;
    notes := Printf.sprintf "statement %d: after has fewer iterators than before" before.index :: !notes)
  else if list_drop (List.length after_vars - List.length before_vars) after_vars <> before_vars then (
    ok := false;
    notes :=
      Printf.sprintf
        "statement %d: tiled iterators do not end with the original iterators"
        before.index
      :: !notes);
  (!ok, List.rev !notes)

let check_transformation_contract original_iterators tiled_iterators added_iterators links statement_id =
  let notes = ref [] in
  let ok = ref true in
  if tiled_iterators <> added_iterators @ original_iterators then (
    ok := false;
    notes :=
      Printf.sprintf
        "statement %d: tiled iterator order is not added_iterators ++ original_iterators"
        statement_id
      :: !notes);
  let parents = List.map (fun link -> link.parent) links in
  if parents <> added_iterators then (
    ok := false;
    notes :=
      Printf.sprintf
        "statement %d: ordered tile-link parents do not match added iterators"
        statement_id
      :: !notes);
  let seen = ref original_iterators in
  List.iter
    (fun link ->
      if link.tile_size <= 0 then (
        ok := false;
        notes := Printf.sprintf "statement %d: tile size for %s is not positive" statement_id link.parent :: !notes);
      let unknown = List.filter (fun dep -> not (List.mem dep !seen)) (expr_dependencies link.expr) in
      if unknown <> [] then (
        ok := false;
        notes :=
          Printf.sprintf
            "statement %d: tile link %s depends on unresolved iterators [%s]"
            statement_id link.parent (String.concat ", " unknown)
          :: !notes);
      if List.mem link.parent !seen then (
        ok := false;
        notes :=
          Printf.sprintf
            "statement %d: tile parent %s is not fresh in ordered links"
            statement_id link.parent
          :: !notes);
      seen := !seen @ [ link.parent ])
    links;
  (!ok, List.rev !notes)

let check_pinstr_shape = check_statement_shape

let check_domain_and_infer_links before after =
  let before_domain =
    match before.domain with Some d -> d | None -> raise (Validation_error "missing domain relation")
  in
  let after_domain =
    match after.domain with Some d -> d | None -> raise (Validation_error "missing domain relation")
  in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  if List.length after_vars < List.length before_vars then
    raise (Validation_error (Printf.sprintf "statement %d: after has fewer iterators than before" before.index));
  let added_count = List.length after_vars - List.length before_vars in
  let after_suffix = list_drop added_count after_vars in
  if after_suffix <> before_vars then
    raise
      (Validation_error
         (Printf.sprintf
            "statement %d: expected tiled iterators to end with original iterators"
            before.index));
  let before_counter = counter_of_rows before_domain.rows in
  let after_base_counter = ref StringMap.empty in
  let link_rows = ref [] in
  List.iter
    (fun row ->
      let coeffs_added = list_take added_count (list_drop 1 row) in
      if List.for_all (( = ) 0) coeffs_added then
        let reduced =
          delete_domain_added_coeffs row added_count (List.length after_vars) (List.length before_domain.param_names)
        in
        after_base_counter := counter_add !after_base_counter (row_key reduced)
      else link_rows := row :: !link_rows)
    after_domain.rows;
  let base_ok = compare_counters before_counter !after_base_counter in
  let notes = ref [] in
  if not base_ok then
    notes :=
      Printf.sprintf
        "statement %d: lifted base-domain rows do not match before-domain rows"
        before.index
      :: !notes;
  let added_names = list_take added_count after_vars in
  let pair_kinds = Hashtbl.create 8 in
  let unsupported = ref false in
  List.iter
    (fun row ->
      match classify_tile_link_row row after_vars added_names before_domain.param_names with
      | None ->
          notes :=
            Printf.sprintf "statement %d: unsupported non-base row in tiled domain" before.index :: !notes;
          unsupported := true
      | Some ((parent, tile_size, expr), kind) ->
          let key =
            parent ^ "|" ^ string_of_int tile_size ^ "|" ^ expr_render expr
          in
          let kinds = match Hashtbl.find_opt pair_kinds key with Some ks -> ks | None -> [] in
          Hashtbl.replace pair_kinds key ((parent, tile_size, expr, kind) :: kinds))
    !link_rows;
  if !unsupported then (base_ok, false, [], List.rev !notes)
  else
    let links = ref [] in
    Hashtbl.iter
      (fun _ entries ->
        match entries with
        | [] -> ()
        | (parent, tile_size, expr, _) :: _ ->
            let kinds = List.sort String.compare (List.map (fun (_, _, _, kind) -> kind) entries) in
            if kinds <> [ "lb"; "ub" ] then
              notes :=
                Printf.sprintf "statement %d: incomplete tile-link pair for %s" before.index parent :: !notes
            else if List.mem parent (expr_dependencies expr) then
              notes :=
                Printf.sprintf "statement %d: tile parent %s occurs in its own affine expression" before.index parent
                :: !notes
            else links := { parent; tile_size; expr } :: !links)
      pair_kinds;
    let links = sorted_links !links in
    let parent_set = List.sort String.compare (List.map (fun link -> link.parent) links) in
    let added_names = List.sort String.compare added_names in
    let links_ok = !notes = [] && parent_set = added_names in
    if parent_set <> added_names then
      notes :=
        Printf.sprintf "statement %d: tile parents do not cover all added iterators" before.index :: !notes;
    (base_ok, links_ok, canonical_statement_links before_vars (list_take added_count after_vars) links, List.rev !notes)

let check_pinstr_links = check_domain_and_infer_links

let evaluate_affine_expr expr values params =
  let total = ref expr.const in
  List.iter (fun (name, coeff) -> total := !total + (coeff * assoc_default name values)) expr.var_coeffs;
  List.iter (fun (name, coeff) -> total := !total + (coeff * assoc_default name params)) expr.param_coeffs;
  !total

let check_accesses before after added_count =
  let notes = ref [] in
  let ok = ref true in
  if List.length before.accesses <> List.length after.accesses then
    ( false,
      [
        Printf.sprintf "statement %d: access count changed from %d to %d" before.index
          (List.length before.accesses) (List.length after.accesses);
      ] )
  else (
    List.iter2
      (fun b_acc a_acc ->
        if b_acc.kind <> a_acc.kind then (
          notes := Printf.sprintf "statement %d: access kind changed" before.index :: !notes;
          ok := false)
        else
          let b = b_acc.relation in
          let a = a_acc.relation in
          if a.meta.input_dims <> b.meta.input_dims + added_count then (
            notes :=
              Printf.sprintf "statement %d: access expected %d input dims, got %d" before.index
                (b.meta.input_dims + added_count) a.meta.input_dims
              :: !notes;
            ok := false)
          else (
            let reduced_counter = ref StringMap.empty in
            List.iter
              (fun row ->
                let reduced, added =
                  delete_access_added_coeffs row a.meta.output_dims a.meta.input_dims added_count a.meta.param_dims
                in
                if List.exists (( <> ) 0) added then (
                  notes :=
                    Printf.sprintf "statement %d: access uses added tile iterators directly" before.index
                    :: !notes;
                  ok := false);
                reduced_counter := counter_add !reduced_counter (row_key reduced))
              a.rows;
            if not (compare_counters !reduced_counter (counter_of_rows b.rows)) then (
              notes :=
                Printf.sprintf "statement %d: access rows changed after removing added tile iterators" before.index
                :: !notes;
              ok := false)))
      before.accesses after.accesses;
    (!ok, List.rev !notes))

let check_pinstr_accesses = check_accesses

let check_scattering_sanity before after added_count =
  match (before.scattering, after.scattering) with
  | Some b, Some a ->
      let notes = ref [] in
      if a.meta.input_dims <> b.meta.input_dims + added_count then
        ( false,
          [
            Printf.sprintf
              "statement %d: scattering input dims %d do not match before+added (%d+%d)"
              before.index a.meta.input_dims b.meta.input_dims added_count;
          ] )
      else if a.meta.output_dims < a.meta.input_dims then
        ( false,
          [
            Printf.sprintf "statement %d: scattering output dims %d are fewer than scattering input dims %d"
              before.index a.meta.output_dims a.meta.input_dims;
          ] )
      else if List.exists (fun row -> match row with flag :: _ -> flag <> 0 | [] -> true) a.rows then
        (false, [ Printf.sprintf "statement %d: scattering contains non-equality rows" before.index ])
      else (
        if a.meta.output_dims < b.meta.output_dims then
          notes :=
            Printf.sprintf
              "statement %d: after scattering compresses source-style separator dimensions (%d -> %d)"
              before.index b.meta.output_dims a.meta.output_dims
            :: !notes;
        (true, List.rev !notes))
  | _ -> (false, [ Printf.sprintf "statement %d: missing scattering relation" before.index ])

let check_pinstr_schedule_sanity = check_scattering_sanity

let check_pinstr_transformation_contract = check_transformation_contract

let row_satisfied row values var_names params param_names =
  let coeffs = list_take (List.length var_names) (list_drop 1 row) in
  let pcoeffs =
    list_take (List.length param_names) (list_drop (1 + List.length var_names) row)
  in
  let total =
    List.fold_left2 (fun acc name coeff -> acc + (coeff * assoc_default name values)) 0 var_names coeffs
    + List.fold_left2 (fun acc name coeff -> acc + (coeff * assoc_default name params)) 0 param_names pcoeffs
    + List.hd (List.rev row)
  in
  match row with
  | flag :: _ -> if flag = 0 then total = 0 else total >= 0
  | [] -> false

let ceil_div a b =
  if b <= 0 then raise (Validation_error "ceil_div expects positive divisor");
  if a >= 0 then (a + b - 1) / b else -((-a) / b)

let floor_div a b =
  if b <= 0 then raise (Validation_error "floor_div expects positive divisor");
  if a >= 0 then a / b else -(((-a) + b - 1) / b)

let infer_before_bounds statement params =
  let domain = match statement.domain with Some d -> d | None -> raise (Validation_error "missing before domain") in
  let var_names = if domain.output_names <> [] then domain.output_names else statement.iterators in
  let initial_hi =
    match List.map snd params with
    | [] -> 16
    | xs -> List.fold_left max 16 xs
  in
  let bounds = Hashtbl.create 8 in
  List.iter (fun name -> Hashtbl.replace bounds name (0, initial_hi)) var_names;
  List.iter
    (fun row ->
      let coeffs = list_take (List.length var_names) (list_drop 1 row) in
      let nz =
        List.filter_map
          (fun (name, coeff) -> if coeff <> 0 then Some (name, coeff) else None)
          (List.combine var_names coeffs)
      in
      match nz with
      | [ (name, coeff) ] ->
          let pcoeffs =
            list_take (List.length domain.param_names) (list_drop (1 + List.length var_names) row)
          in
          let rest =
            List.fold_left2
              (fun acc pname pcoeff -> acc + (pcoeff * assoc_default pname params))
              (List.hd (List.rev row)) domain.param_names pcoeffs
          in
          begin
            match row with
            | flag :: _ when flag = 1 ->
                let lb, ub = match Hashtbl.find_opt bounds name with Some b -> b | None -> (0, initial_hi) in
                if coeff > 0 then Hashtbl.replace bounds name (max lb (ceil_div (-rest) coeff), ub)
                else if coeff < 0 then Hashtbl.replace bounds name (lb, min ub (floor_div rest (-coeff)))
            | _ -> ()
          end
      | _ -> ())
    domain.rows;
  List.map
    (fun name ->
      let lb, ub = match Hashtbl.find_opt bounds name with Some b -> b | None -> (0, initial_hi) in
      if lb > ub then raise (Validation_error (Printf.sprintf "empty inferred bound for %s: %d..%d" name lb ub));
      (name, (lb, ub)))
    var_names

let rec cartesian_product = function
  | [] -> [ [] ]
  | (name, (lb, ub)) :: rest ->
      let tails = cartesian_product rest in
      let rec range i acc = if i < lb then acc else range (i - 1) (i :: acc) in
      List.concat_map
        (fun value -> List.map (fun tail -> (name, value) :: tail) tails)
        (range ub [])

let check_bounded_coverage before after links params =
  let before_domain = match before.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let after_domain = match after.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  let bounds = infer_before_bounds before params in
  let count = ref 0 in
  let rec resolve_links values pending =
    match pending with
    | [] -> values
    | _ ->
        let ready, blocked =
          List.partition
            (fun link -> List.for_all (fun name -> List.mem_assoc name values) (expr_dependencies link.expr))
            pending
        in
        if ready = [] then
          raise (Validation_error "cannot resolve tile links during bounded coverage");
        let values =
          List.fold_left
            (fun acc link ->
              let expr_value = evaluate_affine_expr link.expr acc params in
              acc @ [ (link.parent, floor_div expr_value link.tile_size) ])
            values ready
        in
        resolve_links values blocked
  in
  try
    List.iter
      (fun point ->
        if List.for_all (fun row -> row_satisfied row point before_vars params before_domain.param_names) before_domain.rows then (
          let tiled_env = resolve_links point links in
          if not (List.for_all (fun row -> row_satisfied row tiled_env after_vars params after_domain.param_names) after_domain.rows)
          then raise (Validation_error "tiled lift failed during bounded coverage");
          incr count))
      (cartesian_product bounds);
    (true, [ Printf.sprintf "statement %d: checked bounded coverage on %d original points" before.index !count ])
  with Validation_error msg -> (false, [ Printf.sprintf "statement %d: %s" before.index msg ])

let require_same_program_shape (before : scop) (after : scop) =
  if List.length before.statements <> List.length after.statements then
    raise
      (Validation_error
         (Printf.sprintf "statement count mismatch: before has %d, after has %d"
            (List.length before.statements) (List.length after.statements)));
  if before.params <> after.params then
    raise
      (Validation_error
         (Printf.sprintf "parameter mismatch: before=%s after=%s"
            (String.concat "," before.params) (String.concat "," after.params)));
  List.iter2
    (fun b a ->
      if b.body <> "" && a.body <> "" && b.body <> a.body then
        raise
          (Validation_error
             (Printf.sprintf "statement body mismatch for statement %d" b.index)))
    before.statements after.statements

let infer_statement_witness before after =
  let before_domain = match before.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let after_domain = match after.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  let base_ok, links_ok, links, notes = check_domain_and_infer_links before after in
  if not base_ok || not links_ok then
    raise
      (Validation_error
         (Printf.sprintf "statement %d: cannot infer tiling witness: %s" before.index
            (String.concat "; " notes)));
  let added_count = List.length after_vars - List.length before_vars in
  {
    statement = before.index;
    original_iterators = before_vars;
    tiled_iterators = after_vars;
    added_iterators = list_take added_count after_vars;
    links = canonical_statement_links before_vars (list_take added_count after_vars) links;
  }

let infer_tiling_witness before_path after_path =
  let before = parse_scop before_path in
  let after = parse_scop after_path in
  require_same_program_shape before after;
  {
    before = before_path;
    after = after_path;
    params = before.params;
    statements = List.map2 infer_statement_witness before.statements after.statements;
  }

let check_witness_matches (before : statement) (after : statement)
    (witness : statement_tiling_witness) actual_links =
  let before_domain = match before.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let after_domain = match after.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  let added_count = max 0 (List.length after_vars - List.length before_vars) in
  let notes = ref [] in
  let ok = ref true in
  if witness.statement <> before.index then (
    ok := false;
    notes := Printf.sprintf "statement %d: witness statement id is %d" before.index witness.statement :: !notes);
  if witness.original_iterators <> before_vars then (
    ok := false;
    notes := Printf.sprintf "statement %d: witness original iterators do not match actual" before.index :: !notes);
  if witness.tiled_iterators <> after_vars then (
    ok := false;
    notes := Printf.sprintf "statement %d: witness tiled iterators do not match actual" before.index :: !notes);
  if witness.added_iterators <> list_take added_count after_vars then (
    ok := false;
    notes := Printf.sprintf "statement %d: witness added iterators do not match actual" before.index :: !notes);
  if
    canonical_statement_links before_vars (list_take added_count after_vars) witness.links
    <> canonical_statement_links before_vars (list_take added_count after_vars) actual_links
  then (
    ok := false;
    notes := Printf.sprintf "statement %d: witness tile links do not match inferred tile links" before.index :: !notes);
  (!ok, List.rev !notes)

let check_pinstr_tiling (before : statement) (after : statement)
    (witness : statement_tiling_witness option) params check_coverage =
  let before_domain = match before.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let after_domain = match after.domain with Some d -> d | None -> raise (Validation_error "missing domain") in
  let before_vars = if before_domain.output_names <> [] then before_domain.output_names else before.iterators in
  let after_vars = if after_domain.output_names <> [] then after_domain.output_names else after.iterators in
  let added_count = max 0 (List.length after_vars - List.length before_vars) in
  let shape_ok, notes0 = check_pinstr_shape before after in
  let base_ok, links_ok, links, notes1 =
    if shape_ok then check_pinstr_links before after else (false, false, [], [])
  in
  let access_ok, notes2 = check_pinstr_accesses before after added_count in
  let schedule_ok, notes3 = check_pinstr_schedule_sanity before after added_count in
  let witness_ok, notes4, coverage_links =
    match witness with
    | None -> (true, [], links)
    | Some w ->
        let ok, notes = check_witness_matches before after w links in
        (ok, notes, canonical_statement_links before_vars (list_take added_count after_vars) w.links)
  in
  let transformation_ok, notes5 =
    check_pinstr_transformation_contract before_vars after_vars (list_take added_count after_vars) coverage_links before.index
  in
  let compiled_relation_ok =
    shape_ok
    && transformation_ok
    && base_ok
    && links_ok
    && access_ok
    &&
    match witness with
    | None -> true
    | Some _ -> witness_ok
  in
  let bounded_ok, notes6 =
    if check_coverage && compiled_relation_ok then
      let ok, notes = check_bounded_coverage before after coverage_links params in
      (Some ok, notes)
    else (None, [])
  in
  {
    statement = before.index;
    original_iterators = before_vars;
    tiled_iterators = after_vars;
    added_iterators = list_take added_count after_vars;
    links = coverage_links;
    shape_ok;
    transformation_contract_ok = transformation_ok;
    witness_match_ok = witness_ok;
    base_domain_ok = base_ok;
    link_rows_ok = links_ok;
    access_ok;
    compiled_relation_ok;
    schedule_sanity_ok = schedule_ok;
    bounded_coverage_ok = bounded_ok;
    notes = notes0 @ notes1 @ notes2 @ notes3 @ notes4 @ notes5 @ notes6;
  }

let parse_param_assignments raw =
  List.map
    (fun item ->
      match String.split_on_char '=' item with
      | [ name; value ] -> (name, int_of_string value)
      | _ -> raise (Validation_error ("bad parameter assignment " ^ item)))
    raw

let check_tiling_witness before_path after_path (witness : tiling_witness) params check_bounded_coverage =
  let before = parse_scop before_path in
  let after = parse_scop after_path in
  require_same_program_shape before after;
  if witness.params <> before.params then
    raise (Validation_error "witness parameter mismatch");
  if List.length witness.statements <> List.length before.statements then
    raise (Validation_error "witness statement count mismatch");
  if check_bounded_coverage then
    List.iter
      (fun name ->
        if not (List.mem_assoc name params) then
          raise (Validation_error ("missing parameter assignments for bounded coverage: " ^ name)))
      before.params;
  let statements =
    list_map3
      (fun b a w -> check_pinstr_tiling b a (Some w) params check_bounded_coverage)
      before.statements after.statements witness.statements
  in
  let ok =
    List.for_all
      (fun item ->
        item.compiled_relation_ok
        && item.schedule_sanity_ok
        && item.witness_match_ok
        &&
        match item.bounded_coverage_ok with
        | None -> true
        | Some v -> v)
      statements
  in
  {
    before = before_path;
    after = after_path;
    params;
    ok;
    witness_source = "provided";
    statements;
    limitations =
      [
        "prototype only targets Pluto-style affine floor-link tiling constraints";
        "transformation checking currently validates only the ordered-link contract needed by inserted-after-env lifting";
        "schedule checking is only a sanity check on arity growth, not a full schedule-proof";
        "ISS, statement splitting, and parallel codegen are out of scope";
        "bounded coverage uses explicit parameter assignments and deterministic tile reconstruction";
      ];
  }

let validate_tiling before_path after_path params check_bounded_coverage =
  let witness = infer_tiling_witness before_path after_path in
  let report = check_tiling_witness before_path after_path witness params check_bounded_coverage in
  { report with witness_source = "inferred" }

let affine_expr_to_yojson expr =
  `Assoc
    [
      ("var_coeffs", `List (List.map (fun (n, c) -> `List [ `String n; `Int c ]) expr.var_coeffs));
      ("param_coeffs", `List (List.map (fun (n, c) -> `List [ `String n; `Int c ]) expr.param_coeffs));
      ("const", `Int expr.const);
    ]

let tile_link_to_yojson link =
  `Assoc
    [
      ("parent", `String link.parent);
      ("expr", affine_expr_to_yojson link.expr);
      ("tile_size", `Int link.tile_size);
    ]

let statement_validation_to_yojson (stmt : statement_validation) =
  `Assoc
    [
      ("statement", `Int stmt.statement);
      ("original_iterators", `List (List.map (fun s -> `String s) stmt.original_iterators));
      ("tiled_iterators", `List (List.map (fun s -> `String s) stmt.tiled_iterators));
      ("added_iterators", `List (List.map (fun s -> `String s) stmt.added_iterators));
      ("links", `List (List.map tile_link_to_yojson stmt.links));
      ("shape_ok", `Bool stmt.shape_ok);
      ("transformation_contract_ok", `Bool stmt.transformation_contract_ok);
      ("witness_match_ok", `Bool stmt.witness_match_ok);
      ("base_domain_ok", `Bool stmt.base_domain_ok);
      ("link_rows_ok", `Bool stmt.link_rows_ok);
      ("access_ok", `Bool stmt.access_ok);
      ("compiled_relation_ok", `Bool stmt.compiled_relation_ok);
      ("schedule_sanity_ok", `Bool stmt.schedule_sanity_ok);
      ( "bounded_coverage_ok",
        match stmt.bounded_coverage_ok with
        | None -> `Null
        | Some b -> `Bool b );
      ("notes", `List (List.map (fun s -> `String s) stmt.notes));
    ]

let statement_witness_to_yojson (stmt : statement_tiling_witness) =
  `Assoc
    [
      ("statement", `Int stmt.statement);
      ("original_iterators", `List (List.map (fun s -> `String s) stmt.original_iterators));
      ("tiled_iterators", `List (List.map (fun s -> `String s) stmt.tiled_iterators));
      ("added_iterators", `List (List.map (fun s -> `String s) stmt.added_iterators));
      ("links", `List (List.map tile_link_to_yojson stmt.links));
    ]

let witness_to_yojson (witness : tiling_witness) =
  `Assoc
    [
      ("before", `String witness.before);
      ("after", `String witness.after);
      ("params", `List (List.map (fun s -> `String s) witness.params));
      ("statements", `List (List.map statement_witness_to_yojson witness.statements));
    ]

let validation_report_to_yojson (report : validation_report) =
  `Assoc
    [
      ("before", `String report.before);
      ("after", `String report.after);
      ("params", `Assoc (List.map (fun (k, v) -> (k, `Int v)) report.params));
      ("ok", `Bool report.ok);
      ("witness_source", `String report.witness_source);
      ("statements", `List (List.map statement_validation_to_yojson report.statements));
      ("limitations", `List (List.map (fun s -> `String s) report.limitations));
    ]

let string_list_field json name =
  match Yojson.Safe.Util.member name json with
  | `List xs -> List.map Yojson.Safe.Util.to_string xs
  | _ -> []

let coeff_pairs_field json name =
  match Yojson.Safe.Util.member name json with
  | `List xs ->
      List.map
        (function
          | `List [ `String n; `Int c ] -> (n, c)
          | _ -> raise (Validation_error ("bad coeff pair in " ^ name)))
        xs
  | _ -> []

let affine_expr_of_yojson json =
  {
    var_coeffs = coeff_pairs_field json "var_coeffs";
    param_coeffs = coeff_pairs_field json "param_coeffs";
    const =
      (match Yojson.Safe.Util.member "const" json with `Int n -> n | _ -> 0);
  }

let tile_link_of_yojson json =
  {
    parent = Yojson.Safe.Util.(json |> member "parent" |> to_string);
    expr = affine_expr_of_yojson Yojson.Safe.Util.(json |> member "expr");
    tile_size = Yojson.Safe.Util.(json |> member "tile_size" |> to_int);
  }

let statement_witness_of_yojson json =
  let original_iterators = string_list_field json "original_iterators" in
  let added_iterators = string_list_field json "added_iterators" in
  {
    statement = Yojson.Safe.Util.(json |> member "statement" |> to_int);
    original_iterators;
    tiled_iterators = string_list_field json "tiled_iterators";
    added_iterators;
    links =
      (match Yojson.Safe.Util.member "links" json with
      | `List xs -> canonical_statement_links original_iterators added_iterators (List.map tile_link_of_yojson xs)
      | _ -> []);
  }

let witness_of_yojson json =
  {
    before =
      (match Yojson.Safe.Util.member "before" json with `String s -> s | _ -> "");
    after =
      (match Yojson.Safe.Util.member "after" json with `String s -> s | _ -> "");
    params = string_list_field json "params";
    statements =
      (match Yojson.Safe.Util.member "statements" json with
      | `List xs -> List.map statement_witness_of_yojson xs
      | _ -> []);
  }

let render_tiling_witness (witness : tiling_witness) =
  let lines =
    [ Printf.sprintf "before: %s" witness.before; Printf.sprintf "after:  %s" witness.after ]
    @ [ Printf.sprintf "params: %s" (String.concat "," witness.params) ]
  in
  let stmt_lines (stmt : statement_tiling_witness) =
    let base =
      [
        "";
        Printf.sprintf "statement %d:" stmt.statement;
        Printf.sprintf "  original iterators: [%s]" (String.concat ", " stmt.original_iterators);
        Printf.sprintf "  tiled iterators:    [%s]" (String.concat ", " stmt.tiled_iterators);
      ]
    in
    let base =
      if stmt.added_iterators = [] then base
      else base @ [ Printf.sprintf "  added iterators:    [%s]" (String.concat ", " stmt.added_iterators) ]
    in
    base
    @ List.map
        (fun link ->
          Printf.sprintf "  tile link: %s = floor((%s) / %d)" link.parent (expr_render link.expr) link.tile_size)
        stmt.links
  in
  String.concat "\n" (lines @ List.concat_map stmt_lines witness.statements)

let render_validation_report (report : validation_report) =
  let header =
    [
      Printf.sprintf "before: %s" report.before;
      Printf.sprintf "after:  %s" report.after;
      Printf.sprintf "overall: %s" (if report.ok then "PASS" else "FAIL");
      Printf.sprintf "witness: %s" report.witness_source;
    ]
  in
  let header =
    if report.params = [] then header
    else
      header
      @
      [
        Printf.sprintf "params: %s"
          (String.concat ", " (List.map (fun (k, v) -> Printf.sprintf "%s=%d" k v) report.params));
      ]
  in
  let stmt_lines (stmt : statement_validation) =
    let status =
      Printf.sprintf
        "statement %d: shape=%b transformation_contract=%b witness_match=%b base_domain=%b links=%b access=%b compiled_relation=%b schedule_sanity=%b bounded_coverage=%s"
        stmt.statement stmt.shape_ok stmt.transformation_contract_ok stmt.witness_match_ok
        stmt.base_domain_ok stmt.link_rows_ok stmt.access_ok stmt.compiled_relation_ok stmt.schedule_sanity_ok
        (match stmt.bounded_coverage_ok with None -> "n/a" | Some true -> "true" | Some false -> "false")
    in
    [ ""; status ]
    @ [ Printf.sprintf "  original iterators: [%s]" (String.concat ", " stmt.original_iterators) ]
    @ [ Printf.sprintf "  tiled iterators:    [%s]" (String.concat ", " stmt.tiled_iterators) ]
    @
    (if stmt.added_iterators = [] then []
     else [ Printf.sprintf "  added iterators:    [%s]" (String.concat ", " stmt.added_iterators) ])
    @ List.map
        (fun link ->
          Printf.sprintf "  tile link: %s = floor((%s) / %d)" link.parent (expr_render link.expr) link.tile_size)
        stmt.links
    @ List.map (fun note -> "  note: " ^ note) stmt.notes
  in
  String.concat "\n"
    (header @ List.concat_map stmt_lines report.statements @ [ ""; "limitations:" ]
   @ List.map (fun item -> "  - " ^ item) report.limitations)
