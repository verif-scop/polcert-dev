

(* let scheduler  *)
open Result
open Driveraux
(* open CPolIRs *)
open Camlcoq
open Filename
open Str  (* Required for regular expressions *)
open TilingWitness

(** scop to scop *)

(** TODO: specify dump scop file name in pluto*)
let run_pluto_scop flags inscop =
  let inscop_file = tmp_file ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [["pluto"; "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  (* print_string ((String.concat " " cmd) ^ "\n"); *)
  let stdout =  (tmp_file (".stdout")) in
  let exc = command ?stdout:(Some stdout) cmd in
  match OpenScopReader.read outscop_file with
  | Some outscop -> Okk outscop
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let affine_only_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar";
  ]

let tile_only_flags =
  [
    "--identity";
    "--tile";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]

let affine_only_scop_scheduler inscop =
  run_pluto_scop affine_only_flags inscop

let tile_only_scop_scheduler inscop =
  run_pluto_scop tile_only_flags inscop

let phase_scop_scheduler inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop -> Okk (midscop, outscop)
      end

let coeff_of_assoc assoc name =
  match List.assoc_opt name assoc with
  | Some coeff -> coeff
  | None -> Z.zero

let convert_affine_expr names params
    (expr : PlutoTilingValidator.affine_expr) =
  {
    ae_var_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.var_coeffs) names;
    ae_param_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.param_coeffs) params;
    ae_const = expr.PlutoTilingValidator.const;
  }

let convert_statement_witness params
    (stmt : PlutoTilingValidator.statement_witness) =
  let rec convert_links prefix = function
    | [] -> []
    | link :: tl ->
        let names = prefix @ stmt.PlutoTilingValidator.original_iterators in
        let expr = convert_affine_expr names params link.PlutoTilingValidator.expr in
        let link' =
          {
            tl_expr = expr;
            tl_tile_size = link.PlutoTilingValidator.tile_size;
          }
        in
        link' :: convert_links (prefix @ [link.PlutoTilingValidator.parent]) tl
  in
  {
    stw_point_dim =
      Camlcoq.Nat.of_int
        (List.length stmt.PlutoTilingValidator.original_iterators);
    stw_links = convert_links [] stmt.PlutoTilingValidator.links;
  }

let convert_witness (witness : PlutoTilingValidator.witness) =
  List.map (convert_statement_witness witness.PlutoTilingValidator.params)
    witness.PlutoTilingValidator.statements

let infer_tiling_witness_scops before_scop after_scop =
  try
    let witness =
      PlutoTilingValidator.extract_witness_from_scops
        ~before_path:"mid_affine"
        ~after_path:"after_tiled"
        before_scop
        after_scop
    in
    Okk (convert_witness witness)
  with
  | PlutoTilingValidator.ValidationError msg ->
      Err (coqstring_of_camlstring msg)
  | exn ->
      Err (coqstring_of_camlstring (Printexc.to_string exn))

let scheduler' = affine_only_scop_scheduler


let find_and_extract_time filename =
  let ic = open_in filename in
  let rec process_lines () =
    try
      let line = input_line ic in
      let regex = regexp "\\[pluto\\] Auto-transformation time: \\([0-9.]+\\)s" in
      if string_match regex line 0 then begin
        let time_str = matched_group 1 line in
        let time_float = float_of_string time_str in
        close_in ic;
        time_float
      end else
        process_lines ()
    with
      End_of_file -> close_in ic; max_float
  in
  process_lines ()


(* also return the autoscheduling time, in pluto's stdout, "Auto-transformation time" *)
let invoke_pluto testname =
  let inscop_file = testname ^ ".beforescheduling.scop" in
  let outscop_file = testname ^ ".afterscheduling.scop" in
  let cmd = List.concat [
    ["pluto";
    "--dumpscop";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar"];
    [testname ^ ".c"]
  ] in
  let stdout =  (tmp_file ("." ^ testname ^ ".stdout")) in
  print_string ("\027[90mInfo\027[0m: Executing \"" ^ (String.concat " " cmd) ^ "\"\n");
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    command_error "invoke pluto failed" exc;)
  else 
    (* [pluto] Auto-transformation time: 0.001530s *)
    let runtime = find_and_extract_time stdout in
    Printf.printf "\027[90mInfo\027[0m: Invoke pluto succeed, with auto-transformation time %fs\n" runtime;
    print_string ("\027[90mInfo\027[0m: Reading " ^ (inscop_file) ^ " ...\n");
    match OpenScopReader.read inscop_file with 
    | Some inscop -> 
      print_string ("\027[90mInfo\027[0m: Read " ^ (inscop_file) ^ " successfully\n");
      (match OpenScopReader.read outscop_file with 
      | Some outscop ->
        print_string ("\027[90mInfo\027[0m: Read " ^ (outscop_file) ^ " successfully\n");
        Okk (inscop, outscop, runtime)
      | None -> Err (coqstring_of_camlstring ("invoke pluto failed"))
      )
    | None -> Err (coqstring_of_camlstring ("invoke pluto failed")) 
    
  (* match OpenScopReader.read inscop_file with
  | Some outscop -> Okk outscop
  | None -> Err (coqstring_of_camlstring ("cannot read " ^ inscop_file ^ "\n")) *)

(* let scheduler' cpol =
  let inscop = CPolIRs.PolyLang.to_openscop cpol in
  let inscop_file = tmp_file ".scop" in
  let outscop_file = tmp_file ".scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  match OpenScopReader.read inscop_file with
  | Some outscop -> CPolIRs.PolyLang.from_openscop cpol outscop
  | None -> Err (coqstring_of_camlstring ("Error: cannot read " ^ inscop_file ^ "\n")) *)

let scop_scheduler inscop = scheduler' inscop;;
