open Diagnostics
open Result
open TPolValidator
open TPolOpt
open TilingWitness

let tool_name = "Verified Validator for Affine Scheduling and Tiling"

type validation_kind =
  | Kind_auto
  | Kind_affine
  | Kind_tiling

type file_mode =
  | Pair_mode of string * string
  | Phase_mode of string * string * string

let usage prog =
  Printf.sprintf
    "Usage:\n  %s [--kind auto|affine|tiling] <before.scop> <after.scop>\n  %s [--kind auto|affine|tiling] <before.scop> <mid.scop> <after.scop>\n\nTwo-input mode:\n  auto   : try affine validation first, then tiling validation\n  affine : run affine validation on before/after\n  tiling : run tiling validation on before/after\n\nThree-input mode:\n  auto   : run affine(before, mid), then tiling(mid, after)\n  affine : run affine(before, mid) only\n  tiling : run tiling(mid, after) only\n"
    prog prog

let string_of_coq_err msg = Camlcoq.camlstring_of_coqstring msg

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let kind_of_string = function
  | "auto" -> Kind_auto
  | "affine" -> Kind_affine
  | "tiling" -> Kind_tiling
  | s -> invalid_arg ("unknown validation kind: " ^ s)

let read_scop_or_fail path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> failwith ("cannot read OpenScop file " ^ path)

let import_complete_or_fail path scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
           "cannot import %s as a complete polyhedral model: %s"
           path
           (string_of_coq_err msg))

let import_complete_tiling_or_fail path scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
          "cannot import %s as a tiling polyhedral model: %s"
           path
           (string_of_coq_err msg))

let affine_relation before_path after_path =
  let scop1 = read_scop_or_fail before_path in
  let scop2 = read_scop_or_fail after_path in
  let pol1 = import_complete_or_fail before_path scop1 in
  let pol2 = import_complete_or_fail after_path scop2 in
  let (res1, ok1) = TVal.validate pol1 pol2 in
  let (res2, ok2) = TVal.validate pol2 pol1 in
  (ok1, res1, ok2, res2)

let affine_forward before_path after_path =
  let scop1 = read_scop_or_fail before_path in
  let scop2 = read_scop_or_fail after_path in
  let pol1 = import_complete_or_fail before_path scop1 in
  let pol2 = import_complete_or_fail after_path scop2 in
  let (res, ok) = TVal.validate pol1 pol2 in
  (ok, res)

let coeff_of_assoc assoc name =
  match List.assoc_opt name assoc with
  | Some coeff -> coeff
  | None -> Camlcoq.Z.zero

let max_int a b = if a >= b then a else b

let required_vars_for_pinstr env_size pi =
  let module PL = TPolIRs.TPolIRs.PolyLang in
  max_int
    (env_size + Camlcoq.Nat.to_int (PL.pi_depth pi))
    (max_int
       (List.length (PL.pi_poly pi))
       (List.length (PL.pi_schedule pi)))

let required_vars_for_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_pinstr env_size pi))
    (List.length vars)
    pis

let pad_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, TPolIRs.TPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_tiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_pprog before_pol)
      (required_vars_for_pprog after_pol)
  in
  (pad_vars_to required before_pol, pad_vars_to required after_pol)

let convert_affine_expr
    names
    params
    (expr : PlutoTilingValidator.affine_expr) =
  {
    ae_var_coeffs = List.map (coeff_of_assoc expr.PlutoTilingValidator.var_coeffs) names;
    ae_param_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.param_coeffs) params;
    ae_const = expr.PlutoTilingValidator.const;
  }

let convert_statement_witness
    params
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
    stw_point_dim = Camlcoq.Nat.of_int (List.length stmt.PlutoTilingValidator.original_iterators);
    stw_links = convert_links [] stmt.PlutoTilingValidator.links;
  }

let convert_witness (witness : PlutoTilingValidator.witness) =
  List.map (convert_statement_witness witness.PlutoTilingValidator.params)
    witness.PlutoTilingValidator.statements

let build_canonical_tiled_after before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = Tiling.compiled_pinstr_tiling_witness w in
        {
          TPolIRs.TPolIRs.PolyLang.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (TPolIRs.TPolIRs.PolyLang.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = TPolIRs.TPolIRs.PolyLang.pi_instr before_pi;
          pi_poly =
            (Tiling.ptw_link_domain cw)
            @
            (Tiling.lifted_base_domain_after_env
               env_size
               cw
               (TPolIRs.TPolIRs.PolyLang.pi_poly before_pi));
          pi_schedule =
            Tiling.lift_schedule_after_env
              (Tiling.ptw_added_dims cw)
              env_size
              (TPolIRs.TPolIRs.PolyLang.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = TPolIRs.TPolIRs.PolyLang.pi_transformation before_pi;
          pi_access_transformation =
            TPolIRs.TPolIRs.PolyLang.pi_access_transformation before_pi;
          pi_waccess = TPolIRs.TPolIRs.PolyLang.pi_waccess before_pi;
          pi_raccess = TPolIRs.TPolIRs.PolyLang.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let canonicalize_tiled_after before_pol after_path after_scop ws =
  let canonical_after = build_canonical_tiled_after before_pol ws in
  match TPolIRs.TPolIRs.PolyLang.from_openscop_schedule_only canonical_after after_scop with
  | Okk pol -> pol
  | Err msg ->
      failwith
        (Printf.sprintf
           "cannot import %s as a schedule over the canonical tiled skeleton: %s"
           after_path
           (string_of_coq_err msg))

let split_at_int n xs =
  let rec go i left = function
    | [] -> (List.rev left, [])
    | rest when i <= 0 -> (List.rev left, rest)
    | x :: tl -> go (i - 1) (x :: left) tl
  in
  go n [] xs

let insert_zero_coeffs_after_env env_size added_dim (coeffs, c) =
  let env_coeffs, rest = split_at_int env_size coeffs in
  (env_coeffs @ List.init added_dim (fun _ -> Camlcoq.Z.zero) @ rest, c)

let identity_affine_row total_cols pos =
  ( List.init total_cols (fun i ->
        if i = pos then Camlcoq.Z.one else Camlcoq.Z.zero),
    Camlcoq.Z.zero )

let pad_transformation_after_env env_size added_dim tf =
  let tf_lifted = List.map (insert_zero_coeffs_after_env env_size added_dim) tf in
  let env_rows, point_rows = split_at_int env_size tf_lifted in
  let total_cols =
    match tf_lifted with
    | (coeffs, _) :: _ -> List.length coeffs
    | [] -> env_size + added_dim
  in
  let added_rows =
    List.init added_dim (fun i -> identity_affine_row total_cols (env_size + i))
  in
  env_rows @ added_rows @ point_rows

let print_tiling_validate_components label pp1 pp2 =
  let ((pil1, varctxt1), _) = pp1 in
  let ((pil2, _), _) = pp2 in
  let env_dim = nat_of_int (List.length varctxt1) in
  let (wf1_res, wf1_ok) = TilingVal.check_wf_polyprog pp1 in
  let (wf2_res, wf2_ok) = TilingVal.check_wf_polyprog pp2 in
  let (eqdom_res, eqdom_ok) = TilingVal.coq_EqDom pp1 pp2 in
  let pil_ext = Tiling.PL.compose_pinstrs_ext pil1 pil2 in
  let access_ok = TilingVal.check_valid_access pil_ext in
  let (sched_res, sched_alarm_ok) =
    TilingVal.validate_instr_list (List.rev pil_ext) env_dim
  in
  Printf.eprintf
    "[tiling-debug] %s wf1=%b(ok=%b) wf2=%b(ok=%b) eqdom=%b(ok=%b) access=%b sched=%b(ok=%b)\n"
    label wf1_res wf1_ok wf2_res wf2_ok eqdom_res eqdom_ok access_ok sched_res
    sched_alarm_ok

let check_pinstr_tiling_padded_tf before_pi after_pi before_ctxt w =
  let env_size = List.length before_ctxt in
  let cw = Tiling.compiled_pinstr_tiling_witness w in
  TilingCheck.check_statement_tiling_witnessb
    (nat_of_int env_size)
    w
  &&
  PeanoNat.Nat.eqb w.stw_point_dim (Tiling.PL.pi_depth before_pi)
  &&
  TPolIRs.TPolIRs.Instr.eqb
    (Tiling.PL.pi_instr after_pi)
    (Tiling.PL.pi_instr before_pi)
  &&
  Camlcoq.Nat.to_int (Tiling.PL.pi_depth after_pi)
  =
  (Camlcoq.Nat.to_int (Tiling.PL.pi_depth before_pi)
   + List.length w.stw_links)
  &&
  Tiling.PL.pi_transformation after_pi
  =
  pad_transformation_after_env
    env_size
    (List.length w.stw_links)
    (Tiling.PL.pi_transformation before_pi)
  &&
  Tiling.PL.pi_poly after_pi
  =
  (Tiling.ptw_link_domain cw)
  @
  (Tiling.lifted_base_domain_after_env
     (nat_of_int env_size)
     cw
     (Tiling.PL.pi_poly before_pi))
  &&
  Tiling.PL.pi_waccess after_pi
  =
  Tiling.lifted_accesses_after_env
    (nat_of_int env_size)
    cw
    (Tiling.PL.pi_waccess before_pi)
  &&
  Tiling.PL.pi_raccess after_pi
  =
  Tiling.lifted_accesses_after_env
    (nat_of_int env_size)
    cw
    (Tiling.PL.pi_raccess before_pi)

let run_tiling_pair before_path after_path =
  let before_scop = read_scop_or_fail before_path in
  let after_scop = read_scop_or_fail after_path in
  let before_pol = import_complete_tiling_or_fail before_path before_scop in
  let witness : PlutoTilingValidator.witness =
    PlutoTilingValidator.extract_witness_from_files before_path after_path
  in
  let ws = convert_witness witness in
  let after_pol = canonicalize_tiled_after before_pol after_path after_scop ws in
  let (before_pol, after_pol) =
    normalize_tiling_validator_inputs before_pol after_pol
  in
  let (res, ok) = checked_tiling_validate before_pol after_pol ws in
  (ok, res)

let print_affine_relation before_path after_path =
  let (ok1, res1, ok2, res2) = affine_relation before_path after_path in
  if ok1 && res1 && ok2 && res2 then
    Printf.printf "[EQ] The two polyhedral models (%s, %s) are equivalent.\n"
      before_path after_path
  else if ok1 && res1 then
    Printf.printf "[GT] Polyhedral model %s refines %s.\n" after_path before_path
  else if ok2 && res2 then
    Printf.printf "[LT] Polyhedral model %s refines %s.\n" before_path after_path
  else
    Printf.printf
      "[NE] Cannot determine refinement relations between the two polyhedral models (%s, %s).\n"
      before_path after_path

let print_tiling_result before_path after_path =
  let (ok, res) = run_tiling_pair before_path after_path in
  if ok && res then
    Printf.printf "[TILING-OK] %s validates %s as a tiling-derived refinement.\n"
      after_path before_path
  else
    Printf.printf "[TILING-FAIL] %s does not validate %s as a tiling-derived refinement.\n"
      after_path before_path

let parse_args () =
  let kind = ref Kind_auto in
  let files = ref [] in
  let rec go i =
    if i >= Array.length Sys.argv then ()
    else
      match Sys.argv.(i) with
      | "--kind" ->
          if i + 1 >= Array.length Sys.argv then begin
            prerr_endline "option --kind expects a value";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          kind := kind_of_string Sys.argv.(i + 1);
          go (i + 2)
      | "--help" | "-h" ->
          print_string (usage Sys.argv.(0));
          exit 0
      | s when String.length s > 0 && s.[0] = '-' ->
          prerr_endline ("unknown option: " ^ s);
          prerr_endline (usage Sys.argv.(0));
          exit 2
      | path ->
          files := !files @ [path];
          go (i + 1)
  in
  go 1;
  let mode =
    match !files with
    | [before_path; after_path] -> Pair_mode (before_path, after_path)
    | [before_path; mid_path; after_path] ->
        Phase_mode (before_path, mid_path, after_path)
    | _ ->
        prerr_endline (usage Sys.argv.(0));
        exit 2
  in
  (!kind, mode)

let run_pair kind before_path after_path =
  match kind with
  | Kind_affine ->
      print_affine_relation before_path after_path
  | Kind_tiling ->
      print_tiling_result before_path after_path
  | Kind_auto ->
      let (ok1, res1, ok2, res2) = affine_relation before_path after_path in
      if (ok1 && res1) || (ok2 && res2) then
        print_affine_relation before_path after_path
      else
        print_tiling_result before_path after_path

let run_phase kind before_path mid_path after_path =
  match kind with
  | Kind_affine ->
      let (ok, res) = affine_forward before_path mid_path in
      if ok && res then
        Printf.printf "[AFFINE-OK] %s validates %s as an affine refinement.\n"
          mid_path before_path
      else
        Printf.printf "[AFFINE-FAIL] %s does not validate %s as an affine refinement.\n"
          mid_path before_path
  | Kind_tiling ->
      print_tiling_result mid_path after_path
  | Kind_auto ->
      let (ok_affine, res_affine) = affine_forward before_path mid_path in
      let (ok_tiling, res_tiling) = run_tiling_pair mid_path after_path in
      Printf.printf "[PHASE] affine(before, mid): %s\n"
        (if ok_affine && res_affine then "OK" else "FAIL");
      Printf.printf "[PHASE] tiling(mid, after): %s\n"
        (if ok_tiling && res_tiling then "OK" else "FAIL");
      if ok_affine && res_affine && ok_tiling && res_tiling then
        Printf.printf
          "[OK] Phase-aligned validation succeeded for (%s -> %s -> %s).\n"
          before_path mid_path after_path
      else
        Printf.printf
          "[FAIL] Phase-aligned validation failed for (%s -> %s -> %s).\n"
          before_path mid_path after_path

let _ =
  try
    Gc.set
      {
        (Gc.get ()) with
        Gc.minor_heap_size = 524288;
        Gc.major_heap_increment = 4194304;
      };
    let (kind, mode) = parse_args () in
    begin
      match mode with
      | Pair_mode (before_path, after_path) ->
          run_pair kind before_path after_path
      | Phase_mode (before_path, mid_path, after_path) ->
          run_phase kind before_path mid_path after_path
    end
  with
  | Invalid_argument msg ->
      error no_loc "%s" msg;
      exit 2
  | Failure msg ->
      error no_loc "%s" msg;
      exit 2
  | PlutoTilingValidator.ValidationError msg ->
      error no_loc "%s" msg;
      exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      error no_loc "validation failed inside extracted runtime: %s" msg;
      exit 2
  | Sys_error msg ->
      error no_loc "%s" msg;
      exit 2
  | e -> crash e
