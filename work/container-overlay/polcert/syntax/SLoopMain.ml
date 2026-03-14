open Diagnostics
open Result

let tool_name = "Syntax-Frontend Polyhedral Optimizer"

exception FrontendFailure of string

let frontend_failf fmt = Printf.ksprintf (fun s -> raise (FrontendFailure s)) fmt

let usage prog =
  Printf.sprintf
    "Usage: %s [--dump-input] [--dump-extracted-openscop] [--dump-scheduled-openscop] [--debug-scheduler] [--extract-only] <file.loop>\n       %s --extract-tiling-witness-openscop <before.scop> <after.scop>\n       %s --validate-tiling-openscop <before.scop> <after.scop>\n\nDefault optimization path:\n  phase-aligned Pluto pipeline with two external calls\n  1. affine-only Pluto scheduling\n  2. tile-only Pluto transformation\n  followed by affine validation(before, mid) and tiling validation(mid, after)\n"
    prog
    prog
    prog

type config = {
  mutable dump_input : bool;
  mutable dump_extracted_openscop : bool;
  mutable dump_scheduled_openscop : bool;
  mutable debug_scheduler : bool;
  mutable extract_only : bool;
  mutable extract_tiling_witness_openscop : (string * string) option;
  mutable validate_tiling_openscop : (string * string) option;
  mutable input : string option;
}

let parse_args () =
  let cfg =
    {
      dump_input = false;
      dump_extracted_openscop = false;
      dump_scheduled_openscop = false;
      debug_scheduler = false;
      extract_only = false;
      extract_tiling_witness_openscop = None;
      validate_tiling_openscop = None;
      input = None;
    }
  in
  let rec go i =
    if i >= Array.length Sys.argv then cfg
    else begin
      match Sys.argv.(i) with
      | "--dump-input" -> cfg.dump_input <- true; go (i + 1)
      | "--dump-extracted-openscop" -> cfg.dump_extracted_openscop <- true; go (i + 1)
      | "--dump-scheduled-openscop" -> cfg.dump_scheduled_openscop <- true; go (i + 1)
      | "--debug-scheduler" -> cfg.debug_scheduler <- true; go (i + 1)
      | "--extract-only" -> cfg.extract_only <- true; go (i + 1)
      | "--help" | "-h" ->
          print_endline (usage Sys.argv.(0));
          exit 0
      | "--extract-tiling-witness-openscop" ->
          if i + 2 >= Array.length Sys.argv then begin
            prerr_endline "option --extract-tiling-witness-openscop expects two file paths";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          cfg.extract_tiling_witness_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | "--validate-tiling-openscop" ->
          if i + 2 >= Array.length Sys.argv then begin
            prerr_endline "option --validate-tiling-openscop expects two file paths";
            prerr_endline (usage Sys.argv.(0));
            exit 2
          end;
          cfg.validate_tiling_openscop <- Some (Sys.argv.(i + 1), Sys.argv.(i + 2));
          go (i + 3)
      | s when String.length s > 0 && s.[0] = '-' ->
          prerr_endline ("unknown option: " ^ s);
          prerr_endline (usage Sys.argv.(0));
          exit 2
      | file ->
          begin match cfg.input with
          | None -> cfg.input <- Some file; go (i + 1)
          | Some _ ->
              prerr_endline "only one input file is supported";
              prerr_endline (usage Sys.argv.(0));
              exit 2
          end
    end
  in
  go 1

let string_of_coq_err msg = Camlcoq.camlstring_of_coqstring msg

let print_section title body =
  print_endline ("== " ^ title ^ " ==");
  print_string body;
  if body = "" || body.[String.length body - 1] <> '\n' then print_newline ();
  print_newline ()

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> 1 + int_of_nat n

let max_int a b = if a >= b then a else b

let string_of_z z = string_of_int (Camlcoq.Z.to_int z)

let string_of_aff (zs, c) =
  let coeffs = String.concat "," (List.map string_of_z zs) in
  Printf.sprintf "[%s | %s]" coeffs (string_of_z c)

let string_of_aff_list affs =
  "[" ^ String.concat "; " (List.map string_of_aff affs) ^ "]"

let string_of_access acc =
  let (arr, affs) = acc in
  Printf.sprintf "(%s,%s)" (string_of_int (Camlcoq.P.to_int arr)) (string_of_aff_list affs)

let string_of_access_list accs =
  "[" ^ String.concat "; " (List.map string_of_access accs) ^ "]"

let dump_poly_payload label pp =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ((pis, varctxt), vars) = pp in
  Printf.eprintf
    "[debug] %s payload: pis=%d varctxt=%d vars=%d
"
    label (List.length pis) (List.length varctxt) (List.length vars);
  List.iteri
    (fun idx pi ->
      Printf.eprintf
        "[debug]   pi[%d]: depth=%d poly_rows=%d sched_rows=%d tf_rows=%d w=%d r=%d
"
        idx
        (int_of_nat (PL.pi_depth pi))
        (List.length (PL.pi_poly pi))
        (List.length (PL.pi_schedule pi))
        (List.length (PL.pi_transformation pi))
        (List.length (PL.pi_waccess pi))
        (List.length (PL.pi_raccess pi));
      Printf.eprintf
        "[debug]     schedule=%s
"
        (string_of_aff_list (PL.pi_schedule pi));
      Printf.eprintf
        "[debug]     transformation=%s
"
        (string_of_aff_list (PL.pi_transformation pi));
      Printf.eprintf
        "[debug]     waccess=%s
"
        (string_of_access_list (PL.pi_waccess pi));
      Printf.eprintf
        "[debug]     raccess=%s
"
        (string_of_access_list (PL.pi_raccess pi)))
    pis

let debug_env_enabled name =
  match Sys.getenv_opt name with
  | Some ("1" | "true" | "TRUE" | "yes" | "YES") -> true
  | _ -> false

let dump_poly_payload_if name label pp =
  if debug_env_enabled name then dump_poly_payload label pp

let extract_poly loop =
  match SPolOpt.CoreOpt.Extractor.extractor loop with
  | Err msg -> frontend_failf "extractor failed: %s" (string_of_coq_err msg)
  | Okk pol -> pol

let poly_to_openscop pol =
  match SPolOpt.to_source_openscop pol with
  | None -> frontend_failf "cannot convert extracted polyhedral model to OpenScop"
  | Some scop -> scop

let validate_components pp1 pp2 =
  let ((pil1, varctxt1), _) = pp1 in
  let ((pil2, _), _) = pp2 in
  let (wf1, wf1_ok) = SPolOpt.SVal.check_wf_polyprog pp1 in
  let (wf2, wf2_ok) = SPolOpt.SVal.check_wf_polyprog pp2 in
  let (eqdom, eqdom_ok) = SPolOpt.SVal.coq_EqDom pp1 pp2 in
  let env_dim = nat_of_int (List.length varctxt1) in
  let pil_ext = SPolIRs.SPolIRs.PolyLang.compose_pinstrs_ext pil1 pil2 in
  let valid_access = SPolOpt.SVal.check_valid_access pil_ext in
  let (res, res_ok) = SPolOpt.SVal.validate_instr_list (List.rev pil_ext) env_dim in
  ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, true), (res, res_ok))

let print_validate_components label pp1 pp2 =
  let ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, _), (res, res_ok)) =
    validate_components pp1 pp2
  in
  Printf.eprintf
    "[debug] %s components: wf1=%b(ok=%b) wf2=%b(ok=%b) eqdom=%b(ok=%b) valid_access=%b res=%b(ok=%b)\n"
    label wf1 wf1_ok wf2 wf2_ok eqdom eqdom_ok valid_access res res_ok

let extract_to_openscop loop =
  poly_to_openscop (extract_poly loop)

let schedule_poly pol =
  match SPolIRs.SPolIRs.scheduler pol with
  | Err msg -> frontend_failf "scheduler failed: %s" (string_of_coq_err msg)
  | Okk pol' -> pol'

let dump_scheduled_openscop loop =
  print_endline "== Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop (schedule_poly (extract_poly loop)));
  print_newline ()

let debug_scheduler loop =
  let pol0 = extract_poly loop in
  dump_poly_payload "extracted" pol0;
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  dump_poly_payload "strengthened" pol;
  let inscop = poly_to_openscop pol in
  let (self_valid, self_ok) = SPolOpt.SVal.validate pol pol in
  print_validate_components "validate(strengthened, strengthened)" pol pol;
  Printf.eprintf
    "[debug] validate(strengthened, strengthened) = %b (ok=%b, alarm=%b)\n"
    self_valid self_ok (not self_ok);
  let pol_roundtrip =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_like_source pol inscop with
    | Okk pol' -> pol'
    | Err msg -> frontend_failf "self round-trip failed: %s" (string_of_coq_err msg)
  in
  let pol_complete_before =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_complete inscop with
    | Okk pol' -> pol'
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "roundtrip-before" pol_roundtrip;
  dump_poly_payload "complete-before" pol_complete_before;
  let (roundtrip_valid, roundtrip_ok) = SPolOpt.SVal.validate pol pol_roundtrip in
  print_validate_components "validate(strengthened, roundtrip-before)" pol pol_roundtrip;
  let (complete_before_valid, complete_before_ok) = SPolOpt.SVal.validate pol pol_complete_before in
  print_validate_components "validate(strengthened, complete-before)" pol pol_complete_before;
  print_endline "== Debug Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout inscop;
  print_newline ();
  print_endline "== Debug Roundtrip-Before OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_roundtrip);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, roundtrip-before) = %b (ok=%b, alarm=%b)\n"
    roundtrip_valid roundtrip_ok (not roundtrip_ok);
  let pol_sched = schedule_poly pol in
  dump_poly_payload "scheduled" pol_sched;
  let pol_complete_after =
    match SPolIRs.SPolIRs.scop_scheduler inscop with
    | Okk outscop ->
        begin match SPolIRs.SPolIRs.PolyLang.from_openscop_complete outscop with
        | Okk pol' -> pol'
        | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
        end
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "complete-after" pol_complete_after;
  let (sched_valid, sched_ok) = SPolOpt.SVal.validate pol pol_sched in
  print_validate_components "validate(strengthened, scheduled)" pol pol_sched;
  let (old_complete_sched_valid, old_complete_sched_ok) = SPolOpt.SVal.validate pol_complete_before pol_sched in
  print_validate_components "validate(complete-before, scheduled)" pol_complete_before pol_sched;
  let (new_complete_sched_valid, new_complete_sched_ok) = SPolOpt.SVal.validate pol pol_complete_after in
  print_validate_components "validate(strengthened, complete-after)" pol pol_complete_after;
  let (complete_sched_valid, complete_sched_ok) = SPolOpt.SVal.validate pol_complete_before pol_complete_after in
  print_validate_components "validate(complete-before, complete-after)" pol_complete_before pol_complete_after;
  print_endline "== Debug Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_sched);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, scheduled) = %b (ok=%b, alarm=%b)\n"
    sched_valid sched_ok (not sched_ok)

let dump_extracted_openscop loop =
  print_endline "== Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (extract_to_openscop loop);
  print_newline ()

let import_complete_spol_or_fail label scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into syntax polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_schedule_only_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as schedule-only syntax IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tpol_or_fail label scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into validator polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tiling_or_fail label scop =
  match TPolOpt.Tiling.PL.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into tiling validator IR: %s"
        label
        (string_of_coq_err msg)

let coeff_of_assoc assoc name =
  match List.assoc_opt name assoc with
  | Some coeff -> coeff
  | None -> Camlcoq.Z.zero

let convert_tiling_affine_expr
    names
    params
    (expr : PlutoTilingValidator.affine_expr) =
  let open TilingWitness in
  {
    ae_var_coeffs = List.map (coeff_of_assoc expr.PlutoTilingValidator.var_coeffs) names;
    ae_param_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.param_coeffs) params;
    ae_const = expr.PlutoTilingValidator.const;
  }

let convert_tiling_statement_witness
    params
    (stmt : PlutoTilingValidator.statement_witness) =
  let open TilingWitness in
  let rec convert_links prefix = function
    | [] -> []
    | link :: tl ->
        let names = prefix @ stmt.PlutoTilingValidator.original_iterators in
        let expr = convert_tiling_affine_expr names params link.PlutoTilingValidator.expr in
        let link' = { tl_expr = expr; tl_tile_size = link.PlutoTilingValidator.tile_size } in
        link' :: convert_links (prefix @ [link.PlutoTilingValidator.parent]) tl
  in
  {
    stw_point_dim =
      Camlcoq.Nat.of_int (List.length stmt.PlutoTilingValidator.original_iterators);
    stw_links = convert_links [] stmt.PlutoTilingValidator.links;
  }

let convert_tiling_witness (witness : PlutoTilingValidator.witness) =
  List.map (convert_tiling_statement_witness witness.PlutoTilingValidator.params)
    witness.PlutoTilingValidator.statements

let required_vars_for_tiling_pinstr env_size pi =
  max_int
    (env_size + Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth pi))
    (max_int
       (List.length (TPolOpt.Tiling.PL.pi_poly pi))
       (List.length (TPolOpt.Tiling.PL.pi_schedule pi)))

let required_vars_for_tiling_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_tiling_pinstr env_size pi))
    (List.length vars)
    pis

let pad_tiling_vars_to required ((pis, ctxt), vars) =
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
      (required_vars_for_tiling_pprog before_pol)
      (required_vars_for_tiling_pprog after_pol)
  in
  (pad_tiling_vars_to required before_pol, pad_tiling_vars_to required after_pol)

let build_canonical_tiled_after before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        {
          TPolOpt.Tiling.PL.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = TPolOpt.Tiling.PL.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (TPolOpt.Tiling.PL.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              (TPolOpt.Tiling.ptw_added_dims cw)
              env_size
              (TPolOpt.Tiling.PL.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = TPolOpt.Tiling.PL.pi_transformation before_pi;
          pi_access_transformation =
            TPolOpt.Tiling.PL.pi_access_transformation before_pi;
          pi_waccess = TPolOpt.Tiling.PL.pi_waccess before_pi;
          pi_raccess = TPolOpt.Tiling.PL.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let build_canonical_tiled_after_spol before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        let added_dims = TPolOpt.Tiling.ptw_added_dims cw in
        {
          SPolIRs.SPolIRs.PolyLang.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (SPolIRs.SPolIRs.PolyLang.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = SPolIRs.SPolIRs.PolyLang.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (SPolIRs.SPolIRs.PolyLang.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              added_dims
              env_size
              (SPolIRs.SPolIRs.PolyLang.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = SPolIRs.SPolIRs.PolyLang.pi_transformation before_pi;
          pi_access_transformation =
            SPolIRs.SPolIRs.PolyLang.pi_access_transformation before_pi;
          pi_waccess = SPolIRs.SPolIRs.PolyLang.pi_waccess before_pi;
          pi_raccess = SPolIRs.SPolIRs.PolyLang.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let required_vars_for_spol_pinstr env_size pi =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let access_width accs =
    List.fold_left
      (fun acc (_, affs) ->
        List.fold_left
          (fun acc' (zs, _) -> max_int acc' (List.length zs))
          acc
          affs)
      0
      accs
  in
  max_int
    (env_size + Camlcoq.Nat.to_int (PL.pi_depth pi))
    (max_int
       (List.fold_left
          (fun acc (zs, _) -> max_int acc (List.length zs))
          0
          (PL.pi_poly pi))
       (max_int
          (List.fold_left
             (fun acc (zs, _) -> max_int acc (List.length zs))
             0
             (PL.pi_schedule pi))
          (max_int
             (List.fold_left
                (fun acc (zs, _) -> max_int acc (List.length zs))
                0
                (PL.pi_transformation pi))
             (max_int
                (access_width (PL.pi_waccess pi))
                (access_width (PL.pi_raccess pi))))))

let required_vars_for_spol_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_spol_pinstr env_size pi))
    (List.length vars)
    pis

let pad_spol_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_codegen_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, SPolIRs.SPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_spol_codegen_input pp =
  pad_spol_vars_to (required_vars_for_spol_pprog pp) pp

let normalize_stiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_spol_pprog before_pol)
      (required_vars_for_spol_pprog after_pol)
  in
  (pad_spol_vars_to required before_pol, pad_spol_vars_to required after_pol)

let canonicalize_tiled_after before_label after_label before_pol after_scop ws =
  let canonical_after = build_canonical_tiled_after before_pol ws in
  match TPolOpt.Tiling.PL.from_openscop_schedule_only canonical_after after_scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
        after_label
        before_label
        (string_of_coq_err msg)

let affine_forward_scops before_label after_label before_scop after_scop =
  let before_pol = import_complete_tpol_or_fail before_label before_scop in
  let after_pol = import_complete_tpol_or_fail after_label after_scop in
  TPolValidator.TVal.validate before_pol after_pol

let tiling_forward_scops ~before_label ~after_label before_scop after_scop =
  let before_pol = import_complete_spol_or_fail before_label before_scop in
  let witness : PlutoTilingValidator.witness =
    PlutoTilingValidator.extract_witness_from_scops
      ~before_path:before_label
      ~after_path:after_label
      before_scop
      after_scop
  in
  let ws = convert_tiling_witness witness in
  let after_pol =
    let canonical_after = build_canonical_tiled_after_spol before_pol ws in
    match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only canonical_after after_scop with
    | Okk pol -> pol
    | Err msg ->
        frontend_failf
          "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
          after_label
          before_label
          (string_of_coq_err msg)
  in
  let (before_pol, after_pol) =
    normalize_stiling_validator_inputs before_pol after_pol
  in
  SPolOpt.CoreOpt.checked_tiling_validate before_pol after_pol ws

let pluto_phase_scops loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  match Scheduler.phase_scop_scheduler before_scop with
  | Err msg ->
      frontend_failf "phase-aligned Pluto pipeline failed: %s" (string_of_coq_err msg)
  | Okk (mid_scop, after_scop) -> (before_scop, mid_scop, after_scop)

let debug_generic_tiling_runtime loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let (mid_scop, after_scop) =
    match Scheduler.phase_scop_scheduler before_scop with
    | Err msg ->
        frontend_failf "phase-aligned Pluto pipeline failed: %s" (string_of_coq_err msg)
    | Okk (mid_scop, after_scop) -> (mid_scop, after_scop)
  in
  let pol_mid =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_like_source pol mid_scop with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf "cannot import mid_affine like_source: %s" (string_of_coq_err msg)
  in
  let (aff_res, aff_ok) = SPolOpt.SVal.validate pol pol_mid in
  let witness : PlutoTilingValidator.witness =
    PlutoTilingValidator.extract_witness_from_scops
      ~before_path:"mid_affine"
      ~after_path:"after_tiled"
      mid_scop
      after_scop
  in
  let ws = convert_tiling_witness witness in
  let pol_after =
    let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
    match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only canonical_after after_scop with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf "cannot import after_tiled over canonical skeleton: %s"
          (string_of_coq_err msg)
  in
  let before_t = SPolOpt.CoreOpt.CheckedTiling.outer_to_tiling_pprog pol_mid in
  let after_t = SPolOpt.CoreOpt.CheckedTiling.outer_to_tiling_pprog pol_after in
  let struct_ok =
    SPolOpt.CoreOpt.CheckedTiling.TilingCheck.check_pprog_tiling_sourceb before_t after_t ws
  in
  let (checked_res, checked_ok) =
    SPolOpt.CoreOpt.checked_tiling_validate pol_mid pol_after ws
  in
  let (pol_mid_norm, pol_after_norm) =
    normalize_stiling_validator_inputs pol_mid pol_after
  in
  let (checked_norm_res, checked_norm_ok) =
    SPolOpt.CoreOpt.checked_tiling_validate pol_mid_norm pol_after_norm ws
  in
  Printf.eprintf
    "[debug-generic-tiling] affine=%b(ok=%b) struct=%b checked=%b(ok=%b) checked_norm=%b(ok=%b)\n"
    aff_res aff_ok struct_ok checked_res checked_ok checked_norm_res checked_norm_ok;
  dump_poly_payload "generic-mid(like-source)" pol_mid;
  dump_poly_payload "generic-after(canonical-schedule-only)" pol_after;
  dump_poly_payload "generic-mid(normalized)" pol_mid_norm;
  dump_poly_payload "generic-after(normalized)" pol_after_norm

let dump_scheduled_openscop loop =
  let (_, _, after_scop) = pluto_phase_scops loop in
  print_endline "== Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout after_scop;
  print_newline ()

let optimize_with_phase_aligned_pluto loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let (mid_scop, after_scop) =
    match Scheduler.phase_scop_scheduler before_scop with
    | Err msg ->
        frontend_failf "phase-aligned Pluto pipeline failed: %s" (string_of_coq_err msg)
    | Okk (mid_scop, after_scop) -> (mid_scop, after_scop)
  in
  let (affine_res, affine_ok) =
    affine_forward_scops "before" "mid_affine" before_scop mid_scop
  in
  if not (affine_ok && affine_res) then
    (loop, false)
  else
    let (tiling_res, tiling_ok) =
      tiling_forward_scops
        ~before_label:"mid_affine"
        ~after_label:"after_tiled"
        mid_scop
        after_scop
    in
    if not (tiling_ok && tiling_res) then
      (loop, false)
    else
      let pol_mid = import_schedule_only_spol_or_fail "mid_affine" pol mid_scop in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "mid-affine(schedule-only)" pol_mid;
      let witness : PlutoTilingValidator.witness =
        PlutoTilingValidator.extract_witness_from_scops
          ~before_path:"mid_affine"
          ~after_path:"after_tiled"
          mid_scop
          after_scop
      in
      let ws = convert_tiling_witness witness in
      let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "canonical-after" canonical_after;
      let pol_after_sched =
        import_schedule_only_spol_or_fail "after_tiled" canonical_after after_scop
      in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "after-tiled(schedule-only)" pol_after_sched;
      if debug_env_enabled "POLCERT_DEBUG_TILING_CODEGEN" then begin
        let raw_after = import_complete_spol_or_fail "after_tiled(raw)" after_scop in
        dump_poly_payload "after-tiled(raw)" raw_after
      end;
      let pol_after = pol_after_sched in
      let pol_after = normalize_spol_codegen_input pol_after in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "after-tiled(used-for-codegen)" pol_after;
      let (res, ok) =
        SPolOpt.CoreOpt.checked_tiling_validate pol_mid pol_after ws
      in
      if ok && res then
        SPolOpt.CoreOpt.Prepare.prepared_codegen
          (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
      else
        (loop, false)

let run_tiling_validator before_file after_file =
  let report = PlutoTilingValidator.validate_files before_file after_file in
  print_endline (PlutoTilingValidator.render_report report);
  if report.ok then 0 else 2

let run_tiling_witness_extractor before_file after_file =
  let witness = PlutoTilingValidator.extract_witness_from_files before_file after_file in
  print_endline (PlutoTilingValidator.render_witness witness);
  0

let () =
  try
    Gc.set { (Gc.get()) with
               Gc.minor_heap_size = 524288;
               Gc.major_heap_increment = 4194304 };
    let cfg = parse_args () in
    match cfg.extract_tiling_witness_openscop, cfg.validate_tiling_openscop with
    | Some _, Some _ ->
        prerr_endline "only one tiling OpenScop action may be selected";
        prerr_endline (usage Sys.argv.(0));
        exit 2
    | Some (before_file, after_file), None ->
        exit (run_tiling_witness_extractor before_file after_file)
    | None, Some (before_file, after_file) ->
        exit (run_tiling_validator before_file after_file)
    | None, None ->
      begin match cfg.input with
      | None ->
        print_endline (usage Sys.argv.(0));
        exit 2
      | Some file ->
        let prog = SLoopParse.parse_file file in
        let loop = SLoopElab.elaborate prog in
        if cfg.dump_input then print_section "Input Loop" (SLoopPretty.string_of_loop loop);
        if cfg.extract_only then begin
          OpenScopPrinter.openscop_printer' stdout (extract_to_openscop loop);
          print_newline ();
          exit 0
        end;
        if cfg.dump_extracted_openscop then dump_extracted_openscop loop;
        if cfg.dump_scheduled_openscop then dump_scheduled_openscop loop;
        if cfg.debug_scheduler then debug_scheduler loop;
        if debug_env_enabled "POLCERT_DEBUG_GENERIC_TILING" then
          debug_generic_tiling_runtime loop;
        let (optimized, ok) = SPolOpt.opt loop in
        if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
        print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized)
      end
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | SLoopParse.Error (pos, msg) -> error no_loc "parse error at byte %d: %s" pos msg; exit 2
  | SLoopElab.Error msg -> error no_loc "elaboration error: %s" msg; exit 2
  | FrontendFailure msg -> error no_loc "%s" msg; exit 2
  | PlutoTilingValidator.ValidationError msg -> error no_loc "%s" msg; exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      error no_loc "optimization failed inside extracted runtime: %s" msg; exit 2
  | e -> crash e
