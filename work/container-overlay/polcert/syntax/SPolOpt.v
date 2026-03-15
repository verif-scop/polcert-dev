Require Import SPolIRs.
Require Import List.
Require Import Linalg.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Local Open Scope string_scope.

Module CoreOpt := PolOpt SPolIRs.
Module Extractor := CoreOpt.Extractor.

Definition add_var_nodup (vars : list (AST.ident * SPolIRs.Ty.t))
  (v : AST.ident * SPolIRs.Ty.t)
  : list (AST.ident * SPolIRs.Ty.t) :=
  if List.existsb (fun '(id, _) => SPolIRs.Instr.ident_eqb id (fst v)) vars
  then vars
  else vars ++ (v :: nil).

Definition export_pi_for_openscop (varctxt : list AST.ident) (pi : SPolIRs.PolyLang.PolyInstr)
  : SPolIRs.PolyLang.PolyInstr :=
  let names :=
    List.app (List.map SPolIRs.Instr.ident_to_varname varctxt)
      (List.map SPolIRs.Instr.iterator_to_varname (List.seq 0 (SPolIRs.PolyLang.pi_depth pi))) in
  {|
    SPolIRs.PolyLang.pi_depth := SPolIRs.PolyLang.pi_depth pi;
    SPolIRs.PolyLang.pi_instr := SPolIRs.PolyLang.pi_instr pi;
    SPolIRs.PolyLang.pi_poly := SPolIRs.PolyLang.pi_poly pi;
    SPolIRs.PolyLang.pi_schedule := SPolIRs.PolyLang.pi_schedule pi;
    SPolIRs.PolyLang.pi_point_witness := SPolIRs.PolyLang.pi_point_witness pi;
    SPolIRs.PolyLang.pi_transformation := SPolIRs.PolyLang.pi_transformation pi;
    SPolIRs.PolyLang.pi_access_transformation := SPolIRs.PolyLang.pi_access_transformation pi;
    SPolIRs.PolyLang.pi_waccess := SPolIRs.PolyLang.pi_waccess pi;
    SPolIRs.PolyLang.pi_raccess :=
      SPolIRs.PolyLang.pi_raccess pi ++
      SPolIRs.Instr.export_scalar_reads names (SPolIRs.PolyLang.pi_instr pi);
  |}.

Definition export_pprog_for_openscop (pol : SPolIRs.PolyLang.t) : SPolIRs.PolyLang.t :=
  let '(pis, varctxt, vars) := pol in
  let names := List.map SPolIRs.Instr.ident_to_varname varctxt in
  let vars' :=
    List.fold_left
      (fun acc pi =>
         List.fold_left add_var_nodup
           (SPolIRs.Instr.export_scalar_read_vars
              (List.app names
                 (List.map SPolIRs.Instr.iterator_to_varname
                    (List.seq 0 (SPolIRs.PolyLang.pi_depth pi))))
              (SPolIRs.PolyLang.pi_instr pi))
           acc)
      pis vars in
  (List.map (export_pi_for_openscop varctxt) pis, varctxt, vars').

Definition to_source_openscop (pol : SPolIRs.PolyLang.t) : option OpenScop :=
  SPolIRs.PolyLang.to_openscop (export_pprog_for_openscop pol).

Definition proved_opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreOpt.Opt.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  proved_opt loop.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
