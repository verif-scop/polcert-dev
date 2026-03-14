Require Import PolIRs.
Require Import SInstr.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.
Require Import TilingWitness.

Local Open Scope string_scope.

Module SPolIRs <: POLIRS with Module Instr := SInstr.
  Module Instr := SInstr.
  Module State := State.
  Module Ty := Ty.
  Module PolyLang := PolyLang SInstr.
  Module PolyLoop := PolyLoop SInstr.
  Module Loop := Loop SInstr.
  Parameter scop_scheduler : OpenScop -> result OpenScop.
  Parameter phase_scop_scheduler : OpenScop -> result (OpenScop * OpenScop).
  Parameter infer_tiling_witness_scops :
    OpenScop -> OpenScop -> result (list statement_tiling_witness).

  Definition add_var_nodup (vars : list (Instr.ident * Ty.t)) (v : Instr.ident * Ty.t)
    : list (Instr.ident * Ty.t) :=
    if List.existsb (fun '(id, _) => Instr.ident_eqb id (fst v)) vars
    then vars
    else vars ++ (v :: nil).

  Definition export_pi_for_openscop (varctxt : list Instr.ident) (pi : PolyLang.PolyInstr)
    : PolyLang.PolyInstr :=
    let names :=
      List.app (List.map Instr.ident_to_varname varctxt)
        (List.map Instr.iterator_to_varname (List.seq 0 (PolyLang.pi_depth pi))) in
    {|
      PolyLang.pi_depth := PolyLang.pi_depth pi;
      PolyLang.pi_instr := PolyLang.pi_instr pi;
      PolyLang.pi_poly := PolyLang.pi_poly pi;
      PolyLang.pi_schedule := PolyLang.pi_schedule pi;
      PolyLang.pi_point_witness := PolyLang.pi_point_witness pi;
      PolyLang.pi_transformation := PolyLang.pi_transformation pi;
      PolyLang.pi_access_transformation := PolyLang.pi_access_transformation pi;
      PolyLang.pi_waccess := PolyLang.pi_waccess pi;
      PolyLang.pi_raccess :=
        PolyLang.pi_raccess pi ++ Instr.export_scalar_reads names (PolyLang.pi_instr pi);
    |}.

  Definition export_pprog_for_openscop (pol : PolyLang.t) : PolyLang.t :=
    let '(pis, varctxt, vars) := pol in
    let names :=
      List.map Instr.ident_to_varname varctxt in
    let vars' :=
      List.fold_left
        (fun acc pi =>
           List.fold_left add_var_nodup
             (Instr.export_scalar_read_vars
                (List.app names
                   (List.map Instr.iterator_to_varname (List.seq 0 (PolyLang.pi_depth pi))))
                (PolyLang.pi_instr pi))
             acc)
        pis vars in
    (List.map (export_pi_for_openscop varctxt) pis, varctxt, vars').

  Definition to_openscop_source (pol : PolyLang.t) : option OpenScop :=
    PolyLang.to_openscop (export_pprog_for_openscop pol).

  Definition scheduler cpol :=
    match to_openscop_source cpol with
    | Some inscop =>
        match scop_scheduler inscop with
      | Okk outscop =>
          match PolyLang.from_openscop_schedule_only cpol outscop with
          | Okk pol => Okk pol
          | Err msg => Err msg
          end
        | Err msg => Err msg
        end
    | None => Err "Transform pol to openscop failed"
    end.

  Definition to_phase_openscop (cpol: PolyLang.t) : option OpenScop :=
    to_openscop_source cpol.
End SPolIRs.
