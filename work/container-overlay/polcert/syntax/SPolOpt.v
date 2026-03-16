Require Import SPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt SPolIRs.
Module Extractor := CoreOpt.Extractor.

Definition add_var_nodup := SPolIRs.add_var_nodup.
Definition export_pi_for_openscop := SPolIRs.export_pi_for_openscop.
Definition export_pprog_for_openscop := SPolIRs.export_pprog_for_openscop.
Definition to_source_openscop := SPolIRs.to_openscop_source.

Definition proved_opt : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreOpt.Opt.

Definition proved_opt_with_iss : SPolIRs.Loop.t -> imp SPolIRs.Loop.t :=
  CoreOpt.Opt_with_iss.

Definition opt (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  proved_opt loop.

Definition opt_with_iss (loop : SPolIRs.Loop.t) : imp SPolIRs.Loop.t :=
  proved_opt_with_iss loop.

Definition opt_poly (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_poly_with_iss (pol : SPolIRs.PolyLang.t) : imp SPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly_with_iss
    (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_scop (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.

Definition opt_scop_with_iss (scop : OpenScop) : imp SPolIRs.Loop.t :=
  match SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly_with_iss pol
  | Err msg => res_to_alarm SPolIRs.Loop.dummy (Err msg)
  end.
