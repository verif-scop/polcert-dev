Require Import CPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import TilingWitness.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt CPolIRs.

Definition opt : CPolIRs.Loop.t -> imp CPolIRs.Loop.t := CoreOpt.Opt.

Definition opt_poly (pol : CPolIRs.PolyLang.t) : imp CPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_scop (scop : OpenScop) : imp CPolIRs.Loop.t :=
  match CPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm CPolIRs.Loop.dummy (Err msg)
  end.

Definition checked_tiling_validate
    (before after: CPolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  CoreOpt.checked_tiling_validate before after ws.
