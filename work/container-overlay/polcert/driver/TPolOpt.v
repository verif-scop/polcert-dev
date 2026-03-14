Require Import TPolIRs.
Require Import OpenScop.
Require Import Result.
Require Import PolOpt.
Require Import TilingWitness.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := PolOpt TPolIRs.
Module TilingCheck := CoreOpt.TilingCheck.
Module Tiling := CoreOpt.CheckedTiling.Tiling.
Module TilingPolIRs := CoreOpt.CheckedTiling.TilingPolIRs.
Module TilingVal := CoreOpt.CheckedTiling.TilingVal.
Module TPrepare := CoreOpt.CheckedTiling.TPrepare.

Definition opt : TPolIRs.Loop.t -> imp TPolIRs.Loop.t := CoreOpt.Opt.

Definition opt_poly (pol : TPolIRs.PolyLang.t) : imp TPolIRs.Loop.t :=
  CoreOpt.phase_opt_prepared_from_poly (CoreOpt.Strengthen.strengthen_pprog pol).

Definition opt_scop (scop : OpenScop) : imp TPolIRs.Loop.t :=
  match TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol => opt_poly pol
  | Err msg => res_to_alarm TPolIRs.Loop.dummy (Err msg)
  end.

Definition checked_tiling_validate
    (before after: TPolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  CoreOpt.checked_tiling_validate before after ws.
