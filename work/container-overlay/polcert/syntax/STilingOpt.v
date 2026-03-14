Require Import SPolIRs.
Require Import SPolOpt.
Require Import OpenScop.
Require Import Result.
Require Import TilingWitness.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module CoreOpt := SPolOpt.CoreOpt.
Module TilingCheck := CoreOpt.TilingCheck.
Module Tiling := CoreOpt.CheckedTiling.Tiling.
Module TilingPolIRs := CoreOpt.CheckedTiling.TilingPolIRs.

Definition checked_tiling_validate
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  CoreOpt.CheckedTiling.checked_tiling_validate before after ws.

Definition checked_tiling_prepared_codegen
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp TilingPolIRs.Loop.t :=
  CoreOpt.CheckedTiling.checked_tiling_prepared_codegen before after ws.
