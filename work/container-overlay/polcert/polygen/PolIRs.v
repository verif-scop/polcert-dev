Require Import InstrTy.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import TilingWitness.

Module Type POLIRS.

Declare Module Instr : INSTR.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module PolyLang := PolyLang Instr.
Module PolyLoop := PolyLoop Instr.
Module Loop := Loop Instr.

Parameter scheduler: PolyLang.t -> result PolyLang.t.
(** Clear alias: the legacy [scheduler] field is the affine-only scheduler
    contract used by the old validated pipeline. *)
Definition affine_scheduler := scheduler.

Parameter to_phase_openscop: PolyLang.t -> option OpenScop.
(** Clear alias: export a program to the OpenScop view consumed by the external
    two-stage Pluto phase pipeline (affine phase, then tiling phase). *)
Definition export_for_pluto_phase_pipeline := to_phase_openscop.

Parameter phase_scop_scheduler: OpenScop -> result (OpenScop * OpenScop).
(** Clear alias: run the external two-stage Pluto phase pipeline and return the
    affine mid-point and the final tiled OpenScop. *)
Definition run_pluto_phase_pipeline := phase_scop_scheduler.

Parameter infer_tiling_witness_scops:
  OpenScop -> OpenScop -> result (list statement_tiling_witness).


End POLIRS.
