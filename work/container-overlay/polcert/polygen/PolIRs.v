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
Parameter to_phase_openscop: PolyLang.t -> option OpenScop.
Parameter phase_scop_scheduler: OpenScop -> result (OpenScop * OpenScop).
Parameter infer_tiling_witness_scops:
  OpenScop -> OpenScop -> result (list statement_tiling_witness).


End POLIRS.
