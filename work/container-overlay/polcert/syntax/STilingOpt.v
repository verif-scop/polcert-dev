Require Import SPolIRs.
Require Import SPolOpt.
Require Import ImpureAlarmConfig.
Require Import TilingWitness.
Require Import Vpl.Impure.

Definition outer_to_tiling_pprog :=
  SPolOpt.CoreOpt.outer_to_tiling_pprog.

Definition check_pprog_tiling_sourceb :=
  SPolOpt.CoreOpt.check_pprog_tiling_sourceb.

Definition checked_tiling_validate :=
  SPolOpt.CoreOpt.checked_tiling_validate.
