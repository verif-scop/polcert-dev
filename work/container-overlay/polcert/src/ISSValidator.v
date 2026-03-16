Require Import ISSBoolChecker.
Require Import ISSRefinement.
Require Import ISSWitness.
Require Import PolIRs.

Module ISSValidator (PolIRs: POLIRS).

Module ISSCheck := ISSBoolChecker PolIRs.
Module ISSRefine := ISSRefinement PolIRs.

Definition check_domain_partition_shapeb :=
  ISSCheck.check_domain_partition_shapeb.

Definition checked_iss_shape_validate :=
  check_domain_partition_shapeb.

Definition check_domain_partition_cut_shapeb :=
  ISSCheck.check_domain_partition_cut_shapeb.

Definition checked_iss_cut_shape_validate :=
  check_domain_partition_cut_shapeb.

Definition check_domain_partition_complete_cut_shapeb :=
  ISSCheck.check_domain_partition_complete_cut_shapeb.

Definition checked_iss_complete_cut_shape_validate :=
  check_domain_partition_complete_cut_shapeb.

Definition domain_partition_shape :=
  ISSRefine.domain_partition_shape.

Definition domain_partition_shape_with_witness :=
  ISSRefine.domain_partition_shape_with_witness.

Definition domain_partition_cut_shape :=
  ISSRefine.domain_partition_cut_shape.

Definition domain_partition_complete_cut_shape :=
  ISSRefine.domain_partition_complete_cut_shape.

Definition checked_iss_shape_validate_correct :=
  ISSCheck.check_domain_partition_shapeb_sound.

Definition checked_iss_cut_shape_validate_correct :=
  ISSCheck.check_domain_partition_cut_shapeb_sound.

Definition checked_iss_complete_cut_shape_validate_correct :=
  ISSCheck.check_domain_partition_complete_cut_shapeb_sound.

End ISSValidator.
