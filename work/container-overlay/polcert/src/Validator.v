Require Import AffineValidator.
Require Import TilingValidator.
Require Import PolIRs.

Module Validator (PolIRs: POLIRS).

Module AffineCore := AffineValidator PolIRs.
Module TilingCore := TilingValidator PolIRs.

Module TilingCheck := TilingCore.TilingCheck.
Module TilingPolIRs := TilingCore.TilingPolIRs.
Module GeneralValidator := TilingCore.TilingVal.
Module TPrepare := TilingCore.TPrepare.

(** Affine-only validator API. *)
Definition check_wf_polyinstr := AffineCore.check_wf_polyinstr.
Definition check_wf_polyprog := AffineCore.check_wf_polyprog.
Definition check_wf_polyinstr_tiling := AffineCore.check_wf_polyinstr_tiling.
Definition check_wf_polyprog_tiling := AffineCore.check_wf_polyprog_tiling.
Definition check_wf_polyinstr_general := AffineCore.check_wf_polyinstr_general.
Definition check_wf_polyprog_general := AffineCore.check_wf_polyprog_general.
Definition check_wf_polyinstr_correct := AffineCore.check_wf_polyinstr_correct.
Definition check_wf_polyprog_correct := AffineCore.check_wf_polyprog_correct.
Definition check_wf_polyinstr_affine_correct :=
  AffineCore.check_wf_polyinstr_affine_correct.
Definition check_wf_polyprog_general_correct :=
  AffineCore.check_wf_polyprog_tiling_correct.
Definition EqDom := AffineCore.EqDom.
Definition check_valid_access := AffineCore.check_valid_access.
Definition validate_instr_list := AffineCore.validate_instr_list.
Definition validate := AffineCore.validate.
Definition validate_general := AffineCore.validate_general.
Definition validate_tiling := AffineCore.validate_tiling.
Definition validate_correct := AffineCore.validate_correct.
Definition validate_general_correct := AffineCore.validate_tiling_correct.
Definition validate_tiling_correct := AffineCore.validate_tiling_correct.
Definition validate_preserve_wf_pprog := AffineCore.validate_preserve_wf_pprog.

(** Checked tiling validator API on the generic outer PolyLang type. *)
Definition to_tiling_pprog := TilingCore.to_tiling_pprog.
Definition from_tiling_pprog := TilingCore.from_tiling_pprog.
Definition outer_to_tiling_pprog := TilingCore.outer_to_tiling_pprog.
Definition check_pprog_tiling_sourceb :=
  TilingCheck.check_pprog_tiling_sourceb.
Definition checked_tiling_validate := TilingCore.checked_tiling_validate.
Definition checked_tiling_validate_outer := TilingCore.checked_tiling_validate_outer.
Definition checked_tiling_validate_poly := TilingCore.checked_tiling_validate_outer.
Definition import_canonical_tiled_after_outer :=
  TilingCore.import_canonical_tiled_after_outer.
Definition import_canonical_tiled_after_poly :=
  TilingCore.import_canonical_tiled_after_outer.
Definition checked_tiling_prepared_codegen :=
  TilingCore.checked_tiling_prepared_codegen.
Definition checked_tiling_validate_correct :=
  TilingCore.checked_tiling_validate_correct.
Definition checked_tiling_validate_outer_correct :=
  TilingCore.checked_tiling_validate_outer_correct.
Definition checked_tiling_validate_poly_correct :=
  TilingCore.checked_tiling_validate_outer_correct.
Definition checked_tiling_validate_implies_wf_after :=
  TilingCore.checked_tiling_validate_implies_wf_after.
Definition checked_tiling_validate_outer_implies_wf_after :=
  TilingCore.checked_tiling_validate_outer_implies_wf_after.
Definition checked_tiling_validate_poly_implies_wf_after :=
  TilingCore.checked_tiling_validate_outer_implies_wf_after.
Definition checked_tiling_prepared_codegen_correct :=
  TilingCore.checked_tiling_prepared_codegen_correct.

End Validator.
