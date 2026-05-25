Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import LayoutWitness.
Require Import PaddingLayoutWitness.
Require Import LayoutValueWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for padded/injective layout maps.

    The finite witness proves only allocation and separation facts for the
    boundary cell map.  The instruction-level proof that all target accesses
    use the mapped physical cells and preserve the represented values remains
    the semantic refinement obligation. *)

Module PaddingLayoutValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.
Module Layout := LayoutWitness PolIRs.

Definition check_padding_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_padding_source_view_correct :
  forall before source_view ok,
    mayReturn (check_padding_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition padding_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record padding_layout_view_contract
    (input_view output_view: View.view)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  plvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  plvvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plvvc_values :
    layout_value_obligations value mapping entries;
  plvvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_access_view_contract
    (input_view output_view: View.view)
    (renames: list array_rename)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  plavc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plavc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_rename_cell_relation renames)
      source_view after;
  plavc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_access_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (renames: list array_rename)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  plavvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plavvc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_rename_cell_relation renames)
      source_view after;
  plavvc_values :
    layout_value_obligations value mapping entries;
  plavvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_permutation_access_view_contract
    (input_view output_view: View.view)
    (layouts: list array_index_permutation)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  plpavc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plpavc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_index_permutation_cell_relation layouts)
      source_view after;
  plpavc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_permutation_access_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (layouts: list array_index_permutation)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  plpavvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plpavvc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_index_permutation_cell_relation layouts)
      source_view after;
  plpavvc_values :
    layout_value_obligations value mapping entries;
  plpavvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_affine_access_view_contract
    (input_view output_view: View.view)
    (layouts: list array_affine_layout)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  plaavc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plaavc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_affine_layout_cell_relation layouts)
      source_view after;
  plaavc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_affine_access_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (layouts: list array_affine_layout)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  plaavvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  plaavvc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (array_affine_layout_cell_relation layouts)
      source_view after;
  plaavvc_values :
    layout_value_obligations value mapping entries;
  plaavvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_declared_access_view_contract
    (input_view output_view: View.view)
    (layouts: list declared_array_layout)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  pldavc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  pldavc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (declared_layout_cell_relation layouts)
      source_view after;
  pldavc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_declared_access_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (layouts: list declared_array_layout)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  pldavvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  pldavvc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (declared_layout_cell_relation layouts)
      source_view after;
  pldavvc_values :
    layout_value_obligations value mapping entries;
  pldavvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Record padding_layout_declared_access_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (layouts: list declared_array_layout)
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell)
    (logical_specs physical_specs: list storage_spec)
    (entries: list (layout_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  pldacvvc_padding :
    padding_layout_obligations
      mapping padding_cells allocated_cells;
  pldacvvc_access_remap :
    Layout.Storage.pprog_same_instance_access_remap
      (declared_layout_cell_relation layouts)
      source_view after;
  pldacvvc_values :
    layout_value_obligations value mapping entries;
  pldacvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  pldacvvc_semantic_refinement :
    padding_source_view_refines_view
      input_view output_view source_view after;
}.

Definition padding_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_padding_layout_view_correct :
  forall input_view output_view
         mapping padding_cells allocated_cells
         before source_view after ok,
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_view_contract
      input_view output_view mapping padding_cells allocated_cells
      source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         mapping padding_cells allocated_cells
         before source_view after ok Hret Hok Hpadding Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         mapping padding_cells allocated_cells entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_value_view_contract
      value input_view output_view mapping padding_cells allocated_cells
      entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view
         mapping padding_cells allocated_cells entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Hvalues Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_access_view_correct :
  forall input_view output_view renames
         mapping padding_cells allocated_cells
         before source_view after ok,
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_access_view_contract
      input_view output_view renames mapping padding_cells allocated_cells
      source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view renames
         mapping padding_cells allocated_cells
         before source_view after ok
         Hret Hok Hpadding Haccess Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_rename_access_remapb_sound
       renames source_view after Haccess)
    as Haccess_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_permutation_access_view_correct :
  forall input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok,
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_index_permutation_access_remapb
      layouts source_view after = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_permutation_access_view_contract
      input_view output_view layouts mapping padding_cells allocated_cells
      source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok
         Hret Hok Hpadding Haccess Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_index_permutation_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_affine_access_view_correct :
  forall input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok,
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_affine_layout_access_remapb
      layouts source_view after = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_affine_access_view_contract
      input_view output_view layouts mapping padding_cells allocated_cells
      source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok
         Hret Hok Hpadding Haccess Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_affine_layout_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_declared_access_view_correct :
  forall input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok,
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_declared_layout_access_remapb
      layouts source_view after = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_declared_access_view_contract
      input_view output_view layouts mapping padding_cells allocated_cells
      source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view layouts
         mapping padding_cells allocated_cells
         before source_view after ok
         Hret Hok Hpadding Haccess Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_declared_layout_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_access_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view renames
         mapping padding_cells allocated_cells entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_access_value_view_contract
      value input_view output_view renames
      mapping padding_cells allocated_cells entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view renames
         mapping padding_cells allocated_cells entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Haccess Hvalues Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_rename_access_remapb_sound
       renames source_view after Haccess)
    as Haccess_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_permutation_access_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_index_permutation_access_remapb
      layouts source_view after = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_permutation_access_value_view_contract
      value input_view output_view layouts
      mapping padding_cells allocated_cells entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Haccess Hvalues Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_index_permutation_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_affine_access_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_array_affine_layout_access_remapb
      layouts source_view after = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_affine_access_value_view_contract
      value input_view output_view layouts
      mapping padding_cells allocated_cells entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Haccess Hvalues Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_array_affine_layout_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_declared_access_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_declared_layout_access_remapb
      layouts source_view after = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_declared_access_value_view_contract
      value input_view output_view layouts
      mapping padding_cells allocated_cells entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view layouts
         mapping padding_cells allocated_cells entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Haccess Hvalues Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_declared_layout_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_padding_layout_declared_access_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view layouts
         mapping padding_cells allocated_cells
         logical_specs physical_specs entries
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn
      (check_padding_source_view before source_view) ok ->
    ok = true ->
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    Layout.check_pprog_declared_layout_access_remapb
      layouts source_view after = true ->
    check_layout_valueb value value_eqb mapping entries = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    padding_source_view_refines_view
      input_view output_view source_view after ->
    padding_layout_declared_access_compatible_value_view_contract
      value input_view output_view layouts
      mapping padding_cells allocated_cells
      logical_specs physical_specs entries source_view after /\
    View.view_refinement
      input_view
      (padding_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb
         input_view output_view layouts
         mapping padding_cells allocated_cells
         logical_specs physical_specs entries
         before source_view after ok Hvalue_eqb Hret Hok
         Hpadding Haccess Hvalues Hstorage Hsemantics.
  pose proof
    (check_padding_layoutb_sound
       mapping padding_cells allocated_cells Hpadding)
    as Hpadding_obligations.
  pose proof
    (Layout.check_pprog_declared_layout_access_remapb_sound
       layouts source_view after Haccess)
    as Haccess_obligations.
  pose proof
    (check_layout_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalues)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hstorage)
    as Hstorage_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

End PaddingLayoutValidator.
