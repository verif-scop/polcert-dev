Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.
Require Import InstanceProjectionWitness.
Require Import OverlapClosureWitness.
Require Import OverlapValueWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** Combined wrapper for overlapped tiling / private recomputation.

    Overlap is primarily an instance-count-changing transformation: target
    computations may duplicate source instances, but only commit-role instances
    are source-visible.  If a transformation materializes tile-private halo or
    local storage, it also needs a separation witness.

    This module provides two composable theorem shapes:

      - no-private overlap: projection + commit exact cover;
      - private-buffer overlap: projection + commit exact cover + private
        storage separation.
      - closure-aware overlap: projection + commit exact cover + finite
        tile-local dependence closure, optionally with private separation.
      - ordered closure-aware overlap: the same local closure, plus a finite
        producer-before-consumer condition for tile-produced dependencies.

    Dependence closure and value equivalence of recomputed/internal instances
    are separate obligations: the finite closure witness records where each
    dependency may come from, while the value witness records that every
    projected recomputation has the same finite value as the source instance it
    represents. *)

Module OverlapTilingValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_overlap_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_overlap_source_view_correct :
  forall before source_view ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition overlap_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record overlap_no_private_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (source_view after: PolyLang.t) : Prop := {
  onp_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  onp_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  op_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  op_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  op_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (source_view after: PolyLang.t) : Prop := {
  oc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  oc_closure :
    overlap_closure_obligations tiles;
  oc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  opc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  opc_closure :
    overlap_closure_obligations tiles;
  opc_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  opc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_ordered_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (source_view after: PolyLang.t) : Prop := {
  ooc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  ooc_closure :
    overlap_ordered_closure_obligations tiles;
  ooc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_ordered_closure_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  opoc_projection :
    instance_projection_obligations
      source_domain source_liveouts (overlap_tiles_targets tiles);
  opoc_closure :
    overlap_ordered_closure_obligations tiles;
  opoc_private_separation :
    private_separation_obligations
      private_cells public_cells frame_cells;
  opoc_semantic_refinement :
    overlap_source_view_refines_view
      input_view output_view source_view after;
}.

Record overlap_private_ordered_closure_compatible_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (private_cells public_cells frame_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  opocc_base :
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after;
  opocc_storage_compatible :
    storage_compatibility_obligations
      private_mapping logical_specs private_specs;
}.

Record overlap_private_ordered_closure_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (tiles: list overlap_tile)
    (target_values: list (overlap_value_entry value))
    (private_cells public_cells frame_cells: list MemCell)
    (private_mapping: reuse_mapping)
    (logical_specs private_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  opoccv_compatible_base :
    overlap_private_ordered_closure_compatible_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after;
  opoccv_values :
    overlap_value_obligations
      value (overlap_tiles_targets tiles) target_values;
}.

Definition overlap_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_overlap_no_private_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_no_private_view_contract
      input_view output_view source_domain source_liveouts targets
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets
         before source_view after ok Hret Hok Hprojection Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_closureb tiles = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok
         Hret Hok Hprojection Hclosure Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_ordered_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         before source_view after ok
         Hret Hok Hprojection Hclosure Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_ordered_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_view_contract
      input_view output_view source_domain source_liveouts targets
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_ordered_closure_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts
       (overlap_tiles_targets tiles) Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_overlap_ordered_closureb_sound tiles Hclosure)
    as Hclosure_obligations.
  pose proof
    (check_private_separationb_sound
       private_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_overlap_private_ordered_closure_compatible_view_correct :
  forall input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok,
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_compatible_view_contract
      input_view output_view source_domain source_liveouts tiles
      private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts tiles
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok
         Hret Hok Hprojection Hclosure Hseparation Hstorage Hsemantics.
  pose proof
    (checked_overlap_private_ordered_closure_view_correct
       input_view output_view source_domain source_liveouts tiles
       private_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hclosure Hseparation Hsemantics)
    as [Hbase Hview].
  pose proof
    (check_storage_compatibilityb_sound
       private_mapping logical_specs private_specs Hstorage)
    as Hstorage_obligations.
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_overlap_private_ordered_closure_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok,
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    mayReturn (check_overlap_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts
      (overlap_tiles_targets tiles) = true ->
    check_overlap_ordered_closureb tiles = true ->
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    check_storage_compatibilityb
      private_mapping logical_specs private_specs = true ->
    check_overlap_valueb
      value_eqb (overlap_tiles_targets tiles) target_values = true ->
    overlap_source_view_refines_view
      input_view output_view source_view after ->
    overlap_private_ordered_closure_compatible_value_view_contract
      value input_view output_view source_domain source_liveouts tiles
      target_values private_cells public_cells frame_cells
      private_mapping logical_specs private_specs source_view after /\
    View.view_refinement
      input_view
      (overlap_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts tiles target_values
         private_cells public_cells frame_cells
         private_mapping logical_specs private_specs
         before source_view after ok
         Hvalue_eqb Hret Hok Hprojection Hclosure Hseparation Hstorage
         Hvalues Hsemantics.
  pose proof
    (check_overlap_valueb_sound
       value value_eqb Hvalue_eqb
       (overlap_tiles_targets tiles) target_values Hvalues)
    as Hvalue_obligations.
  pose proof
    (checked_overlap_private_ordered_closure_compatible_view_correct
       input_view output_view source_domain source_liveouts tiles
       private_cells public_cells frame_cells
       private_mapping logical_specs private_specs
       before source_view after ok
       Hret Hok Hprojection Hclosure Hseparation Hstorage Hsemantics)
    as [Hcompatible_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End OverlapTilingValidator.
