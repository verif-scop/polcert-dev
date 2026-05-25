Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import FramePreservationWitness.

Import ListNotations.

(** View-level wrapper for contextual frame preservation.

    The finite frame witness says that the transformed fragment writes only
    allowed cells, and those allowed cells are disjoint from the surrounding
    context frame.  This validator layer packages that side condition with the
    standard source-view pipeline theorem.  It does not change the output view;
    it records the context-safety obligation that should be composed with a
    feature-specific storage view. *)

Module FramePreservationValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_frame_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_frame_source_view_correct :
  forall before source_view ok,
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition frame_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record frame_preservation_view_contract
    (input_view output_view: View.view)
    (frame_cells write_cells allowed_write_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  fpvc_frame :
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells;
  fpvc_writes_disjoint :
    writes_disjoint_from_frame write_cells frame_cells;
  fpvc_semantic_refinement :
    frame_source_view_refines_view
      input_view output_view source_view after;
}.

Definition frame_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_frame_preservation_view_correct :
  forall input_view output_view frame_cells write_cells allowed_write_cells
         before source_view after ok,
    mayReturn (check_frame_source_view before source_view) ok ->
    ok = true ->
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    frame_source_view_refines_view
      input_view output_view source_view after ->
    frame_preservation_view_contract
      input_view output_view frame_cells write_cells allowed_write_cells
      source_view after /\
    View.view_refinement
      input_view
      (frame_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view frame_cells write_cells allowed_write_cells
         before source_view after ok Hret Hok Hframe Hsemantics.
  pose proof
    (check_frame_preservationb_sound
       frame_cells write_cells allowed_write_cells Hframe)
    as Hframe_obligations.
  pose proof
    (frame_preservation_writes_disjoint
       frame_cells write_cells allowed_write_cells Hframe_obligations)
    as Hwrites_disjoint.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

End FramePreservationValidator.
