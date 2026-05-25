Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** View-level wrapper for instance-count-changing transformations.

    The witness layer handles only projection/role bookkeeping: target
    instances project to source instances, and commit-role instances cover the
    source live-outs exactly once.  Dependence closure, recomputed value
    equivalence, and storage visibility are still semantic obligations.

    This wrapper makes the separation explicit while letting overlap/helper
    transformations participate in the same [view_refinement] composition
    discipline as schedule and storage passes. *)

Module InstanceProjectionValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_projection_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_projection_source_view_correct :
  forall before source_view ok,
    mayReturn (check_projection_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition projection_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record instance_projection_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (source_view after: PolyLang.t) : Prop := {
  ipvc_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  ipvc_semantic_refinement :
    projection_source_view_refines_view
      input_view output_view source_view after;
}.

Definition projection_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_instance_projection_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets
         before source_view after ok,
    mayReturn
      (check_projection_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    projection_source_view_refines_view
      input_view output_view source_view after ->
    instance_projection_view_contract
      input_view output_view source_domain source_liveouts targets
      source_view after /\
    View.view_refinement
      input_view
      (projection_pipeline_final_view output_view)
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

End InstanceProjectionValidator.
