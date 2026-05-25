Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.

Import ListNotations.

(** Common source-view pipeline for storage-aware validators.

    Most exploratory storage validators have the same shape:

      1. use the existing schedule/control validator to relate [before] to a
         storage-neutral [source_view];
      2. prove feature-specific finite witness obligations;
      3. assume or prove a semantic [view_refinement] from [source_view] to
         the storage-changing [after] program;
      4. compose the two refinements.

    This module factors out step 1 and step 4.  It deliberately says nothing
    about the feature-specific witness; each validator can keep its own
    bookkeeping, value-flow, algebra, or lifetime obligations while sharing the
    same endpoint relation discipline. *)

Module ViewPipeline (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module AffineCore := AffineValidator PolIRs.
Module Transform := TransformContract PolIRs.
Module View := StateView PolIRs.

Definition check_source_view
    (before source_view: PolyLang.t) : imp bool :=
  AffineCore.validate_general before source_view.

Theorem check_source_view_correct :
  forall before source_view ok,
    mayReturn (check_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  unfold check_source_view.
  intros before source_view ok Hret Hok.
  eapply Transform.general_validate_identity_sound; eauto.
Qed.

Definition source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  View.view_refinement
    input_view output_view source_view after.

Definition pipeline_final_view
    (output_view: View.view) : View.view :=
  View.compose_view output_view View.identity_view.

Theorem compose_checked_source_view :
  forall input_view output_view before source_view after ok,
    mayReturn (check_source_view before source_view) ok ->
    ok = true ->
    source_view_refines_view
      input_view output_view source_view after ->
    View.view_refinement
      input_view
      (pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view before source_view after ok
         Hret Hok Hsemantics.
  pose proof
    (View.view_refinement_compose
       input_view output_view
       View.same_state_view View.identity_view
       before source_view after
       Hsemantics
       (View.refinement_under_to_view_refinement
          View.identity_view before source_view
          (check_source_view_correct before source_view ok Hret Hok)))
    as Hcomposed.
  eapply
    (View.view_refinement_monotone
       (View.compose_view input_view View.same_state_view)
       (View.compose_view output_view View.identity_view)
       input_view
       (pipeline_final_view output_view)
       before after).
  - apply View.view_included_compose_right_same_intro.
  - unfold View.view_included.
    unfold pipeline_final_view.
    simpl.
    unfold Transform.relation_included.
    intros st_target st_source Hrel.
    exact Hrel.
  - exact Hcomposed.
Qed.

End ViewPipeline.
