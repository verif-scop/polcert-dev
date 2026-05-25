Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.

Import ListNotations.

(** A first-class endpoint relation for storage-aware validation.

    [TransformContract] exposes the semantic shape:

      relational_refinement R_in R_out before after

    This module packages those relations as named state views.  The current
    affine validators use two standard views:

      - [same_state_view] for the input side, because the existing theorem
        starts source and target from the same Coq state object;
      - [identity_view] for the output side, because the final observation is
        [State.eq].

    Future storage transformations should add concrete view constructors for
    layout projection, private erasure, commit selection, merge, reuse, and
    phase selection.  They should prove [view_refinement] theorems rather than
    inventing feature-specific final-state relations. *)

(** The view carrier is intentionally defined outside the [StateView] functor.
    Otherwise each functor application creates a fresh record type, and
    validators that instantiate [StateView PolIRs] independently cannot share
    endpoint views through a common facade. *)
Record generic_state_view (state: Type) := {
  generic_state_view_rel : state -> state -> Prop;
}.

Arguments generic_state_view_rel {state} _ _ _.

Module StateView (PolIRs: POLIRS).

Module State := PolIRs.State.
Module PolyLang := PolIRs.PolyLang.
Module AffineCore := AffineValidator PolIRs.
Module Transform := TransformContract PolIRs.

Definition view := generic_state_view State.t.

Definition state_view_rel (state_view: view) : Transform.state_relation :=
  generic_state_view_rel state_view.

Definition mk_view (rel: Transform.state_relation) : view := {|
  generic_state_view_rel := rel;
|}.

Definition identity_view : view :=
  mk_view Transform.identity_observation.

Definition same_state_view : view :=
  mk_view Transform.same_state_relation.

Definition compose_view (target_mid mid_source: view) : view :=
  mk_view
    (Transform.compose_state_relation
      (state_view_rel target_mid)
      (state_view_rel mid_source)).

Definition view_included (smaller larger: view) : Prop :=
  Transform.relation_included
    (state_view_rel smaller)
    (state_view_rel larger).

Theorem view_included_refl :
  forall state_view,
    view_included state_view state_view.
Proof.
  unfold view_included.
  intros state_view.
  apply Transform.relation_included_refl.
Qed.

Theorem view_included_trans :
  forall first second third,
    view_included first second ->
    view_included second third ->
    view_included first third.
Proof.
  unfold view_included.
  intros first second third Hfirst_second Hsecond_third.
  eapply Transform.relation_included_trans; eauto.
Qed.

Theorem compose_view_monotone :
  forall target_mid target_mid'
         mid_source mid_source',
    view_included target_mid target_mid' ->
    view_included mid_source mid_source' ->
    view_included
      (compose_view target_mid mid_source)
      (compose_view target_mid' mid_source').
Proof.
  unfold view_included, compose_view.
  simpl.
  intros target_mid target_mid' mid_source mid_source'
         Htarget Hsource.
  apply Transform.compose_state_relation_monotone; assumption.
Qed.

Definition view_refinement
    (input_view output_view: view)
    (before after: PolyLang.t) : Prop :=
  Transform.relational_refinement
    (state_view_rel input_view)
    (state_view_rel output_view)
    before after.

Theorem identity_view_contains_state_eq :
  Transform.observation_contains_state_eq
    (state_view_rel identity_view).
Proof.
  unfold Transform.observation_contains_state_eq.
  intros st_target st_source Heq.
  exact Heq.
Qed.

Theorem same_state_view_included_identity_view :
  view_included same_state_view identity_view.
Proof.
  unfold view_included, Transform.relation_included.
  unfold same_state_view, identity_view.
  simpl.
  unfold Transform.same_state_relation.
  intros st_target st_source Heq.
  subst st_source.
  apply State.eq_refl.
Qed.

Theorem view_included_compose_right_same_intro :
  forall input_view,
    view_included
      input_view
      (compose_view input_view same_state_view).
Proof.
  unfold view_included, compose_view, same_state_view.
  simpl.
  intros input_view.
  apply Transform.relation_included_compose_right_same_intro.
Qed.

Theorem view_included_compose_right_same_elim :
  forall input_view,
    view_included
      (compose_view input_view same_state_view)
      input_view.
Proof.
  unfold view_included, compose_view, same_state_view.
  simpl.
  intros input_view.
  apply Transform.relation_included_compose_right_same_elim.
Qed.

Theorem refinement_under_to_view_refinement :
  forall output_view before after,
    Transform.refinement_under
      (state_view_rel output_view) before after ->
    view_refinement same_state_view output_view before after.
Proof.
  unfold view_refinement.
  intros output_view before after Href.
  apply Transform.refinement_under_to_relational.
  exact Href.
Qed.

Theorem view_refinement_compose :
  forall target_mid_in target_mid_out
         mid_source_in mid_source_out
         before mid after,
    view_refinement target_mid_in target_mid_out mid after ->
    view_refinement mid_source_in mid_source_out before mid ->
    view_refinement
      (compose_view target_mid_in mid_source_in)
      (compose_view target_mid_out mid_source_out)
      before after.
Proof.
  unfold view_refinement, compose_view.
  simpl.
  intros target_mid_in target_mid_out mid_source_in mid_source_out
         before mid after Htarget_mid Hmid_source.
  eapply Transform.relational_refinement_compose; eauto.
Qed.

Theorem view_refinement_monotone :
  forall input_view output_view
         input_view' output_view'
         before after,
    view_included input_view' input_view ->
    view_included output_view output_view' ->
    view_refinement input_view output_view before after ->
    view_refinement input_view' output_view' before after.
Proof.
  unfold view_refinement, view_included.
  intros input_view output_view input_view' output_view'
         before after Hinput Houtput Href.
  eapply Transform.relational_refinement_monotone; eauto.
Qed.

Record checked_view_transform_family := {
  cvtf_input_view : view;
  cvtf_output_view : view;
  cvtf_check : PolyLang.t -> PolyLang.t -> imp bool;
  cvtf_check_sound :
    forall before after ok,
      mayReturn (cvtf_check before after) ok ->
      ok = true ->
      view_refinement cvtf_input_view cvtf_output_view before after;
}.

Theorem checked_view_transform_family_pair_compose :
  forall first second before mid after first_ok second_ok,
    mayReturn (cvtf_check first before mid) first_ok ->
    first_ok = true ->
    mayReturn (cvtf_check second mid after) second_ok ->
    second_ok = true ->
    view_refinement
      (compose_view (cvtf_input_view second) (cvtf_input_view first))
      (compose_view (cvtf_output_view second) (cvtf_output_view first))
      before after.
Proof.
  intros first second before mid after first_ok second_ok
         Hfirst_ret Hfirst_ok Hsecond_ret Hsecond_ok.
  eapply view_refinement_compose.
  - eapply cvtf_check_sound; eauto.
  - eapply cvtf_check_sound; eauto.
Qed.

Theorem affine_validate_identity_view_sound :
  forall before after ok,
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    view_refinement same_state_view identity_view before after.
Proof.
  unfold view_refinement, same_state_view, identity_view.
  simpl.
  intros before after ok Hret Hok.
  eapply Transform.affine_validate_identity_relational_sound; eauto.
Qed.

Definition affine_identity_view_family
    : checked_view_transform_family := {|
  cvtf_input_view := same_state_view;
  cvtf_output_view := identity_view;
  cvtf_check := AffineCore.validate;
  cvtf_check_sound := affine_validate_identity_view_sound;
|}.

Theorem general_validate_identity_view_sound :
  forall before after ok,
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    view_refinement same_state_view identity_view before after.
Proof.
  unfold view_refinement, same_state_view, identity_view.
  simpl.
  intros before after ok Hret Hok.
  eapply Transform.general_validate_identity_relational_sound; eauto.
Qed.

Definition general_identity_view_family
    : checked_view_transform_family := {|
  cvtf_input_view := same_state_view;
  cvtf_output_view := identity_view;
  cvtf_check := AffineCore.validate_general;
  cvtf_check_sound := general_validate_identity_view_sound;
|}.

End StateView.
