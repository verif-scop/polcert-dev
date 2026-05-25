Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import StorageWitness.
Require Import StateObservation.
Require Import LayoutWitness.

Import ListNotations.

(** Feature target: injective layout/access remapping.

    The intended optimization shape is:

      - source [before] is the original logical program;
      - [source_view] has source/logical storage accesses but the target schedule
        to be checked by the existing validator;
      - [after] is the physical-layout target program;
      - [rel target_cell source_cell] explains which physical target cell
        represents which logical source cell.

    This module deliberately does not pretend that changing PolyInstr access
    lists is enough: actual PolyLang execution is driven by [pi_instr].  The
    feature-specific obligation is therefore [layout_source_view_refines], a
    semantic proof that the physical-layout target refines the logical
    source-view under the cell-relation observation. *)

Module LayoutRemapValidator
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module Observation := StateObservation PolIRs Observer.
Module View := Pipeline.View.
Module Layout := LayoutWitness PolIRs.
Module Storage := Layout.Storage.

Definition layout_observation
    (rel: cell_relation) : Transform.observation :=
  Observation.related_cells_observation rel.

Definition layout_state_relation
    (rel: cell_relation) : Transform.state_relation :=
  layout_observation rel.

Definition layout_view (rel: cell_relation) : View.view :=
  Observation.related_cells_view rel.

Definition layout_composed_observation
    (rel: cell_relation) : Transform.observation :=
  Transform.compose_observation
    (layout_observation rel)
    Transform.identity_observation.

Definition layout_pipeline_final_relation
    (rel: cell_relation) : Transform.state_relation :=
  Transform.compose_state_relation
    (layout_state_relation rel)
    Transform.identity_observation.

Definition layout_pipeline_final_view
    (rel: cell_relation) : View.view :=
  View.compose_view (layout_view rel) View.identity_view.

Definition check_layout_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_layout_source_view_correct :
  forall before source_view ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition layout_source_view_refines
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop :=
  Transform.refinement_under (layout_observation rel) source_view after.

Definition layout_source_view_relational_refines
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop :=
  Transform.relational_refinement
    (layout_state_relation rel)
    (layout_state_relation rel)
    source_view after.

Definition layout_source_view_refines_view
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop :=
  View.view_refinement
    (layout_view rel)
    (layout_view rel)
    source_view after.

Record layout_remap_contract
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop := {
  lrc_access_remap :
    Storage.pprog_same_instance_access_remap rel source_view after;
  lrc_semantic_refinement :
    layout_source_view_refines rel source_view after;
}.

Record layout_remap_relational_contract
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop := {
  lrrc_access_remap :
    Storage.pprog_same_instance_access_remap rel source_view after;
  lrrc_semantic_refinement :
    layout_source_view_relational_refines rel source_view after;
}.

Record layout_remap_view_contract
    (rel: cell_relation)
    (source_view after: PolyLang.t) : Prop := {
  lrvc_access_remap :
    Storage.pprog_same_instance_access_remap rel source_view after;
  lrvc_semantic_refinement :
    layout_source_view_refines_view rel source_view after;
}.

Theorem checked_layout_remap_correct :
  forall rel before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    layout_remap_contract rel source_view after ->
    Transform.refinement_under
      (layout_composed_observation rel)
      before after.
Proof.
  intros rel before source_view after ok Hret Hok Hcontract.
  destruct Hcontract as [_ Hlayout].
  unfold layout_composed_observation.
  eapply Transform.refinement_under_compose.
  - exact Hlayout.
  - eapply check_layout_source_view_correct; eauto.
Qed.

Theorem checked_layout_remap_relational_correct :
  forall rel before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    layout_remap_relational_contract rel source_view after ->
    Transform.relational_refinement
      (layout_state_relation rel)
      (layout_pipeline_final_relation rel)
      before after.
Proof.
  intros rel before source_view after ok Hret Hok Hcontract.
  destruct Hcontract as [_ Hlayout].
  pose proof
    (Transform.relational_refinement_compose
       (layout_state_relation rel)
       (layout_state_relation rel)
       Transform.same_state_relation
       Transform.identity_observation
       before source_view after
       Hlayout
       (Transform.refinement_under_to_relational
          Transform.identity_observation before source_view
          (check_layout_source_view_correct before source_view ok
             Hret Hok)))
    as Hcomposed.
  eapply Transform.relational_refinement_monotone.
  - apply Transform.relation_included_compose_right_same_intro.
  - unfold Transform.relation_included.
    intros st_target st_source Hrel_final.
    exact Hrel_final.
  - exact Hcomposed.
Qed.

Theorem checked_layout_remap_view_correct :
  forall rel before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    layout_remap_view_contract rel source_view after ->
    View.view_refinement
      (layout_view rel)
      (layout_pipeline_final_view rel)
      before after.
Proof.
  intros rel before source_view after ok Hret Hok Hcontract.
  destruct Hcontract as [_ Hlayout].
  apply
    (Pipeline.compose_checked_source_view
       (layout_view rel) (layout_view rel)
       before source_view after ok);
    assumption.
Qed.

Theorem checked_array_rename_layout_remap_correct :
  forall renames before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    Layout.check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    layout_source_view_refines
      (array_rename_cell_relation renames) source_view after ->
    Transform.refinement_under
      (layout_composed_observation
         (array_rename_cell_relation renames))
      before after.
Proof.
  intros renames before source_view after ok
         Hcheck Htrue Hremap Hlayout.
  eapply checked_layout_remap_correct.
  - exact Hcheck.
  - exact Htrue.
  - constructor.
    + pose proof
        (Layout.check_pprog_array_rename_access_remapb_sound
           renames source_view after Hremap)
        as Haccess.
      exact Haccess.
    + exact Hlayout.
Qed.

Theorem checked_array_rename_layout_remap_relational_correct :
  forall renames before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    Layout.check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    layout_source_view_relational_refines
      (array_rename_cell_relation renames) source_view after ->
    Transform.relational_refinement
      (layout_state_relation
         (array_rename_cell_relation renames))
      (layout_pipeline_final_relation
         (array_rename_cell_relation renames))
      before after.
Proof.
  intros renames before source_view after ok
         Hcheck Htrue Hremap Hlayout.
  eapply checked_layout_remap_relational_correct.
  - exact Hcheck.
  - exact Htrue.
  - constructor.
    + pose proof
        (Layout.check_pprog_array_rename_access_remapb_sound
           renames source_view after Hremap)
        as Haccess.
      exact Haccess.
    + exact Hlayout.
Qed.

Theorem checked_array_rename_layout_remap_view_correct :
  forall renames before source_view after ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    Layout.check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    layout_source_view_refines_view
      (array_rename_cell_relation renames) source_view after ->
    View.view_refinement
      (layout_view
         (array_rename_cell_relation renames))
      (layout_pipeline_final_view
         (array_rename_cell_relation renames))
      before after.
Proof.
  intros renames before source_view after ok
         Hcheck Htrue Hremap Hlayout.
  eapply checked_layout_remap_view_correct.
  - exact Hcheck.
  - exact Htrue.
  - constructor.
    + pose proof
        (Layout.check_pprog_array_rename_access_remapb_sound
           renames source_view after Hremap)
        as Haccess.
      exact Haccess.
    + exact Hlayout.
Qed.

Lemma identity_layout_source_view_refines_self :
  forall pp,
    layout_source_view_refines
      Observation.observer_identity_cell_relation pp pp.
Proof.
  unfold layout_source_view_refines.
  unfold layout_observation.
  unfold Transform.refinement_under.
  intros pp st0 st_after Hsem.
  exists st_after.
  split.
  - exact Hsem.
  - eapply Observation.identity_related_cells_observation_contains_state_eq.
    apply PolIRs.State.eq_refl.
Qed.

Lemma identity_layout_remap_contract_self :
  forall pp,
    layout_remap_contract
      Observation.observer_identity_cell_relation pp pp.
Proof.
  intros pp.
  constructor.
  - apply Storage.pprog_same_instance_access_remap_refl.
    apply Observation.observer_identity_cell_relation_reflexive.
  - apply identity_layout_source_view_refines_self.
Qed.

Theorem checked_identity_layout_remap_correct :
  forall before source_view ok,
    mayReturn (check_layout_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      (layout_composed_observation
         Observation.observer_identity_cell_relation)
      before source_view.
Proof.
  intros before source_view ok Hret Hok.
  eapply checked_layout_remap_correct.
  - exact Hret.
  - exact Hok.
  - apply identity_layout_remap_contract_self.
Qed.

End LayoutRemapValidator.
