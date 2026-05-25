Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.

Import ListNotations.

(** A small vocabulary for treating the current schedule validator as one
    instance of a more general transformation-validation shape.

    The existing affine and witness-aware validators prove a very strong
    postcondition: the target execution can be matched by a source execution
    whose final state is [State.eq] to the target final state.  Storage-changing
    transformations will need weaker observations: erase private storage,
    project layout-remapped cells, or expose only committed versions.  This file
    factors that observation relation out without changing the current
    validators or their proofs. *)

Module TransformContract (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module PolyLang := PolIRs.PolyLang.
Module AffineCore := AffineValidator PolIRs.

Definition state_relation := State.t -> State.t -> Prop.

Definition observation := state_relation.

(** Existing validators use full-state equality.  The argument order is
    target-state first, source-state second, matching [AffineValidator]'s
    correctness conclusion. *)
Definition identity_observation : observation := State.eq.

(** Some existing validators are even stricter than [State.eq] on the input:
    their theorem relates two programs started from the very same Coq state
    object.  This relation lets those same-initial-state theorems participate in
    a larger relational pipeline without requiring a generic state-equivalence
    stability lemma from every [State] implementation. *)
Definition same_state_relation : state_relation :=
  fun st_target st_source => st_target = st_source.

(** A future storage observation may be weaker than full-state equality, for
    example by erasing private buffers or by projecting target physical cells
    back to source logical cells.  To reuse the existing validators through such
    an observation, it is enough to know that [State.eq] implies the observation. *)
Definition observation_contains_state_eq (obs: observation) : Prop :=
  forall st_after st_before,
    State.eq st_after st_before ->
    obs st_after st_before.

Record observation_contract := {
  oc_observation : observation;
  oc_contains_state_eq :
    observation_contains_state_eq oc_observation;
}.

Definition identity_observation_contract : observation_contract := {|
  oc_observation := identity_observation;
  oc_contains_state_eq := fun _ _ H => H;
|}.

(** [refinement_under obs before after] says that every execution of [after] can
    be matched by an execution of [before], and the two final states agree under
    [obs].  The current validator instantiates [obs] with [State.eq].  Future
    storage validators should instantiate it with a projection/commit
    observation instead of weakening the existing theorems. *)
Definition refinement_under
    (obs: observation) (before after: PolyLang.t) : Prop :=
  forall st0 st_after,
    PolyLang.instance_list_semantics after st0 st_after ->
    exists st_before,
      PolyLang.instance_list_semantics before st0 st_before /\
      obs st_after st_before.

Definition relational_refinement
    (initial_rel final_rel: state_relation)
    (before after: PolyLang.t) : Prop :=
  forall st_target0 st_source0 st_target_after,
    initial_rel st_target0 st_source0 ->
    PolyLang.instance_list_semantics after st_target0 st_target_after ->
    exists st_source_after,
      PolyLang.instance_list_semantics before st_source0 st_source_after /\
      final_rel st_target_after st_source_after.

Definition compose_state_relation
    (target_mid mid_source: state_relation) : state_relation :=
  fun st_target st_source =>
    exists st_mid,
      target_mid st_target st_mid /\
      mid_source st_mid st_source.

Definition relation_included
    (smaller larger: state_relation) : Prop :=
  forall st_target st_source,
    smaller st_target st_source ->
    larger st_target st_source.

Theorem relation_included_refl :
  forall rel,
    relation_included rel rel.
Proof.
  unfold relation_included.
  auto.
Qed.

Theorem relation_included_trans :
  forall first second third,
    relation_included first second ->
    relation_included second third ->
    relation_included first third.
Proof.
  unfold relation_included.
  intros first second third Hfirst_second Hsecond_third
         st_target st_source Hfirst.
  apply Hsecond_third.
  apply Hfirst_second.
  exact Hfirst.
Qed.

Definition compose_observation
    (target_mid mid_source: observation) : observation :=
  compose_state_relation target_mid mid_source.

Theorem compose_state_relation_monotone :
  forall target_mid target_mid'
         mid_source mid_source',
    relation_included target_mid target_mid' ->
    relation_included mid_source mid_source' ->
    relation_included
      (compose_state_relation target_mid mid_source)
      (compose_state_relation target_mid' mid_source').
Proof.
  unfold relation_included, compose_state_relation.
  intros target_mid target_mid' mid_source mid_source'
         Htarget Hsource st_target st_source
         (st_mid & Htarget_mid & Hmid_source).
  exists st_mid.
  split.
  - eapply Htarget; eauto.
  - eapply Hsource; eauto.
Qed.

Theorem refinement_under_to_relational :
  forall obs before after,
    refinement_under obs before after ->
    relational_refinement same_state_relation obs before after.
Proof.
  unfold refinement_under, relational_refinement, same_state_relation.
  intros obs before after Href st_target0 st_source0
         st_target_after Heq Hsem_after.
  subst st_source0.
  eapply Href; eauto.
Qed.

Theorem refinement_under_compose :
  forall obs_target_mid obs_mid_source before mid after,
    refinement_under obs_target_mid mid after ->
    refinement_under obs_mid_source before mid ->
    refinement_under
      (compose_observation obs_target_mid obs_mid_source)
      before after.
Proof.
  unfold refinement_under, compose_observation.
  intros obs_target_mid obs_mid_source before mid after
         Hafter_mid Hmid_before st0 st_after Hsem_after.
  destruct (Hafter_mid st0 st_after Hsem_after)
    as (st_mid & Hsem_mid & Hobs_target_mid).
  destruct (Hmid_before st0 st_mid Hsem_mid)
    as (st_before & Hsem_before & Hobs_mid_source).
  exists st_before.
  split.
  - exact Hsem_before.
  - exists st_mid.
    split; auto.
Qed.

Theorem relational_refinement_compose :
  forall rel_target_mid0 rel_target_mid1
         rel_mid_source0 rel_mid_source1
         before mid after,
    relational_refinement rel_target_mid0 rel_target_mid1 mid after ->
    relational_refinement rel_mid_source0 rel_mid_source1 before mid ->
    relational_refinement
      (compose_state_relation rel_target_mid0 rel_mid_source0)
      (compose_state_relation rel_target_mid1 rel_mid_source1)
      before after.
Proof.
  unfold relational_refinement, compose_state_relation.
  intros rel_target_mid0 rel_target_mid1
         rel_mid_source0 rel_mid_source1
         before mid after Hafter_mid Hmid_before
         st_target0 st_source0 st_target_after
         (st_mid0 & Hrel_target_mid0 & Hrel_mid_source0)
         Hsem_after.
  destruct
    (Hafter_mid st_target0 st_mid0 st_target_after
       Hrel_target_mid0 Hsem_after)
    as (st_mid_after & Hsem_mid & Hrel_target_mid1).
  destruct
    (Hmid_before st_mid0 st_source0 st_mid_after
       Hrel_mid_source0 Hsem_mid)
    as (st_source_after & Hsem_source & Hrel_mid_source1).
  exists st_source_after.
  split.
  - exact Hsem_source.
  - exists st_mid_after.
    split; auto.
Qed.

Theorem relational_refinement_monotone :
  forall rel_initial rel_final
         rel_initial' rel_final'
         before after,
    relation_included rel_initial' rel_initial ->
    relation_included rel_final rel_final' ->
    relational_refinement rel_initial rel_final before after ->
    relational_refinement rel_initial' rel_final' before after.
Proof.
  unfold relation_included, relational_refinement.
  intros rel_initial rel_final rel_initial' rel_final'
         before after Hinitial Hfinal Href
         st_target0 st_source0 st_target_after Hrel0 Hsem_after.
  destruct (Href st_target0 st_source0 st_target_after)
    as (st_source_after & Hsem_source & Hrel_final).
  - eapply Hinitial; eauto.
  - exact Hsem_after.
  - exists st_source_after.
    split.
    + exact Hsem_source.
    + eapply Hfinal; eauto.
Qed.

Theorem relation_included_compose_right_same_intro :
  forall rel,
    relation_included
      rel
      (compose_state_relation rel same_state_relation).
Proof.
  unfold relation_included, compose_state_relation, same_state_relation.
  intros rel st_target st_source Hrel.
  exists st_source.
  split; auto.
Qed.

Theorem relation_included_compose_right_same_elim :
  forall rel,
    relation_included
      (compose_state_relation rel same_state_relation)
      rel.
Proof.
  unfold relation_included, compose_state_relation, same_state_relation.
  intros rel st_target st_source
         (st_mid & Hrel & Heq).
  subst st_source.
  exact Hrel.
Qed.

Record checked_transform_family := {
  ctf_observation : observation;
  ctf_check : PolyLang.t -> PolyLang.t -> imp bool;
  ctf_check_sound :
    forall before after ok,
      mayReturn (ctf_check before after) ok ->
      ok = true ->
      refinement_under ctf_observation before after;
}.

Record checked_relational_transform_family := {
  crtf_initial_relation : state_relation;
  crtf_final_relation : state_relation;
  crtf_check : PolyLang.t -> PolyLang.t -> imp bool;
  crtf_check_sound :
    forall before after ok,
      mayReturn (crtf_check before after) ok ->
      ok = true ->
      relational_refinement
        crtf_initial_relation crtf_final_relation before after;
}.

Theorem checked_relational_transform_family_pair_compose :
  forall first second before mid after first_ok second_ok,
    mayReturn (crtf_check first before mid) first_ok ->
    first_ok = true ->
    mayReturn (crtf_check second mid after) second_ok ->
    second_ok = true ->
    relational_refinement
      (compose_state_relation
        (crtf_initial_relation second)
        (crtf_initial_relation first))
      (compose_state_relation
        (crtf_final_relation second)
        (crtf_final_relation first))
      before after.
Proof.
  intros first second before mid after first_ok second_ok
         Hfirst_ret Hfirst_ok Hsecond_ret Hsecond_ok.
  eapply relational_refinement_compose.
  - eapply crtf_check_sound; eauto.
  - eapply crtf_check_sound; eauto.
Qed.

Theorem affine_validate_identity_sound :
  forall before after ok,
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    refinement_under identity_observation before after.
Proof.
  unfold refinement_under, identity_observation.
  intros before after ok Hret Hok st0 st_after Hsem.
  eapply AffineCore.validate_correct; eauto.
Qed.

Theorem affine_validate_observation_sound :
  forall obs before after ok,
    observation_contains_state_eq obs ->
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    refinement_under obs before after.
Proof.
  unfold refinement_under.
  intros obs before after ok Hobs Hret Hok st0 st_after Hsem.
  pose proof
    (AffineCore.validate_correct before after st0 st_after ok Hret Hok Hsem)
    as Hvalid.
  destruct Hvalid as (st_before & Hsem_before & Heq).
  exists st_before.
  split; eauto.
Qed.

Theorem affine_validate_contract_sound :
  forall oc before after ok,
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    refinement_under (oc_observation oc) before after.
Proof.
  intros oc before after ok Hret Hok.
  eapply affine_validate_observation_sound.
  - exact (oc_contains_state_eq oc).
  - exact Hret.
  - exact Hok.
Qed.

Definition affine_transform_family : checked_transform_family := {|
  ctf_observation := identity_observation;
  ctf_check := AffineCore.validate;
  ctf_check_sound := affine_validate_identity_sound;
|}.

Theorem affine_validate_identity_relational_sound :
  forall before after ok,
    mayReturn (AffineCore.validate before after) ok ->
    ok = true ->
    relational_refinement
      same_state_relation identity_observation before after.
Proof.
  intros before after ok Hret Hok.
  apply refinement_under_to_relational.
  eapply affine_validate_identity_sound; eauto.
Qed.

Definition affine_relational_transform_family
    : checked_relational_transform_family := {|
  crtf_initial_relation := same_state_relation;
  crtf_final_relation := identity_observation;
  crtf_check := AffineCore.validate;
  crtf_check_sound := affine_validate_identity_relational_sound;
|}.

Theorem general_validate_identity_sound :
  forall before after ok,
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    refinement_under identity_observation before after.
Proof.
  unfold refinement_under, identity_observation, AffineCore.validate_general.
  intros before after ok Hret Hok st0 st_after Hsem.
  eapply AffineCore.validate_tiling_correct; eauto.
Qed.

Theorem general_validate_observation_sound :
  forall obs before after ok,
    observation_contains_state_eq obs ->
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    refinement_under obs before after.
Proof.
  unfold refinement_under, AffineCore.validate_general.
  intros obs before after ok Hobs Hret Hok st0 st_after Hsem.
  pose proof
    (AffineCore.validate_tiling_correct before after st0 st_after ok Hret Hok Hsem)
    as Hvalid.
  destruct Hvalid as (st_before & Hsem_before & Heq).
  exists st_before.
  split; eauto.
Qed.

Theorem general_validate_contract_sound :
  forall oc before after ok,
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    refinement_under (oc_observation oc) before after.
Proof.
  intros oc before after ok Hret Hok.
  eapply general_validate_observation_sound.
  - exact (oc_contains_state_eq oc).
  - exact Hret.
  - exact Hok.
Qed.

Definition general_transform_family : checked_transform_family := {|
  ctf_observation := identity_observation;
  ctf_check := AffineCore.validate_general;
  ctf_check_sound := general_validate_identity_sound;
|}.

Theorem general_validate_identity_relational_sound :
  forall before after ok,
    mayReturn (AffineCore.validate_general before after) ok ->
    ok = true ->
    relational_refinement
      same_state_relation identity_observation before after.
Proof.
  intros before after ok Hret Hok.
  apply refinement_under_to_relational.
  eapply general_validate_identity_sound; eauto.
Qed.

Definition general_relational_transform_family
    : checked_relational_transform_family := {|
  crtf_initial_relation := same_state_relation;
  crtf_final_relation := identity_observation;
  crtf_check := AffineCore.validate_general;
  crtf_check_sound := general_validate_identity_relational_sound;
|}.

(** Classification axes for later storage-aware families.  These constructors
    intentionally do not commit to a concrete witness representation yet.  They
    name the semantic dimensions that a future checker must instantiate, so the
    existing [EqDom]/same-access route remains the identity point in the design
    space rather than a special case baked into every theorem. *)
Inductive instance_relation_kind :=
| IRExactCover
| IRDuplicateAndProject
| IRInsertedAuxiliaryInstances
| IRMergedInstances.

Inductive storage_relation_kind :=
| SRIdentity
| SRInjectiveAccessRemap
| SRPaddedInjectiveAccessRemap
| SRFreshPrivateStorage
| SRScalarPromotion
| SRCopyMediatedRemap
| SRConflictSafeReuse
| SRVersionSelectionAndCommit
| SRReductionPrivateAndMerge
| SRPhaseSeparatedReuse.

Inductive observation_kind :=
| ORFullStateEquality
| ORProjectionEquality
| ORCommitEquality
| ORRelaxedMergeEquality.

Record transformation_shape := {
  ts_instances : instance_relation_kind;
  ts_storage : storage_relation_kind;
  ts_observation : observation_kind;
}.

Definition current_affine_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRIdentity;
  ts_observation := ORFullStateEquality;
|}.

Definition layout_remap_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRInjectiveAccessRemap;
  ts_observation := ORProjectionEquality;
|}.

Definition padded_layout_remap_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRPaddedInjectiveAccessRemap;
  ts_observation := ORProjectionEquality;
|}.

Definition private_expansion_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRFreshPrivateStorage;
  ts_observation := ORProjectionEquality;
|}.

Definition scalar_promotion_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRScalarPromotion;
  ts_observation := ORProjectionEquality;
|}.

Definition copy_protocol_shape : transformation_shape := {|
  ts_instances := IRInsertedAuxiliaryInstances;
  ts_storage := SRCopyMediatedRemap;
  ts_observation := ORCommitEquality;
|}.

Definition conflict_reuse_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRConflictSafeReuse;
  ts_observation := ORProjectionEquality;
|}.

Definition version_commit_shape : transformation_shape := {|
  ts_instances := IRDuplicateAndProject;
  ts_storage := SRVersionSelectionAndCommit;
  ts_observation := ORCommitEquality;
|}.

Definition overlap_no_private_shape : transformation_shape := {|
  ts_instances := IRDuplicateAndProject;
  ts_storage := SRIdentity;
  ts_observation := ORCommitEquality;
|}.

Definition overlap_private_shape : transformation_shape := {|
  ts_instances := IRDuplicateAndProject;
  ts_storage := SRFreshPrivateStorage;
  ts_observation := ORCommitEquality;
|}.

Definition reduction_merge_shape : transformation_shape := {|
  ts_instances := IRMergedInstances;
  ts_storage := SRReductionPrivateAndMerge;
  ts_observation := ORRelaxedMergeEquality;
|}.

Definition phase_separation_shape : transformation_shape := {|
  ts_instances := IRExactCover;
  ts_storage := SRPhaseSeparatedReuse;
  ts_observation := ORProjectionEquality;
|}.

End TransformContract.
