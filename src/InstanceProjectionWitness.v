Require Import Bool.
Require Import List.
Require Import ZArith.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for target-to-source instance projection.

    This is the instance-count-changing counterpart to the storage witnesses.
    It is aimed at overlapped tiling, helper copy instances, and recomputation:
    target instances may be duplicated or internal, but source-observable
    commits must cover the live-out source instances exactly once. *)

Definition logical_instance := (nat * DomIndex)%type.

Definition logical_instance_eqb
    (i1 i2: logical_instance) : bool :=
  Nat.eqb (fst i1) (fst i2) &&
  z_list_strict_eqb (snd i1) (snd i2).

Lemma logical_instance_eqb_eq :
  forall i1 i2,
    logical_instance_eqb i1 i2 = true ->
    i1 = i2.
Proof.
  intros [sid1 point1] [sid2 point2] Hcheck.
  unfold logical_instance_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hsid Hpoint].
  apply Nat.eqb_eq in Hsid.
  apply z_list_strict_eqb_eq in Hpoint.
  subst. reflexivity.
Qed.

Lemma logical_instance_eq_eqb :
  forall i1 i2,
    i1 = i2 ->
    logical_instance_eqb i1 i2 = true.
Proof.
  intros [sid1 point1] [sid2 point2] Heq.
  inversion Heq; subst.
  unfold logical_instance_eqb.
  simpl.
  rewrite Nat.eqb_refl.
  rewrite z_list_strict_eq_eqb with (ys := point2); auto.
Qed.

Definition logical_instance_inb
    (instance: logical_instance)
    (instances: list logical_instance) : bool :=
  existsb (logical_instance_eqb instance) instances.

Lemma logical_instance_inb_sound :
  forall instance instances,
    logical_instance_inb instance instances = true ->
    In instance instances.
Proof.
  unfold logical_instance_inb.
  intros instance instances Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (instance' & Hin & Heq).
  apply logical_instance_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma logical_instance_inb_complete :
  forall instance instances,
    In instance instances ->
    logical_instance_inb instance instances = true.
Proof.
  unfold logical_instance_inb.
  intros instance instances Hin.
  apply existsb_exists.
  exists instance.
  split.
  - exact Hin.
  - apply logical_instance_eq_eqb.
    reflexivity.
Qed.

Fixpoint logical_instances_subsetb
    (xs ys: list logical_instance) : bool :=
  match xs with
  | [] => true
  | x :: xs' =>
      logical_instance_inb x ys &&
      logical_instances_subsetb xs' ys
  end.

Lemma logical_instances_subsetb_sound :
  forall xs ys,
    logical_instances_subsetb xs ys = true ->
    forall x,
      In x xs ->
      In x ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hcheck x' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply logical_instance_inb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Fixpoint logical_instances_nodupb
    (instances: list logical_instance) : bool :=
  match instances with
  | [] => true
  | instance :: tail =>
      negb (logical_instance_inb instance tail) &&
      logical_instances_nodupb tail
  end.

Lemma logical_instances_nodupb_sound :
  forall instances,
    logical_instances_nodupb instances = true ->
    NoDup instances.
Proof.
  induction instances as [|instance tail IH]; intros Hcheck;
    simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply logical_instance_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH.
      exact Htail.
Qed.

Inductive instance_role :=
| Internal
| Commit.

Record projected_instance := {
  projected_source : logical_instance;
  projected_role : instance_role;
}.

Fixpoint projected_sources
    (targets: list projected_instance) : list logical_instance :=
  match targets with
  | [] => []
  | target :: tail =>
      projected_source target :: projected_sources tail
  end.

Fixpoint commit_sources
    (targets: list projected_instance) : list logical_instance :=
  match targets with
  | [] => []
  | target :: tail =>
      match projected_role target with
      | Internal => commit_sources tail
      | Commit => projected_source target :: commit_sources tail
      end
  end.

Definition projected_sources_in_domain
    (source_domain: list logical_instance)
    (targets: list projected_instance) : Prop :=
  forall source_instance,
    In source_instance (projected_sources targets) ->
    In source_instance source_domain.

Definition commit_exact_cover
    (source_liveouts: list logical_instance)
    (targets: list projected_instance) : Prop :=
  let commits := commit_sources targets in
  NoDup commits /\
  (forall source_instance,
     In source_instance source_liveouts <->
     In source_instance commits).

Definition projected_sources_in_domainb
    (source_domain: list logical_instance)
    (targets: list projected_instance) : bool :=
  logical_instances_subsetb
    (projected_sources targets) source_domain.

Definition commit_exact_coverb
    (source_liveouts: list logical_instance)
    (targets: list projected_instance) : bool :=
  let commits := commit_sources targets in
  logical_instances_nodupb commits &&
  logical_instances_subsetb source_liveouts commits &&
  logical_instances_subsetb commits source_liveouts.

Lemma projected_sources_in_domainb_sound :
  forall source_domain targets,
    projected_sources_in_domainb source_domain targets = true ->
    projected_sources_in_domain source_domain targets.
Proof.
  unfold projected_sources_in_domainb,
         projected_sources_in_domain.
  intros source_domain targets Hcheck source_instance Hin.
  eapply logical_instances_subsetb_sound; eauto.
Qed.

Lemma commit_exact_coverb_sound :
  forall source_liveouts targets,
    commit_exact_coverb source_liveouts targets = true ->
    commit_exact_cover source_liveouts targets.
Proof.
  unfold commit_exact_coverb, commit_exact_cover.
  intros source_liveouts targets Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hliveout_subset) & Hcommit_subset).
  split.
  - apply logical_instances_nodupb_sound.
    exact Hnodup.
  - intros source_instance.
    split.
    + intro Hin_liveout.
      eapply logical_instances_subsetb_sound; eauto.
    + intro Hin_commit.
      eapply logical_instances_subsetb_sound; eauto.
Qed.

Record instance_projection_obligations
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance) : Prop := {
  ipo_projected_sources_in_domain :
    projected_sources_in_domain source_domain targets;
  ipo_commit_exact_cover :
    commit_exact_cover source_liveouts targets;
}.

Definition check_instance_projectionb
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance) : bool :=
  projected_sources_in_domainb source_domain targets &&
  commit_exact_coverb source_liveouts targets.

Lemma commit_sources_projected_sources_subset :
  forall targets source_instance,
    In source_instance (commit_sources targets) ->
    In source_instance (projected_sources targets).
Proof.
  induction targets as [|target targets IH];
    intros source_instance Hin;
    simpl in Hin |- *.
  - contradiction.
  - destruct (projected_role target) eqn:Hrole; simpl in Hin.
    + right.
      apply IH.
      exact Hin.
    + destruct Hin as [Heq | Hin_tail].
      * left. exact Heq.
      * right.
        apply IH.
        exact Hin_tail.
Qed.

Lemma check_instance_projectionb_sound :
  forall source_domain source_liveouts targets,
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    instance_projection_obligations
      source_domain source_liveouts targets.
Proof.
  intros source_domain source_liveouts targets Hcheck.
  unfold check_instance_projectionb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hdomain Hcover].
  constructor.
  - apply projected_sources_in_domainb_sound.
    exact Hdomain.
  - apply commit_exact_coverb_sound.
    exact Hcover.
Qed.

Theorem instance_projection_commit_sources_nodup :
  forall source_domain source_liveouts targets,
    instance_projection_obligations source_domain source_liveouts targets ->
    NoDup (commit_sources targets).
Proof.
  intros source_domain source_liveouts targets Hobligations.
  destruct Hobligations as [_ Hcover].
  destruct Hcover as [Hnodup _].
  exact Hnodup.
Qed.

Theorem instance_projection_liveout_committed :
  forall source_domain source_liveouts targets source_instance,
    instance_projection_obligations source_domain source_liveouts targets ->
    In source_instance source_liveouts ->
    In source_instance (commit_sources targets).
Proof.
  intros source_domain source_liveouts targets source_instance
         Hobligations Hin.
  destruct Hobligations as [_ Hcover].
  destruct Hcover as [_ Hiff].
  apply Hiff.
  exact Hin.
Qed.

Theorem instance_projection_commit_is_liveout :
  forall source_domain source_liveouts targets source_instance,
    instance_projection_obligations source_domain source_liveouts targets ->
    In source_instance (commit_sources targets) ->
    In source_instance source_liveouts.
Proof.
  intros source_domain source_liveouts targets source_instance
         Hobligations Hin.
  destruct Hobligations as [_ Hcover].
  destruct Hcover as [_ Hiff].
  apply Hiff.
  exact Hin.
Qed.

Theorem instance_projection_liveout_in_domain :
  forall source_domain source_liveouts targets source_instance,
    instance_projection_obligations source_domain source_liveouts targets ->
    In source_instance source_liveouts ->
    In source_instance source_domain.
Proof.
  intros source_domain source_liveouts targets source_instance
         Hobligations Hliveout.
  destruct Hobligations as [Hdomain Hcover].
  apply Hdomain.
  apply commit_sources_projected_sources_subset.
  destruct Hcover as [_ Hiff].
  apply Hiff.
  exact Hliveout.
Qed.
