Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import StorageWitness.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Finite witness for version selection and commit.

    This is the P7 primitive used by array expansion/versioning and by passes
    that materialize multiple candidate target values but expose only one final
    version for each source-observable logical cell.

    The mapping direction is source logical cell -> selected target version
    cell, matching [reuse_mapping].  Unlike contraction/reuse, the selected
    version image is required to be duplicate-free. *)

Definition version_commit_mapping := reuse_mapping.

Fixpoint version_commit_sources
    (mapping: version_commit_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (source_cell, _) :: tail =>
      source_cell :: version_commit_sources tail
  end.

Fixpoint version_commit_versions
    (mapping: version_commit_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (_, version_cell) :: tail =>
      version_cell :: version_commit_versions tail
  end.

Lemma version_commit_sources_reuse_mapping_sources :
  forall mapping,
    version_commit_sources mapping = reuse_mapping_sources mapping.
Proof.
  induction mapping as [|[source_cell version_cell] tail IH];
    simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Definition version_commit_exact_cover
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping) : Prop :=
  let sources := version_commit_sources mapping in
  NoDup sources /\
  NoDup (version_commit_versions mapping) /\
  (forall source_cell,
     In source_cell source_liveouts <->
     In source_cell sources).

Definition version_commit_exact_coverb
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping) : bool :=
  let sources := version_commit_sources mapping in
  mem_cells_nodupb sources &&
  mem_cells_nodupb (version_commit_versions mapping) &&
  mem_cells_subsetb source_liveouts sources &&
  mem_cells_subsetb sources source_liveouts.

Lemma version_commit_pair_source_in_sources :
  forall mapping source_cell version_cell,
    In (source_cell, version_cell) mapping ->
    In source_cell (version_commit_sources mapping).
Proof.
  induction mapping as [|[source_head version_head] tail IH];
    intros source_cell version_cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      left. reflexivity.
    + right.
      eapply IH; eauto.
Qed.

Lemma version_commit_pair_version_in_versions :
  forall mapping source_cell version_cell,
    In (source_cell, version_cell) mapping ->
    In version_cell (version_commit_versions mapping).
Proof.
  induction mapping as [|[source_head version_head] tail IH];
    intros source_cell version_cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      left. reflexivity.
    + right.
      eapply IH; eauto.
Qed.

Lemma version_commit_source_in_mapping :
  forall mapping source_cell,
    In source_cell (version_commit_sources mapping) ->
    exists version_cell,
      In (source_cell, version_cell) mapping.
Proof.
  induction mapping as [|[source_head version_head] tail IH];
    intros source_cell Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      exists version_head.
      left. reflexivity.
    + destruct (IH source_cell Hin_tail)
        as (version_cell & Hin_mapping).
      exists version_cell.
      right. exact Hin_mapping.
Qed.

Lemma version_commit_version_in_mapping :
  forall mapping version_cell,
    In version_cell (version_commit_versions mapping) ->
    exists source_cell,
      In (source_cell, version_cell) mapping.
Proof.
  induction mapping as [|[source_head version_head] tail IH];
    intros version_cell Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      exists source_head.
      left. reflexivity.
    + destruct (IH version_cell Hin_tail)
        as (source_cell & Hin_mapping).
      exists source_cell.
      right. exact Hin_mapping.
Qed.

Lemma version_commit_exact_coverb_sound :
  forall source_liveouts mapping,
    version_commit_exact_coverb source_liveouts mapping = true ->
    version_commit_exact_cover source_liveouts mapping.
Proof.
  intros source_liveouts mapping Hcheck.
  unfold version_commit_exact_coverb in Hcheck.
  unfold version_commit_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hsources_nodup & Hversions_nodup)
                       & Hliveout_subset) & Hsource_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hsources_nodup.
  - split.
    + apply mem_cells_nodupb_sound.
      exact Hversions_nodup.
    + intro observed_source_cell.
      split.
      * intro Hin_liveout.
        eapply mem_cells_subsetb_sound; eauto.
      * intro Hin_source.
        eapply mem_cells_subsetb_sound; eauto.
Qed.

Record version_commit_obligations
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping) : Prop := {
  vco_exact_cover :
    version_commit_exact_cover source_liveouts mapping;
}.

Definition check_version_commitb
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping) : bool :=
  version_commit_exact_coverb source_liveouts mapping.

Lemma check_version_commitb_sound :
  forall source_liveouts mapping,
    check_version_commitb source_liveouts mapping = true ->
    version_commit_obligations source_liveouts mapping.
Proof.
  intros source_liveouts mapping Hcheck.
  constructor.
  apply version_commit_exact_coverb_sound.
  exact Hcheck.
Qed.

Definition version_commit_cell_relation
    (mapping: version_commit_mapping) : cell_relation :=
  reuse_cell_relation mapping.

Theorem version_commit_sources_nodup :
  forall source_liveouts mapping,
    version_commit_obligations source_liveouts mapping ->
    NoDup (version_commit_sources mapping).
Proof.
  intros source_liveouts mapping Hobligations.
  destruct Hobligations as [Hcover].
  destruct Hcover as [Hsources_nodup _].
  exact Hsources_nodup.
Qed.

Theorem version_commit_versions_nodup :
  forall source_liveouts mapping,
    version_commit_obligations source_liveouts mapping ->
    NoDup (version_commit_versions mapping).
Proof.
  intros source_liveouts mapping Hobligations.
  destruct Hobligations as [Hcover].
  destruct Hcover as [_ [Hversions_nodup _]].
  exact Hversions_nodup.
Qed.

Theorem version_commit_liveout_selected :
  forall source_liveouts mapping source_cell,
    version_commit_obligations source_liveouts mapping ->
    In source_cell source_liveouts ->
    exists version_cell,
      version_commit_cell_relation mapping version_cell source_cell.
Proof.
  intros source_liveouts mapping source_cell Hobligations Hliveout.
  destruct Hobligations as [Hcover].
  destruct Hcover as [Hsources_nodup [_ Hsource_cover]].
  pose proof (proj1 (Hsource_cover source_cell) Hliveout)
    as Hsource_in_mapping.
  destruct (version_commit_source_in_mapping mapping source_cell
              Hsource_in_mapping)
    as (version_cell & Hin_pair).
  exists version_cell.
  unfold version_commit_cell_relation.
  eapply reuse_lookup_complete_nodup.
  - rewrite <- version_commit_sources_reuse_mapping_sources.
    exact Hsources_nodup.
  - exact Hin_pair.
Qed.

Theorem version_commit_selected_source_liveout :
  forall source_liveouts mapping source_cell version_cell,
    version_commit_obligations source_liveouts mapping ->
    version_commit_cell_relation mapping version_cell source_cell ->
    In source_cell source_liveouts.
Proof.
  intros source_liveouts mapping source_cell version_cell
         Hobligations Hrel.
  destruct Hobligations as [Hcover].
  destruct Hcover as [_ [_ Hsource_cover]].
  apply Hsource_cover.
  unfold version_commit_cell_relation in Hrel.
  pose proof (reuse_lookup_sound source_cell version_cell mapping Hrel)
    as Hsound.
  destruct Hsound as [Hin_pair | (source_cell' & Hin_pair & Heq)].
  - eapply version_commit_pair_source_in_sources; eauto.
  - subst source_cell'.
    eapply version_commit_pair_source_in_sources; eauto.
Qed.

Theorem version_commit_selected_version_in_versions :
  forall source_liveouts mapping source_cell version_cell,
    version_commit_obligations source_liveouts mapping ->
    version_commit_cell_relation mapping version_cell source_cell ->
    In version_cell (version_commit_versions mapping).
Proof.
  intros source_liveouts mapping source_cell version_cell
         Hobligations Hrel.
  unfold version_commit_cell_relation in Hrel.
  pose proof (reuse_lookup_sound source_cell version_cell mapping Hrel)
    as Hsound.
  destruct Hsound as [Hin_pair | (source_cell' & Hin_pair & Heq)].
  - eapply version_commit_pair_version_in_versions; eauto.
  - eapply version_commit_pair_version_in_versions; eauto.
Qed.
