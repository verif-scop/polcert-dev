Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Finite witness for reduction privatization and merge.

    This covers the bookkeeping side of P8:

      - iteration chunks exactly cover the source reduction domain;
      - private accumulator cells are fresh/distinct;
      - merge order consumes exactly those private accumulators once.

    Algebraic assumptions such as associativity/commutativity, and any relaxed
    floating-point semantics, are intentionally not encoded here.  They are
    passed explicitly to the validator layer as semantic assumptions. *)

Definition reduction_chunk := list logical_instance.
Definition reduction_chunks := list reduction_chunk.

Definition reduction_chunk_domain
    (chunks: reduction_chunks) : list logical_instance :=
  concat chunks.

Definition reduction_chunks_exact_cover
    (source_domain: list logical_instance)
    (chunks: reduction_chunks) : Prop :=
  let covered := reduction_chunk_domain chunks in
  NoDup covered /\
  (forall instance,
     In instance source_domain <-> In instance covered).

Definition reduction_chunks_exact_coverb
    (source_domain: list logical_instance)
    (chunks: reduction_chunks) : bool :=
  let covered := reduction_chunk_domain chunks in
  logical_instances_nodupb covered &&
  logical_instances_subsetb source_domain covered &&
  logical_instances_subsetb covered source_domain.

Lemma reduction_chunks_exact_coverb_sound :
  forall source_domain chunks,
    reduction_chunks_exact_coverb source_domain chunks = true ->
    reduction_chunks_exact_cover source_domain chunks.
Proof.
  intros source_domain chunks Hcheck.
  unfold reduction_chunks_exact_coverb in Hcheck.
  unfold reduction_chunks_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hsource_subset) & Hcovered_subset).
  split.
  - apply logical_instances_nodupb_sound.
    exact Hnodup.
  - intro instance.
    split.
    + intro Hin_source.
      eapply logical_instances_subsetb_sound; eauto.
    + intro Hin_covered.
      eapply logical_instances_subsetb_sound; eauto.
Qed.

Definition reduction_private_accumulators
    (partial_accumulators: list MemCell) : Prop :=
  NoDup partial_accumulators.

Definition reduction_private_accumulatorsb
    (partial_accumulators: list MemCell) : bool :=
  mem_cells_nodupb partial_accumulators.

Lemma reduction_private_accumulatorsb_sound :
  forall partial_accumulators,
    reduction_private_accumulatorsb partial_accumulators = true ->
    reduction_private_accumulators partial_accumulators.
Proof.
  unfold reduction_private_accumulators,
         reduction_private_accumulatorsb.
  intros partial_accumulators Hcheck.
  apply mem_cells_nodupb_sound.
  exact Hcheck.
Qed.

Definition reduction_merge_exact_cover
    (partial_accumulators merge_order: list MemCell) : Prop :=
  NoDup merge_order /\
  (forall acc,
     In acc partial_accumulators <-> In acc merge_order).

Definition reduction_merge_exact_coverb
    (partial_accumulators merge_order: list MemCell) : bool :=
  mem_cells_nodupb merge_order &&
  mem_cells_subsetb partial_accumulators merge_order &&
  mem_cells_subsetb merge_order partial_accumulators.

Lemma reduction_merge_exact_coverb_sound :
  forall partial_accumulators merge_order,
    reduction_merge_exact_coverb partial_accumulators merge_order = true ->
    reduction_merge_exact_cover partial_accumulators merge_order.
Proof.
  intros partial_accumulators merge_order Hcheck.
  unfold reduction_merge_exact_coverb in Hcheck.
  unfold reduction_merge_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hpartial_subset) & Hmerge_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - intro acc.
    split.
    + intro Hin_partial.
      eapply mem_cells_subsetb_sound; eauto.
    + intro Hin_merge.
      eapply mem_cells_subsetb_sound; eauto.
Qed.

Record reduction_merge_obligations
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell) : Prop := {
  rmo_chunks_exact_cover :
    reduction_chunks_exact_cover source_domain chunks;
  rmo_private_accumulators :
    reduction_private_accumulators partial_accumulators;
  rmo_merge_exact_cover :
    reduction_merge_exact_cover partial_accumulators merge_order;
}.

Definition check_reduction_mergeb
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell) : bool :=
  reduction_chunks_exact_coverb source_domain chunks &&
  reduction_private_accumulatorsb partial_accumulators &&
  reduction_merge_exact_coverb partial_accumulators merge_order.

Lemma check_reduction_mergeb_sound :
  forall source_domain chunks partial_accumulators merge_order,
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order.
Proof.
  intros source_domain chunks partial_accumulators merge_order Hcheck.
  unfold check_reduction_mergeb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hchunks & Hpartials) & Hmerge).
  constructor.
  - apply reduction_chunks_exact_coverb_sound.
    exact Hchunks.
  - apply reduction_private_accumulatorsb_sound.
    exact Hpartials.
  - apply reduction_merge_exact_coverb_sound.
    exact Hmerge.
Qed.

Theorem reduction_chunks_covered_nodup :
  forall source_domain chunks partial_accumulators merge_order,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    NoDup (reduction_chunk_domain chunks).
Proof.
  intros source_domain chunks partial_accumulators merge_order Hobligations.
  destruct Hobligations as [Hchunks _ _].
  destruct Hchunks as [Hnodup _].
  exact Hnodup.
Qed.

Theorem reduction_source_instance_covered :
  forall source_domain chunks partial_accumulators merge_order instance,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    In instance source_domain ->
    In instance (reduction_chunk_domain chunks).
Proof.
  intros source_domain chunks partial_accumulators merge_order instance
         Hobligations Hin.
  destruct Hobligations as [Hchunks _ _].
  destruct Hchunks as [_ Hcover].
  apply Hcover.
  exact Hin.
Qed.

Theorem reduction_covered_instance_in_source :
  forall source_domain chunks partial_accumulators merge_order instance,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    In instance (reduction_chunk_domain chunks) ->
    In instance source_domain.
Proof.
  intros source_domain chunks partial_accumulators merge_order instance
         Hobligations Hin.
  destruct Hobligations as [Hchunks _ _].
  destruct Hchunks as [_ Hcover].
  apply Hcover.
  exact Hin.
Qed.

Theorem reduction_private_accumulators_nodup :
  forall source_domain chunks partial_accumulators merge_order,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    NoDup partial_accumulators.
Proof.
  intros source_domain chunks partial_accumulators merge_order Hobligations.
  destruct Hobligations as [_ Hprivate _].
  exact Hprivate.
Qed.

Theorem reduction_merge_order_nodup :
  forall source_domain chunks partial_accumulators merge_order,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    NoDup merge_order.
Proof.
  intros source_domain chunks partial_accumulators merge_order Hobligations.
  destruct Hobligations as [_ _ Hmerge].
  destruct Hmerge as [Hnodup _].
  exact Hnodup.
Qed.

Theorem reduction_private_accumulator_merged :
  forall source_domain chunks partial_accumulators merge_order acc,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    In acc partial_accumulators ->
    In acc merge_order.
Proof.
  intros source_domain chunks partial_accumulators merge_order acc
         Hobligations Hin.
  destruct Hobligations as [_ _ Hmerge].
  destruct Hmerge as [_ Hcover].
  apply Hcover.
  exact Hin.
Qed.

Theorem reduction_merged_accumulator_private :
  forall source_domain chunks partial_accumulators merge_order acc,
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order ->
    In acc merge_order ->
    In acc partial_accumulators.
Proof.
  intros source_domain chunks partial_accumulators merge_order acc
         Hobligations Hin.
  destruct Hobligations as [_ _ Hmerge].
  destruct Hmerge as [_ Hcover].
  apply Hcover.
  exact Hin.
Qed.
