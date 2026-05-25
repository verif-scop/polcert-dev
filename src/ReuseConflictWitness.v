Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import StorageWitness.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for conflict-safe non-injective storage reuse.

    This is the array-contraction / rolling-buffer primitive in its smallest
    executable form.  A logical value is represented by a [MemCell] key, and a
    reuse map assigns it to a physical [MemCell].  The map may be non-injective,
    but every listed conflict pair must map to distinct physical cells.

    Later passes should derive the conflict relation from live ranges under a
    schedule.  This file only checks the finite witness once those conflicts
    have been supplied. *)

Definition reuse_mapping := list (MemCell * MemCell).
Definition conflict_pairs := list (MemCell * MemCell).

Fixpoint reuse_lookup
    (logical_cell: MemCell)
    (mapping: reuse_mapping) : option MemCell :=
  match mapping with
  | [] => None
  | (logical_head, physical_head) :: tail =>
      if mem_cell_strict_eqb logical_cell logical_head then
        Some physical_head
      else
        reuse_lookup logical_cell tail
  end.

(** Convert a logical-to-physical reuse map into the target-to-source cell
    relation expected by [StateObservation].  The relation is intended for a
    boundary/observable mapping: [reuse_cell_relation mapping target source]
    means the target physical cell represents the source logical cell at the
    observation point. *)
Definition reuse_cell_relation
    (mapping: reuse_mapping) : cell_relation :=
  fun target_cell source_cell =>
    reuse_lookup source_cell mapping = Some target_cell.

Definition reuse_source_covered
    (mapping: reuse_mapping) (source_cell: MemCell) : Prop :=
  exists target_cell,
    reuse_cell_relation mapping target_cell source_cell.

Definition reuse_mapping_covers_sources
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : Prop :=
  forall source_cell,
    In source_cell source_cells ->
    reuse_source_covered mapping source_cell.

Lemma reuse_lookup_reuse_cell_relation :
  forall mapping source_cell target_cell,
    reuse_lookup source_cell mapping = Some target_cell ->
    reuse_cell_relation mapping target_cell source_cell.
Proof.
  unfold reuse_cell_relation.
  auto.
Qed.

Fixpoint reuse_mapping_covers_sourcesb
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : bool :=
  match source_cells with
  | [] => true
  | source_cell :: tail =>
      match reuse_lookup source_cell mapping with
      | Some _ => reuse_mapping_covers_sourcesb mapping tail
      | None => false
      end
  end.

Lemma reuse_mapping_covers_sourcesb_sound :
  forall mapping source_cells,
    reuse_mapping_covers_sourcesb mapping source_cells = true ->
    reuse_mapping_covers_sources mapping source_cells.
Proof.
  unfold reuse_mapping_covers_sources.
  intros mapping source_cells.
  induction source_cells as [|source_head tail IH];
    intros Hcheck source_cell Hin; simpl in Hcheck, Hin.
  - contradiction.
  - destruct (reuse_lookup source_head mapping) as [target_head|]
      eqn:Hlookup; try discriminate.
    destruct Hin as [Heq | Hin_tail].
    + subst.
      unfold reuse_source_covered.
      exists target_head.
      apply reuse_lookup_reuse_cell_relation.
      exact Hlookup.
    + eapply IH; eauto.
Qed.

Lemma reuse_lookup_sound :
  forall logical_cell physical_cell mapping,
    reuse_lookup logical_cell mapping = Some physical_cell ->
    In (logical_cell, physical_cell) mapping \/
    exists logical_cell',
      In (logical_cell', physical_cell) mapping /\
      logical_cell = logical_cell'.
Proof.
  intros logical_cell physical_cell mapping.
  induction mapping as [|[logical_head physical_head] tail IH];
    intros Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (mem_cell_strict_eqb logical_cell logical_head)
      eqn:Heq.
    + inversion Hlookup; subst.
      right.
      exists logical_head.
      split.
      * left. reflexivity.
      * apply mem_cell_strict_eqb_eq.
        exact Heq.
    + apply IH in Hlookup.
      destruct Hlookup as [Hin | (logical_cell' & Hin & Heq')].
      * left. right. exact Hin.
      * right.
        exists logical_cell'.
        split.
        -- right. exact Hin.
        -- exact Heq'.
Qed.

Fixpoint reuse_mapping_sources (mapping: reuse_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (logical_cell, _) :: tail =>
      logical_cell :: reuse_mapping_sources tail
  end.

Lemma reuse_mapping_pair_source_in_sources :
  forall mapping logical_cell physical_cell,
    In (logical_cell, physical_cell) mapping ->
    In logical_cell (reuse_mapping_sources mapping).
Proof.
  induction mapping as [|[logical_head physical_head] tail IH];
    intros logical_cell physical_cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      left. reflexivity.
    + right.
      eapply IH; eauto.
Qed.

Lemma reuse_lookup_complete_nodup :
  forall mapping logical_cell physical_cell,
    NoDup (reuse_mapping_sources mapping) ->
    In (logical_cell, physical_cell) mapping ->
    reuse_lookup logical_cell mapping = Some physical_cell.
Proof.
  induction mapping as [|[logical_head physical_head] tail IH];
    intros logical_cell physical_cell Hnodup Hin;
    simpl in Hin, Hnodup |- *.
  - contradiction.
  - inversion Hnodup as [|source sources Hnotin Htail_nodup];
      subst.
    destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      rewrite mem_cell_strict_eq_eqb with (c2 := logical_cell).
      * reflexivity.
      * reflexivity.
    + destruct (mem_cell_strict_eqb logical_cell logical_head)
        eqn:Heq_head.
      * apply mem_cell_strict_eqb_eq in Heq_head.
        subst logical_head.
        assert (In logical_cell (reuse_mapping_sources tail)) as Hin_source.
        {
          eapply reuse_mapping_pair_source_in_sources; eauto.
        }
        contradiction.
      * eapply IH; eauto.
Qed.

Definition reuse_mapping_sources_nodupb
    (mapping: reuse_mapping) : bool :=
  mem_cells_nodupb (reuse_mapping_sources mapping).

Lemma reuse_mapping_sources_nodupb_sound :
  forall mapping,
    reuse_mapping_sources_nodupb mapping = true ->
    NoDup (reuse_mapping_sources mapping).
Proof.
  unfold reuse_mapping_sources_nodupb.
  intros mapping Hcheck.
  apply mem_cells_nodupb_sound.
  exact Hcheck.
Qed.

Definition conflict_pair_separatedb
    (mapping: reuse_mapping)
    (conflict: MemCell * MemCell) : bool :=
  let '(logical1, logical2) := conflict in
  match reuse_lookup logical1 mapping,
        reuse_lookup logical2 mapping with
  | Some physical1, Some physical2 =>
      negb (mem_cell_strict_eqb physical1 physical2)
  | _, _ => false
  end.

Fixpoint conflicts_separatedb
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs) : bool :=
  match conflicts with
  | [] => true
  | conflict :: tail =>
      conflict_pair_separatedb mapping conflict &&
      conflicts_separatedb mapping tail
  end.

Definition conflict_pair_separated
    (mapping: reuse_mapping)
    (conflict: MemCell * MemCell) : Prop :=
  let '(logical1, logical2) := conflict in
  exists physical1 physical2,
    reuse_lookup logical1 mapping = Some physical1 /\
    reuse_lookup logical2 mapping = Some physical2 /\
    physical1 <> physical2.

Definition conflicts_separated
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs) : Prop :=
  forall conflict,
    In conflict conflicts ->
    conflict_pair_separated mapping conflict.

Lemma conflict_pair_separatedb_sound :
  forall mapping conflict,
    conflict_pair_separatedb mapping conflict = true ->
    conflict_pair_separated mapping conflict.
Proof.
  intros mapping [logical1 logical2] Hcheck.
  unfold conflict_pair_separatedb in Hcheck.
  unfold conflict_pair_separated.
  destruct (reuse_lookup logical1 mapping) as [physical1|] eqn:Hlookup1;
    try discriminate.
  destruct (reuse_lookup logical2 mapping) as [physical2|] eqn:Hlookup2;
    try discriminate.
  apply negb_true_iff in Hcheck.
  exists physical1, physical2.
  repeat split; auto.
  intro Heq.
  subst.
  rewrite mem_cell_strict_eq_eqb with (c2 := physical2) in Hcheck.
  - discriminate.
  - reflexivity.
Qed.

Lemma conflicts_separatedb_sound :
  forall mapping conflicts,
    conflicts_separatedb mapping conflicts = true ->
    conflicts_separated mapping conflicts.
Proof.
  intros mapping conflicts.
  induction conflicts as [|conflict tail IH];
    intros Hcheck conflict' Hin; simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply conflict_pair_separatedb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Record conflict_safe_reuse_obligations
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs) : Prop := {
  csro_sources_nodup :
    NoDup (reuse_mapping_sources mapping);
  csro_conflicts_separated :
    conflicts_separated mapping conflicts;
}.

Record reuse_boundary_obligations
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : Prop := {
  rbo_sources_nodup :
    NoDup source_cells;
  rbo_sources_covered :
    reuse_mapping_covers_sources mapping source_cells;
}.

Definition check_reuse_boundaryb
    (mapping: reuse_mapping)
    (source_cells: list MemCell) : bool :=
  mem_cells_nodupb source_cells &&
  reuse_mapping_covers_sourcesb mapping source_cells.

Definition check_conflict_safe_reuseb
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs) : bool :=
  reuse_mapping_sources_nodupb mapping &&
  conflicts_separatedb mapping conflicts.

Lemma check_conflict_safe_reuseb_sound :
  forall mapping conflicts,
    check_conflict_safe_reuseb mapping conflicts = true ->
    conflict_safe_reuse_obligations mapping conflicts.
Proof.
  intros mapping conflicts Hcheck.
  unfold check_conflict_safe_reuseb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hnodup Hconflicts].
  constructor.
  - apply reuse_mapping_sources_nodupb_sound.
    exact Hnodup.
  - apply conflicts_separatedb_sound.
    exact Hconflicts.
Qed.

Lemma check_reuse_boundaryb_sound :
  forall mapping source_cells,
    check_reuse_boundaryb mapping source_cells = true ->
    reuse_boundary_obligations mapping source_cells.
Proof.
  intros mapping source_cells Hcheck.
  unfold check_reuse_boundaryb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hnodup Hcover].
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - apply reuse_mapping_covers_sourcesb_sound.
    exact Hcover.
Qed.
