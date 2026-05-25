Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite frame-preservation witness.

    This boundary primitive is meant for contextual correctness: a transformed
    fragment may write represented output cells and private/local cells, but it
    must not write cells owned by the surrounding context.  The checker uses an
    allowed-write set as the interface between feature-specific write analysis
    and a generic frame condition. *)

Record frame_preservation_obligations
    (frame_cells write_cells allowed_write_cells: list MemCell) : Prop := {
  fpo_frame_nodup :
    NoDup frame_cells;
  fpo_writes_allowed :
    forall cell,
      In cell write_cells ->
      In cell allowed_write_cells;
  fpo_allowed_frame_disjoint :
    mem_cells_disjoint allowed_write_cells frame_cells;
}.

Definition check_frame_preservationb
    (frame_cells write_cells allowed_write_cells: list MemCell) : bool :=
  mem_cells_nodupb frame_cells &&
  mem_cells_subsetb write_cells allowed_write_cells &&
  mem_cells_disjointb allowed_write_cells frame_cells.

Lemma check_frame_preservationb_sound :
  forall frame_cells write_cells allowed_write_cells,
    check_frame_preservationb
      frame_cells write_cells allowed_write_cells = true ->
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells.
Proof.
  intros frame_cells write_cells allowed_write_cells Hcheck.
  unfold check_frame_preservationb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hframe & Hwrites) & Hdisjoint).
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hframe.
  - eapply mem_cells_subsetb_sound.
    exact Hwrites.
  - apply mem_cells_disjointb_sound.
    exact Hdisjoint.
Qed.

Definition writes_disjoint_from_frame
    (write_cells frame_cells: list MemCell) : Prop :=
  mem_cells_disjoint write_cells frame_cells.

Lemma frame_preservation_writes_disjoint :
  forall frame_cells write_cells allowed_write_cells,
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells ->
    writes_disjoint_from_frame write_cells frame_cells.
Proof.
  unfold writes_disjoint_from_frame, mem_cells_disjoint.
  intros frame_cells write_cells allowed_write_cells Hframe cell
         Hwrite Hframe_cell.
  destruct Hframe as [_ Hwrites_allowed Hallowed_frame].
  eapply Hallowed_frame.
  - apply Hwrites_allowed.
    exact Hwrite.
  - exact Hframe_cell.
Qed.

Lemma frame_preservation_allowed_not_frame :
  forall frame_cells write_cells allowed_write_cells cell,
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells ->
    In cell allowed_write_cells ->
    ~ In cell frame_cells.
Proof.
  intros frame_cells write_cells allowed_write_cells cell
         Hframe Hallowed Hframe_cell.
  destruct Hframe as [_ _ Hallowed_frame].
  eapply Hallowed_frame; eauto.
Qed.

Lemma frame_preservation_write_not_frame :
  forall frame_cells write_cells allowed_write_cells cell,
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells ->
    In cell write_cells ->
    ~ In cell frame_cells.
Proof.
  intros frame_cells write_cells allowed_write_cells cell
         Hframe Hwrite Hframe_cell.
  pose proof
    (frame_preservation_writes_disjoint
       frame_cells write_cells allowed_write_cells Hframe)
    as Hdisjoint.
  unfold writes_disjoint_from_frame, mem_cells_disjoint in Hdisjoint.
  eapply Hdisjoint; eauto.
Qed.

Lemma frame_preservation_write_neq_frame_cell :
  forall frame_cells write_cells allowed_write_cells write_cell frame_cell,
    frame_preservation_obligations
      frame_cells write_cells allowed_write_cells ->
    In write_cell write_cells ->
    In frame_cell frame_cells ->
    write_cell <> frame_cell.
Proof.
  intros frame_cells write_cells allowed_write_cells write_cell frame_cell
         Hframe Hwrite Hframe_cell Heq.
  subst.
  eapply frame_preservation_write_not_frame; eauto.
Qed.
