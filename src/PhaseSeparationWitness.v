Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for phase separation / ping-pong buffering.

    This is the P9 primitive used by double buffering and other phase-based
    storage protocols.  A phase step records which cells are read, which cells
    are written, and which cells are live at the next phase boundary.

    The checker proves local visibility and overwrite-safety facts:

      - every phase read is already live/visible at phase entry;
      - phase writes are disjoint from entry-live cells, so they cannot
        overwrite values still needed in the same phase;
      - next-live cells come from either entry-live cells or phase writes.

    The witness does not prove that a swap implements the intended logical
    time mapping; that remains a semantic refinement obligation. *)

Record phase_step := {
  phase_reads : list MemCell;
  phase_writes : list MemCell;
  phase_next_live : list MemCell;
}.

Definition phase_step_safe
    (entry_live: list MemCell)
    (step: phase_step) : Prop :=
  (forall cell,
     In cell (phase_reads step) ->
     In cell entry_live) /\
  mem_cells_disjoint (phase_writes step) entry_live /\
  NoDup (phase_writes step) /\
  NoDup (phase_next_live step) /\
  (forall cell,
     In cell (phase_next_live step) ->
     In cell (phase_writes step ++ entry_live)).

Definition check_phase_stepb
    (entry_live: list MemCell)
    (step: phase_step) : bool :=
  mem_cells_subsetb (phase_reads step) entry_live &&
  mem_cells_disjointb (phase_writes step) entry_live &&
  mem_cells_nodupb (phase_writes step) &&
  mem_cells_nodupb (phase_next_live step) &&
  mem_cells_subsetb
    (phase_next_live step)
    (phase_writes step ++ entry_live).

Lemma check_phase_stepb_sound :
  forall entry_live step,
    check_phase_stepb entry_live step = true ->
    phase_step_safe entry_live step.
Proof.
  intros entry_live step Hcheck.
  unfold check_phase_stepb in Hcheck.
  unfold phase_step_safe.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((Hreads & Hwrites_disjoint) & Hwrites_nodup)
       & Hnext_nodup) & Hnext_subset).
  repeat split.
  - intros cell Hin.
    eapply mem_cells_subsetb_sound; eauto.
  - apply mem_cells_disjointb_sound.
    exact Hwrites_disjoint.
  - apply mem_cells_nodupb_sound.
    exact Hwrites_nodup.
  - apply mem_cells_nodupb_sound.
    exact Hnext_nodup.
  - intros cell Hin.
    eapply mem_cells_subsetb_sound; eauto.
Qed.

Fixpoint phase_protocol_safe
    (entry_live: list MemCell)
    (steps: list phase_step) : Prop :=
  match steps with
  | [] => True
  | step :: tail =>
      phase_step_safe entry_live step /\
      phase_protocol_safe (phase_next_live step) tail
  end.

Fixpoint check_phase_protocolb
    (entry_live: list MemCell)
    (steps: list phase_step) : bool :=
  match steps with
  | [] => true
  | step :: tail =>
      check_phase_stepb entry_live step &&
      check_phase_protocolb (phase_next_live step) tail
  end.

Lemma check_phase_protocolb_sound :
  forall entry_live steps,
    check_phase_protocolb entry_live steps = true ->
    phase_protocol_safe entry_live steps.
Proof.
  intros entry_live steps.
  revert entry_live.
  induction steps as [|step tail IH]; intros live Hcheck;
    simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hstep Htail].
    split.
    + apply check_phase_stepb_sound.
      exact Hstep.
    + apply IH.
      exact Htail.
Qed.

Definition phase_protocol_final_live
    (entry_live: list MemCell)
    (steps: list phase_step) : list MemCell :=
  fold_left
    (fun _ step => phase_next_live step)
    steps
    entry_live.
