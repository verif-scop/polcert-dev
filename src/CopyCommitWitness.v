Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.

Import ListNotations.

(** Exact copy-out commit cover for copy-mediated local storage.

    [CopyProtocolWitness] checks that every copy-out reads a defined local cell
    and that committed public targets are duplicate-free.  For update-style
    scratchpad transformations, the validator also needs to know that the
    copy-out targets exactly cover the source-observable outputs.  This witness
    checks that finite boundary set. *)

Definition copy_commit_exact_cover
    (expected_targets: list MemCell)
    (trace: list copy_event) : Prop :=
  let committed_targets := copy_protocol_committed_targets trace in
  NoDup committed_targets /\
  (forall expected_target,
     In expected_target expected_targets <->
     In expected_target committed_targets).

Definition check_copy_commit_coverb
    (expected_targets: list MemCell)
    (trace: list copy_event) : bool :=
  let committed_targets := copy_protocol_committed_targets trace in
  mem_cells_nodupb committed_targets &&
  mem_cells_subsetb expected_targets committed_targets &&
  mem_cells_subsetb committed_targets expected_targets.

Lemma check_copy_commit_coverb_sound :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    copy_commit_exact_cover expected_targets trace.
Proof.
  intros expected_targets trace Hcheck.
  unfold check_copy_commit_coverb in Hcheck.
  unfold copy_commit_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hexpected_subset) & Hcommitted_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - intro expected_target_cell.
    split.
    + intro Hin_expected.
      eapply mem_cells_subsetb_sound; eauto.
    + intro Hin_committed.
      eapply mem_cells_subsetb_sound; eauto.
Qed.

Record copy_commit_obligations
    (expected_targets: list MemCell)
    (trace: list copy_event) : Prop := {
  cco_exact_cover :
    copy_commit_exact_cover expected_targets trace;
}.

Lemma check_copy_commit_coverb_obligations_sound :
  forall expected_targets trace,
    check_copy_commit_coverb expected_targets trace = true ->
    copy_commit_obligations expected_targets trace.
Proof.
  intros expected_targets trace Hcheck.
  constructor.
  apply check_copy_commit_coverb_sound.
  exact Hcheck.
Qed.
