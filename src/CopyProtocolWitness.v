Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for copy-mediated local storage.

    This is the first P4-style protocol checker.  It does not prove instruction
    simulation.  It proves the local bookkeeping obligations that a later
    scratchpad/packing validator will need:

      - every local read is covered by an earlier copy-in or local write;
      - copy-out can only commit a local cell that is currently defined;
      - each destination global cell is committed at most once.

    The witness is deliberately cell-level.  Access-function lifting can reuse
    the same pattern as [PrivateStorageWitness.private_access_event]. *)

Inductive copy_event :=
| CopyIn (source_cell local_cell: MemCell)
| LocalRead (local_cell: MemCell)
| LocalWrite (local_cell: MemCell)
| CopyOut (local_cell target_cell: MemCell).

Fixpoint copy_protocol_defined
    (defined_locals committed_targets: list MemCell)
    (trace: list copy_event) : Prop :=
  match trace with
  | [] => True
  | CopyIn _ local_cell :: tail =>
      copy_protocol_defined
        (local_cell :: defined_locals) committed_targets tail
  | LocalRead local_cell :: tail =>
      In local_cell defined_locals /\
      copy_protocol_defined defined_locals committed_targets tail
  | LocalWrite local_cell :: tail =>
      copy_protocol_defined
        (local_cell :: defined_locals) committed_targets tail
  | CopyOut local_cell target_cell :: tail =>
      In local_cell defined_locals /\
      ~ In target_cell committed_targets /\
      copy_protocol_defined
        defined_locals (target_cell :: committed_targets) tail
  end.

Fixpoint check_copy_protocol_definedb
    (defined_locals committed_targets: list MemCell)
    (trace: list copy_event) : bool :=
  match trace with
  | [] => true
  | CopyIn _ local_cell :: tail =>
      check_copy_protocol_definedb
        (local_cell :: defined_locals) committed_targets tail
  | LocalRead local_cell :: tail =>
      mem_cell_inb local_cell defined_locals &&
      check_copy_protocol_definedb
        defined_locals committed_targets tail
  | LocalWrite local_cell :: tail =>
      check_copy_protocol_definedb
        (local_cell :: defined_locals) committed_targets tail
  | CopyOut local_cell target_cell :: tail =>
      mem_cell_inb local_cell defined_locals &&
      negb (mem_cell_inb target_cell committed_targets) &&
      check_copy_protocol_definedb
        defined_locals (target_cell :: committed_targets) tail
  end.

Lemma check_copy_protocol_definedb_sound :
  forall trace defined_locals committed_targets,
    check_copy_protocol_definedb
      defined_locals committed_targets trace = true ->
    copy_protocol_defined
      defined_locals committed_targets trace.
Proof.
  induction trace as [|event tail IH];
    intros defined_locals committed_targets Hcheck; simpl in Hcheck.
  - exact I.
  - destruct event as
      [source_cell local_cell
      |local_cell
      |local_cell
      |local_cell target_cell].
    + apply IH.
      exact Hcheck.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hdefined Htail].
      split.
      * apply mem_cell_inb_sound.
        exact Hdefined.
      * apply IH.
        exact Htail.
    + apply IH.
      exact Hcheck.
    + repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hdefined & Hfresh_commit) & Htail).
      split.
      * apply mem_cell_inb_sound.
        exact Hdefined.
      * split.
        -- apply negb_true_iff in Hfresh_commit.
           intro Hin.
           apply mem_cell_inb_complete in Hin.
           rewrite Hin in Hfresh_commit.
           discriminate.
        -- apply IH.
           exact Htail.
Qed.

Definition copy_protocol_wf (trace: list copy_event) : Prop :=
  copy_protocol_defined [] [] trace.

Definition check_copy_protocol_wfb (trace: list copy_event) : bool :=
  check_copy_protocol_definedb [] [] trace.

Lemma check_copy_protocol_wfb_sound :
  forall trace,
    check_copy_protocol_wfb trace = true ->
    copy_protocol_wf trace.
Proof.
  unfold check_copy_protocol_wfb, copy_protocol_wf.
  intros trace Hcheck.
  apply check_copy_protocol_definedb_sound.
  exact Hcheck.
Qed.

Fixpoint copy_protocol_committed_targets
    (trace: list copy_event) : list MemCell :=
  match trace with
  | [] => []
  | CopyIn _ _ :: tail
  | LocalRead _ :: tail
  | LocalWrite _ :: tail =>
      copy_protocol_committed_targets tail
  | CopyOut _ target_cell :: tail =>
      target_cell :: copy_protocol_committed_targets tail
  end.

Lemma copy_protocol_defined_no_duplicate_future_commit :
  forall trace defined_locals committed_targets,
    copy_protocol_defined defined_locals committed_targets trace ->
    forall target_cell,
      In target_cell committed_targets ->
      ~ In target_cell (copy_protocol_committed_targets trace).
Proof.
  induction trace as [|event tail IH];
    intros defined_locals committed_targets Hprotocol target_cell Hcommitted;
    simpl.
  - intro Hfuture. contradiction.
  - destruct event as
      [source_cell local_cell
      |local_cell
      |local_cell
      |local_cell target_cell'].
    + eapply IH; eauto.
    + destruct Hprotocol as [_ Htail].
      eapply IH; eauto.
    + eapply IH; eauto.
    + destruct Hprotocol as [_ [Hfresh Htail]].
      intro Hfuture.
      destruct Hfuture as [Heq | Hfuture_tail].
      * subst. apply Hfresh. exact Hcommitted.
      * eapply IH; eauto.
        simpl. right. exact Hcommitted.
Qed.

Lemma copy_protocol_defined_commits_nodup :
  forall trace defined_locals committed_targets,
    copy_protocol_defined defined_locals committed_targets trace ->
    NoDup committed_targets ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  induction trace as [|event tail IH];
    intros defined_locals committed_targets Hprotocol Hnodup; simpl.
  - constructor.
  - destruct event as
      [source_cell local_cell
      |local_cell
      |local_cell
      |local_cell target_cell].
    + eapply IH; eauto.
    + destruct Hprotocol as [_ Htail].
      eapply IH; eauto.
    + eapply IH; eauto.
    + destruct Hprotocol as [_ [Hfresh Htail]].
      constructor.
      * eapply copy_protocol_defined_no_duplicate_future_commit.
        -- exact Htail.
        -- simpl. left. reflexivity.
      * eapply IH.
        -- exact Htail.
        -- constructor.
           ++ exact Hfresh.
           ++ exact Hnodup.
Qed.

Lemma copy_protocol_wf_commits_nodup :
  forall trace,
    copy_protocol_wf trace ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  unfold copy_protocol_wf.
  intros trace Hprotocol.
  eapply copy_protocol_defined_commits_nodup.
  - exact Hprotocol.
  - constructor.
Qed.

Lemma check_copy_protocol_wfb_commits_nodup :
  forall trace,
    check_copy_protocol_wfb trace = true ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  intros trace Hcheck.
  apply copy_protocol_wf_commits_nodup.
  apply check_copy_protocol_wfb_sound.
  exact Hcheck.
Qed.
