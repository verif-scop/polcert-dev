Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Boundary witness for private storage.

    [PrivateStorageWitness] checks the local part of privatization: private
    cells are hidden/fresh enough for the stated finite view, and private reads
    have reaching private writes.  A privatized region with live-in or live-out
    source values additionally needs boundary copies.  This file records that
    finite obligation without trying to prove expression-level value equality:

      - every required public live-in has a copy-in pair;
      - every required public live-out has a copy-out pair;
      - boundary pairs use private cells from the declared private set;
      - public copy-out destinations are unique. *)

Record private_boundary_pair := {
  private_boundary_public : MemCell;
  private_boundary_private : MemCell;
}.

Definition private_boundary_pair_eqb
    (left right: private_boundary_pair) : bool :=
  mem_cell_strict_eqb
    (private_boundary_public left)
    (private_boundary_public right) &&
  mem_cell_strict_eqb
    (private_boundary_private left)
    (private_boundary_private right).

Lemma private_boundary_pair_eqb_eq :
  forall left right,
    private_boundary_pair_eqb left right = true ->
    left = right.
Proof.
  intros [left_public left_private] [right_public right_private] Hcheck.
  unfold private_boundary_pair_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hpublic Hprivate].
  apply mem_cell_strict_eqb_eq in Hpublic.
  apply mem_cell_strict_eqb_eq in Hprivate.
  subst. reflexivity.
Qed.

Fixpoint private_boundary_publics
    (pairs: list private_boundary_pair) : list MemCell :=
  match pairs with
  | [] => []
  | boundary :: tail =>
      private_boundary_public boundary :: private_boundary_publics tail
  end.

Fixpoint private_boundary_privates
    (pairs: list private_boundary_pair) : list MemCell :=
  match pairs with
  | [] => []
  | boundary :: tail =>
      private_boundary_private boundary :: private_boundary_privates tail
  end.

Definition private_boundary_covers
    (required: list MemCell)
    (pairs: list private_boundary_pair) : Prop :=
  forall cell,
    In cell required ->
    In cell (private_boundary_publics pairs).

Definition private_boundary_privates_declared
    (private_cells: list MemCell)
    (pairs: list private_boundary_pair) : Prop :=
  forall cell,
    In cell (private_boundary_privates pairs) ->
    In cell private_cells.

Record private_boundary_obligations
    (private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair) : Prop := {
  pbo_liveins_copied :
    private_boundary_covers public_liveins copyins;
  pbo_liveouts_committed :
    private_boundary_covers public_liveouts copyouts;
  pbo_copyin_private_declared :
    private_boundary_privates_declared private_cells copyins;
  pbo_copyout_private_declared :
    private_boundary_privates_declared private_cells copyouts;
  pbo_copyout_public_unique :
    NoDup (private_boundary_publics copyouts);
}.

Definition check_private_boundaryb
    (private_cells public_liveins public_liveouts: list MemCell)
    (copyins copyouts: list private_boundary_pair) : bool :=
  mem_cells_subsetb public_liveins (private_boundary_publics copyins) &&
  mem_cells_subsetb public_liveouts (private_boundary_publics copyouts) &&
  mem_cells_subsetb (private_boundary_privates copyins) private_cells &&
  mem_cells_subsetb (private_boundary_privates copyouts) private_cells &&
  mem_cells_nodupb (private_boundary_publics copyouts).

Lemma check_private_boundaryb_sound :
  forall private_cells public_liveins public_liveouts copyins copyouts,
    check_private_boundaryb
      private_cells public_liveins public_liveouts copyins copyouts = true ->
    private_boundary_obligations
      private_cells public_liveins public_liveouts copyins copyouts.
Proof.
  intros private_cells public_liveins public_liveouts copyins copyouts Hcheck.
  unfold check_private_boundaryb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((((Hliveins & Hliveouts) & Hcopyins) & Hcopyouts)
                     & Hcopyout_unique).
  constructor.
  - unfold private_boundary_covers.
    intros cell Hin.
    eapply (mem_cells_subsetb_sound
              public_liveins (private_boundary_publics copyins)); eauto.
  - unfold private_boundary_covers.
    intros cell Hin.
    eapply (mem_cells_subsetb_sound
              public_liveouts (private_boundary_publics copyouts)); eauto.
  - unfold private_boundary_privates_declared.
    intros cell Hin.
    eapply (mem_cells_subsetb_sound
              (private_boundary_privates copyins) private_cells); eauto.
  - unfold private_boundary_privates_declared.
    intros cell Hin.
    eapply (mem_cells_subsetb_sound
              (private_boundary_privates copyouts) private_cells); eauto.
  - apply mem_cells_nodupb_sound.
    exact Hcopyout_unique.
Qed.

Theorem private_boundary_liveout_unique :
  forall private_cells public_liveins public_liveouts copyins copyouts,
    private_boundary_obligations
      private_cells public_liveins public_liveouts copyins copyouts ->
    NoDup (private_boundary_publics copyouts).
Proof.
  intros private_cells public_liveins public_liveouts copyins copyouts Hob.
  exact (pbo_copyout_public_unique
           private_cells public_liveins public_liveouts copyins copyouts Hob).
Qed.

Record private_boundary_private_unique_obligations
    (copyins copyouts: list private_boundary_pair) : Prop := {
  pbpu_copyin_private_unique :
    NoDup (private_boundary_privates copyins);
  pbpu_copyout_private_unique :
    NoDup (private_boundary_privates copyouts);
}.

Definition check_private_boundary_private_uniqueb
    (copyins copyouts: list private_boundary_pair) : bool :=
  mem_cells_nodupb (private_boundary_privates copyins) &&
  mem_cells_nodupb (private_boundary_privates copyouts).

Lemma check_private_boundary_private_uniqueb_sound :
  forall copyins copyouts,
    check_private_boundary_private_uniqueb copyins copyouts = true ->
    private_boundary_private_unique_obligations copyins copyouts.
Proof.
  intros copyins copyouts Hcheck.
  unfold check_private_boundary_private_uniqueb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcopyins Hcopyouts].
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hcopyins.
  - apply mem_cells_nodupb_sound.
    exact Hcopyouts.
Qed.

Record private_boundary_value_entry (value: Type) := {
  private_boundary_value_pair : private_boundary_pair;
  private_boundary_public_value : value;
  private_boundary_private_value : value;
}.

Arguments private_boundary_value_pair {value} _.
Arguments private_boundary_public_value {value} _.
Arguments private_boundary_private_value {value} _.

Fixpoint private_boundary_value_entries_match {value: Type}
    (pairs: list private_boundary_pair)
    (entries: list (private_boundary_value_entry value)) : Prop :=
  match pairs, entries with
  | [], [] => True
  | boundary :: pairs_tail, entry :: entries_tail =>
      boundary = private_boundary_value_pair entry /\
      private_boundary_public_value entry =
        private_boundary_private_value entry /\
      private_boundary_value_entries_match pairs_tail entries_tail
  | _, _ => False
  end.

Fixpoint check_private_boundary_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (pairs: list private_boundary_pair)
    (entries: list (private_boundary_value_entry value)) : bool :=
  match pairs, entries with
  | [], [] => true
  | boundary :: pairs_tail, entry :: entries_tail =>
      private_boundary_pair_eqb
        boundary (private_boundary_value_pair entry) &&
      value_eqb
        (private_boundary_public_value entry)
        (private_boundary_private_value entry) &&
      check_private_boundary_value_entriesb
        value_eqb pairs_tail entries_tail
  | _, _ => false
  end.

Definition check_private_boundary_valueb {value: Type}
    (value_eqb: value -> value -> bool)
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value)) : bool :=
  check_private_boundary_value_entriesb
    value_eqb copyins copyin_values &&
  check_private_boundary_value_entriesb
    value_eqb copyouts copyout_values.

Section ValueSoundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_private_boundary_value_entriesb_sound :
  forall pairs entries,
    check_private_boundary_value_entriesb
      value_eqb pairs entries = true ->
    private_boundary_value_entries_match pairs entries.
Proof.
  induction pairs as [|boundary pairs_tail IH];
    intros entries Hcheck; destruct entries as [|entry entries_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as ((Hpair & Hvalue) & Htail).
    apply private_boundary_pair_eqb_eq in Hpair.
    apply value_eqb_sound in Hvalue.
    split.
    + exact Hpair.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Record private_boundary_value_obligations
    (copyins copyouts: list private_boundary_pair)
    (copyin_values copyout_values:
       list (private_boundary_value_entry value)) : Prop := {
  pbvo_copyin_values_match :
    private_boundary_value_entries_match copyins copyin_values;
  pbvo_copyout_values_match :
    private_boundary_value_entries_match copyouts copyout_values;
}.

Lemma check_private_boundary_valueb_sound :
  forall copyins copyouts copyin_values copyout_values,
    check_private_boundary_valueb
      value_eqb copyins copyouts copyin_values copyout_values = true ->
    private_boundary_value_obligations
      copyins copyouts copyin_values copyout_values.
Proof.
  intros copyins copyouts copyin_values copyout_values Hcheck.
  unfold check_private_boundary_valueb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcopyins Hcopyouts].
  constructor.
  - apply check_private_boundary_value_entriesb_sound.
    exact Hcopyins.
  - apply check_private_boundary_value_entriesb_sound.
    exact Hcopyouts.
Qed.

End ValueSoundness.
