Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Boundary value witness for conflict-safe reuse.

    [ReuseConflictWitness] proves that a possibly non-injective logical-to-
    physical storage map separates all supplied live-range conflicts.  At an
    observation boundary, we also need to know that the selected physical cell
    contains the value of the logical cell it represents.  This module checks
    that finite value evidence is aligned with the reuse mapping and that each
    logical value equals its boundary physical value.

    It is intentionally a boundary witness: it does not derive live ranges or
    prove that the map was safe throughout execution. *)

Record reuse_value_entry (value: Type) := {
  rve_logical_cell : MemCell;
  rve_physical_cell : MemCell;
  rve_logical_value : value;
  rve_physical_value : value;
}.

Arguments rve_logical_cell {value} _.
Arguments rve_physical_cell {value} _.
Arguments rve_logical_value {value} _.
Arguments rve_physical_value {value} _.

Definition reuse_value_entry_cells_match {value: Type}
    (mapping_entry: MemCell * MemCell)
    (entry: reuse_value_entry value) : Prop :=
  fst mapping_entry = rve_logical_cell entry /\
  snd mapping_entry = rve_physical_cell entry.

Definition reuse_value_entry_value_match {value: Type}
    (entry: reuse_value_entry value) : Prop :=
  rve_logical_value entry = rve_physical_value entry.

Fixpoint reuse_value_entries_match {value: Type}
    (mapping: reuse_mapping)
    (entries: list (reuse_value_entry value)) : Prop :=
  match mapping, entries with
  | [], [] => True
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      reuse_value_entry_cells_match mapping_entry entry /\
      reuse_value_entry_value_match entry /\
      reuse_value_entries_match mapping_tail entry_tail
  | _, _ => False
  end.

Definition check_reuse_value_entryb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping_entry: MemCell * MemCell)
    (entry: reuse_value_entry value) : bool :=
  mem_cell_strict_eqb (fst mapping_entry) (rve_logical_cell entry) &&
  mem_cell_strict_eqb (snd mapping_entry) (rve_physical_cell entry) &&
  value_eqb (rve_logical_value entry) (rve_physical_value entry).

Fixpoint check_reuse_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping: reuse_mapping)
    (entries: list (reuse_value_entry value)) : bool :=
  match mapping, entries with
  | [], [] => true
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      check_reuse_value_entryb value_eqb mapping_entry entry &&
      check_reuse_value_entriesb value_eqb mapping_tail entry_tail
  | _, _ => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_reuse_value_entryb_sound :
  forall mapping_entry entry,
    check_reuse_value_entryb value_eqb mapping_entry entry = true ->
    reuse_value_entry_cells_match mapping_entry entry /\
    reuse_value_entry_value_match entry.
Proof.
  intros [logical_cell physical_cell] entry Hcheck.
  unfold check_reuse_value_entryb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hlogical & Hphysical) & Hvalue).
  apply mem_cell_strict_eqb_eq in Hlogical.
  apply mem_cell_strict_eqb_eq in Hphysical.
  apply value_eqb_sound in Hvalue.
  split.
  - unfold reuse_value_entry_cells_match.
    simpl.
    split; assumption.
  - unfold reuse_value_entry_value_match.
    exact Hvalue.
Qed.

Lemma check_reuse_value_entriesb_sound :
  forall mapping entries,
    check_reuse_value_entriesb value_eqb mapping entries = true ->
    reuse_value_entries_match mapping entries.
Proof.
  induction mapping as [|mapping_entry mapping_tail IH];
    intros entries Hcheck; destruct entries as [|entry entry_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    pose proof
      (check_reuse_value_entryb_sound mapping_entry entry Hhead)
      as [Hcells Hvalue].
    split.
    + exact Hcells.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Record reuse_value_obligations
    (mapping: reuse_mapping)
    (entries: list (reuse_value_entry value)) : Prop := {
  rvo_entries_match :
    reuse_value_entries_match mapping entries;
}.

Definition check_reuse_valueb
    (mapping: reuse_mapping)
    (entries: list (reuse_value_entry value)) : bool :=
  check_reuse_value_entriesb value_eqb mapping entries.

Lemma check_reuse_valueb_sound :
  forall mapping entries,
    check_reuse_valueb mapping entries = true ->
    reuse_value_obligations mapping entries.
Proof.
  unfold check_reuse_valueb.
  intros mapping entries Hcheck.
  constructor.
  apply check_reuse_value_entriesb_sound.
  exact Hcheck.
Qed.

End Soundness.
