Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import PaddingLayoutWitness.

Import ListNotations.

(** Boundary value witness for injective layout and padding maps.

    [PaddingLayoutWitness] proves finite structural facts: the source-to-target
    cell map is functional/injective, represented target cells are allocated,
    and padding cells are allocated but outside the represented image.  At an
    observation boundary we also need to know that each represented target cell
    contains the value of the corresponding source logical cell.  This module
    checks that finite value evidence, while leaving derivation from concrete
    instruction semantics explicit. *)

Record layout_value_entry (value: Type) := {
  lve_source_cell : MemCell;
  lve_target_cell : MemCell;
  lve_source_value : value;
  lve_target_value : value;
}.

Arguments lve_source_cell {value} _.
Arguments lve_target_cell {value} _.
Arguments lve_source_value {value} _.
Arguments lve_target_value {value} _.

Definition layout_value_entry_cells_match {value: Type}
    (mapping_entry: MemCell * MemCell)
    (entry: layout_value_entry value) : Prop :=
  fst mapping_entry = lve_source_cell entry /\
  snd mapping_entry = lve_target_cell entry.

Definition layout_value_entry_value_match {value: Type}
    (entry: layout_value_entry value) : Prop :=
  lve_source_value entry = lve_target_value entry.

Fixpoint layout_value_entries_match {value: Type}
    (mapping: padding_layout_mapping)
    (entries: list (layout_value_entry value)) : Prop :=
  match mapping, entries with
  | [], [] => True
  | mapping_entry :: mapping_tail, value_entry :: entry_tail =>
      layout_value_entry_cells_match mapping_entry value_entry /\
      layout_value_entry_value_match value_entry /\
      layout_value_entries_match mapping_tail entry_tail
  | _, _ => False
  end.

Definition check_layout_value_entryb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping_entry: MemCell * MemCell)
    (entry: layout_value_entry value) : bool :=
  mem_cell_strict_eqb (fst mapping_entry) (lve_source_cell entry) &&
  mem_cell_strict_eqb (snd mapping_entry) (lve_target_cell entry) &&
  value_eqb (lve_source_value entry) (lve_target_value entry).

Fixpoint check_layout_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping: padding_layout_mapping)
    (entries: list (layout_value_entry value)) : bool :=
  match mapping, entries with
  | [], [] => true
  | mapping_entry :: mapping_tail, value_entry :: entry_tail =>
      check_layout_value_entryb value_eqb mapping_entry value_entry &&
      check_layout_value_entriesb value_eqb mapping_tail entry_tail
  | _, _ => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_layout_value_entryb_sound :
  forall mapping_entry entry,
    check_layout_value_entryb value_eqb mapping_entry entry = true ->
    layout_value_entry_cells_match mapping_entry entry /\
    layout_value_entry_value_match entry.
Proof.
  intros [source_cell target_cell] entry Hcheck.
  unfold check_layout_value_entryb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hsource & Htarget) & Hvalue).
  apply mem_cell_strict_eqb_eq in Hsource.
  apply mem_cell_strict_eqb_eq in Htarget.
  apply value_eqb_sound in Hvalue.
  split.
  - unfold layout_value_entry_cells_match.
    simpl.
    split; assumption.
  - unfold layout_value_entry_value_match.
    exact Hvalue.
Qed.

Lemma check_layout_value_entriesb_sound :
  forall mapping entries,
    check_layout_value_entriesb value_eqb mapping entries = true ->
    layout_value_entries_match mapping entries.
Proof.
  induction mapping as [|mapping_entry mapping_tail IH];
    intros entries Hcheck; destruct entries as [|value_entry entry_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    pose proof
      (check_layout_value_entryb_sound mapping_entry value_entry Hhead)
      as [Hcells Hvalue].
    split.
    + exact Hcells.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Record layout_value_obligations
    (mapping: padding_layout_mapping)
    (entries: list (layout_value_entry value)) : Prop := {
  lvo_entries_match :
    layout_value_entries_match mapping entries;
}.

Definition check_layout_valueb
    (mapping: padding_layout_mapping)
    (entries: list (layout_value_entry value)) : bool :=
  check_layout_value_entriesb value_eqb mapping entries.

Lemma check_layout_valueb_sound :
  forall mapping entries,
    check_layout_valueb mapping entries = true ->
    layout_value_obligations mapping entries.
Proof.
  unfold check_layout_valueb.
  intros mapping entries Hcheck.
  constructor.
  apply check_layout_value_entriesb_sound.
  exact Hcheck.
Qed.

End Soundness.
