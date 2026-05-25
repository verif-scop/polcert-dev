Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import VersionCommitWitness.

Import ListNotations.

(** Value witness for version selection and commit.

    [VersionCommitWitness] checks that source live-outs select unique target
    versions.  This module checks the value side of that selection: every
    selected target version must contain the value of the source logical cell
    it represents.  The witness is aligned positionally with the finite
    source-to-version mapping so the selected cells and the value evidence
    cannot silently talk about different pairs. *)

Record version_value_entry (value: Type) := {
  vve_source_cell : MemCell;
  vve_version_cell : MemCell;
  vve_source_value : value;
  vve_version_value : value;
}.

Arguments vve_source_cell {value} _.
Arguments vve_version_cell {value} _.
Arguments vve_source_value {value} _.
Arguments vve_version_value {value} _.

Definition version_value_entry_cells_match {value: Type}
    (mapping_entry: MemCell * MemCell)
    (entry: version_value_entry value) : Prop :=
  fst mapping_entry = vve_source_cell entry /\
  snd mapping_entry = vve_version_cell entry.

Definition version_value_entry_value_match {value: Type}
    (entry: version_value_entry value) : Prop :=
  vve_source_value entry = vve_version_value entry.

Fixpoint version_value_entries_match {value: Type}
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value)) : Prop :=
  match mapping, entries with
  | [], [] => True
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      version_value_entry_cells_match mapping_entry entry /\
      version_value_entry_value_match entry /\
      version_value_entries_match mapping_tail entry_tail
  | _, _ => False
  end.

Definition check_version_value_entryb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping_entry: MemCell * MemCell)
    (entry: version_value_entry value) : bool :=
  mem_cell_strict_eqb (fst mapping_entry) (vve_source_cell entry) &&
  mem_cell_strict_eqb (snd mapping_entry) (vve_version_cell entry) &&
  value_eqb (vve_source_value entry) (vve_version_value entry).

Fixpoint check_version_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value)) : bool :=
  match mapping, entries with
  | [], [] => true
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      check_version_value_entryb value_eqb mapping_entry entry &&
      check_version_value_entriesb value_eqb mapping_tail entry_tail
  | _, _ => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_version_value_entryb_sound :
  forall mapping_entry entry,
    check_version_value_entryb value_eqb mapping_entry entry = true ->
    version_value_entry_cells_match mapping_entry entry /\
    version_value_entry_value_match entry.
Proof.
  intros [source_cell version_cell] entry Hcheck.
  unfold check_version_value_entryb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hsource & Hversion) & Hvalue).
  apply mem_cell_strict_eqb_eq in Hsource.
  apply mem_cell_strict_eqb_eq in Hversion.
  apply value_eqb_sound in Hvalue.
  split.
  - unfold version_value_entry_cells_match.
    simpl.
    split; assumption.
  - unfold version_value_entry_value_match.
    exact Hvalue.
Qed.

Lemma check_version_value_entriesb_sound :
  forall mapping entries,
    check_version_value_entriesb value_eqb mapping entries = true ->
    version_value_entries_match mapping entries.
Proof.
  induction mapping as [|mapping_entry mapping_tail IH];
    intros entries Hcheck; destruct entries as [|entry entry_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    pose proof
      (check_version_value_entryb_sound mapping_entry entry Hhead)
      as [Hcells Hvalue].
    split.
    + exact Hcells.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Record version_value_obligations
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value)) : Prop := {
  vvo_entries_match :
    version_value_entries_match mapping entries;
}.

Definition check_version_valueb
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value)) : bool :=
  check_version_value_entriesb value_eqb mapping entries.

Lemma check_version_valueb_sound :
  forall mapping entries,
    check_version_valueb mapping entries = true ->
    version_value_obligations mapping entries.
Proof.
  unfold check_version_valueb.
  intros mapping entries Hcheck.
  constructor.
  apply check_version_value_entriesb_sound.
  exact Hcheck.
Qed.

End Soundness.
