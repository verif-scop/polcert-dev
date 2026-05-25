Require Import Bool.
Require Import List.

Require Import InstanceProjectionWitness.

Import ListNotations.

(** Finite value witness for overlapped recomputation.

    Projection and closure say which source instance a duplicated target
    instance represents and where its dependencies may come from.  This witness
    records the finite value side condition: each projected target computation,
    including internal/halo recomputation, has the same value as its projected
    source instance.  It does not derive those values from instruction
    semantics; it gives later trace/value validators a concrete obligation to
    discharge. *)

Definition instance_role_eqb (left right: instance_role) : bool :=
  match left, right with
  | Internal, Internal => true
  | Commit, Commit => true
  | _, _ => false
  end.

Lemma instance_role_eqb_eq :
  forall left right,
    instance_role_eqb left right = true ->
    left = right.
Proof.
  intros left right Hcheck.
  destruct left, right; simpl in Hcheck; try discriminate; reflexivity.
Qed.

Definition projected_instance_eqb
    (left right: projected_instance) : bool :=
  logical_instance_eqb (projected_source left) (projected_source right) &&
  instance_role_eqb (projected_role left) (projected_role right).

Lemma projected_instance_eqb_eq :
  forall left right,
    projected_instance_eqb left right = true ->
    left = right.
Proof.
  intros [left_source left_role] [right_source right_role] Hcheck.
  unfold projected_instance_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hsource Hrole].
  apply logical_instance_eqb_eq in Hsource.
  apply instance_role_eqb_eq in Hrole.
  subst. reflexivity.
Qed.

Record overlap_value_entry (value: Type) := {
  overlap_value_target : projected_instance;
  overlap_value_source_value : value;
  overlap_value_target_value : value;
}.

Arguments overlap_value_target {value} _.
Arguments overlap_value_source_value {value} _.
Arguments overlap_value_target_value {value} _.

Fixpoint overlap_value_entries_match {value: Type}
    (targets: list projected_instance)
    (entries: list (overlap_value_entry value)) : Prop :=
  match targets, entries with
  | [], [] => True
  | target :: target_tail, entry :: entry_tail =>
      target = overlap_value_target entry /\
      overlap_value_source_value entry =
        overlap_value_target_value entry /\
      overlap_value_entries_match target_tail entry_tail
  | _, _ => False
  end.

Fixpoint check_overlap_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (targets: list projected_instance)
    (entries: list (overlap_value_entry value)) : bool :=
  match targets, entries with
  | [], [] => true
  | target :: target_tail, entry :: entry_tail =>
      projected_instance_eqb target (overlap_value_target entry) &&
      value_eqb
        (overlap_value_source_value entry)
        (overlap_value_target_value entry) &&
      check_overlap_value_entriesb value_eqb target_tail entry_tail
  | _, _ => false
  end.

Record overlap_value_obligations
    (value: Type)
    (targets: list projected_instance)
    (entries: list (overlap_value_entry value)) : Prop := {
  ovo_entries_match :
    overlap_value_entries_match targets entries;
}.

Lemma check_overlap_value_entriesb_sound :
  forall (value: Type) (value_eqb: value -> value -> bool),
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    forall targets entries,
      check_overlap_value_entriesb
        value_eqb targets entries = true ->
      overlap_value_entries_match targets entries.
Proof.
  intros value value_eqb Hvalue_eqb targets.
  induction targets as [|target target_tail IH];
    intros entries Hcheck;
    destruct entries as [|entry entry_tail]; simpl in Hcheck; try discriminate.
  - exact I.
  - repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as ((Htarget & Hvalue) & Htail).
    split.
    + apply projected_instance_eqb_eq.
      exact Htarget.
    + split.
      * apply Hvalue_eqb.
        exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Definition check_overlap_valueb {value: Type}
    (value_eqb: value -> value -> bool)
    (targets: list projected_instance)
    (entries: list (overlap_value_entry value)) : bool :=
  check_overlap_value_entriesb value_eqb targets entries.

Lemma check_overlap_valueb_sound :
  forall (value: Type) (value_eqb: value -> value -> bool),
    (forall left right,
        value_eqb left right = true ->
        left = right) ->
    forall targets entries,
      check_overlap_valueb value_eqb targets entries = true ->
      overlap_value_obligations value targets entries.
Proof.
  intros value value_eqb Hvalue_eqb targets entries Hcheck.
  constructor.
  apply check_overlap_value_entriesb_sound with (value_eqb := value_eqb).
  - exact Hvalue_eqb.
  - exact Hcheck.
Qed.
