Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.

Import ListNotations.

(** Finite remapping witness for copy-mediated local storage.

    [CopyProtocolWitness] checks that local reads and copy-outs are defined in
    a concrete trace.  This file checks a different finite side condition: the
    local cells used by copy-in/read/write/copy-out events are consistent with a
    declared public-to-local cell mapping.

    The mapping is intentionally simple and injective on both public and local
    cells.  This covers the common packing/scratchpad case where a local cell
    represents one public logical cell during the region.  More aggressive
    local reuse can compose this with lifetime/conflict witnesses later. *)

Definition copy_cell_mapping := list (MemCell * MemCell).

Fixpoint copy_mapping_publics
    (mapping: copy_cell_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (public_cell, _) :: tail =>
      public_cell :: copy_mapping_publics tail
  end.

Fixpoint copy_mapping_locals
    (mapping: copy_cell_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (_, local_cell) :: tail =>
      local_cell :: copy_mapping_locals tail
  end.

Definition copy_mapping_pair
    (mapping: copy_cell_mapping)
    (public_cell local_cell: MemCell) : Prop :=
  In (public_cell, local_cell) mapping.

Definition copy_mapping_pairb
    (mapping: copy_cell_mapping)
    (public_cell local_cell: MemCell) : bool :=
  existsb
    (fun mapping_entry =>
       mem_cell_strict_eqb public_cell (fst mapping_entry) &&
       mem_cell_strict_eqb local_cell (snd mapping_entry))
    mapping.

Lemma copy_mapping_pairb_sound :
  forall mapping public_cell local_cell,
    copy_mapping_pairb mapping public_cell local_cell = true ->
    copy_mapping_pair mapping public_cell local_cell.
Proof.
  unfold copy_mapping_pairb, copy_mapping_pair.
  intros mapping public_cell local_cell Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as ([mapped_public mapped_local] & Hin & Hentry).
  apply andb_true_iff in Hentry.
  destruct Hentry as [Hpublic Hlocal].
  apply mem_cell_strict_eqb_eq in Hpublic.
  apply mem_cell_strict_eqb_eq in Hlocal.
  subst. exact Hin.
Qed.

Definition copy_mapping_local_declared
    (mapping: copy_cell_mapping)
    (local_cell: MemCell) : Prop :=
  In local_cell (copy_mapping_locals mapping).

Definition copy_mapping_local_declaredb
    (mapping: copy_cell_mapping)
    (local_cell: MemCell) : bool :=
  mem_cell_inb local_cell (copy_mapping_locals mapping).

Lemma copy_mapping_local_declaredb_sound :
  forall mapping local_cell,
    copy_mapping_local_declaredb mapping local_cell = true ->
    copy_mapping_local_declared mapping local_cell.
Proof.
  unfold copy_mapping_local_declaredb,
         copy_mapping_local_declared.
  intros mapping local_cell Hcheck.
  apply mem_cell_inb_sound.
  exact Hcheck.
Qed.

Definition copy_event_mapping_consistent
    (mapping: copy_cell_mapping)
    (event: copy_event) : Prop :=
  match event with
  | CopyIn public_cell local_cell =>
      copy_mapping_pair mapping public_cell local_cell
  | LocalRead local_cell =>
      copy_mapping_local_declared mapping local_cell
  | LocalWrite local_cell =>
      copy_mapping_local_declared mapping local_cell
  | CopyOut local_cell public_cell =>
      copy_mapping_pair mapping public_cell local_cell
  end.

Definition check_copy_event_mappingb
    (mapping: copy_cell_mapping)
    (event: copy_event) : bool :=
  match event with
  | CopyIn public_cell local_cell =>
      copy_mapping_pairb mapping public_cell local_cell
  | LocalRead local_cell =>
      copy_mapping_local_declaredb mapping local_cell
  | LocalWrite local_cell =>
      copy_mapping_local_declaredb mapping local_cell
  | CopyOut local_cell public_cell =>
      copy_mapping_pairb mapping public_cell local_cell
  end.

Lemma check_copy_event_mappingb_sound :
  forall mapping event,
    check_copy_event_mappingb mapping event = true ->
    copy_event_mapping_consistent mapping event.
Proof.
  intros mapping event Hcheck.
  destruct event as
    [public_cell local_cell
    |local_cell
    |local_cell
    |local_cell public_cell];
    simpl in Hcheck.
  - apply copy_mapping_pairb_sound.
    exact Hcheck.
  - apply copy_mapping_local_declaredb_sound.
    exact Hcheck.
  - apply copy_mapping_local_declaredb_sound.
    exact Hcheck.
  - apply copy_mapping_pairb_sound.
    exact Hcheck.
Qed.

Fixpoint copy_trace_mapping_consistent
    (mapping: copy_cell_mapping)
    (trace: list copy_event) : Prop :=
  match trace with
  | [] => True
  | event :: tail =>
      copy_event_mapping_consistent mapping event /\
      copy_trace_mapping_consistent mapping tail
  end.

Fixpoint check_copy_trace_mappingb
    (mapping: copy_cell_mapping)
    (trace: list copy_event) : bool :=
  match trace with
  | [] => true
  | event :: tail =>
      check_copy_event_mappingb mapping event &&
      check_copy_trace_mappingb mapping tail
  end.

Lemma check_copy_trace_mappingb_sound :
  forall mapping trace,
    check_copy_trace_mappingb mapping trace = true ->
    copy_trace_mapping_consistent mapping trace.
Proof.
  intros mapping trace.
  induction trace as [|event tail IH]; intros Hcheck; simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hevent Htail].
    split.
    + apply check_copy_event_mappingb_sound.
      exact Hevent.
    + apply IH.
      exact Htail.
Qed.

Record copy_mapping_obligations
    (mapping: copy_cell_mapping)
    (trace: list copy_event) : Prop := {
  cmo_public_injective :
    NoDup (copy_mapping_publics mapping);
  cmo_local_injective :
    NoDup (copy_mapping_locals mapping);
  cmo_trace_consistent :
    copy_trace_mapping_consistent mapping trace;
}.

Definition check_copy_mappingb
    (mapping: copy_cell_mapping)
    (trace: list copy_event) : bool :=
  mem_cells_nodupb (copy_mapping_publics mapping) &&
  mem_cells_nodupb (copy_mapping_locals mapping) &&
  check_copy_trace_mappingb mapping trace.

Lemma check_copy_mappingb_sound :
  forall mapping trace,
    check_copy_mappingb mapping trace = true ->
    copy_mapping_obligations mapping trace.
Proof.
  intros mapping trace Hcheck.
  unfold check_copy_mappingb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hpublic & Hlocal) & Htrace).
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hpublic.
  - apply mem_cells_nodupb_sound.
    exact Hlocal.
  - apply check_copy_trace_mappingb_sound.
    exact Htrace.
Qed.
