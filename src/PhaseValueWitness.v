Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import PhaseSeparationWitness.

Import ListNotations.

(** Value witness for phase-separated storage protocols.

    [PhaseSeparationWitness] checks the set-level protocol: reads must be
    visible at phase entry, writes must not overwrite entry-live cells, and
    next-live cells must come from either phase writes or entry-live cells.
    This module adds a boundary value layer for the same protocol.  Each phase
    carries finite value snapshots for entry-live cells, phase writes, and the
    next-live boundary.  The checker proves that reads have entry values and
    each next-live value is either the written value for that cell or the
    inherited entry value.

    The witness still does not explain what a phase means semantically, e.g.
    that ping-pong buffer indices implement logical time.  That remains a
    view-refinement obligation. *)

Definition phase_cell_value (value: Type) :=
  (MemCell * value)%type.

Fixpoint phase_value_lookup {value: Type}
    (cell: MemCell)
    (values: list (phase_cell_value value)) : option value :=
  match values with
  | [] => None
  | (value_cell, value') :: tail =>
      if mem_cell_strict_eqb cell value_cell
      then Some value'
      else phase_value_lookup cell tail
  end.

Fixpoint phase_value_cells {value: Type}
    (values: list (phase_cell_value value)) : list MemCell :=
  match values with
  | [] => []
  | (cell, _) :: tail => cell :: phase_value_cells tail
  end.

Definition phase_snapshot_matches_cells {value: Type}
    (cells: list MemCell)
    (values: list (phase_cell_value value)) : Prop :=
  NoDup cells /\
  NoDup (phase_value_cells values) /\
  (forall cell,
     In cell cells <-> In cell (phase_value_cells values)).

Definition check_phase_snapshot_matches_cellsb {value: Type}
    (cells: list MemCell)
    (values: list (phase_cell_value value)) : bool :=
  mem_cells_nodupb cells &&
  mem_cells_nodupb (phase_value_cells values) &&
  mem_cells_subsetb cells (phase_value_cells values) &&
  mem_cells_subsetb (phase_value_cells values) cells.

Lemma check_phase_snapshot_matches_cellsb_sound :
  forall (value: Type) cells (values: list (phase_cell_value value)),
    check_phase_snapshot_matches_cellsb cells values = true ->
    phase_snapshot_matches_cells cells values.
Proof.
  intros value cells values Hcheck.
  unfold check_phase_snapshot_matches_cellsb in Hcheck.
  unfold phase_snapshot_matches_cells.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hcells_nodup & Hvalues_nodup)
                        & Hcells_subset) & Hvalues_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hcells_nodup.
  - split.
    + apply mem_cells_nodupb_sound.
      exact Hvalues_nodup.
    + intro query_cell.
      split.
      * intro Hin.
        eapply mem_cells_subsetb_sound; eauto.
      * intro Hin.
        eapply mem_cells_subsetb_sound; eauto.
Qed.

Definition phase_reads_have_values {value: Type}
    (reads: list MemCell)
    (entry_values: list (phase_cell_value value)) : Prop :=
  forall cell,
    In cell reads ->
    exists value',
      phase_value_lookup cell entry_values = Some value'.

Fixpoint check_phase_reads_have_valuesb {value: Type}
    (entry_values: list (phase_cell_value value))
    (reads: list MemCell) : bool :=
  match reads with
  | [] => true
  | cell :: tail =>
      match phase_value_lookup cell entry_values with
      | Some _ =>
          check_phase_reads_have_valuesb entry_values tail
      | None => false
      end
  end.

Lemma check_phase_reads_have_valuesb_sound :
  forall (value: Type)
         (entry_values: list (phase_cell_value value))
         reads,
    check_phase_reads_have_valuesb entry_values reads = true ->
    phase_reads_have_values reads entry_values.
Proof.
  intros value entry_values reads.
  induction reads as [|cell tail IH]; intros Hcheck cell' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - destruct (phase_value_lookup cell entry_values) as [value'|]
      eqn:Hlookup; try discriminate.
    destruct Hin as [Heq | Hin_tail].
    + subst.
      exists value'.
      exact Hlookup.
    + eapply IH; eauto.
Qed.

Definition phase_next_cell_value_flow {value: Type}
    (entry_values write_values next_values: list (phase_cell_value value))
    (cell: MemCell) : Prop :=
  exists next_value,
    phase_value_lookup cell next_values = Some next_value /\
    ((exists write_value,
        phase_value_lookup cell write_values = Some write_value /\
        next_value = write_value) \/
     (phase_value_lookup cell write_values = None /\
      exists entry_value,
        phase_value_lookup cell entry_values = Some entry_value /\
        next_value = entry_value)).

Definition check_phase_next_cell_valueb {value: Type}
    (value_eqb: value -> value -> bool)
    (entry_values write_values next_values: list (phase_cell_value value))
    (cell: MemCell) : bool :=
  match phase_value_lookup cell next_values with
  | None => false
  | Some next_value =>
      match phase_value_lookup cell write_values with
      | Some write_value =>
          value_eqb next_value write_value
      | None =>
          match phase_value_lookup cell entry_values with
          | Some entry_value =>
              value_eqb next_value entry_value
          | None => false
          end
      end
  end.

Fixpoint check_phase_next_valuesb {value: Type}
    (value_eqb: value -> value -> bool)
    (entry_values write_values next_values: list (phase_cell_value value))
    (next_live: list MemCell) : bool :=
  match next_live with
  | [] => true
  | cell :: tail =>
      check_phase_next_cell_valueb
        value_eqb entry_values write_values next_values cell &&
      check_phase_next_valuesb
        value_eqb entry_values write_values next_values tail
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_phase_next_cell_valueb_sound :
  forall entry_values write_values next_values cell,
    check_phase_next_cell_valueb
      value_eqb entry_values write_values next_values cell = true ->
    phase_next_cell_value_flow
      entry_values write_values next_values cell.
Proof.
  intros entry_values write_values next_values cell Hcheck.
  unfold check_phase_next_cell_valueb in Hcheck.
  unfold phase_next_cell_value_flow.
  destruct (phase_value_lookup cell next_values)
    as [next_value|] eqn:Hnext; try discriminate.
  destruct (phase_value_lookup cell write_values)
    as [write_value|] eqn:Hwrite.
  - apply value_eqb_sound in Hcheck.
    exists next_value.
    split.
    + reflexivity.
    + left.
      exists write_value.
      split; auto.
  - destruct (phase_value_lookup cell entry_values)
      as [entry_value|] eqn:Hentry; try discriminate.
    apply value_eqb_sound in Hcheck.
    exists next_value.
    split.
    + reflexivity.
    + right.
      split.
      * reflexivity.
      * exists entry_value.
        split; auto.
Qed.

Definition phase_next_values_flow
    (entry_values write_values next_values: list (phase_cell_value value))
    (next_live: list MemCell) : Prop :=
  forall cell,
    In cell next_live ->
    phase_next_cell_value_flow
      entry_values write_values next_values cell.

Lemma check_phase_next_valuesb_sound :
  forall entry_values write_values next_values next_live,
    check_phase_next_valuesb
      value_eqb entry_values write_values next_values next_live = true ->
    phase_next_values_flow
      entry_values write_values next_values next_live.
Proof.
  intros entry_values write_values next_values next_live.
  induction next_live as [|cell tail IH]; intros Hcheck cell' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply check_phase_next_cell_valueb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Record phase_value_step (value: Type) := {
  pvs_write_values : list (phase_cell_value value);
  pvs_next_values : list (phase_cell_value value);
}.

Arguments pvs_write_values {value} _.
Arguments pvs_next_values {value} _.

Record phase_step_value_flow
    (entry_live: list MemCell)
    (entry_values: list (phase_cell_value value))
    (step: phase_step)
    (value_step: phase_value_step value) : Prop := {
  psvf_entry_snapshot :
    phase_snapshot_matches_cells entry_live entry_values;
  psvf_write_snapshot :
    phase_snapshot_matches_cells
      (phase_writes step) (pvs_write_values value_step);
  psvf_next_snapshot :
    phase_snapshot_matches_cells
      (phase_next_live step) (pvs_next_values value_step);
  psvf_reads_have_values :
    phase_reads_have_values (phase_reads step) entry_values;
  psvf_next_values :
    phase_next_values_flow
      entry_values
      (pvs_write_values value_step)
      (pvs_next_values value_step)
      (phase_next_live step);
}.

Definition check_phase_step_value_flowb
    (entry_live: list MemCell)
    (entry_values: list (phase_cell_value value))
    (step: phase_step)
    (value_step: phase_value_step value) : bool :=
  check_phase_snapshot_matches_cellsb entry_live entry_values &&
  check_phase_snapshot_matches_cellsb
    (phase_writes step) (pvs_write_values value_step) &&
  check_phase_snapshot_matches_cellsb
    (phase_next_live step) (pvs_next_values value_step) &&
  check_phase_reads_have_valuesb entry_values (phase_reads step) &&
  check_phase_next_valuesb
    value_eqb
    entry_values
    (pvs_write_values value_step)
    (pvs_next_values value_step)
    (phase_next_live step).

Lemma check_phase_step_value_flowb_sound :
  forall entry_live entry_values step value_step,
    check_phase_step_value_flowb
      entry_live entry_values step value_step = true ->
    phase_step_value_flow entry_live entry_values step value_step.
Proof.
  intros entry_live entry_values step value_step Hcheck.
  unfold check_phase_step_value_flowb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((Hentry & Hwrite) & Hnext) & Hreads) & Hnext_values).
  constructor.
  - apply check_phase_snapshot_matches_cellsb_sound.
    exact Hentry.
  - apply check_phase_snapshot_matches_cellsb_sound.
    exact Hwrite.
  - apply check_phase_snapshot_matches_cellsb_sound.
    exact Hnext.
  - apply check_phase_reads_have_valuesb_sound.
    exact Hreads.
  - apply check_phase_next_valuesb_sound.
    exact Hnext_values.
Qed.

Fixpoint phase_value_protocol
    (entry_live: list MemCell)
    (entry_values: list (phase_cell_value value))
    (steps: list phase_step)
    (value_steps: list (phase_value_step value)) : Prop :=
  match steps, value_steps with
  | [], [] =>
      phase_snapshot_matches_cells entry_live entry_values
  | step :: step_tail, value_step :: value_tail =>
      phase_step_value_flow entry_live entry_values step value_step /\
      phase_value_protocol
        (phase_next_live step)
        (pvs_next_values value_step)
        step_tail value_tail
  | _, _ => False
  end.

Fixpoint check_phase_value_protocolb
    (entry_live: list MemCell)
    (entry_values: list (phase_cell_value value))
    (steps: list phase_step)
    (value_steps: list (phase_value_step value)) : bool :=
  match steps, value_steps with
  | [], [] =>
      check_phase_snapshot_matches_cellsb entry_live entry_values
  | step :: step_tail, value_step :: value_tail =>
      check_phase_step_value_flowb
        entry_live entry_values step value_step &&
      check_phase_value_protocolb
        (phase_next_live step)
        (pvs_next_values value_step)
        step_tail value_tail
  | _, _ => false
  end.

Fixpoint phase_value_protocol_final_values
    (entry_values: list (phase_cell_value value))
    (value_steps: list (phase_value_step value))
    : list (phase_cell_value value) :=
  match value_steps with
  | [] => entry_values
  | value_step :: value_tail =>
      phase_value_protocol_final_values
        (pvs_next_values value_step) value_tail
  end.

Lemma check_phase_value_protocolb_sound :
  forall entry_live entry_values steps value_steps,
    check_phase_value_protocolb
      entry_live entry_values steps value_steps = true ->
    phase_value_protocol entry_live entry_values steps value_steps.
Proof.
  intros live values steps value_steps.
  revert live values value_steps.
  induction steps as [|step step_tail IH];
    intros live values value_steps Hcheck;
    destruct value_steps as [|value_step value_tail];
    simpl in Hcheck; try discriminate.
  - apply check_phase_snapshot_matches_cellsb_sound.
    exact Hcheck.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    split.
    + apply check_phase_step_value_flowb_sound.
      exact Hhead.
    + apply IH.
      exact Htail.
Qed.

Theorem phase_value_protocol_final_snapshot :
  forall entry_live entry_values steps value_steps,
    phase_value_protocol entry_live entry_values steps value_steps ->
    phase_snapshot_matches_cells
      (phase_protocol_final_live entry_live steps)
      (phase_value_protocol_final_values entry_values value_steps).
Proof.
  intros entry_live entry_values steps.
  revert entry_live entry_values.
  induction steps as [|step step_tail IH];
    intros live values value_steps Hprotocol;
    destruct value_steps as [|value_step value_tail];
    simpl in Hprotocol; try contradiction.
  - exact Hprotocol.
  - destruct Hprotocol as [_ Htail].
    simpl.
    apply IH.
    exact Htail.
Qed.

Theorem check_phase_value_protocolb_final_snapshot :
  forall entry_live entry_values steps value_steps,
    check_phase_value_protocolb
      entry_live entry_values steps value_steps = true ->
    phase_snapshot_matches_cells
      (phase_protocol_final_live entry_live steps)
      (phase_value_protocol_final_values entry_values value_steps).
Proof.
  intros entry_live entry_values steps value_steps Hcheck.
  apply phase_value_protocol_final_snapshot.
  apply check_phase_value_protocolb_sound.
  exact Hcheck.
Qed.

End Soundness.
