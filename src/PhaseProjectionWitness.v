Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import StorageWitness.
Require Import PhaseValueWitness.

Import ListNotations.

(** Final-boundary projection witness for phase-separated storage.

    [PhaseSeparationWitness] checks that every phase has visible reads,
    overwrite-safe writes, and a well-formed next-live boundary.  For
    double-buffering and ping-pong storage, a final boundary also needs a
    projection from source-observable logical cells to the final physical
    phase cells.  This file checks that finite projection map and its optional
    boundary value evidence. *)

Definition phase_projection_mapping := list (MemCell * MemCell).

Definition phase_projection_cell_relation
    (mapping: phase_projection_mapping) : cell_relation :=
  fun target_cell source_cell =>
    In (source_cell, target_cell) mapping.

Fixpoint phase_projection_sources
    (mapping: phase_projection_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (source_cell, _) :: tail =>
      source_cell :: phase_projection_sources tail
  end.

Fixpoint phase_projection_targets
    (mapping: phase_projection_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (_, target_cell) :: tail =>
      target_cell :: phase_projection_targets tail
  end.

Definition phase_projection_exact_cover
    (source_liveouts final_live: list MemCell)
    (mapping: phase_projection_mapping) : Prop :=
  let sources := phase_projection_sources mapping in
  let targets := phase_projection_targets mapping in
  NoDup sources /\
  NoDup targets /\
  (forall source_cell,
     In source_cell source_liveouts <->
     In source_cell sources) /\
  (forall target_cell,
     In target_cell targets ->
     In target_cell final_live).

Definition check_phase_projectionb
    (source_liveouts final_live: list MemCell)
    (mapping: phase_projection_mapping) : bool :=
  mem_cells_nodupb (phase_projection_sources mapping) &&
  mem_cells_nodupb (phase_projection_targets mapping) &&
  mem_cells_subsetb source_liveouts (phase_projection_sources mapping) &&
  mem_cells_subsetb (phase_projection_sources mapping) source_liveouts &&
  mem_cells_subsetb (phase_projection_targets mapping) final_live.

Lemma phase_projection_pair_source_in_sources :
  forall mapping source_cell target_cell,
    In (source_cell, target_cell) mapping ->
    In source_cell (phase_projection_sources mapping).
Proof.
  induction mapping as [|[source_head target_head] tail IH];
    intros source_cell target_cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      left. reflexivity.
    + right.
      eapply IH; eauto.
Qed.

Lemma phase_projection_pair_target_in_targets :
  forall mapping source_cell target_cell,
    In (source_cell, target_cell) mapping ->
    In target_cell (phase_projection_targets mapping).
Proof.
  induction mapping as [|[source_head target_head] tail IH];
    intros source_cell target_cell Hin; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      left. reflexivity.
    + right.
      eapply IH; eauto.
Qed.

Lemma phase_projection_source_in_mapping :
  forall mapping source_cell,
    In source_cell (phase_projection_sources mapping) ->
    exists target_cell,
      In (source_cell, target_cell) mapping.
Proof.
  induction mapping as [|[source_head target_head] tail IH];
    intros source_cell Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      exists target_head.
      left. reflexivity.
    + destruct (IH source_cell Hin_tail)
        as (target_cell & Hin_mapping).
      exists target_cell.
      right. exact Hin_mapping.
Qed.

Lemma phase_projection_target_in_mapping :
  forall mapping target_cell,
    In target_cell (phase_projection_targets mapping) ->
    exists source_cell,
      In (source_cell, target_cell) mapping.
Proof.
  induction mapping as [|[source_head target_head] tail IH];
    intros target_cell Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst.
      exists source_head.
      left. reflexivity.
    + destruct (IH target_cell Hin_tail)
        as (source_cell & Hin_mapping).
      exists source_cell.
      right. exact Hin_mapping.
Qed.

Lemma check_phase_projectionb_sound :
  forall source_liveouts final_live mapping,
    check_phase_projectionb source_liveouts final_live mapping = true ->
    phase_projection_exact_cover source_liveouts final_live mapping.
Proof.
  intros source_liveouts final_live mapping Hcheck.
  unfold check_phase_projectionb in Hcheck.
  unfold phase_projection_exact_cover.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((Hsources_nodup & Htargets_nodup) & Hliveout_subset)
       & Hsource_subset) & Htarget_subset).
  split.
  - apply mem_cells_nodupb_sound.
    exact Hsources_nodup.
  - split.
    + apply mem_cells_nodupb_sound.
      exact Htargets_nodup.
    + split.
      * intro projection_source_cell.
        split.
        -- intro Hin_liveout.
           eapply mem_cells_subsetb_sound; eauto.
        -- intro Hin_source.
           eapply mem_cells_subsetb_sound; eauto.
      * intros projection_target_cell Hin_target.
        eapply mem_cells_subsetb_sound; eauto.
Qed.

Record phase_projection_obligations
    (source_liveouts final_live: list MemCell)
    (mapping: phase_projection_mapping) : Prop := {
  ppo_exact_cover :
    phase_projection_exact_cover source_liveouts final_live mapping;
}.

Lemma check_phase_projection_obligationsb_sound :
  forall source_liveouts final_live mapping,
    check_phase_projectionb source_liveouts final_live mapping = true ->
    phase_projection_obligations source_liveouts final_live mapping.
Proof.
  intros source_liveouts final_live mapping Hcheck.
  constructor.
  apply check_phase_projectionb_sound.
  exact Hcheck.
Qed.

Theorem phase_projection_sources_nodup :
  forall source_liveouts final_live mapping,
    phase_projection_obligations source_liveouts final_live mapping ->
    NoDup (phase_projection_sources mapping).
Proof.
  intros source_liveouts final_live mapping Hobligations.
  destruct Hobligations as [Hcover].
  destruct Hcover as [Hsources_nodup _].
  exact Hsources_nodup.
Qed.

Theorem phase_projection_targets_nodup :
  forall source_liveouts final_live mapping,
    phase_projection_obligations source_liveouts final_live mapping ->
    NoDup (phase_projection_targets mapping).
Proof.
  intros source_liveouts final_live mapping Hobligations.
  destruct Hobligations as [Hcover].
  destruct Hcover as [_ [Htargets_nodup _]].
  exact Htargets_nodup.
Qed.

Theorem phase_projection_liveout_mapped :
  forall source_liveouts final_live mapping source_cell,
    phase_projection_obligations source_liveouts final_live mapping ->
    In source_cell source_liveouts ->
    exists target_cell,
      phase_projection_cell_relation mapping target_cell source_cell /\
      In target_cell final_live.
Proof.
  intros source_liveouts final_live mapping source_cell
         Hobligations Hliveout.
  destruct Hobligations as [Hcover].
  destruct Hcover as
    [_ [_ [Hsource_cover Htarget_final]]].
  pose proof (proj1 (Hsource_cover source_cell) Hliveout)
    as Hsource_in_mapping.
  destruct
    (phase_projection_source_in_mapping
       mapping source_cell Hsource_in_mapping)
    as (target_cell & Hpair).
  exists target_cell.
  split.
  - unfold phase_projection_cell_relation.
    exact Hpair.
  - apply Htarget_final.
    eapply phase_projection_pair_target_in_targets; eauto.
Qed.

Theorem phase_projection_mapped_source_liveout :
  forall source_liveouts final_live mapping source_cell target_cell,
    phase_projection_obligations source_liveouts final_live mapping ->
    phase_projection_cell_relation mapping target_cell source_cell ->
    In source_cell source_liveouts.
Proof.
  intros source_liveouts final_live mapping source_cell target_cell
         Hobligations Hrel.
  destruct Hobligations as [Hcover].
  destruct Hcover as [_ [_ [Hsource_cover _]]].
  apply Hsource_cover.
  unfold phase_projection_cell_relation in Hrel.
  eapply phase_projection_pair_source_in_sources; eauto.
Qed.

Theorem phase_projection_mapped_target_final_live :
  forall source_liveouts final_live mapping source_cell target_cell,
    phase_projection_obligations source_liveouts final_live mapping ->
    phase_projection_cell_relation mapping target_cell source_cell ->
    In target_cell final_live.
Proof.
  intros source_liveouts final_live mapping source_cell target_cell
         Hobligations Hrel.
  destruct Hobligations as [Hcover].
  destruct Hcover as [_ [_ [_ Htarget_final]]].
  apply Htarget_final.
  unfold phase_projection_cell_relation in Hrel.
  eapply phase_projection_pair_target_in_targets; eauto.
Qed.

Record phase_projection_value_entry (value: Type) := {
  ppve_source_cell : MemCell;
  ppve_target_cell : MemCell;
  ppve_source_value : value;
  ppve_target_value : value;
}.

Arguments ppve_source_cell {value} _.
Arguments ppve_target_cell {value} _.
Arguments ppve_source_value {value} _.
Arguments ppve_target_value {value} _.

Definition phase_projection_value_entry_cells_match {value: Type}
    (mapping_entry: MemCell * MemCell)
    (entry: phase_projection_value_entry value) : Prop :=
  fst mapping_entry = ppve_source_cell entry /\
  snd mapping_entry = ppve_target_cell entry.

Definition phase_projection_value_entry_value_match {value: Type}
    (entry: phase_projection_value_entry value) : Prop :=
  ppve_source_value entry = ppve_target_value entry.

Fixpoint phase_projection_value_entries_match {value: Type}
    (mapping: phase_projection_mapping)
    (entries: list (phase_projection_value_entry value)) : Prop :=
  match mapping, entries with
  | [], [] => True
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      phase_projection_value_entry_cells_match mapping_entry entry /\
      phase_projection_value_entry_value_match entry /\
      phase_projection_value_entries_match mapping_tail entry_tail
  | _, _ => False
  end.

Definition check_phase_projection_value_entryb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping_entry: MemCell * MemCell)
    (entry: phase_projection_value_entry value) : bool :=
  mem_cell_strict_eqb (fst mapping_entry) (ppve_source_cell entry) &&
  mem_cell_strict_eqb (snd mapping_entry) (ppve_target_cell entry) &&
  value_eqb (ppve_source_value entry) (ppve_target_value entry).

Fixpoint check_phase_projection_value_entriesb {value: Type}
    (value_eqb: value -> value -> bool)
    (mapping: phase_projection_mapping)
    (entries: list (phase_projection_value_entry value)) : bool :=
  match mapping, entries with
  | [], [] => true
  | mapping_entry :: mapping_tail, entry :: entry_tail =>
      check_phase_projection_value_entryb value_eqb mapping_entry entry &&
      check_phase_projection_value_entriesb value_eqb mapping_tail entry_tail
  | _, _ => false
  end.

Section ValueSoundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_phase_projection_value_entryb_sound :
  forall mapping_entry entry,
    check_phase_projection_value_entryb
      value_eqb mapping_entry entry = true ->
    phase_projection_value_entry_cells_match mapping_entry entry /\
    phase_projection_value_entry_value_match entry.
Proof.
  intros [source_cell target_cell] entry Hcheck.
  unfold check_phase_projection_value_entryb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hsource & Htarget) & Hvalue).
  apply mem_cell_strict_eqb_eq in Hsource.
  apply mem_cell_strict_eqb_eq in Htarget.
  apply value_eqb_sound in Hvalue.
  split.
  - unfold phase_projection_value_entry_cells_match.
    simpl.
    split; assumption.
  - unfold phase_projection_value_entry_value_match.
    exact Hvalue.
Qed.

Lemma check_phase_projection_value_entriesb_sound :
  forall mapping entries,
    check_phase_projection_value_entriesb
      value_eqb mapping entries = true ->
    phase_projection_value_entries_match mapping entries.
Proof.
  induction mapping as [|mapping_entry mapping_tail IH];
    intros entries Hcheck; destruct entries as [|entry entry_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    pose proof
      (check_phase_projection_value_entryb_sound
         mapping_entry entry Hhead)
      as [Hcells Hvalue].
    split.
    + exact Hcells.
    + split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
Qed.

Record phase_projection_value_obligations
    (mapping: phase_projection_mapping)
    (entries: list (phase_projection_value_entry value)) : Prop := {
  ppvo_entries_match :
    phase_projection_value_entries_match mapping entries;
}.

Definition check_phase_projection_valueb
    (mapping: phase_projection_mapping)
    (entries: list (phase_projection_value_entry value)) : bool :=
  check_phase_projection_value_entriesb value_eqb mapping entries.

Lemma check_phase_projection_valueb_sound :
  forall mapping entries,
    check_phase_projection_valueb mapping entries = true ->
    phase_projection_value_obligations mapping entries.
Proof.
  unfold check_phase_projection_valueb.
  intros mapping entries Hcheck.
  constructor.
  apply check_phase_projection_value_entriesb_sound.
  exact Hcheck.
Qed.

End ValueSoundness.
