Require Import Arith.
Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Finite live-range witness for conflict-safe reuse.

    [ReuseConflictWitness] checks that supplied conflict pairs are physically
    separated by a non-injective reuse map.  This file checks the preceding
    finite obligation: the supplied conflict relation covers all overlapping
    live intervals.  The live intervals are still explicit evidence; deriving
    them from a concrete schedule and access trace is a separate semantic
    proof obligation. *)

Record live_interval := {
  li_cell : MemCell;
  li_start : nat;
  li_stop : nat;
}.

Definition live_interval_wf (interval: live_interval) : Prop :=
  li_start interval < li_stop interval.

Definition check_live_interval_wfb
    (interval: live_interval) : bool :=
  Nat.ltb (li_start interval) (li_stop interval).

Lemma check_live_interval_wfb_sound :
  forall interval,
    check_live_interval_wfb interval = true ->
    live_interval_wf interval.
Proof.
  intros interval Hcheck.
  unfold check_live_interval_wfb in Hcheck.
  unfold live_interval_wf.
  apply Nat.ltb_lt.
  exact Hcheck.
Qed.

Fixpoint check_live_intervals_wfb
    (intervals: list live_interval) : bool :=
  match intervals with
  | [] => true
  | interval :: tail =>
      check_live_interval_wfb interval &&
      check_live_intervals_wfb tail
  end.

Definition live_intervals_wf
    (intervals: list live_interval) : Prop :=
  forall interval,
    In interval intervals ->
    live_interval_wf interval.

Lemma check_live_intervals_wfb_sound :
  forall intervals,
    check_live_intervals_wfb intervals = true ->
    live_intervals_wf intervals.
Proof.
  induction intervals as [|interval tail IH];
    intros Hcheck interval' Hin; simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply check_live_interval_wfb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Fixpoint live_interval_cells
    (intervals: list live_interval) : list MemCell :=
  match intervals with
  | [] => []
  | interval :: tail =>
      li_cell interval :: live_interval_cells tail
  end.

Definition check_live_interval_cells_nodupb
    (intervals: list live_interval) : bool :=
  mem_cells_nodupb (live_interval_cells intervals).

Lemma check_live_interval_cells_nodupb_sound :
  forall intervals,
    check_live_interval_cells_nodupb intervals = true ->
    NoDup (live_interval_cells intervals).
Proof.
  unfold check_live_interval_cells_nodupb.
  intros intervals Hcheck.
  apply mem_cells_nodupb_sound.
  exact Hcheck.
Qed.

Definition live_interval_overlap
    (left right: live_interval) : Prop :=
  li_start left < li_stop right /\
  li_start right < li_stop left.

Definition check_live_interval_overlapb
    (left right: live_interval) : bool :=
  Nat.ltb (li_start left) (li_stop right) &&
  Nat.ltb (li_start right) (li_stop left).

Lemma check_live_interval_overlapb_sound :
  forall left right,
    check_live_interval_overlapb left right = true ->
    live_interval_overlap left right.
Proof.
  intros left right Hcheck.
  unfold check_live_interval_overlapb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hleft Hright].
  unfold live_interval_overlap.
  split; apply Nat.ltb_lt; assumption.
Qed.

Lemma check_live_interval_overlapb_complete :
  forall left right,
    live_interval_overlap left right ->
    check_live_interval_overlapb left right = true.
Proof.
  intros left right [Hleft Hright].
  unfold check_live_interval_overlapb.
  apply andb_true_iff.
  split; apply Nat.ltb_lt; assumption.
Qed.

Lemma live_interval_overlap_sym :
  forall left right,
    live_interval_overlap left right ->
    live_interval_overlap right left.
Proof.
  intros left right [Hleft Hright].
  split; assumption.
Qed.

Definition conflict_pair_strict_eqb
    (left right: MemCell * MemCell) : bool :=
  mem_cell_strict_eqb (fst left) (fst right) &&
  mem_cell_strict_eqb (snd left) (snd right).

Lemma conflict_pair_strict_eqb_sound :
  forall left right,
    conflict_pair_strict_eqb left right = true ->
    left = right.
Proof.
  intros [left1 left2] [right1 right2] Hcheck.
  unfold conflict_pair_strict_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hfirst Hsecond].
  apply mem_cell_strict_eqb_eq in Hfirst.
  apply mem_cell_strict_eqb_eq in Hsecond.
  subst.
  reflexivity.
Qed.

Definition conflict_pair_present
    (left right: MemCell)
    (conflicts: conflict_pairs) : Prop :=
  In (left, right) conflicts \/
  In (right, left) conflicts.

Definition conflict_pair_presentb
    (left right: MemCell)
    (conflicts: conflict_pairs) : bool :=
  existsb
    (fun conflict =>
       conflict_pair_strict_eqb (left, right) conflict ||
       conflict_pair_strict_eqb (right, left) conflict)
    conflicts.

Lemma conflict_pair_present_sym :
  forall left right conflicts,
    conflict_pair_present left right conflicts ->
    conflict_pair_present right left conflicts.
Proof.
  unfold conflict_pair_present.
  intros left right conflicts [Hdirect | Hreverse].
  - right. exact Hdirect.
  - left. exact Hreverse.
Qed.

Lemma conflict_pair_presentb_sound :
  forall left right conflicts,
    conflict_pair_presentb left right conflicts = true ->
    conflict_pair_present left right conflicts.
Proof.
  unfold conflict_pair_presentb.
  intros left right conflicts Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (conflict & Hin & Hmatch).
  apply orb_true_iff in Hmatch.
  destruct Hmatch as [Hdirect | Hreverse].
  - apply conflict_pair_strict_eqb_sound in Hdirect.
    subst.
    left. exact Hin.
  - apply conflict_pair_strict_eqb_sound in Hreverse.
    subst.
    right. exact Hin.
Qed.

Definition check_live_pair_conflictb
    (conflicts: conflict_pairs)
    (left right: live_interval) : bool :=
  if check_live_interval_overlapb left right then
    conflict_pair_presentb (li_cell left) (li_cell right) conflicts
  else
    true.

Lemma check_live_pair_conflictb_sound :
  forall conflicts left right,
    check_live_pair_conflictb conflicts left right = true ->
    live_interval_overlap left right ->
    conflict_pair_present (li_cell left) (li_cell right) conflicts.
Proof.
  intros conflicts left right Hcheck Hoverlap.
  unfold check_live_pair_conflictb in Hcheck.
  destruct (check_live_interval_overlapb left right) eqn:Hoverlapb.
  - apply conflict_pair_presentb_sound.
    exact Hcheck.
  - pose proof
      (check_live_interval_overlapb_complete left right Hoverlap)
      as Hcomplete.
    rewrite Hoverlapb in Hcomplete.
    discriminate.
Qed.

Fixpoint check_live_head_conflictsb
    (conflicts: conflict_pairs)
    (head: live_interval)
    (tail: list live_interval) : bool :=
  match tail with
  | [] => true
  | interval :: tail' =>
      check_live_pair_conflictb conflicts head interval &&
      check_live_head_conflictsb conflicts head tail'
  end.

Lemma check_live_head_conflictsb_sound :
  forall conflicts head tail interval,
    check_live_head_conflictsb conflicts head tail = true ->
    In interval tail ->
    live_interval_overlap head interval ->
    conflict_pair_present (li_cell head) (li_cell interval) conflicts.
Proof.
  induction tail as [|interval_head tail IH];
    intros interval Hcheck Hin Hoverlap; simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply check_live_pair_conflictb_sound; eauto.
    + eapply IH; eauto.
Qed.

Fixpoint check_live_conflict_coverb
    (intervals: list live_interval)
    (conflicts: conflict_pairs) : bool :=
  match intervals with
  | [] => true
  | interval :: tail =>
      check_live_head_conflictsb conflicts interval tail &&
      check_live_conflict_coverb tail conflicts
  end.

Definition live_conflict_cover
    (intervals: list live_interval)
    (conflicts: conflict_pairs) : Prop :=
  forall left right,
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    live_interval_overlap left right ->
    conflict_pair_present (li_cell left) (li_cell right) conflicts.

Lemma check_live_conflict_coverb_sound :
  forall intervals conflicts,
    check_live_conflict_coverb intervals conflicts = true ->
    live_conflict_cover intervals conflicts.
Proof.
  induction intervals as [|head tail IH];
    intros conflicts Hcheck left right Hin_left Hin_right Hneq Hoverlap;
    simpl in Hcheck, Hin_left, Hin_right.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin_left as [Hleft_eq | Hin_left_tail];
      destruct Hin_right as [Hright_eq | Hin_right_tail].
    + subst.
      contradiction Hneq.
      reflexivity.
    + subst.
      eapply check_live_head_conflictsb_sound; eauto.
    + subst.
      apply conflict_pair_present_sym.
      eapply check_live_head_conflictsb_sound; eauto.
      apply live_interval_overlap_sym.
      exact Hoverlap.
    + eapply IH; eauto.
Qed.

Record live_conflict_obligations
    (intervals: list live_interval)
    (conflicts: conflict_pairs) : Prop := {
  lco_intervals_wf :
    live_intervals_wf intervals;
  lco_cells_nodup :
    NoDup (live_interval_cells intervals);
  lco_overlap_covered :
    live_conflict_cover intervals conflicts;
}.

Definition check_live_conflictb
    (intervals: list live_interval)
    (conflicts: conflict_pairs) : bool :=
  check_live_intervals_wfb intervals &&
  check_live_interval_cells_nodupb intervals &&
  check_live_conflict_coverb intervals conflicts.

Lemma check_live_conflictb_sound :
  forall intervals conflicts,
    check_live_conflictb intervals conflicts = true ->
    live_conflict_obligations intervals conflicts.
Proof.
  intros intervals conflicts Hcheck.
  unfold check_live_conflictb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hwf & Hnodup) & Hcover).
  constructor.
  - apply check_live_intervals_wfb_sound.
    exact Hwf.
  - apply check_live_interval_cells_nodupb_sound.
    exact Hnodup.
  - apply check_live_conflict_coverb_sound.
    exact Hcover.
Qed.

Definition interval_cells_reuse_separated
    (mapping: reuse_mapping)
    (left right: live_interval) : Prop :=
  exists physical_left physical_right,
    reuse_lookup (li_cell left) mapping = Some physical_left /\
    reuse_lookup (li_cell right) mapping = Some physical_right /\
    physical_left <> physical_right.

Definition live_overlaps_reuse_separated
    (mapping: reuse_mapping)
    (intervals: list live_interval) : Prop :=
  forall left right,
    In left intervals ->
    In right intervals ->
    li_cell left <> li_cell right ->
    live_interval_overlap left right ->
    interval_cells_reuse_separated mapping left right.

Lemma conflict_pair_separated_to_interval :
  forall mapping left right,
    conflict_pair_separated
      mapping (li_cell left, li_cell right) ->
    interval_cells_reuse_separated mapping left right.
Proof.
  intros mapping left right Hseparated.
  unfold conflict_pair_separated in Hseparated.
  unfold interval_cells_reuse_separated.
  simpl in Hseparated.
  exact Hseparated.
Qed.

Lemma conflict_pair_separated_to_interval_sym :
  forall mapping left right,
    conflict_pair_separated
      mapping (li_cell right, li_cell left) ->
    interval_cells_reuse_separated mapping left right.
Proof.
  intros mapping left right Hseparated.
  unfold conflict_pair_separated in Hseparated.
  simpl in Hseparated.
  destruct Hseparated
    as (physical_right & physical_left & Hlookup_right &
        Hlookup_left & Hneq).
  unfold interval_cells_reuse_separated.
  exists physical_left, physical_right.
  repeat split; auto.
Qed.

Lemma live_conflict_and_conflict_safe_reuse_sound :
  forall mapping conflicts intervals,
    live_conflict_obligations intervals conflicts ->
    conflict_safe_reuse_obligations mapping conflicts ->
    live_overlaps_reuse_separated mapping intervals.
Proof.
  intros mapping conflicts intervals Hlive Hreuse.
  unfold live_overlaps_reuse_separated.
  intros left right Hin_left Hin_right Hneq Hoverlap.
  destruct Hlive as [_ _ Hcover].
  destruct Hreuse as [_ Hseparated].
  pose proof
    (Hcover left right Hin_left Hin_right Hneq Hoverlap)
    as Hpresent.
  unfold conflict_pair_present in Hpresent.
  destruct Hpresent as [Hdirect | Hreverse].
  - apply conflict_pair_separated_to_interval.
    apply Hseparated.
    exact Hdirect.
  - apply conflict_pair_separated_to_interval_sym.
    apply Hseparated.
    exact Hreverse.
Qed.
