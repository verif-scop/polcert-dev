Require Import Bool.
Require Import List.
Require Import ZArith.

Require Import AST.
Require Import Base.
Require Import PolyBase.
Require Import PolIRs.
Require Import StorageWitness.
Require Import StateObservation.

Import ListNotations.

(** Small witness vocabulary for private-erasure views.

    The first checkable fragment is intentionally narrow: a finite list of
    target-private cells is hidden from a finite public identity view.  This is
    enough to mechanize the "private cells are not observable" side condition
    used by [PrivateStorageValidator].  Freshness, reaching definitions,
    copy-in/copy-out, and non-escape are separate obligations and should not be
    smuggled into this simple visibility check.  Non-escape is still finite
    here: a caller supplies the cells whose addresses or locations may be
    exposed to the surrounding context, and private cells must be disjoint from
    that exposed set. *)

Fixpoint z_list_strict_eqb (xs ys: list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      Z.eqb x y && z_list_strict_eqb xs' ys'
  | _, _ => false
  end.

Lemma z_list_strict_eqb_eq :
  forall xs ys,
    z_list_strict_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hcheck;
    destruct ys as [|y ys]; simpl in Hcheck; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply Z.eqb_eq in Hhead.
    apply IH in Htail.
    subst. reflexivity.
Qed.

Lemma z_list_strict_eq_eqb :
  forall xs ys,
    xs = ys ->
    z_list_strict_eqb xs ys = true.
Proof.
  induction xs as [|x xs IH]; intros ys Heq;
    destruct ys as [|y ys]; inversion Heq; subst; simpl.
  - reflexivity.
  - rewrite Z.eqb_refl.
    rewrite IH; auto.
Qed.

Definition mem_cell_strict_eqb (c1 c2: MemCell) : bool :=
  Pos.eqb (arr_id c1) (arr_id c2) &&
  z_list_strict_eqb (arr_index c1) (arr_index c2).

Lemma mem_cell_strict_eqb_eq :
  forall c1 c2,
    mem_cell_strict_eqb c1 c2 = true ->
    c1 = c2.
Proof.
  intros [id1 index1] [id2 index2] Hcheck.
  unfold mem_cell_strict_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hid Hindex].
  apply Pos.eqb_eq in Hid.
  apply z_list_strict_eqb_eq in Hindex.
  subst. reflexivity.
Qed.

Lemma mem_cell_strict_eq_eqb :
  forall c1 c2,
    c1 = c2 ->
    mem_cell_strict_eqb c1 c2 = true.
Proof.
  intros [id1 index1] [id2 index2] Heq.
  inversion Heq; subst.
  unfold mem_cell_strict_eqb.
  simpl.
  rewrite Pos.eqb_refl.
  rewrite z_list_strict_eq_eqb with (ys := index2); auto.
Qed.

Definition mem_cell_inb (cell: MemCell) (cells: list MemCell) : bool :=
  existsb (mem_cell_strict_eqb cell) cells.

Lemma mem_cell_inb_sound :
  forall cell cells,
    mem_cell_inb cell cells = true ->
    In cell cells.
Proof.
  unfold mem_cell_inb.
  intros cell cells Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (cell' & Hin & Heq).
  apply mem_cell_strict_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma mem_cell_inb_complete :
  forall cell cells,
    In cell cells ->
    mem_cell_inb cell cells = true.
Proof.
  unfold mem_cell_inb.
  intros cell cells Hin.
  apply existsb_exists.
  exists cell.
  split.
  - exact Hin.
  - apply mem_cell_strict_eq_eqb.
    reflexivity.
Qed.

Fixpoint mem_cells_subsetb
    (private_cells hidden_cells: list MemCell) : bool :=
  match private_cells with
  | [] => true
  | cell :: private_tail =>
      mem_cell_inb cell hidden_cells &&
      mem_cells_subsetb private_tail hidden_cells
  end.

Lemma mem_cells_subsetb_sound :
  forall private_cells hidden_cells,
    mem_cells_subsetb private_cells hidden_cells = true ->
    forall cell,
      In cell private_cells ->
      In cell hidden_cells.
Proof.
  induction private_cells as [|private_cell private_tail IH];
    intros hidden_cells Hcheck cell Hin; simpl in Hin.
  - contradiction.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply mem_cell_inb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Fixpoint mem_cells_nodupb (cells: list MemCell) : bool :=
  match cells with
  | [] => true
  | cell :: tail =>
      negb (mem_cell_inb cell tail) &&
      mem_cells_nodupb tail
  end.

Lemma mem_cells_nodupb_sound :
  forall cells,
    mem_cells_nodupb cells = true ->
    NoDup cells.
Proof.
  induction cells as [|cell tail IH]; intros Hcheck; simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply mem_cell_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH.
      exact Htail.
Qed.

Fixpoint mem_cells_disjointb
    (left right: list MemCell) : bool :=
  match left with
  | [] => true
  | cell :: tail =>
      negb (mem_cell_inb cell right) &&
      mem_cells_disjointb tail right
  end.

Definition mem_cells_disjoint
    (left right: list MemCell) : Prop :=
  forall cell,
    In cell left ->
    ~ In cell right.

Lemma mem_cells_disjointb_sound :
  forall left right,
    mem_cells_disjointb left right = true ->
    mem_cells_disjoint left right.
Proof.
  induction left as [|cell tail IH]; intros right Hcheck cell' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply negb_true_iff in Hhead.
      intro Hin_right.
      apply mem_cell_inb_complete in Hin_right.
      rewrite Hin_right in Hhead.
      discriminate.
    + eapply IH; eauto.
Qed.

Lemma mem_cells_disjoint_sym :
  forall left right,
    mem_cells_disjoint left right ->
    mem_cells_disjoint right left.
Proof.
  unfold mem_cells_disjoint.
  intros left right Hdisjoint cell Hin_right Hin_left.
  eapply Hdisjoint; eauto.
Qed.

Record private_separation_obligations
    (private_cells public_cells frame_cells: list MemCell) : Prop := {
  pso_private_nodup :
    NoDup private_cells;
  pso_private_public_disjoint :
    mem_cells_disjoint private_cells public_cells;
  pso_private_frame_disjoint :
    mem_cells_disjoint private_cells frame_cells;
}.

Definition check_private_separationb
    (private_cells public_cells frame_cells: list MemCell) : bool :=
  mem_cells_nodupb private_cells &&
  mem_cells_disjointb private_cells public_cells &&
  mem_cells_disjointb private_cells frame_cells.

Lemma check_private_separationb_sound :
  forall private_cells public_cells frame_cells,
    check_private_separationb
      private_cells public_cells frame_cells = true ->
    private_separation_obligations
      private_cells public_cells frame_cells.
Proof.
  intros private_cells public_cells frame_cells Hcheck.
  unfold check_private_separationb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hnodup & Hpublic) & Hframe).
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - apply mem_cells_disjointb_sound.
    exact Hpublic.
  - apply mem_cells_disjointb_sound.
    exact Hframe.
Qed.

Record private_non_escape_obligations
    (private_cells escaped_cells: list MemCell) : Prop := {
  pneo_private_not_escaped :
    mem_cells_disjoint private_cells escaped_cells;
}.

Definition check_private_non_escapeb
    (private_cells escaped_cells: list MemCell) : bool :=
  mem_cells_disjointb private_cells escaped_cells.

Lemma check_private_non_escapeb_sound :
  forall private_cells escaped_cells,
    check_private_non_escapeb private_cells escaped_cells = true ->
    private_non_escape_obligations private_cells escaped_cells.
Proof.
  intros private_cells escaped_cells Hcheck.
  constructor.
  apply mem_cells_disjointb_sound.
  exact Hcheck.
Qed.

Inductive private_event :=
| PrivateWrite (cell: MemCell)
| PrivateRead (cell: MemCell).

Fixpoint private_reads_defined
    (defined_cells: list MemCell)
    (trace: list private_event) : Prop :=
  match trace with
  | [] => True
  | PrivateWrite cell :: tail =>
      private_reads_defined (cell :: defined_cells) tail
  | PrivateRead cell :: tail =>
      In cell defined_cells /\
      private_reads_defined defined_cells tail
  end.

Fixpoint check_private_reads_definedb
    (defined_cells: list MemCell)
    (trace: list private_event) : bool :=
  match trace with
  | [] => true
  | PrivateWrite cell :: tail =>
      check_private_reads_definedb (cell :: defined_cells) tail
  | PrivateRead cell :: tail =>
      mem_cell_inb cell defined_cells &&
      check_private_reads_definedb defined_cells tail
  end.

Lemma check_private_reads_definedb_sound :
  forall trace defined_cells,
    check_private_reads_definedb defined_cells trace = true ->
    private_reads_defined defined_cells trace.
Proof.
  induction trace as [|event tail IH]; intros defined_cells Hcheck;
    simpl in Hcheck.
  - exact I.
  - destruct event as [write_cell | read_cell].
    + apply IH.
      exact Hcheck.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hread Htail].
      split.
      * apply mem_cell_inb_sound.
        exact Hread.
      * apply IH.
        exact Htail.
Qed.

Definition private_use_def_trace (trace: list private_event) : Prop :=
  private_reads_defined [] trace.

Definition check_private_use_def_traceb
    (trace: list private_event) : bool :=
  check_private_reads_definedb [] trace.

Lemma check_private_use_def_traceb_sound :
  forall trace,
    check_private_use_def_traceb trace = true ->
    private_use_def_trace trace.
Proof.
  unfold check_private_use_def_traceb, private_use_def_trace.
  intros trace Hcheck.
  apply check_private_reads_definedb_sound.
  exact Hcheck.
Qed.

Inductive private_access_event :=
| PrivateAccessWrite (access: AccessFunction)
| PrivateAccessRead (access: AccessFunction).

Definition private_access_inb
    (access: AccessFunction) (accesses: list AccessFunction) : bool :=
  existsb (access_strict_eqb access) accesses.

Lemma private_access_inb_sound :
  forall access accesses,
    private_access_inb access accesses = true ->
    In access accesses.
Proof.
  unfold private_access_inb.
  intros access accesses Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (access' & Hin & Heq).
  apply access_strict_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma private_access_inb_complete :
  forall access accesses,
    In access accesses ->
    private_access_inb access accesses = true.
Proof.
  unfold private_access_inb.
  intros access accesses Hin.
  apply existsb_exists.
  exists access.
  split.
  - exact Hin.
  - apply access_strict_eq_eqb.
    reflexivity.
Qed.

Fixpoint private_access_reads_defined
    (defined_accesses: list AccessFunction)
    (trace: list private_access_event) : Prop :=
  match trace with
  | [] => True
  | PrivateAccessWrite access :: tail =>
      private_access_reads_defined (access :: defined_accesses) tail
  | PrivateAccessRead access :: tail =>
      In access defined_accesses /\
      private_access_reads_defined defined_accesses tail
  end.

Fixpoint check_private_access_reads_definedb
    (defined_accesses: list AccessFunction)
    (trace: list private_access_event) : bool :=
  match trace with
  | [] => true
  | PrivateAccessWrite access :: tail =>
      check_private_access_reads_definedb
        (access :: defined_accesses) tail
  | PrivateAccessRead access :: tail =>
      private_access_inb access defined_accesses &&
      check_private_access_reads_definedb
        defined_accesses tail
  end.

Lemma check_private_access_reads_definedb_sound :
  forall trace defined_accesses,
    check_private_access_reads_definedb
      defined_accesses trace = true ->
    private_access_reads_defined defined_accesses trace.
Proof.
  induction trace as [|event tail IH];
    intros defined_accesses Hcheck; simpl in Hcheck.
  - exact I.
  - destruct event as [write_access | read_access].
    + apply IH.
      exact Hcheck.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hread Htail].
      split.
      * apply private_access_inb_sound.
        exact Hread.
      * apply IH.
        exact Htail.
Qed.

Definition private_access_use_def_trace
    (trace: list private_access_event) : Prop :=
  private_access_reads_defined [] trace.

Definition check_private_access_use_def_traceb
    (trace: list private_access_event) : bool :=
  check_private_access_reads_definedb [] trace.

Lemma check_private_access_use_def_traceb_sound :
  forall trace,
    check_private_access_use_def_traceb trace = true ->
    private_access_use_def_trace trace.
Proof.
  unfold check_private_access_use_def_traceb,
         private_access_use_def_trace.
  intros trace Hcheck.
  apply check_private_access_reads_definedb_sound.
  exact Hcheck.
Qed.

Definition instantiate_private_access_event
    (p: DomIndex)
    (event: private_access_event) : private_event :=
  match event with
  | PrivateAccessWrite access =>
      PrivateWrite (exact_cell access p)
  | PrivateAccessRead access =>
      PrivateRead (exact_cell access p)
  end.

Definition instantiate_private_access_trace
    (p: DomIndex)
    (trace: list private_access_event) : list private_event :=
  map (instantiate_private_access_event p) trace.

Definition instantiate_private_defined_accesses
    (p: DomIndex)
    (defined_accesses: list AccessFunction) : list MemCell :=
  map (fun access => exact_cell access p) defined_accesses.

Lemma in_instantiate_private_defined_accesses :
  forall p access defined_accesses,
    In access defined_accesses ->
    In (exact_cell access p)
      (instantiate_private_defined_accesses p defined_accesses).
Proof.
  unfold instantiate_private_defined_accesses.
  intros p access defined_accesses Hin.
  induction defined_accesses as [|access_head access_tail IH];
    simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin_tail].
    + subst. left. reflexivity.
    + right. apply IH. exact Hin_tail.
Qed.

Lemma private_access_reads_defined_instantiates :
  forall trace defined_accesses p,
    private_access_reads_defined defined_accesses trace ->
    private_reads_defined
      (instantiate_private_defined_accesses p defined_accesses)
      (instantiate_private_access_trace p trace).
Proof.
  induction trace as [|event tail IH];
    intros defined_accesses p Hdefined; simpl in Hdefined.
  - exact I.
  - destruct event as [write_access | read_access];
      unfold instantiate_private_access_trace; simpl.
    + fold (instantiate_private_access_trace p tail).
      change
        (private_reads_defined
           (instantiate_private_defined_accesses p
              (write_access :: defined_accesses))
           (instantiate_private_access_trace p tail)).
      apply IH.
      exact Hdefined.
    + destruct Hdefined as [Hread Htail].
      split.
      * apply in_instantiate_private_defined_accesses.
        exact Hread.
      * apply IH.
        exact Htail.
Qed.

Lemma private_access_use_def_trace_instantiates :
  forall trace p,
    private_access_use_def_trace trace ->
    private_use_def_trace
      (instantiate_private_access_trace p trace).
Proof.
  unfold private_access_use_def_trace, private_use_def_trace.
  intros trace p Hdefined.
  pose proof
    (private_access_reads_defined_instantiates
       trace [] p Hdefined)
    as Hcell_trace.
  simpl in Hcell_trace.
  exact Hcell_trace.
Qed.

Lemma check_private_access_use_def_traceb_instantiates :
  forall trace p,
    check_private_access_use_def_traceb trace = true ->
    private_use_def_trace
      (instantiate_private_access_trace p trace).
Proof.
  intros trace p Hcheck.
  apply private_access_use_def_trace_instantiates.
  apply check_private_access_use_def_traceb_sound.
  exact Hcheck.
Qed.

Definition public_not_hidden
    (hidden_cells: list MemCell) (cell: MemCell) : Prop :=
  ~ In cell hidden_cells.

Definition hidden_identity_cell_relation
    (hidden_cells: list MemCell) : cell_relation :=
  fun target_cell source_cell =>
    target_cell = source_cell /\
    public_not_hidden hidden_cells target_cell /\
    public_not_hidden hidden_cells source_cell.

Module PrivateStorageWitness
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Observation := StateObservation PolIRs Observer.
Module View := Observation.View.
Module Transform := Observation.Transform.
Module O := Observer.

Definition hidden_identity_cell_view
    (hidden_cells: list MemCell) : Observation.cell_view := {|
  Observation.cv_cell_relation :=
    hidden_identity_cell_relation hidden_cells;
  Observation.cv_source_observable :=
    public_not_hidden hidden_cells;
  Observation.cv_target_observable :=
    public_not_hidden hidden_cells;
  Observation.cv_related_source_observable :=
    fun _ _ Hrel => proj2 (proj2 Hrel);
  Observation.cv_related_target_observable :=
    fun _ _ Hrel => proj1 (proj2 Hrel);
  Observation.cv_source_observable_covered :=
    fun source_cell Hpublic =>
      ex_intro _
        source_cell
        (conj Hpublic (conj eq_refl (conj Hpublic Hpublic)));
  Observation.cv_target_observable_covered :=
    fun target_cell Hpublic =>
      ex_intro _
        target_cell
        (conj Hpublic (conj eq_refl (conj Hpublic Hpublic)));
|}.

Lemma hidden_identity_view_contains_state_eq :
  forall hidden_cells,
    Transform.observation_contains_state_eq
      (Observation.cell_view_observation
         (hidden_identity_cell_view hidden_cells)).
Proof.
  unfold Transform.observation_contains_state_eq.
  unfold Observation.cell_view_observation.
  unfold Observation.related_cells_observation.
  simpl.
  intros hidden_cells st_target st_source Hstate
         target_cell source_cell target_value Hrel Htarget.
  destruct Hrel as [Heq _].
  subst source_cell.
  pose proof
    (O.observe_cell_state_eq st_target st_source target_cell target_value
       Hstate Htarget)
    as Hstate_obs.
  destruct Hstate_obs as (source_value & Hsource & Hvalue).
  exists source_value.
  split; auto.
Qed.

Definition private_cells_hidden
    (private_cells hidden_cells: list MemCell) : Prop :=
  forall cell,
    In cell private_cells ->
    In cell hidden_cells.

Lemma private_cells_hidden_sound :
  forall private_cells hidden_cells,
    mem_cells_subsetb private_cells hidden_cells = true ->
    private_cells_hidden private_cells hidden_cells.
Proof.
  unfold private_cells_hidden.
  intros private_cells hidden_cells Hcheck cell Hin.
  eapply mem_cells_subsetb_sound; eauto.
Qed.

Record private_local_obligations
    (hidden_cells private_cells: list MemCell)
    (trace: list private_event) : Prop := {
  plo_private_hidden :
    private_cells_hidden private_cells hidden_cells;
  plo_private_nodup :
    NoDup private_cells;
  plo_private_use_def :
    private_use_def_trace trace;
}.

Definition check_private_local_obligationsb
    (hidden_cells private_cells: list MemCell)
    (trace: list private_event) : bool :=
  mem_cells_subsetb private_cells hidden_cells &&
  mem_cells_nodupb private_cells &&
  check_private_use_def_traceb trace.

Lemma check_private_local_obligationsb_sound :
  forall hidden_cells private_cells trace,
    check_private_local_obligationsb
      hidden_cells private_cells trace = true ->
    private_local_obligations
      hidden_cells private_cells trace.
Proof.
  intros hidden_cells private_cells trace Hcheck.
  unfold check_private_local_obligationsb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hhidden & Hnodup) & Husedef).
  constructor.
  - apply private_cells_hidden_sound.
    exact Hhidden.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - apply check_private_use_def_traceb_sound.
    exact Husedef.
Qed.

Record private_access_local_obligations
    (hidden_cells private_cells: list MemCell)
    (trace: list private_access_event) : Prop := {
  palo_private_hidden :
    private_cells_hidden private_cells hidden_cells;
  palo_private_nodup :
    NoDup private_cells;
  palo_private_access_use_def :
    private_access_use_def_trace trace;
  palo_private_instantiated_use_def :
    forall p,
      private_use_def_trace
        (instantiate_private_access_trace p trace);
}.

Definition check_private_access_local_obligationsb
    (hidden_cells private_cells: list MemCell)
    (trace: list private_access_event) : bool :=
  mem_cells_subsetb private_cells hidden_cells &&
  mem_cells_nodupb private_cells &&
  check_private_access_use_def_traceb trace.

Lemma check_private_access_local_obligationsb_sound :
  forall hidden_cells private_cells trace,
    check_private_access_local_obligationsb
      hidden_cells private_cells trace = true ->
    private_access_local_obligations
      hidden_cells private_cells trace.
Proof.
  intros hidden_cells private_cells trace Hcheck.
  unfold check_private_access_local_obligationsb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hhidden & Hnodup) & Husedef).
  pose proof
    (check_private_access_use_def_traceb_sound trace Husedef)
    as Haccess_use_def.
  constructor.
  - apply private_cells_hidden_sound.
    exact Hhidden.
  - apply mem_cells_nodupb_sound.
    exact Hnodup.
  - exact Haccess_use_def.
  - intro p.
    apply private_access_use_def_trace_instantiates.
    exact Haccess_use_def.
Qed.

Lemma private_cells_hidden_unobservable :
  forall private_cells hidden_cells,
    private_cells_hidden private_cells hidden_cells ->
    forall target_cell source_cell,
      In target_cell private_cells ->
      ~ Observation.cv_cell_relation
          (hidden_identity_cell_view hidden_cells)
          target_cell source_cell.
Proof.
  intros private_cells hidden_cells Hhidden target_cell source_cell
         Hprivate Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [Hpublic_target _]].
  apply Hpublic_target.
  eapply Hhidden; eauto.
Qed.

End PrivateStorageWitness.
