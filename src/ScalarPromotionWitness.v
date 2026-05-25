Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for scalar promotion / register replacement.

    A promoted scalar is private target storage that simulates one public source
    cell over a local region.  This witness checks only the protocol shape:

      - a load initializes the scalar before scalar reads/writes;
      - scalar events refer to the expected promoted scalar;
      - ordinary writes to the promoted source cell do not interfere;
      - if the source cell is live out, the trace ends with a store back.

    The value-simulation proof that scalar events compute the same value as the
    original memory events remains a semantic refinement obligation. *)

Inductive scalar_promotion_event :=
| PromotionLoad (source_cell scalar_cell: MemCell)
| PromotionScalarRead (scalar_cell: MemCell)
| PromotionScalarWrite (scalar_cell: MemCell)
| PromotionStore (scalar_cell source_cell: MemCell)
| PromotionGlobalWrite (cell: MemCell).

Fixpoint scalar_promotion_trace_safe_from
    (source_cell scalar_cell: MemCell)
    (loaded: bool)
    (trace: list scalar_promotion_event) : Prop :=
  match trace with
  | [] => True
  | PromotionLoad source' scalar' :: tail =>
      source' = source_cell /\
      scalar' = scalar_cell /\
      scalar_promotion_trace_safe_from
        source_cell scalar_cell true tail
  | PromotionScalarRead scalar' :: tail =>
      loaded = true /\
      scalar' = scalar_cell /\
      scalar_promotion_trace_safe_from
        source_cell scalar_cell loaded tail
  | PromotionScalarWrite scalar' :: tail =>
      loaded = true /\
      scalar' = scalar_cell /\
      scalar_promotion_trace_safe_from
        source_cell scalar_cell loaded tail
  | PromotionStore scalar' source' :: tail =>
      loaded = true /\
      scalar' = scalar_cell /\
      source' = source_cell /\
      scalar_promotion_trace_safe_from
        source_cell scalar_cell loaded tail
  | PromotionGlobalWrite cell :: tail =>
      cell <> source_cell /\
      scalar_promotion_trace_safe_from
        source_cell scalar_cell loaded tail
  end.

Fixpoint check_scalar_promotion_trace_safe_fromb
    (source_cell scalar_cell: MemCell)
    (loaded: bool)
    (trace: list scalar_promotion_event) : bool :=
  match trace with
  | [] => true
  | PromotionLoad source' scalar' :: tail =>
      mem_cell_strict_eqb source' source_cell &&
      mem_cell_strict_eqb scalar' scalar_cell &&
      check_scalar_promotion_trace_safe_fromb
        source_cell scalar_cell true tail
  | PromotionScalarRead scalar' :: tail =>
      loaded &&
      mem_cell_strict_eqb scalar' scalar_cell &&
      check_scalar_promotion_trace_safe_fromb
        source_cell scalar_cell loaded tail
  | PromotionScalarWrite scalar' :: tail =>
      loaded &&
      mem_cell_strict_eqb scalar' scalar_cell &&
      check_scalar_promotion_trace_safe_fromb
        source_cell scalar_cell loaded tail
  | PromotionStore scalar' source' :: tail =>
      loaded &&
      mem_cell_strict_eqb scalar' scalar_cell &&
      mem_cell_strict_eqb source' source_cell &&
      check_scalar_promotion_trace_safe_fromb
        source_cell scalar_cell loaded tail
  | PromotionGlobalWrite cell :: tail =>
      negb (mem_cell_strict_eqb cell source_cell) &&
      check_scalar_promotion_trace_safe_fromb
        source_cell scalar_cell loaded tail
  end.

Lemma check_scalar_promotion_trace_safe_fromb_sound :
  forall trace source_cell scalar_cell loaded,
    check_scalar_promotion_trace_safe_fromb
      source_cell scalar_cell loaded trace = true ->
    scalar_promotion_trace_safe_from
      source_cell scalar_cell loaded trace.
Proof.
  induction trace as [|event tail IH];
    intros source_cell scalar_cell loaded Hcheck; simpl in Hcheck.
  - exact I.
  - destruct event as [source' scalar' | scalar' | scalar'
                       | scalar' source' | cell]; simpl.
    + repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hsource & Hscalar) & Htail).
      apply mem_cell_strict_eqb_eq in Hsource.
      apply mem_cell_strict_eqb_eq in Hscalar.
      subst.
      repeat split.
      apply IH.
      exact Htail.
    + repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hloaded & Hscalar) & Htail).
      apply mem_cell_strict_eqb_eq in Hscalar.
      subst.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- apply IH.
           exact Htail.
    + repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hloaded & Hscalar) & Htail).
      apply mem_cell_strict_eqb_eq in Hscalar.
      subst.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- apply IH.
           exact Htail.
    + repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as (((Hloaded & Hscalar) & Hsource) & Htail).
      apply mem_cell_strict_eqb_eq in Hscalar.
      apply mem_cell_strict_eqb_eq in Hsource.
      subst.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ apply IH.
              exact Htail.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hnot_source Htail].
      apply negb_true_iff in Hnot_source.
      split.
      * intro Heq.
        apply mem_cell_strict_eq_eqb in Heq.
        rewrite Heq in Hnot_source.
        discriminate.
      * apply IH.
        exact Htail.
Qed.

Definition scalar_promotion_trace_safe
    (source_cell scalar_cell: MemCell)
    (trace: list scalar_promotion_event) : Prop :=
  scalar_promotion_trace_safe_from
    source_cell scalar_cell false trace.

Definition check_scalar_promotion_trace_safeb
    (source_cell scalar_cell: MemCell)
    (trace: list scalar_promotion_event) : bool :=
  check_scalar_promotion_trace_safe_fromb
    source_cell scalar_cell false trace.

Lemma check_scalar_promotion_trace_safeb_sound :
  forall trace source_cell scalar_cell,
    check_scalar_promotion_trace_safeb
      source_cell scalar_cell trace = true ->
    scalar_promotion_trace_safe
      source_cell scalar_cell trace.
Proof.
  unfold check_scalar_promotion_trace_safeb,
         scalar_promotion_trace_safe.
  intros trace source_cell scalar_cell Hcheck.
  apply check_scalar_promotion_trace_safe_fromb_sound.
  exact Hcheck.
Qed.

Fixpoint scalar_promotion_ends_with_store
    (source_cell scalar_cell: MemCell)
    (trace: list scalar_promotion_event) : Prop :=
  match trace with
  | [] => False
  | PromotionStore scalar' source' :: [] =>
      scalar' = scalar_cell /\ source' = source_cell
  | _ :: tail =>
      scalar_promotion_ends_with_store
        source_cell scalar_cell tail
  end.

Fixpoint check_scalar_promotion_ends_with_storeb
    (source_cell scalar_cell: MemCell)
    (trace: list scalar_promotion_event) : bool :=
  match trace with
  | [] => false
  | PromotionStore scalar' source' :: [] =>
      mem_cell_strict_eqb scalar' scalar_cell &&
      mem_cell_strict_eqb source' source_cell
  | _ :: tail =>
      check_scalar_promotion_ends_with_storeb
        source_cell scalar_cell tail
  end.

Lemma check_scalar_promotion_ends_with_storeb_sound :
  forall trace source_cell scalar_cell,
    check_scalar_promotion_ends_with_storeb
      source_cell scalar_cell trace = true ->
    scalar_promotion_ends_with_store
      source_cell scalar_cell trace.
Proof.
  induction trace as [|event tail IH];
    intros source_cell scalar_cell Hcheck; simpl in Hcheck.
  - discriminate.
  - destruct tail as [|next tail'].
    + destruct event as [source' scalar' | scalar' | scalar'
                         | scalar' source' | cell]; simpl in Hcheck;
        try discriminate.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hscalar Hsource].
      apply mem_cell_strict_eqb_eq in Hscalar.
      apply mem_cell_strict_eqb_eq in Hsource.
      subst.
      split; reflexivity.
    + destruct event as [source' scalar' | scalar' | scalar'
                         | scalar' source' | cell]; simpl in Hcheck;
        simpl; apply IH; exact Hcheck.
Qed.

Definition scalar_promotion_liveout_store
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event) : Prop :=
  if source_liveout
  then scalar_promotion_ends_with_store source_cell scalar_cell trace
  else True.

Definition check_scalar_promotion_liveout_storeb
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event) : bool :=
  if source_liveout
  then check_scalar_promotion_ends_with_storeb
         source_cell scalar_cell trace
  else true.

Lemma check_scalar_promotion_liveout_storeb_sound :
  forall trace source_cell scalar_cell source_liveout,
    check_scalar_promotion_liveout_storeb
      source_cell scalar_cell source_liveout trace = true ->
    scalar_promotion_liveout_store
      source_cell scalar_cell source_liveout trace.
Proof.
  intros trace source_cell scalar_cell source_liveout Hcheck.
  unfold check_scalar_promotion_liveout_storeb,
         scalar_promotion_liveout_store in *.
  destruct source_liveout.
  - apply check_scalar_promotion_ends_with_storeb_sound.
    exact Hcheck.
  - exact I.
Qed.

Record scalar_promotion_obligations
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event) : Prop := {
  spo_trace_safe :
    scalar_promotion_trace_safe source_cell scalar_cell trace;
  spo_liveout_store :
    scalar_promotion_liveout_store
      source_cell scalar_cell source_liveout trace;
}.

Definition check_scalar_promotionb
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event) : bool :=
  check_scalar_promotion_trace_safeb source_cell scalar_cell trace &&
  check_scalar_promotion_liveout_storeb
    source_cell scalar_cell source_liveout trace.

Lemma check_scalar_promotionb_sound :
  forall source_cell scalar_cell source_liveout trace,
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace.
Proof.
  intros source_cell scalar_cell source_liveout trace Hcheck.
  unfold check_scalar_promotionb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Htrace Hstore].
  constructor.
  - apply check_scalar_promotion_trace_safeb_sound.
    exact Htrace.
  - apply check_scalar_promotion_liveout_storeb_sound.
    exact Hstore.
Qed.
