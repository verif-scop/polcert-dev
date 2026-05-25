Require Import Values.

Require Import PolyBase.
Require Import CPolIRs.
Require Import CState.
Require Import CTy.
Require Import StateObservation.
Require Import LayoutRemapValidator.
Require Import PrivateStorageValidator.
Require Import ReuseStateView.
Require Import StorageBoundaryView.

(** Concrete observer for the C-like state model.

    The observer intentionally uses strict [MemCell] equality as its observable
    cell equivalence.  [PolyBase.cell_eq] is a logical/polyhedral equality using
    [veq], which can identify index lists up to trailing zeros; [CState.read_cell]
    goes through concrete array typing and offset calculation, so strict cell
    equality is the safer first adapter boundary. *)

Module CStateObserver <: CELL_OBSERVER CPolIRs.

Module State := CPolIRs.State.

Definition cell_value : Type := (CTy.basetype * val)%type.

Definition cell_value_eq (v1 v2: cell_value) : Prop :=
  fst v1 = fst v2 /\ snd v1 = snd v2.

Lemma cell_value_eq_refl :
  forall v, cell_value_eq v v.
Proof.
  intros [ty v].
  unfold cell_value_eq; simpl; auto.
Qed.

Lemma cell_value_eq_sym :
  forall v1 v2, cell_value_eq v1 v2 -> cell_value_eq v2 v1.
Proof.
  intros [ty1 val1] [ty2 val2] [Hty Hval].
  unfold cell_value_eq in *; simpl in *.
  subst; auto.
Qed.

Lemma cell_value_eq_trans :
  forall v1 v2 v3,
    cell_value_eq v1 v2 ->
    cell_value_eq v2 v3 ->
    cell_value_eq v1 v3.
Proof.
  intros [ty1 val1] [ty2 val2] [ty3 val3]
         [Hty12 Hval12] [Hty23 Hval23].
  unfold cell_value_eq in *; simpl in *.
  subst; auto.
Qed.

Definition observed_cell_eq (c1 c2: MemCell) : Prop :=
  c1 = c2.

Lemma observed_cell_eq_refl :
  forall c, observed_cell_eq c c.
Proof.
  unfold observed_cell_eq; auto.
Qed.

Definition observe_cell
    (st: State.t) (cell: MemCell) (observed: cell_value) : Prop :=
  CState.read_cell cell (fst observed) (snd observed) st.

Lemma observe_cell_state_eq :
  forall st1 st2 c v1,
    State.eq st1 st2 ->
    observe_cell st1 c v1 ->
    exists v2,
      observe_cell st2 c v2 /\
      cell_value_eq v1 v2.
Proof.
  intros st1 st2 c [ty v] Heq Hread.
  exists (ty, v).
  split.
  - unfold observe_cell in *; simpl in *.
    eapply CState.read_cell_stable_under_eq; eauto.
  - apply cell_value_eq_refl.
Qed.

Lemma observe_cell_cell_eq :
  forall st c1 c2 v1,
    observed_cell_eq c1 c2 ->
    observe_cell st c1 v1 ->
    exists v2,
      observe_cell st c2 v2 /\
      cell_value_eq v1 v2.
Proof.
  intros st c1 c2 [ty v] Hcell Hread.
  unfold observed_cell_eq in Hcell.
  subst.
  exists (ty, v).
  split.
  - exact Hread.
  - apply cell_value_eq_refl.
Qed.

End CStateObserver.

Module CStateObservation := StateObservation CPolIRs CStateObserver.
Module CLayoutRemapValidator :=
  LayoutRemapValidator CPolIRs CStateObserver.
Module CPrivateStorageValidator :=
  PrivateStorageValidator CPolIRs CStateObserver.
Module CPrivateStorageWitness :=
  CPrivateStorageValidator.Witness.
Module CReuseStateView :=
  ReuseStateView CPolIRs CStateObserver.
Module CStorageBoundaryView :=
  StorageBoundaryView CPolIRs CStateObserver.
