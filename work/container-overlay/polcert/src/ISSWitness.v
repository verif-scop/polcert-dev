Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import PolyBase.
Import ListNotations.

Inductive iss_halfspace_sign :=
| ISSCutLtZero
| ISSCutGeZero.

Definition iss_halfspace_sign_eqb
    (s1 s2: iss_halfspace_sign) : bool :=
  match s1, s2 with
  | ISSCutLtZero, ISSCutLtZero => true
  | ISSCutGeZero, ISSCutGeZero => true
  | _, _ => false
  end.

Lemma iss_halfspace_sign_eqb_eq :
  forall s1 s2,
    iss_halfspace_sign_eqb s1 s2 = true ->
    s1 = s2.
Proof.
  intros s1 s2 H.
  destruct s1, s2; simpl in H; try discriminate; reflexivity.
Qed.

Fixpoint iss_halfspace_sign_list_eqb
    (ss1 ss2: list iss_halfspace_sign) : bool :=
  match ss1, ss2 with
  | [], [] => true
  | s1 :: ss1', s2 :: ss2' =>
      iss_halfspace_sign_eqb s1 s2 &&
      iss_halfspace_sign_list_eqb ss1' ss2'
  | _, _ => false
  end.

Lemma iss_halfspace_sign_list_eqb_eq :
  forall ss1 ss2,
    iss_halfspace_sign_list_eqb ss1 ss2 = true ->
    ss1 = ss2.
Proof.
  induction ss1 as [|s1 ss1 IH]; intros ss2 H.
  - destruct ss2; simpl in *; congruence.
  - destruct ss2 as [|s2 ss2]; simpl in *; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hsign Htail].
    apply iss_halfspace_sign_eqb_eq in Hsign.
    apply IH in Htail.
    subst. reflexivity.
Qed.

Definition iss_cut := (list Z * Z)%type.

Definition iss_cut_eqb : iss_cut -> iss_cut -> bool :=
  listzz_strict_eqb.

Lemma iss_cut_eqb_eq :
  forall c1 c2,
    iss_cut_eqb c1 c2 = true ->
    c1 = c2.
Proof.
  intros.
  unfold iss_cut_eqb in H.
  eapply listzz_strict_eqb_eq; eauto.
Qed.

Record iss_stmt_witness := {
  isw_parent_stmt : nat;
  isw_piece_signs : list iss_halfspace_sign;
}.

Definition iss_stmt_witness_eqb
    (w1 w2: iss_stmt_witness) : bool :=
  Nat.eqb w1.(isw_parent_stmt) w2.(isw_parent_stmt) &&
  iss_halfspace_sign_list_eqb w1.(isw_piece_signs) w2.(isw_piece_signs).

Lemma iss_stmt_witness_eqb_eq :
  forall w1 w2,
    iss_stmt_witness_eqb w1 w2 = true ->
    w1 = w2.
Proof.
  intros [p1 s1] [p2 s2] H.
  unfold iss_stmt_witness_eqb in H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H as [Hp Hs].
  apply Nat.eqb_eq in Hp.
  apply iss_halfspace_sign_list_eqb_eq in Hs.
  subst. reflexivity.
Qed.

Record iss_witness := {
  iw_cuts : list iss_cut;
  iw_stmt_witnesses : list iss_stmt_witness;
}.

Fixpoint iss_cut_list_eqb
    (cs1 cs2: list iss_cut) : bool :=
  match cs1, cs2 with
  | [], [] => true
  | c1 :: cs1', c2 :: cs2' =>
      iss_cut_eqb c1 c2 &&
      iss_cut_list_eqb cs1' cs2'
  | _, _ => false
  end.

Lemma iss_cut_list_eqb_eq :
  forall cs1 cs2,
    iss_cut_list_eqb cs1 cs2 = true ->
    cs1 = cs2.
Proof.
  induction cs1 as [|c1 cs1 IH]; intros cs2 H.
  - destruct cs2; simpl in *; congruence.
  - destruct cs2 as [|c2 cs2]; simpl in *; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hc Hcs].
    apply iss_cut_eqb_eq in Hc.
    apply IH in Hcs.
    subst. reflexivity.
Qed.

Fixpoint iss_stmt_witness_list_eqb
    (ws1 ws2: list iss_stmt_witness) : bool :=
  match ws1, ws2 with
  | [], [] => true
  | w1 :: ws1', w2 :: ws2' =>
      iss_stmt_witness_eqb w1 w2 &&
      iss_stmt_witness_list_eqb ws1' ws2'
  | _, _ => false
  end.

Lemma iss_stmt_witness_list_eqb_eq :
  forall ws1 ws2,
    iss_stmt_witness_list_eqb ws1 ws2 = true ->
    ws1 = ws2.
Proof.
  induction ws1 as [|w1 ws1 IH]; intros ws2 H.
  - destruct ws2; simpl in *; congruence.
  - destruct ws2 as [|w2 ws2]; simpl in *; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hw Hws].
    apply iss_stmt_witness_eqb_eq in Hw.
    apply IH in Hws.
    subst. reflexivity.
Qed.

Definition iss_witness_eqb
    (w1 w2: iss_witness) : bool :=
  iss_cut_list_eqb w1.(iw_cuts) w2.(iw_cuts) &&
  iss_stmt_witness_list_eqb
    w1.(iw_stmt_witnesses) w2.(iw_stmt_witnesses).

Lemma iss_witness_eqb_eq :
  forall w1 w2,
    iss_witness_eqb w1 w2 = true ->
    w1 = w2.
Proof.
  intros [cuts1 stmts1] [cuts2 stmts2] H.
  unfold iss_witness_eqb in H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H as [Hcuts Hstmts].
  apply iss_cut_list_eqb_eq in Hcuts.
  apply iss_stmt_witness_list_eqb_eq in Hstmts.
  subst. reflexivity.
Qed.
