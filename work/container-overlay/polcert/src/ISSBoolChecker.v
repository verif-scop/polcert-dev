Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import PolyBase.
Require Import PolyLang.
Require Import InstrTy.
Require Import ISSWitness.
Require Import ISSRefinement.
Require Import PolIRs.

Module ISSBoolChecker (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.
Module Refine := ISSRefinement PolIRs.

Fixpoint ctxt_eqb (l1 l2: list Instr.ident): bool :=
  match l1, l2 with
  | id1 :: l1', id2 :: l2' =>
      Instr.ident_eqb id1 id2 && ctxt_eqb l1' l2'
  | [], [] => true
  | _, _ => false
  end.

Lemma ctxt_eqb_eq :
  forall l1 l2,
    ctxt_eqb l1 l2 = true ->
    l1 = l2.
Proof.
  induction l1 as [|x xs IH]; intros l2 H.
  - destruct l2; simpl in H; try discriminate; reflexivity.
  - destruct l2 as [|y ys]; simpl in H; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Heq Htl].
    apply Instr.ident_eqb_eq in Heq.
    apply IH in Htl.
    subst. reflexivity.
Qed.

Fixpoint ctxt_ty_eqb
    (vs1 vs2: list (Instr.ident * Ty.t)) : bool :=
  match vs1, vs2 with
  | (v1, ty1) :: vs1', (v2, ty2) :: vs2' =>
      Instr.ident_eqb v1 v2 && Ty.eqb ty1 ty2 && ctxt_ty_eqb vs1' vs2'
  | [], [] => true
  | _, _ => false
  end.

Lemma ctxt_ty_eqb_eq :
  forall vs1 vs2,
    ctxt_ty_eqb vs1 vs2 = true ->
    vs1 = vs2.
Proof.
  induction vs1 as [|(v1, ty1) vs1' IH]; intros vs2 H.
  - destruct vs2; simpl in H; try discriminate; reflexivity.
  - destruct vs2 as [|(v2, ty2) vs2']; simpl in H; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as [[Hid Hty] Htl].
    apply Instr.ident_eqb_eq in Hid.
    apply Ty.eqb_eq in Hty.
    apply IH in Htl.
    subst. reflexivity.
Qed.

Fixpoint check_parent_witnesses_in_rangeb
    (before_len: nat)
    (stmt_ws: list iss_stmt_witness) : bool :=
  match stmt_ws with
  | [] => true
  | w :: stmt_ws' =>
      Nat.ltb (isw_parent_stmt w) before_len &&
      check_parent_witnesses_in_rangeb before_len stmt_ws'
  end.

Lemma check_parent_witnesses_in_rangeb_sound :
  forall before_pis stmt_ws,
    check_parent_witnesses_in_rangeb (length before_pis) stmt_ws = true ->
    Refine.parent_witnesses_in_range before_pis stmt_ws.
Proof.
  intros before_pis stmt_ws.
  induction stmt_ws as [|w stmt_ws IH]; intro Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hparent Hrest].
    constructor.
    + apply Nat.ltb_lt. exact Hparent.
    + apply IH. exact Hrest.
Qed.

Definition stmt_payload_matches_witnessb
    (before_pis: list PolyLang.PolyInstr)
    (after_pi: PolyLang.PolyInstr)
    (w: iss_stmt_witness) : bool :=
  match nth_error before_pis (isw_parent_stmt w) with
  | Some source => Refine.payload_eq_except_domainb source after_pi
  | None => false
  end.

Lemma stmt_payload_matches_witnessb_sound :
  forall before_pis after_pi w,
    stmt_payload_matches_witnessb before_pis after_pi w = true ->
    Refine.stmt_payload_matches_witness before_pis after_pi w.
Proof.
  intros before_pis after_pi w Hcheck.
  unfold stmt_payload_matches_witnessb in Hcheck.
  destruct (nth_error before_pis (isw_parent_stmt w)) as [source|] eqn:Hsource;
    try discriminate.
  exists source.
  split; [exact Hsource|].
  eapply Refine.payload_eq_except_domainb_correct; eauto.
Qed.

Fixpoint check_stmt_parent_payload_relationb
    (before_pis: list PolyLang.PolyInstr)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : bool :=
  match after_pis, stmt_ws with
  | after_pi :: after_pis', w :: stmt_ws' =>
      stmt_payload_matches_witnessb before_pis after_pi w &&
      check_stmt_parent_payload_relationb before_pis after_pis' stmt_ws'
  | [], [] => true
  | _, _ => false
  end.

Lemma check_stmt_parent_payload_relationb_sound :
  forall before_pis after_pis stmt_ws,
    check_stmt_parent_payload_relationb before_pis after_pis stmt_ws = true ->
    Refine.stmt_parent_payload_relation before_pis after_pis stmt_ws.
Proof.
  intros before_pis after_pis stmt_ws.
  revert stmt_ws.
  induction after_pis as [|after_pi after_pis IH]; intros stmt_ws Hcheck.
  - destruct stmt_ws; simpl in Hcheck; try discriminate.
    constructor.
  - destruct stmt_ws as [|w stmt_ws]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    constructor.
    + eapply stmt_payload_matches_witnessb_sound; eauto.
    + eapply IH; eauto.
Qed.

Definition check_stmt_piece_signs_wfb
    (cuts: list iss_cut)
    (w: iss_stmt_witness) : bool :=
  Nat.eqb (length w.(isw_piece_signs)) (length cuts).

Lemma check_stmt_piece_signs_wfb_sound :
  forall cuts w,
    check_stmt_piece_signs_wfb cuts w = true ->
    Refine.stmt_piece_signs_wf cuts w.
Proof.
  intros cuts w Hcheck.
  unfold check_stmt_piece_signs_wfb in Hcheck.
  unfold Refine.stmt_piece_signs_wf.
  apply Nat.eqb_eq in Hcheck.
  exact Hcheck.
Qed.

Fixpoint check_stmt_piece_signs_relationb
    (cuts: list iss_cut)
    (stmt_ws: list iss_stmt_witness) : bool :=
  match stmt_ws with
  | [] => true
  | w :: stmt_ws' =>
      check_stmt_piece_signs_wfb cuts w &&
      check_stmt_piece_signs_relationb cuts stmt_ws'
  end.

Lemma check_stmt_piece_signs_relationb_sound :
  forall cuts stmt_ws,
    check_stmt_piece_signs_relationb cuts stmt_ws = true ->
    Refine.stmt_piece_signs_relation cuts stmt_ws.
Proof.
  intros cuts stmt_ws.
  induction stmt_ws as [|w stmt_ws IH]; intro Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    constructor.
    + eapply check_stmt_piece_signs_wfb_sound; eauto.
    + eapply IH; eauto.
Qed.

Definition stmt_domain_matches_cutsb
    (before_pis: list PolyLang.PolyInstr)
    (cuts: list iss_cut)
    (after_pi: PolyLang.PolyInstr)
    (w: iss_stmt_witness) : bool :=
  match nth_error before_pis (isw_parent_stmt w),
        Refine.iss_piece_constraints cuts w.(isw_piece_signs) with
  | Some source, Some piece_constrs =>
      listzzs_strict_eqb
        after_pi.(PolyLang.pi_poly)
        (source.(PolyLang.pi_poly) ++ piece_constrs)
  | _, _ => false
  end.

Lemma stmt_domain_matches_cutsb_sound :
  forall before_pis cuts after_pi w,
    stmt_domain_matches_cutsb before_pis cuts after_pi w = true ->
    Refine.stmt_domain_matches_cuts before_pis cuts after_pi w.
Proof.
  intros before_pis cuts after_pi w Hcheck.
  unfold stmt_domain_matches_cutsb in Hcheck.
  destruct (nth_error before_pis (isw_parent_stmt w)) as [source|] eqn:Hsource;
    try discriminate.
  destruct (Refine.iss_piece_constraints cuts (isw_piece_signs w))
    as [piece_constrs|] eqn:Hpiece; try discriminate.
  exists source, piece_constrs.
  repeat split; try assumption.
  apply listzzs_strict_eqb_eq in Hcheck.
  exact Hcheck.
Qed.

Fixpoint check_stmt_domain_cut_relationb
    (before_pis: list PolyLang.PolyInstr)
    (after_pis: list PolyLang.PolyInstr)
    (cuts: list iss_cut)
    (stmt_ws: list iss_stmt_witness) : bool :=
  match after_pis, stmt_ws with
  | after_pi :: after_pis', w :: stmt_ws' =>
      stmt_domain_matches_cutsb before_pis cuts after_pi w &&
      check_stmt_domain_cut_relationb before_pis after_pis' cuts stmt_ws'
  | [], [] => true
  | _, _ => false
  end.

Lemma check_stmt_domain_cut_relationb_sound :
  forall before_pis after_pis cuts stmt_ws,
    check_stmt_domain_cut_relationb before_pis after_pis cuts stmt_ws = true ->
    Refine.stmt_domain_cut_relation before_pis after_pis cuts stmt_ws.
Proof.
  intros before_pis after_pis cuts stmt_ws.
  revert stmt_ws.
  induction after_pis as [|after_pi after_pis IH]; intros stmt_ws Hcheck.
  - destruct stmt_ws; simpl in Hcheck; try discriminate.
    constructor.
  - destruct stmt_ws as [|w stmt_ws]; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    constructor.
    + eapply stmt_domain_matches_cutsb_sound; eauto.
    + eapply IH; eauto.
Qed.

Fixpoint sign_list_memb
    (signs: list iss_halfspace_sign)
    (rows: list (list iss_halfspace_sign)) : bool :=
  match rows with
  | [] => false
  | row :: rows' =>
      iss_halfspace_sign_list_eqb signs row || sign_list_memb signs rows'
  end.

Lemma sign_list_memb_sound :
  forall signs rows,
    sign_list_memb signs rows = true ->
    In signs rows.
Proof.
  intros signs rows.
  induction rows as [|row rows IH]; intro Hmemb.
  - simpl in Hmemb. discriminate.
  - simpl in Hmemb.
    apply orb_true_iff in Hmemb.
    destruct Hmemb as [Heq | Htail].
    + left.
      apply iss_halfspace_sign_list_eqb_eq in Heq.
      exact (eq_sym Heq).
    + right.
      eapply IH; eauto.
Qed.

Lemma iss_halfspace_sign_list_eqb_refl :
  forall signs,
    iss_halfspace_sign_list_eqb signs signs = true.
Proof.
  induction signs as [|sign signs IH]; simpl; auto.
  destruct sign; simpl; rewrite IH; reflexivity.
Qed.

Lemma sign_list_memb_complete :
  forall signs rows,
    In signs rows ->
    sign_list_memb signs rows = true.
Proof.
  intros signs rows.
  induction rows as [|row rows IH]; intro Hin.
  - inversion Hin.
  - simpl.
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst.
      rewrite iss_halfspace_sign_list_eqb_refl.
      reflexivity.
    + apply orb_true_iff.
      right.
      eapply IH; eauto.
Qed.

Fixpoint check_sign_list_nodupb
    (rows: list (list iss_halfspace_sign)) : bool :=
  match rows with
  | [] => true
  | row :: rows' =>
      negb (sign_list_memb row rows') &&
      check_sign_list_nodupb rows'
  end.

Lemma check_sign_list_nodupb_sound :
  forall rows,
    check_sign_list_nodupb rows = true ->
    NoDup rows.
Proof.
  induction rows as [|row rows IH]; intro Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    constructor.
    + intro Hin.
      apply sign_list_memb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + eapply IH; eauto.
Qed.

Fixpoint check_all_expected_sign_listsb
    (expected actual: list (list iss_halfspace_sign)) : bool :=
  match expected with
  | [] => true
  | signs :: expected' =>
      sign_list_memb signs actual &&
      check_all_expected_sign_listsb expected' actual
  end.

Lemma check_all_expected_sign_listsb_sound :
  forall expected actual,
    check_all_expected_sign_listsb expected actual = true ->
    forall signs,
      In signs expected ->
      In signs actual.
Proof.
  intros expected actual.
  induction expected as [|signs expected IH]; intros Hcheck target Hin.
  - inversion Hin.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hmemb Hrest].
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst.
      eapply sign_list_memb_sound; eauto.
    + eapply IH; eauto.
Qed.

Definition check_parent_sign_partitionb
    (cuts: list iss_cut)
    (parent: nat)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : bool :=
  let signs := Refine.child_signs_for_parent parent after_pis stmt_ws in
  check_sign_list_nodupb signs &&
  check_all_expected_sign_listsb
    (Refine.all_iss_sign_vectors (length cuts)) signs.

Lemma check_parent_sign_partitionb_sound :
  forall cuts parent after_pis stmt_ws,
    check_parent_sign_partitionb cuts parent after_pis stmt_ws = true ->
    Refine.parent_sign_partition_complete cuts parent after_pis stmt_ws.
Proof.
  intros cuts parent after_pis stmt_ws Hcheck.
  unfold check_parent_sign_partitionb in Hcheck.
  set (signs := Refine.child_signs_for_parent parent after_pis stmt_ws) in *.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hnodup Hall].
  unfold Refine.parent_sign_partition_complete.
  split.
  - subst signs.
    eapply check_sign_list_nodupb_sound; eauto.
  - intros target.
    intro Hin.
    subst signs.
    eapply check_all_expected_sign_listsb_sound; eauto.
Qed.

Fixpoint check_parent_sign_partition_rangeb
    (cuts: list iss_cut)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    (parent count: nat) : bool :=
  match count with
  | O => true
  | S count' =>
      check_parent_sign_partitionb cuts parent after_pis stmt_ws &&
      check_parent_sign_partition_rangeb
        cuts after_pis stmt_ws (S parent) count'
  end.

Lemma check_parent_sign_partition_rangeb_sound :
  forall cuts
         (before_pis after_pis: list PolyLang.PolyInstr)
         stmt_ws parent count,
    check_parent_sign_partition_rangeb cuts after_pis stmt_ws parent count = true ->
    forall idx (source: PolyLang.PolyInstr),
      nth_error before_pis idx = Some source ->
      parent <= idx < parent + count ->
      Refine.parent_sign_partition_complete cuts idx after_pis stmt_ws.
Proof.
  intros cuts before_pis after_pis stmt_ws parent count.
  revert parent.
  induction count as [|count IH]; intros parent Hcheck idx source Hnth Hrange.
  - lia.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhere Hrest].
    destruct Hrange as [Hlo Hhi].
    destruct (Nat.eq_dec idx parent) as [Heq | Hneq].
    + subst idx.
      eapply check_parent_sign_partitionb_sound; eauto.
    + eapply IH; eauto.
      lia.
Qed.

Definition check_domain_partition_shapeb
    (before after: PolyLang.t)
    (w: iss_witness) : bool :=
  let '(before_pis, before_varctxt, before_vars) := before in
  let '(after_pis, after_varctxt, after_vars) := after in
  ctxt_eqb before_varctxt after_varctxt &&
  ctxt_ty_eqb before_vars after_vars &&
  check_parent_witnesses_in_rangeb (length before_pis) w.(iw_stmt_witnesses) &&
  check_stmt_parent_payload_relationb
    before_pis after_pis w.(iw_stmt_witnesses).

Lemma check_domain_partition_shapeb_sound :
  forall before after w,
    check_domain_partition_shapeb before after w = true ->
    Refine.domain_partition_shape_with_witness before after w.
Proof.
  intros before after w Hcheck.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold check_domain_partition_shapeb in Hcheck.
  unfold Refine.domain_partition_shape_with_witness.
  unfold Refine.domain_partition_shape.
  simpl in *.
  repeat match goal with
  | Hconj : _ && _ = true |- _ => apply andb_true_iff in Hconj
  | Hconj : _ /\ _ |- _ => destruct Hconj
  end.
  repeat match goal with
  | Heq : ctxt_eqb _ _ = true |- _ => apply ctxt_eqb_eq in Heq
  | Heq : ctxt_ty_eqb _ _ = true |- _ => apply ctxt_ty_eqb_eq in Heq
  | Heq : check_parent_witnesses_in_rangeb _ _ = true |- _ =>
      apply check_parent_witnesses_in_rangeb_sound in Heq
  | Heq : check_stmt_parent_payload_relationb _ _ _ = true |- _ =>
      apply check_stmt_parent_payload_relationb_sound in Heq
  end.
  repeat split; assumption.
Qed.

Definition check_domain_partition_cut_shapeb
    (before after: PolyLang.t)
    (w: iss_witness) : bool :=
  let '(before_pis, _, _) := before in
  let '(after_pis, _, _) := after in
  check_domain_partition_shapeb before after w &&
  check_stmt_piece_signs_relationb w.(iw_cuts) w.(iw_stmt_witnesses) &&
  check_stmt_domain_cut_relationb
    before_pis after_pis w.(iw_cuts) w.(iw_stmt_witnesses).

Lemma check_domain_partition_cut_shapeb_sound :
  forall before after w,
    check_domain_partition_cut_shapeb before after w = true ->
    Refine.domain_partition_cut_shape before after w.
Proof.
  intros before after w Hcheck.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold check_domain_partition_cut_shapeb in Hcheck.
  unfold Refine.domain_partition_cut_shape.
  simpl in *.
  repeat match goal with
  | Hconj : _ && _ = true |- _ => apply andb_true_iff in Hconj
  | Hconj : _ /\ _ |- _ => destruct Hconj
  end.
  assert (Hshape_bool :
            check_domain_partition_shapeb
              (before_pis, before_varctxt, before_vars)
              (after_pis, after_varctxt, after_vars) w = true).
  {
    unfold check_domain_partition_shapeb.
    simpl.
    rewrite H.
    rewrite H4.
    rewrite H3.
    rewrite H2.
    reflexivity.
  }
  pose proof (check_domain_partition_shapeb_sound
                (before_pis, before_varctxt, before_vars)
                (after_pis, after_varctxt, after_vars)
                w Hshape_bool) as Hshape.
  pose proof (check_stmt_piece_signs_relationb_sound
                (iw_cuts w) (iw_stmt_witnesses w) H1) as Hsigns.
  pose proof (check_stmt_domain_cut_relationb_sound
                before_pis after_pis (iw_cuts w) (iw_stmt_witnesses w) H0)
    as Hdomains.
  exact (conj Hshape (conj Hsigns Hdomains)).
Qed.

Definition check_domain_partition_complete_cut_shapeb
    (before after: PolyLang.t)
    (w: iss_witness) : bool :=
  let '(before_pis, _, _) := before in
  let '(after_pis, _, _) := after in
  check_domain_partition_cut_shapeb before after w &&
  check_parent_sign_partition_rangeb
    w.(iw_cuts) after_pis w.(iw_stmt_witnesses) 0 (length before_pis).

Lemma check_domain_partition_complete_cut_shapeb_sound :
  forall before after w,
    check_domain_partition_complete_cut_shapeb before after w = true ->
    Refine.domain_partition_complete_cut_shape before after w.
Proof.
  intros before after w Hcheck.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold check_domain_partition_complete_cut_shapeb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcut Hparts].
  split.
  - eapply check_domain_partition_cut_shapeb_sound; eauto.
  - unfold Refine.cut_partition_complete.
    simpl.
    intros parent source Hnth.
    eapply check_parent_sign_partition_rangeb_sound
      with (before_pis := before_pis) (parent := 0) (count := length before_pis);
      eauto.
    split.
    + lia.
    + apply nth_error_Some.
      rewrite Hnth.
      discriminate.
Qed.

End ISSBoolChecker.
