Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import SelectionSort.
Require Import SetoidList.
Require Import Sorting.Permutation.
Require Import Base.
Require Import Linalg.
Require Import LinalgExt.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import ISSWitness.
Require Import ISSRefinement.
Require Import ISSSemantics.
Require Import TilingRelation.
Require Import PolIRs.
Import ListNotations.

Module ISSCutSemantics (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module Refine := ISSRefinement PolIRs.
Module Sem := ISSSemantics PolIRs.
Module TileRel := TilingRelation Instr.

Lemma NoDup_map_on_local :
  forall (A B: Type) (f: A -> B) (l: list A),
    NoDup l ->
    (forall x y,
      In x l ->
      In y l ->
      f x = f y ->
      x = y) ->
    NoDup (List.map f l).
Proof.
  intros A B f l Hnodup Hinj.
  induction Hnodup as [|x l Hnotin Hnodup IH].
  - constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hin_y]].
      assert (x = y) as ->.
      {
        eapply Hinj.
        - left. reflexivity.
        - right. exact Hin_y.
        - symmetry. exact Hfy.
      }
      contradiction.
    + eapply IH.
      intros x' y' Hinx Hiny Heq.
      eapply Hinj.
      * right. exact Hinx.
      * right. exact Hiny.
      * exact Heq.
Qed.

Definition instr_point_np_key (ip: PolyLang.InstrPoint) : list Z :=
  Z.of_nat (PolyLang.ip_nth ip) :: PolyLang.ip_index ip.

Definition instr_point_np_ltb
    (ip1 ip2: PolyLang.InstrPoint) : bool :=
  comparison_eqb
    (lex_compare (instr_point_np_key ip1) (instr_point_np_key ip2))
    Lt.

Definition instr_point_np_eqb
    (ip1 ip2: PolyLang.InstrPoint) : bool :=
  comparison_eqb
    (lex_compare (instr_point_np_key ip1) (instr_point_np_key ip2))
    Eq.

Lemma instr_point_np_ltb_trans :
  transitive instr_point_np_ltb.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  unfold instr_point_np_ltb in *.
  eapply comparison_eqb_iff_eq in Hxy.
  eapply comparison_eqb_iff_eq in Hyz.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.

Lemma instr_point_np_eqb_trans :
  transitive instr_point_np_eqb.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  unfold instr_point_np_eqb in *.
  eapply comparison_eqb_iff_eq in Hxy.
  eapply comparison_eqb_iff_eq in Hyz.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_trans; eauto.
Qed.

Lemma instr_point_np_eqb_refl :
  reflexive instr_point_np_eqb.
Proof.
  unfold reflexive, instr_point_np_eqb.
  intro x.
  eapply comparison_eqb_iff_eq.
  eapply lex_compare_reflexive.
Qed.

Lemma instr_point_np_eqb_symm :
  symmetric instr_point_np_eqb.
Proof.
  unfold symmetric, instr_point_np_eqb.
  intros x y.
  rewrite lex_compare_antisym.
  destruct (lex_compare (instr_point_np_key y) (instr_point_np_key x)); reflexivity.
Qed.

Lemma instr_point_np_cmp_total :
  total instr_point_np_ltb instr_point_np_eqb.
Proof.
  unfold total, instr_point_np_ltb, instr_point_np_eqb.
  intros x y.
  destruct (lex_compare (instr_point_np_key x) (instr_point_np_key y)) eqn:Hcmp.
  - right. right. reflexivity.
  - left. reflexivity.
  - right. left.
    rewrite lex_compare_antisym.
    rewrite Hcmp.
    reflexivity.
Qed.

Lemma instr_point_np_eqb_ltb_implies_ltb :
  eqb_ltb_implies_ltb instr_point_np_ltb instr_point_np_eqb.
Proof.
  unfold eqb_ltb_implies_ltb.
  intros x y z Hxy Hyz.
  unfold instr_point_np_eqb in Hxy.
  unfold instr_point_np_ltb in *.
  rewrite comparison_eqb_iff_eq in Hxy.
  rewrite comparison_eqb_iff_eq in Hyz.
  rewrite comparison_eqb_iff_eq.
  remember (instr_point_np_key x) as a.
  remember (instr_point_np_key y) as b.
  remember (instr_point_np_key z) as c.
  clear Heqa Heqb Heqc.
  rewrite lex_compare_left_eq with (t2 := b); trivial.
  eapply is_eq_iff_cmp_eq; eauto.
Qed.

Lemma instr_point_np_ltb_eqb_implies_ltb :
  ltb_eqb_implies_ltb instr_point_np_ltb instr_point_np_eqb.
Proof.
  unfold ltb_eqb_implies_ltb.
  intros x y z Hxy Hyz.
  unfold instr_point_np_eqb in Hyz.
  unfold instr_point_np_ltb in *.
  rewrite comparison_eqb_iff_eq in Hxy.
  rewrite comparison_eqb_iff_eq in Hyz.
  rewrite comparison_eqb_iff_eq.
  remember (instr_point_np_key x) as a.
  remember (instr_point_np_key y) as b.
  remember (instr_point_np_key z) as c.
  clear Heqa Heqb Heqc.
  eapply is_eq_iff_cmp_eq in Hyz; eauto.
  eapply lex_compare_right_eq with (t1 := a) in Hyz; eauto.
  rewrite Hyz in Hxy.
  exact Hxy.
Qed.

Lemma instr_point_np_eqb_implies_np_eq :
  forall ip1 ip2,
    instr_point_np_eqb ip1 ip2 = true ->
    PolyLang.np_eq ip1 ip2.
Proof.
  intros [nth1 idx1 tf1 ts1 instr1 dep1]
         [nth2 idx2 tf2 ts2 instr2 dep2].
  unfold instr_point_np_eqb, instr_point_np_key, PolyLang.np_eq.
  simpl.
  intros Heq.
  rewrite comparison_eqb_iff_eq in Heq.
  simpl in Heq.
  destruct (Z.of_nat nth1 ?= Z.of_nat nth2) eqn:Hcmp; try discriminate.
  split.
  - apply Z.compare_eq_iff in Hcmp.
    lia.
  - exact Heq.
Qed.

Lemma instr_point_np_ltb_implies_np_lt :
  forall ip1 ip2,
    instr_point_np_ltb ip1 ip2 = true ->
    PolyLang.np_lt ip1 ip2.
Proof.
  intros [nth1 idx1 tf1 ts1 instr1 dep1]
         [nth2 idx2 tf2 ts2 instr2 dep2].
  unfold instr_point_np_ltb, instr_point_np_key, PolyLang.np_lt.
  simpl.
  intros Hlt.
  rewrite comparison_eqb_iff_eq in Hlt.
  simpl in Hlt.
  destruct (Z.of_nat nth1 ?= Z.of_nat nth2) eqn:Hcmp; try discriminate.
  - right.
    split.
    + apply Z.compare_eq_iff in Hcmp.
      lia.
    + exact Hlt.
  - left.
    apply Z.compare_lt_iff in Hcmp.
    apply Nat2Z.inj_lt.
    exact Hcmp.
Qed.

Lemma sortedb_instr_point_np_implies_sorted_np :
  forall ipl,
    Sorted_b (combine_leb instr_point_np_ltb instr_point_np_eqb) ipl ->
    NoDupA PolyLang.np_eq ipl ->
    Sorted PolyLang.np_lt ipl.
Proof.
  assert (Hhd_strict :
    forall a tail,
      HdRel
        (fun x y =>
           combine_leb instr_point_np_ltb instr_point_np_eqb x y = true)
        a tail ->
      ~ InA PolyLang.np_eq a tail ->
      HdRel PolyLang.np_lt a tail).
  {
    intros a tail Hhd Hnotin.
    inversion Hhd as [|b tail' Hord]; subst.
    - constructor.
    - constructor.
      unfold combine_leb in Hord.
      apply orb_true_iff in Hord.
      destruct Hord as [Hlt|Heq].
      + eapply instr_point_np_ltb_implies_np_lt; eauto.
      + exfalso.
        apply Hnotin.
        eapply InA_cons_hd.
        eapply instr_point_np_eqb_implies_np_eq; eauto.
  }
  induction ipl as [|a ipl IH]; intros Hsorted Hnd.
  - constructor.
  - inversion Hsorted as [|? ? Hsorted_tail Hhd]; subst.
    inversion Hnd as [|? ? Hnotin Hnd_tail]; subst.
    constructor.
    + eapply IH; eauto.
    + eapply Hhd_strict; eauto.
Qed.

Lemma instr_point_list_semantics_map_preserved :
  forall (f: PolyLang.InstrPoint -> PolyLang.InstrPoint) ipl st1 st2,
    (forall ip s1 s2,
      In ip ipl ->
      (PolyLang.ILSema.instr_point_sema ip s1 s2 <->
       PolyLang.ILSema.instr_point_sema (f ip) s1 s2)) ->
    PolyLang.ILSema.instr_point_list_semantics ipl st1 st2 ->
    PolyLang.ILSema.instr_point_list_semantics (List.map f ipl) st1 st2.
Proof.
  intros f ipl st1 st2 Hequiv Hsema.
  induction Hsema.
  - simpl.
    econstructor.
    exact H.
  - simpl.
    econstructor.
    + eapply (proj1 (Hequiv ip st1 st2 (or_introl eq_refl))).
      exact H.
    + eapply IHHsema.
      intros ip' s1 s2 Hin.
      eapply Hequiv.
      right.
      exact Hin.
Qed.

Lemma HdRel_sched_map_time_stamp_preserved :
  forall (f: PolyLang.InstrPoint -> PolyLang.InstrPoint) ip ipl,
    (forall ip',
      In ip' (ip :: ipl) ->
      PolyLang.ip_time_stamp (f ip') = PolyLang.ip_time_stamp ip') ->
    HdRel PolyLang.instr_point_sched_le ip ipl ->
    HdRel PolyLang.instr_point_sched_le (f ip) (List.map f ipl).
Proof.
  intros f ip ipl Hts Hhd.
  induction Hhd as [|b l Hle].
  - simpl.
    constructor.
  - simpl.
    constructor.
    unfold PolyLang.instr_point_sched_le in *.
    rewrite (Hts ip (or_introl eq_refl)).
    rewrite (Hts b (or_intror (or_introl eq_refl))).
    exact Hle.
Qed.

Lemma sorted_sched_map_time_stamp_preserved :
  forall (f: PolyLang.InstrPoint -> PolyLang.InstrPoint) ipl,
    (forall ip,
      In ip ipl ->
      PolyLang.ip_time_stamp (f ip) = PolyLang.ip_time_stamp ip) ->
    Sorted PolyLang.instr_point_sched_le ipl ->
    Sorted PolyLang.instr_point_sched_le (List.map f ipl).
Proof.
  intros f ipl Hts Hsorted.
  induction Hsorted.
  - simpl.
    constructor.
  - simpl.
    constructor.
    + eapply IHHsorted.
      intros ip' Hip'.
      eapply Hts.
      right.
      exact Hip'.
    + eapply HdRel_sched_map_time_stamp_preserved.
      * intros ip' Hip'.
        eapply Hts.
        exact Hip'.
      * exact H.
Qed.

Lemma NoDup_map_value_unique :
  forall (A B: Type) (f: A -> B) xs x y,
    NoDup (map f xs) ->
    In x xs ->
    In y xs ->
    f x = f y ->
    x = y.
Proof.
  intros A B f xs x y Hnodup Hinx Hiny Heq.
  destruct (In_nth_error _ _ Hinx) as [nx Hx].
  destruct (In_nth_error _ _ Hiny) as [ny Hy].
  assert (Hmx :
            nth_error (map f xs) nx = Some (f x)).
  {
    eapply Refine.nth_error_map_some; eauto.
  }
  assert (Hmy :
            nth_error (map f xs) ny = Some (f y)).
  {
    eapply Refine.nth_error_map_some; eauto.
  }
  rewrite <- Heq in Hmy.
  assert (nx = ny).
  {
    eapply Refine.NoDup_nth_error_injective; eauto.
  }
  subst ny.
  rewrite Hx in Hy.
  inversion Hy.
  reflexivity.
Qed.

Lemma parent_sign_partition_complete_nodup_child_pairs :
  forall cuts parent after_pis stmt_ws,
    Refine.parent_sign_partition_complete cuts parent after_pis stmt_ws ->
    NoDup (Refine.child_pairs_for_parent parent after_pis stmt_ws).
Proof.
  intros cuts parent after_pis stmt_ws Hpart.
  destruct Hpart as [Hnodup_signs _].
  unfold Refine.child_signs_for_parent in Hnodup_signs.
  eapply NoDup_map_inv.
  exact Hnodup_signs.
Qed.

Lemma child_pair_unique_by_sign :
  forall cuts parent after_pis stmt_ws pair1 pair2,
    Refine.parent_sign_partition_complete cuts parent after_pis stmt_ws ->
    In pair1 (Refine.child_pairs_for_parent parent after_pis stmt_ws) ->
    In pair2 (Refine.child_pairs_for_parent parent after_pis stmt_ws) ->
    isw_piece_signs (snd pair1) = isw_piece_signs (snd pair2) ->
    pair1 = pair2.
Proof.
  intros cuts parent after_pis stmt_ws pair1 pair2 Hpart Hin1 Hin2 Hsign.
  destruct Hpart as [Hnodup_signs _].
  unfold Refine.child_signs_for_parent in Hnodup_signs.
  eapply NoDup_map_value_unique; eauto.
Qed.

Lemma NoDup_filter_nth_error_unique :
  forall (A: Type) (pred: A -> bool) xs i j x,
    NoDup (filter pred xs) ->
    nth_error xs i = Some x ->
    nth_error xs j = Some x ->
    pred x = true ->
    i = j.
Proof.
  intros A pred xs.
  induction xs as [|h t IH]; intros i j x Hnd Hi Hj Hpred.
  - destruct i; inversion Hi.
  - destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj.
    + reflexivity.
    + inversion Hi; subst h; clear Hi.
      simpl in Hnd.
      rewrite Hpred in Hnd.
      apply NoDup_cons_iff in Hnd.
      destruct Hnd as [Hnotin _].
      exfalso.
      apply Hnotin.
      apply filter_In.
      split.
      * eapply nth_error_In; eauto.
      * exact Hpred.
    + inversion Hj; subst h; clear Hj.
      simpl in Hnd.
      rewrite Hpred in Hnd.
      apply NoDup_cons_iff in Hnd.
      destruct Hnd as [Hnotin _].
      exfalso.
      apply Hnotin.
      apply filter_In.
      split.
      * eapply nth_error_In; eauto.
      * exact Hpred.
    + destruct (pred h) eqn:Hph.
      -- simpl in Hnd.
         rewrite Hph in Hnd.
         simpl in Hnd.
         apply NoDup_cons_iff in Hnd.
         destruct Hnd as [_ Hnd].
         f_equal.
         exact (IH i' j' x Hnd Hi Hj Hpred).
      -- simpl in Hnd.
         rewrite Hph in Hnd.
         simpl in Hnd.
         f_equal.
         exact (IH i' j' x Hnd Hi Hj Hpred).
Qed.

Lemma Forall2_nth_error_local :
  forall A B (P: A -> B -> Prop) xs ys n x y,
    Forall2 P xs ys ->
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    P x y.
Proof.
  intros A B P xs ys n.
  revert xs ys.
  induction n as [|n IH]; intros xs ys x y Hrel Hx Hy.
  - destruct xs as [|xh xt], ys as [|yh yt];
      inversion Hrel; simpl in *; try discriminate.
    inversion Hx; inversion Hy; subst.
    assumption.
  - destruct xs as [|xh xt], ys as [|yh yt];
      inversion Hrel; simpl in *; try discriminate.
    eapply IH; eauto.
Qed.

Lemma domain_partition_complete_cut_shape_nth_domain_relation :
  forall before after w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
         n after_pi stmt_w,
    before = (before_pis, before_varctxt, before_vars) ->
    after = (after_pis, after_varctxt, after_vars) ->
    Refine.domain_partition_complete_cut_shape before after w ->
    nth_error after_pis n = Some after_pi ->
    nth_error w.(iw_stmt_witnesses) n = Some stmt_w ->
    Refine.stmt_domain_matches_cuts
      before_pis w.(iw_cuts) after_pi stmt_w.
Proof.
  intros before after w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
         n after_pi stmt_w Hbefore Hafter Hcomplete Hnth_after Hnth_w.
  subst before after.
  unfold Refine.domain_partition_complete_cut_shape in Hcomplete.
  destruct Hcomplete as [Hcut _].
  unfold Refine.domain_partition_cut_shape in Hcut.
  simpl in Hcut.
  destruct Hcut as [_ [_ Hrel]].
  eapply Forall2_nth_error_local; eauto.
Qed.

Lemma domain_partition_complete_cut_shape_nth_payload_relation :
  forall before after w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
         n after_pi stmt_w,
    before = (before_pis, before_varctxt, before_vars) ->
    after = (after_pis, after_varctxt, after_vars) ->
    Refine.domain_partition_complete_cut_shape before after w ->
    nth_error after_pis n = Some after_pi ->
    nth_error w.(iw_stmt_witnesses) n = Some stmt_w ->
    Refine.stmt_payload_matches_witness before_pis after_pi stmt_w.
Proof.
  intros before after w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
         n after_pi stmt_w Hbefore Hafter Hcomplete Hnth_after Hnth_w.
  subst before after.
  unfold Refine.domain_partition_complete_cut_shape in Hcomplete.
  destruct Hcomplete as [Hcut _].
  unfold Refine.domain_partition_cut_shape in Hcut.
  simpl in Hcut.
  destruct Hcut as [Hshape _].
  unfold Refine.domain_partition_shape in Hshape.
  simpl in Hshape.
  destruct Hshape as [_ [_ [_ Hrel]]].
  eapply Forall2_nth_error_local; eauto.
Qed.

Lemma complete_cut_shape_after_point_signs_match :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n after_pi stmt_w ip_after source piece_constrs,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    nth_error after_pis n = Some after_pi ->
    nth_error w.(iw_stmt_witnesses) n = Some stmt_w ->
    nth_error before_pis (isw_parent_stmt stmt_w) = Some source ->
    Refine.iss_piece_constraints w.(iw_cuts) (isw_piece_signs stmt_w) = Some piece_constrs ->
    PolyLang.belongs_to ip_after after_pi ->
    isw_piece_signs stmt_w = Refine.iss_signs_for_point (PolyLang.ip_index ip_after) w.(iw_cuts).
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n after_pi stmt_w ip_after source piece_constrs
         Hcomplete Hnth_after Hnth_w Hsource Hpiece Hbel.
  pose proof
    (domain_partition_complete_cut_shape_nth_domain_relation
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
       n after_pi stmt_w eq_refl eq_refl Hcomplete Hnth_after Hnth_w)
    as Hmatch.
  pose proof
    (proj1
       (Refine.stmt_domain_matches_cuts_in_domain_iff
          before_pis
          w.(iw_cuts)
          after_pi
          stmt_w
          (PolyLang.ip_index ip_after)
          source
          piece_constrs
          Hmatch Hsource Hpiece))
    as Hiff.
  destruct Hbel as [Hdom_after _].
  specialize (Hiff Hdom_after).
  destruct Hiff as [_ Hsat_stmt].
  assert (Hsat_expected :
            Forall2
              (Refine.point_satisfies_iss_cut (PolyLang.ip_index ip_after))
              w.(iw_cuts)
              (Refine.iss_signs_for_point (PolyLang.ip_index ip_after) w.(iw_cuts))).
  {
    apply Refine.iss_signs_for_point_satisfy.
  }
  symmetry.
  eapply Refine.point_satisfies_iss_cuts_functional; eauto.
Qed.

Lemma nth_error_after_stmt_implies_child_pair :
  forall after_pis stmt_ws n after_pi w parent,
    nth_error after_pis n = Some after_pi ->
    nth_error stmt_ws n = Some w ->
    isw_parent_stmt w = parent ->
    In (after_pi, w) (Refine.child_pairs_for_parent parent after_pis stmt_ws).
Proof.
  intros after_pis stmt_ws n after_pi w parent Hafter Hw Hparent.
  unfold Refine.child_pairs_for_parent, Refine.iss_pairs.
  apply filter_In.
  split.
  - eapply nth_error_In.
    eapply Sem.nth_error_combine_local; eauto.
  - simpl.
    apply Nat.eqb_eq.
    exact Hparent.
Qed.

Lemma complete_cut_shape_after_point_signs_match_nth :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n after_pi stmt_w ip_after,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    nth_error after_pis n = Some after_pi ->
    nth_error w.(iw_stmt_witnesses) n = Some stmt_w ->
    PolyLang.belongs_to ip_after after_pi ->
    isw_piece_signs stmt_w =
      Refine.iss_signs_for_point (PolyLang.ip_index ip_after) w.(iw_cuts).
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n after_pi stmt_w ip_after
         Hcomplete Hnth_after Hnth_w Hbel.
  pose proof
    (domain_partition_complete_cut_shape_nth_domain_relation
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
       n after_pi stmt_w eq_refl eq_refl Hcomplete Hnth_after Hnth_w)
    as Hmatch.
  destruct Hmatch as
      [source [piece_constrs [Hsource [Hpiece _]]]].
  eapply complete_cut_shape_after_point_signs_match; eauto.
Qed.

Lemma before_of_after_point_injective_complete_cut_shape :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after ip1 ip2,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    In ip1 ipl_after ->
    In ip2 ipl_after ->
    Sem.before_of_after_point w.(iw_stmt_witnesses) ip1 =
    Sem.before_of_after_point w.(iw_stmt_witnesses) ip2 ->
    ip1 = ip2.
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after
         [n1 idx1 tf1 ts1 instr1 depth1]
         [n2 idx2 tf2 ts2 instr2 depth2]
         Hcomplete Hflat Hin1 Hin2 Heq.
  pose proof Hflat as Hflat_all.
  destruct Hflat as [_ [Hmem [Hnodup _]]].
  destruct (Hmem
              {|
                PolyLang.ip_nth := n1;
                PolyLang.ip_index := idx1;
                PolyLang.ip_transformation := tf1;
                PolyLang.ip_time_stamp := ts1;
                PolyLang.ip_instruction := instr1;
                PolyLang.ip_depth := depth1
              |}) as [Hmem1 _].
  destruct (Hmem
              {|
                PolyLang.ip_nth := n2;
                PolyLang.ip_index := idx2;
                PolyLang.ip_transformation := tf2;
                PolyLang.ip_time_stamp := ts2;
                PolyLang.ip_instruction := instr2;
                PolyLang.ip_depth := depth2
              |}) as [Hmem2 _].
  destruct (Hmem1 Hin1) as
      [after_pi1 [Hafter1 [_ [Hbel1 _]]]].
  destruct (Hmem2 Hin2) as
      [after_pi2 [Hafter2 [_ [Hbel2 _]]]].
  pose proof
    (Refine.domain_partition_cut_shape_implies_shape
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w
       (proj1 Hcomplete))
    as Hshape.
  pose proof
    (Refine.domain_partition_shape_stmt_witnesses_length
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w Hshape)
    as Hlen_stmt_ws.
  assert (Hrange1 : (n1 < length w.(iw_stmt_witnesses))%nat).
  {
    rewrite <- Hlen_stmt_ws.
    pose proof
      (PolyLang.flatten_instrs_ipl_n_lt_len
         env after_pis ipl_after Hflat_all
         {|
           PolyLang.ip_nth := n1;
           PolyLang.ip_index := idx1;
           PolyLang.ip_transformation := tf1;
           PolyLang.ip_time_stamp := ts1;
           PolyLang.ip_instruction := instr1;
           PolyLang.ip_depth := depth1
         |}
         Hin1) as Hlt.
    simpl in Hlt.
    exact Hlt.
  }
  assert (Hrange2 : (n2 < length w.(iw_stmt_witnesses))%nat).
  {
    rewrite <- Hlen_stmt_ws.
    pose proof
      (PolyLang.flatten_instrs_ipl_n_lt_len
         env after_pis ipl_after Hflat_all
         {|
           PolyLang.ip_nth := n2;
           PolyLang.ip_index := idx2;
           PolyLang.ip_transformation := tf2;
           PolyLang.ip_time_stamp := ts2;
           PolyLang.ip_instruction := instr2;
           PolyLang.ip_depth := depth2
         |}
         Hin2) as Hlt.
    simpl in Hlt.
    exact Hlt.
  }
  destruct (nth_error w.(iw_stmt_witnesses) n1) as [w1|] eqn:Hw1.
  2: {
    apply nth_error_None in Hw1.
    lia.
  }
  destruct (nth_error w.(iw_stmt_witnesses) n2) as [w2|] eqn:Hw2.
  2: {
    apply nth_error_None in Hw2.
    lia.
  }
  unfold Sem.before_of_after_point, Sem.before_parent_nth, Sem.set_ip_nth in Heq.
  simpl in Heq.
  rewrite Hw1, Hw2 in Heq.
  simpl in Heq.
  injection Heq as Hparent_eq Hidx_eq Htf_eq Hts_eq Hinstr_eq Hdepth_eq.
  pose proof
    (domain_partition_complete_cut_shape_nth_domain_relation
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
       n1 after_pi1 w1 eq_refl eq_refl Hcomplete Hafter1 Hw1)
    as Hmatch1.
  pose proof
    (domain_partition_complete_cut_shape_nth_domain_relation
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w before_pis after_pis before_varctxt before_vars after_varctxt after_vars
       n2 after_pi2 w2 eq_refl eq_refl Hcomplete Hafter2 Hw2)
    as Hmatch2.
  destruct Hmatch1 as [source1 [piece1 [Hsource1 [Hpiece1 _]]]].
  destruct Hmatch2 as [source2 [piece2 [Hsource2 [Hpiece2 _]]]].
  rewrite <- Hparent_eq in Hsource2.
  rewrite Hsource1 in Hsource2.
  inversion Hsource2; subst source2.
  clear Hsource2.
  assert (Hpart :
            Refine.parent_sign_partition_complete
              w.(iw_cuts) (isw_parent_stmt w1) after_pis w.(iw_stmt_witnesses)).
  {
    unfold Refine.domain_partition_complete_cut_shape in Hcomplete.
    destruct Hcomplete as [_ Hpart].
    unfold Refine.cut_partition_complete in Hpart.
    simpl in Hpart.
    eapply Hpart; eauto.
  }
  assert (Hsign1 :
            isw_piece_signs w1 =
            Refine.iss_signs_for_point idx1 w.(iw_cuts)).
  {
    eapply
      (complete_cut_shape_after_point_signs_match_nth
         before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n1 after_pi1 w1
         {|
           PolyLang.ip_nth := n1;
           PolyLang.ip_index := idx1;
           PolyLang.ip_transformation := tf1;
           PolyLang.ip_time_stamp := ts1;
           PolyLang.ip_instruction := instr1;
           PolyLang.ip_depth := depth1
         |}); eauto.
  }
  assert (Hsign2 :
            isw_piece_signs w2 =
            Refine.iss_signs_for_point idx2 w.(iw_cuts)).
  {
    eapply
      (complete_cut_shape_after_point_signs_match_nth
         before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w n2 after_pi2 w2
         {|
           PolyLang.ip_nth := n2;
           PolyLang.ip_index := idx2;
           PolyLang.ip_transformation := tf2;
           PolyLang.ip_time_stamp := ts2;
           PolyLang.ip_instruction := instr2;
           PolyLang.ip_depth := depth2
         |}); eauto.
  }
  rewrite <- Hidx_eq in Hsign2.
  assert (Hpair1_in :
            In (after_pi1, w1)
               (Refine.child_pairs_for_parent
                  (isw_parent_stmt w1) after_pis w.(iw_stmt_witnesses))).
  {
    eapply nth_error_after_stmt_implies_child_pair; eauto.
  }
  assert (Hpair2_in :
            In (after_pi2, w2)
               (Refine.child_pairs_for_parent
                  (isw_parent_stmt w1) after_pis w.(iw_stmt_witnesses))).
  {
    eapply nth_error_after_stmt_implies_child_pair; eauto.
  }
  assert (Hpair_eq : (after_pi1, w1) = (after_pi2, w2)).
  {
    eapply (child_pair_unique_by_sign
              w.(iw_cuts)
              (isw_parent_stmt w1)
              after_pis
              w.(iw_stmt_witnesses)
              (after_pi1, w1)
              (after_pi2, w2)); eauto.
    transitivity (Refine.iss_signs_for_point idx1 w.(iw_cuts)).
    - exact Hsign1.
    - symmetry.
      exact Hsign2.
  }
  assert (Hpair_nth1 :
            nth_error (Refine.iss_pairs after_pis w.(iw_stmt_witnesses)) n1 =
            Some (after_pi1, w1)).
  {
    eapply Sem.nth_error_combine_local; eauto.
  }
  assert (Hpair_nth2 :
            nth_error (Refine.iss_pairs after_pis w.(iw_stmt_witnesses)) n2 =
            Some (after_pi1, w1)).
  {
    rewrite Hpair_eq.
    eapply Sem.nth_error_combine_local; eauto.
  }
  assert (Hnth_eq : n1 = n2).
  {
    eapply (@NoDup_filter_nth_error_unique
              (PolyLang.PolyInstr * iss_stmt_witness)
              (fun pair =>
                 Nat.eqb (isw_parent_stmt (snd pair))
                         (isw_parent_stmt w1))
              (Refine.iss_pairs after_pis w.(iw_stmt_witnesses))
              n1 n2 (after_pi1, w1)); eauto.
    - unfold Refine.child_pairs_for_parent in *.
      eapply parent_sign_partition_complete_nodup_child_pairs; eauto.
    - simpl.
      apply Nat.eqb_eq.
      reflexivity.
  }
  subst n2.
  subst idx2 tf2 ts2 instr2 depth2.
  reflexivity.
Qed.

Lemma before_ipl_from_after_nodup_complete_cut_shape :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    NoDup (Sem.before_ipl_from_after w.(iw_stmt_witnesses) ipl_after).
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after Hcomplete Hflat.
  pose proof Hflat as Hflat_all.
  destruct Hflat as [_ [_ [Hnodup _]]].
  unfold Sem.before_ipl_from_after.
  eapply NoDup_map_on_local.
  - exact Hnodup.
  - intros ip1 ip2 Hin1 Hin2 Heq.
    eapply before_of_after_point_injective_complete_cut_shape; eauto.
Qed.

Lemma NoDup_np_eq_unique_implies_NoDupA :
  forall ipl,
    NoDup ipl ->
    (forall ip1 ip2,
      In ip1 ipl ->
      In ip2 ipl ->
      PolyLang.np_eq ip1 ip2 ->
      ip1 = ip2) ->
    NoDupA PolyLang.np_eq ipl.
Proof.
  intros ipl Hnodup Huniq.
  induction Hnodup as [|ip ipl Hnotin Hnodup IH].
  - constructor.
  - constructor.
    + intro HinA.
      apply InA_alt in HinA.
      destruct HinA as [ip' [Hnpeq Hin']].
      assert (ip = ip').
      {
        eapply Huniq; eauto.
        left; reflexivity.
        right; exact Hin'.
      }
      subst ip'.
      contradiction.
    + eapply IH.
      intros ip1 ip2 Hin1 Hin2 Hnpeq.
      eapply Huniq; eauto.
      right; exact Hin1.
      right; exact Hin2.
Qed.

Lemma lex_compare_eq_same_length_implies_eq_local :
  forall t1 t2,
    lex_compare t1 t2 = Eq ->
    length t1 = length t2 ->
    t1 = t2.
Proof.
  induction t1 as [|x t1 IH]; intros t2 Hcmp Hlen.
  - destruct t2 as [|y t2].
    + reflexivity.
    + simpl in Hlen. discriminate.
  - destruct t2 as [|y t2].
    + simpl in Hlen. discriminate.
    + simpl in Hcmp.
      destruct (Z.compare x y) eqn:Hxy; try discriminate.
      apply Z.compare_eq_iff in Hxy.
      subst y.
      f_equal.
      eapply IH.
      * exact Hcmp.
      * simpl in Hlen. lia.
Qed.

Lemma belongs_to_same_source_same_np_implies_eq :
  forall source ip1 ip2,
    PolyLang.belongs_to ip1 source ->
    PolyLang.belongs_to ip2 source ->
    length (PolyLang.ip_index ip1) = length (PolyLang.ip_index ip2) ->
    PolyLang.np_eq ip1 ip2 ->
    ip1 = ip2.
Proof.
  intros source
         [n1 idx1 tf1 ts1 instr1 depth1]
         [n2 idx2 tf2 ts2 instr2 depth2]
         Hbel1 Hbel2 Hlen_eq Hnp.
  unfold PolyLang.belongs_to in Hbel1, Hbel2.
  unfold PolyLang.np_eq in Hnp.
  simpl in *.
  destruct Hbel1 as [_ [Htf1 [Hts1 [Hinstr1 Hdepth1]]]].
  destruct Hbel2 as [_ [Htf2 [Hts2 [Hinstr2 Hdepth2]]]].
  destruct Hnp as [Hnth Hidx_cmp].
  eapply lex_compare_eq_same_length_implies_eq_local in Hidx_cmp.
  2: exact Hlen_eq.
  subst n2.
  subst idx2.
  rewrite <- Htf1 in Htf2.
  rewrite <- Hts1 in Hts2.
  rewrite <- Hinstr1 in Hinstr2.
  rewrite <- Hdepth1 in Hdepth2.
  subst tf2 ts2 instr2 depth2.
  reflexivity.
Qed.

Lemma before_ipl_from_after_member_np_eq_implies_eq :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip1 ip2,
    Refine.domain_partition_refinement
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      stmt_ws ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    In ip1 (Sem.before_ipl_from_after stmt_ws ipl_after) ->
    In ip2 (Sem.before_ipl_from_after stmt_ws ipl_after) ->
    PolyLang.np_eq ip1 ip2 ->
    ip1 = ip2.
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip1 ip2
         Href Hflat Hin1 Hin2 Hnp.
  destruct
    (Sem.before_ipl_from_after_forward
       before_pis before_varctxt before_vars
       after_pis after_varctxt after_vars
       stmt_ws env ipl_after ip1
       Href Hflat Hin1)
    as [source1 [Hsource1 [Hpref1 [Hbel1 Hlen1]]]].
  destruct
    (Sem.before_ipl_from_after_forward
       before_pis before_varctxt before_vars
       after_pis after_varctxt after_vars
       stmt_ws env ipl_after ip2
       Href Hflat Hin2)
    as [source2 [Hsource2 [Hpref2 [Hbel2 Hlen2]]]].
  unfold PolyLang.np_eq in Hnp.
  destruct Hnp as [Hnth Hidx].
  rewrite <- Hnth in Hsource2.
  rewrite Hsource1 in Hsource2.
  inversion Hsource2; subst source2.
  eapply belongs_to_same_source_same_np_implies_eq; eauto.
  rewrite Hlen1, Hlen2.
  reflexivity.
  unfold PolyLang.np_eq.
  split; assumption.
Qed.

Theorem flatten_instrs_after_implies_before_exists_perm_complete_cut_shape :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    exists ipl_before,
      PolyLang.flatten_instrs env before_pis ipl_before /\
      Permutation
        ipl_before
        (Sem.before_ipl_from_after w.(iw_stmt_witnesses) ipl_after).
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w env ipl_after Hcomplete Hflat_after.
  set (raw_before :=
         Sem.before_ipl_from_after w.(iw_stmt_witnesses) ipl_after).
  set (sorted_before :=
         SelectionSort instr_point_np_ltb
                       instr_point_np_eqb
                       raw_before).
  exists sorted_before.
  split.
  - assert (Hperm_before : Permutation raw_before sorted_before).
    {
      subst sorted_before.
      eapply selection_sort_perm.
    }
    assert (Hnodup_raw : NoDup raw_before).
    {
      subst raw_before.
      eapply before_ipl_from_after_nodup_complete_cut_shape; eauto.
    }
    assert (Hnodup_sorted : NoDup sorted_before).
    {
      eapply Permutation_NoDup; eauto.
    }
    pose proof
      (Refine.domain_partition_refinement_from_complete_cut_shape
         (before_pis, before_varctxt, before_vars)
         (after_pis, after_varctxt, after_vars)
         w Hcomplete)
      as Href.
    assert (Hmem_sorted :
              forall ip,
                In ip sorted_before <->
                exists source,
                  nth_error before_pis (PolyLang.ip_nth ip) = Some source /\
                  firstn (length env) (PolyLang.ip_index ip) = env /\
                  PolyLang.belongs_to ip source /\
                  length (PolyLang.ip_index ip) =
                    (length env + PolyLang.pi_depth source)%nat).
    {
      intros ip.
      split; intro Hin.
      - eapply Sem.before_ipl_from_after_forward; eauto.
        eapply Permutation_in.
        + eapply Permutation_sym.
          exact Hperm_before.
        + exact Hin.
      - destruct Hin as [source [Hsource [Hpref [Hbel Hlen]]]].
        eapply Permutation_in.
        + exact Hperm_before.
        + eapply Sem.before_ipl_from_after_backward; eauto.
    }
    assert (HnodupA_sorted : NoDupA PolyLang.np_eq sorted_before).
    {
      eapply NoDup_np_eq_unique_implies_NoDupA; eauto.
      intros ip1 ip2 Hin1 Hin2 Hnp.
      destruct (Hmem_sorted ip1) as [Hmem1 _].
      destruct (Hmem_sorted ip2) as [Hmem2 _].
      apply Hmem1 in Hin1.
      apply Hmem2 in Hin2.
      destruct Hin1 as [source1 [Hsource1 [Hpref1 [Hbel1 Hlen1]]]].
      destruct Hin2 as [source2 [Hsource2 [Hpref2 [Hbel2 Hlen2]]]].
      unfold PolyLang.np_eq in Hnp.
      destruct Hnp as [Hnth Hidx].
      rewrite <- Hnth in Hsource2.
      rewrite Hsource1 in Hsource2.
      inversion Hsource2; subst source2.
      eapply belongs_to_same_source_same_np_implies_eq; eauto.
      rewrite Hlen1, Hlen2.
      reflexivity.
      unfold PolyLang.np_eq.
      split; assumption.
    }
    assert (Hsortedb :
              Sorted_b
                (combine_leb instr_point_np_ltb
                             instr_point_np_eqb)
                sorted_before).
    {
      subst sorted_before.
      eapply selection_sort_sorted.
      - eapply instr_point_np_ltb_trans.
      - eapply instr_point_np_eqb_trans.
      - eapply instr_point_np_eqb_refl.
      - eapply instr_point_np_eqb_symm.
      - eapply instr_point_np_cmp_total.
      - eapply instr_point_np_eqb_ltb_implies_ltb.
      - eapply instr_point_np_ltb_eqb_implies_ltb.
    }
    split.
    + intros ip Hin.
      destruct (Hmem_sorted ip) as [Hmem_ip _].
      apply Hmem_ip in Hin.
      destruct Hin as [source [Hsource [Hpref [Hbel Hlen]]]].
      exact Hpref.
    + split.
      * exact Hmem_sorted.
      * split.
        -- exact Hnodup_sorted.
        -- eapply sortedb_instr_point_np_implies_sorted_np; eauto.
  - eapply Permutation_sym.
    subst sorted_before.
    eapply selection_sort_perm.
Qed.

Theorem iss_complete_cut_shape_to_before_poly_correct :
  forall env before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w st1 st2,
    Refine.domain_partition_complete_cut_shape
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      w ->
    PolyLang.poly_instance_list_semantics
      env
      (after_pis, after_varctxt, after_vars)
      st1 st2 ->
    exists st2',
      PolyLang.poly_instance_list_semantics
        env
        (before_pis, before_varctxt, before_vars)
        st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros env before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         w st1 st2 Hcomplete Hsem.
  inversion Hsem as
      [env' pprog pis varctxt vars st1' st2'
       ipl_after sorted_after
       Hpprog Hflat_after Hperm_after Hsorted_after Hlist_after];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  destruct
    (flatten_instrs_after_implies_before_exists_perm_complete_cut_shape
       before_pis before_varctxt before_vars
       pis varctxt vars
       w env ipl_after
       Hcomplete Hflat_after)
    as [ipl_before [Hflat_before Hperm_before]].
  set (sorted_before :=
         map (Sem.before_of_after_point w.(iw_stmt_witnesses)) sorted_after).
  assert (Hlist_before :
            PolyLang.ILSema.instr_point_list_semantics
              sorted_before st1 st2).
  {
    subst sorted_before.
    eapply instr_point_list_semantics_map_preserved.
    - intros ip s1 s2 Hin_sorted.
      symmetry.
      apply Sem.point_semantics_before_of_after_preserved.
    - exact Hlist_after.
  }
  assert (Hsorted_before :
            Sorted PolyLang.instr_point_sched_le sorted_before).
  {
    subst sorted_before.
    eapply sorted_sched_map_time_stamp_preserved.
    - intros ip Hin_sorted.
      eapply Sem.before_of_after_point_time_stamp_preserved.
    - exact Hsorted_after.
  }
  assert (Hperm_before_sorted :
            Permutation ipl_before sorted_before).
  {
    subst sorted_before.
    eapply Permutation_trans.
    - exact Hperm_before.
    - eapply Permutation_map.
      exact Hperm_after.
  }
  exists st2.
  split.
  - eapply PolyLang.PolyPointListSema
      with (ipl := ipl_before) (sorted_ipl := sorted_before).
    + reflexivity.
    + exact Hflat_before.
    + exact Hperm_before_sorted.
    + exact Hsorted_before.
    + exact Hlist_before.
  - eapply Instr.State.eq_refl.
Qed.

Theorem iss_complete_cut_shape_to_before_correct :
  forall before after w st1 st2,
    Refine.domain_partition_complete_cut_shape before after w ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros before after w st1 st2 Hcomplete Hsem.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold Refine.domain_partition_complete_cut_shape in Hcomplete.
  destruct Hcomplete as [Hcut_shape Hcut_complete].
  pose proof
    (Refine.domain_partition_cut_shape_implies_shape
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       w Hcut_shape)
    as Hshape.
  unfold Refine.domain_partition_shape_with_witness in Hshape.
  unfold Refine.domain_partition_shape in Hshape.
  simpl in Hshape.
  destruct Hshape as [Hctxt_eq0 [Hvars_eq0 [_ _]]].
  pose proof Hctxt_eq0 as Hctxt_eq.
  pose proof Hvars_eq0 as Hvars_eq.
  inversion Hsem as
      [pprog pis varctxt vars env st1' st2'
       Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  destruct
    (iss_complete_cut_shape_to_before_poly_correct
       env before_pis varctxt vars
       pis varctxt vars
       w st1 st2
       (conj Hcut_shape Hcut_complete)
       Hpoly)
    as [st2' [Hpoly_before Heq]].
  exists st2'.
  split.
  - eapply PolyLang.PIPSemaIntro.
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hpoly_before.
  - exact Heq.
Qed.

End ISSCutSemantics.
