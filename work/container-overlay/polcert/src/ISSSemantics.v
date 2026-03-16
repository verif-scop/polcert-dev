Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import ClassicalDescription.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import SetoidList.
Require Import SelectionSort.
Require Import Base.
Require Import PolyBase.
Require Import PolyLang.
Require Import ISSWitness.
Require Import ISSRefinement.
Require Import TilingRelation.
Require Import Extractor.
Require Import PolIRs.
Import ListNotations.

Module ISSSemantics (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module PolyLang := PolIRs.PolyLang.
Module Refine := ISSRefinement PolIRs.
Module TileRel := TilingRelation Instr.
Module Extractor := Extractor PolIRs.

Definition set_ip_nth
    (n: nat)
    (ip: PolyLang.InstrPoint) : PolyLang.InstrPoint :=
  {|
    PolyLang.ip_nth := n;
    PolyLang.ip_index := ip.(PolyLang.ip_index);
    PolyLang.ip_transformation := ip.(PolyLang.ip_transformation);
    PolyLang.ip_time_stamp := ip.(PolyLang.ip_time_stamp);
    PolyLang.ip_instruction := ip.(PolyLang.ip_instruction);
    PolyLang.ip_depth := ip.(PolyLang.ip_depth);
  |}.

Definition before_parent_nth
    (stmt_ws: list iss_stmt_witness)
    (n: nat) : nat :=
  match nth_error stmt_ws n with
  | Some w => isw_parent_stmt w
  | None => n
  end.

Definition before_of_after_point
    (stmt_ws: list iss_stmt_witness)
    (ip_after: PolyLang.InstrPoint) : PolyLang.InstrPoint :=
  set_ip_nth
    (before_parent_nth stmt_ws ip_after.(PolyLang.ip_nth))
    ip_after.

Definition before_ipl_from_after
    (stmt_ws: list iss_stmt_witness)
    (ipl_after: list PolyLang.InstrPoint) : list PolyLang.InstrPoint :=
  map (before_of_after_point stmt_ws) ipl_after.

Fixpoint find_after_stmt_index
    (parent: nat)
    (point: DomIndex)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    : option nat :=
  match after_pis, stmt_ws with
  | after_pi :: after_pis', w :: stmt_ws' =>
      if Nat.eqb (isw_parent_stmt w) parent
      then
        if excluded_middle_informative
             (Refine.point_in_pinstr_domain point after_pi)
        then Some 0%nat
        else option_map S (find_after_stmt_index parent point after_pis' stmt_ws')
      else option_map S (find_after_stmt_index parent point after_pis' stmt_ws')
  | _, _ => None
  end.

Definition after_of_before_point
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    (ip_before: PolyLang.InstrPoint) : PolyLang.InstrPoint :=
  match find_after_stmt_index
          ip_before.(PolyLang.ip_nth)
          ip_before.(PolyLang.ip_index)
          after_pis
          stmt_ws with
  | Some n => set_ip_nth n ip_before
  | None => ip_before
  end.

Definition after_ipl_from_before
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    (ipl_before: list PolyLang.InstrPoint) : list PolyLang.InstrPoint :=
  map (after_of_before_point after_pis stmt_ws) ipl_before.

Lemma belongs_to_set_ip_nth_iff :
  forall n ip pi,
    PolyLang.belongs_to (set_ip_nth n ip) pi <->
    PolyLang.belongs_to ip pi.
Proof.
  intros n ip pi.
  unfold PolyLang.belongs_to, set_ip_nth.
  simpl.
  tauto.
Qed.

Lemma instr_point_sema_set_ip_nth :
  forall n ip st1 st2,
    PolyLang.instr_point_sema (set_ip_nth n ip) st1 st2 <->
    PolyLang.instr_point_sema ip st1 st2.
Proof.
  intros n ip st1 st2.
  split; intro Hsema.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
Qed.

Lemma point_semantics_before_of_after_preserved :
  forall stmt_ws ip st1 st2,
    PolyLang.instr_point_sema (before_of_after_point stmt_ws ip) st1 st2 <->
    PolyLang.instr_point_sema ip st1 st2.
Proof.
  intros stmt_ws ip st1 st2.
  unfold before_of_after_point.
  apply instr_point_sema_set_ip_nth.
Qed.

Lemma point_semantics_after_of_before_preserved :
  forall after_pis stmt_ws ip st1 st2,
    PolyLang.instr_point_sema (after_of_before_point after_pis stmt_ws ip) st1 st2 <->
    PolyLang.instr_point_sema ip st1 st2.
Proof.
  intros after_pis stmt_ws ip st1 st2.
  unfold after_of_before_point.
  destruct (find_after_stmt_index
              (PolyLang.ip_nth ip)
              (PolyLang.ip_index ip)
              after_pis stmt_ws) as [n|].
  - apply instr_point_sema_set_ip_nth.
  - tauto.
Qed.

Lemma before_of_after_point_time_stamp_preserved :
  forall stmt_ws ip,
    PolyLang.ip_time_stamp (before_of_after_point stmt_ws ip) =
    PolyLang.ip_time_stamp ip.
Proof.
  intros stmt_ws ip.
  unfold before_of_after_point, set_ip_nth.
  reflexivity.
Qed.

Lemma after_of_before_point_time_stamp_preserved :
  forall after_pis stmt_ws ip,
    PolyLang.ip_time_stamp (after_of_before_point after_pis stmt_ws ip) =
    PolyLang.ip_time_stamp ip.
Proof.
  intros after_pis stmt_ws ip.
  unfold after_of_before_point.
  destruct (find_after_stmt_index
              (PolyLang.ip_nth ip)
              (PolyLang.ip_index ip)
              after_pis stmt_ws) as [n|];
    reflexivity.
Qed.

Lemma payload_eq_except_domain_implies_depth :
  forall source piece,
    Refine.payload_eq_except_domain source piece ->
    PolyLang.pi_depth source = PolyLang.pi_depth piece.
Proof.
  intros source piece Hpayload.
  unfold Refine.payload_eq_except_domain in Hpayload.
  tauto.
Qed.

Lemma payload_eq_except_domain_transfer_belongs_to :
  forall source piece ip,
    Refine.payload_eq_except_domain source piece ->
    Refine.point_in_pinstr_domain (PolyLang.ip_index ip) source ->
    PolyLang.belongs_to ip piece ->
    PolyLang.belongs_to ip source.
Proof.
  intros source piece ip Hpayload Hdom Hbel.
  unfold Refine.payload_eq_except_domain in Hpayload.
  unfold PolyLang.belongs_to in *.
  destruct Hpayload as
      [Hdepth [Hinstr [Hsched [Hwitness [Htf [Hatf [Hwacc Hracc]]]]]]].
  destruct Hbel as [Hpiece_dom [Htf_ip [Hts_ip [Hinstr_ip Hdepth_ip]]]].
  repeat split.
  - exact Hdom.
  - unfold PolyLang.current_transformation_of,
           PolyLang.current_env_dim_of,
           PolyLang.current_transformation_at,
           PolyLang.current_transformation_for_witness in *.
    rewrite Hwitness.
    rewrite Htf.
    exact Htf_ip.
  - rewrite Hsched. exact Hts_ip.
  - rewrite Hinstr. exact Hinstr_ip.
  - rewrite Hdepth. exact Hdepth_ip.
Qed.

Lemma stmt_partition_refinement_payload_of_child :
  forall source pieces piece,
    Refine.stmt_partition_refinement source pieces ->
    In piece pieces ->
    Refine.payload_eq_except_domain source piece.
Proof.
  intros source pieces piece Href Hin.
  unfold Refine.stmt_partition_refinement in Href.
  destruct Href as [Hpayloads _].
  eapply Forall_forall; eauto.
Qed.

Lemma stmt_partition_refinement_subset_of_child :
  forall source pieces point piece,
    Refine.stmt_partition_refinement source pieces ->
    In piece pieces ->
    Refine.point_in_pinstr_domain point piece ->
    Refine.point_in_pinstr_domain point source.
Proof.
  intros source pieces point piece Href Hin Hdom.
  unfold Refine.stmt_partition_refinement in Href.
  destruct Href as [_ [Hall _]].
  eapply Hall; eauto.
Qed.

Lemma domain_partition_refinement_parent_stmt :
  forall before after stmt_ws parent source,
    Refine.domain_partition_refinement before after stmt_ws ->
    let '(before_pis, _, _) := before in
    let '(after_pis, _, _) := after in
    nth_error before_pis parent = Some source ->
    Refine.stmt_partition_refinement
      source
      (Refine.children_for_parent parent after_pis stmt_ws).
Proof.
  intros before after stmt_ws parent source Href.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  simpl.
  unfold Refine.domain_partition_refinement in Href.
  simpl in Href.
  intros Hsource.
  destruct Href as (_ & _ & _ & _ & Hparts).
  eapply Hparts; eauto.
Qed.

Lemma parent_witnesses_in_range_nth :
  forall before_pis stmt_ws n w,
    Refine.parent_witnesses_in_range before_pis stmt_ws ->
    nth_error stmt_ws n = Some w ->
    (isw_parent_stmt w < length before_pis)%nat.
Proof.
  intros before_pis stmt_ws n w Hrange Hnth.
  unfold Refine.parent_witnesses_in_range in Hrange.
  apply nth_error_In in Hnth.
  eapply Forall_forall in Hrange; eauto.
Qed.

Lemma in_combine_nth_error_local :
  forall A B (xs: list A) (ys: list B) x y,
    In (x, y) (combine xs ys) ->
    exists n,
      nth_error xs n = Some x /\
      nth_error ys n = Some y.
Proof.
  intros A B xs.
  induction xs as [|xh xt IH]; intros ys x y Hin.
  - destruct ys; simpl in Hin; contradiction.
  - destruct ys as [|yh yt]; simpl in Hin.
    + contradiction.
    + destruct Hin as [Heq | Hin].
      * inversion Heq; subst.
        exists 0%nat.
        split; reflexivity.
      * destruct (IH yt x y Hin) as [n [Hxn Hyn]].
        exists (S n).
        split; assumption.
Qed.

Lemma nth_error_combine_local :
  forall A B (xs: list A) (ys: list B) n x y,
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    nth_error (combine xs ys) n = Some (x, y).
Proof.
  intros A B xs.
  induction xs as [|xh xt IH]; intros ys n x y Hx Hy.
  - destruct n; inversion Hx.
  - destruct ys as [|yh yt].
    + destruct n; inversion Hy.
    + destruct n.
      * simpl in *.
        inversion Hx; inversion Hy; subst.
        reflexivity.
      * simpl in *.
        eapply IH; eauto.
Qed.

Lemma nth_error_after_stmt_implies_child :
  forall after_pis stmt_ws n after_pi w,
    nth_error after_pis n = Some after_pi ->
    nth_error stmt_ws n = Some w ->
    In after_pi
      (Refine.children_for_parent
         (isw_parent_stmt w) after_pis stmt_ws).
Proof.
  intros after_pis stmt_ws n after_pi w Hafter Hw.
  unfold Refine.children_for_parent, Refine.child_pairs_for_parent, Refine.iss_pairs.
  apply in_map_iff.
  exists (after_pi, w).
  split.
  - reflexivity.
  - apply filter_In.
    split.
    + eapply nth_error_In.
      eapply nth_error_combine_local; eauto.
    + simpl.
      apply Nat.eqb_eq.
      reflexivity.
Qed.

Lemma find_after_stmt_index_sound :
  forall parent point after_pis stmt_ws n,
    find_after_stmt_index parent point after_pis stmt_ws = Some n ->
    exists after_pi w,
      nth_error after_pis n = Some after_pi /\
      nth_error stmt_ws n = Some w /\
      isw_parent_stmt w = parent /\
      Refine.point_in_pinstr_domain point after_pi.
Proof.
  intros parent point after_pis.
  induction after_pis as [|after_pi after_pis IH];
    intros stmt_ws n Hfind.
  - destruct stmt_ws; simpl in Hfind; discriminate.
  - destruct stmt_ws as [|w stmt_ws']; simpl in Hfind; try discriminate.
    destruct (Nat.eqb (isw_parent_stmt w) parent) eqn:Hparent.
    + destruct (excluded_middle_informative
                  (Refine.point_in_pinstr_domain point after_pi))
        as [Hdom|Hdom].
      * inversion Hfind; subst.
        exists after_pi, w.
        split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ split.
              ** apply Nat.eqb_eq in Hparent.
                 exact Hparent.
              ** exact Hdom.
      * destruct (find_after_stmt_index parent point after_pis stmt_ws')
          as [n'|] eqn:Htail; try discriminate.
        inversion Hfind; subst.
        destruct (IH stmt_ws' n' Htail)
          as [after_pi' [w' [Hafter [Hw' [Hparent' Hdom']]]]].
        exists after_pi', w'.
        repeat split; auto.
    + destruct (find_after_stmt_index parent point after_pis stmt_ws')
        as [n'|] eqn:Htail; try discriminate.
      inversion Hfind; subst.
      destruct (IH stmt_ws' n' Htail)
        as [after_pi' [w' [Hafter [Hw' [Hparent' Hdom']]]]].
      exists after_pi', w'.
      repeat split; auto.
Qed.

Lemma child_in_children_for_parent_inv :
  forall parent after_pis stmt_ws piece,
    In piece (Refine.children_for_parent parent after_pis stmt_ws) ->
    exists n w,
      nth_error after_pis n = Some piece /\
      nth_error stmt_ws n = Some w /\
      isw_parent_stmt w = parent.
Proof.
  intros parent after_pis stmt_ws piece Hin.
  unfold Refine.children_for_parent, Refine.child_pairs_for_parent,
         Refine.iss_pairs in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[after_pi w] [Hpiece Hin_pair]].
  simpl in Hpiece.
  subst after_pi.
  apply filter_In in Hin_pair.
  destruct Hin_pair as [Hin_pair Hparent].
  apply Nat.eqb_eq in Hparent.
  destruct (in_combine_nth_error_local _ _ _ _ _ _ Hin_pair)
    as [n [Hafter Hw]].
  exists n, w.
  repeat split; auto.
Qed.

Lemma NoDupA_np_implies_NoDup :
  forall ipl,
    NoDupA PolyLang.np_eq ipl ->
    NoDup ipl.
Proof.
  induction ipl as [|ip ipl IH]; intro Hnd.
  - constructor.
  - inversion Hnd; subst.
    constructor.
    + intro Hin.
      apply H1.
      eapply InA_alt.
      exists ip.
      split.
      * pose proof PolyLang.np_eq_equivalence as Heqv.
        destruct Heqv as [Hrefl _].
        apply Hrefl.
      * exact Hin.
    + eapply IH; eauto.
Qed.

Lemma before_ipl_from_after_forward :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip_before,
    Refine.domain_partition_refinement
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      stmt_ws ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    In ip_before (before_ipl_from_after stmt_ws ipl_after) ->
    exists source,
      nth_error before_pis (PolyLang.ip_nth ip_before) = Some source /\
      firstn (length env) (PolyLang.ip_index ip_before) = env /\
      PolyLang.belongs_to ip_before source /\
      length (PolyLang.ip_index ip_before) =
        (length env + PolyLang.pi_depth source)%nat.
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip_before
         Href Hflat Hin.
  pose proof Hflat as Hflat_all.
  unfold before_ipl_from_after in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [ip_after [Hip_before Hin_after]].
  subst ip_before.
  destruct Hflat as [Henv [Hmem _]].
  specialize (Henv ip_after Hin_after).
  specialize (Hmem ip_after).
  destruct ((proj1 Hmem) Hin_after)
    as [after_pi [Hafter_nth [Hpref [Hbel_after Hlen_after]]]].
  assert (Hafter_w_range :
            (PolyLang.ip_nth ip_after < length stmt_ws)%nat).
  {
    destruct Href as (_ & _ & Hlen_after_pis & _ & _).
    rewrite <- Hlen_after_pis.
    eapply PolyLang.flatten_instrs_ipl_n_lt_len.
    - exact Hflat_all.
    - exact Hin_after.
  }
  destruct (nth_error stmt_ws (PolyLang.ip_nth ip_after)) as [w|] eqn:Hw.
  2: {
    apply nth_error_None in Hw.
    lia.
  }
  assert (Hparent_range :
            (isw_parent_stmt w < length before_pis)%nat).
  {
    destruct Href as (_ & _ & _ & Hparents & _).
    eapply parent_witnesses_in_range_nth; eauto.
  }
  destruct (nth_error before_pis (isw_parent_stmt w)) as [source|] eqn:Hsource.
  2: {
    apply nth_error_None in Hsource.
    lia.
  }
  assert (Hpiece_in :
            In after_pi
              (Refine.children_for_parent
                 (isw_parent_stmt w) after_pis stmt_ws)).
  {
    eapply nth_error_after_stmt_implies_child; eauto.
  }
  pose proof
    (domain_partition_refinement_parent_stmt
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       stmt_ws
       (isw_parent_stmt w)
       source
       Href Hsource)
    as Hstmt_part.
  assert (Hpayload_piece :
            Refine.payload_eq_except_domain source after_pi).
  {
    eapply stmt_partition_refinement_payload_of_child; eauto.
  }
  assert (Hsource_dom :
            Refine.point_in_pinstr_domain
              (PolyLang.ip_index ip_after) source).
  {
    eapply stmt_partition_refinement_subset_of_child; eauto.
    exact (proj1 Hbel_after).
  }
  exists source.
  split.
  - unfold before_of_after_point, before_parent_nth, set_ip_nth.
    simpl.
    rewrite Hw.
    exact Hsource.
  - split.
    + exact Hpref.
    + split.
      * apply (proj1 (belongs_to_set_ip_nth_iff (isw_parent_stmt w) ip_after source)).
        eapply payload_eq_except_domain_transfer_belongs_to; eauto.
      * unfold before_of_after_point, before_parent_nth, set_ip_nth.
        simpl.
        pose proof (payload_eq_except_domain_implies_depth source after_pi Hpayload_piece)
          as Hdepth_eq.
        rewrite Hdepth_eq.
        exact Hlen_after.
Qed.

Lemma before_ipl_from_after_backward :
  forall before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip_before source,
    Refine.domain_partition_refinement
      (before_pis, before_varctxt, before_vars)
      (after_pis, after_varctxt, after_vars)
      stmt_ws ->
    PolyLang.flatten_instrs env after_pis ipl_after ->
    nth_error before_pis (PolyLang.ip_nth ip_before) = Some source ->
    firstn (length env) (PolyLang.ip_index ip_before) = env ->
    PolyLang.belongs_to ip_before source ->
    length (PolyLang.ip_index ip_before) =
      (length env + PolyLang.pi_depth source)%nat ->
    In ip_before (before_ipl_from_after stmt_ws ipl_after).
Proof.
  intros before_pis before_varctxt before_vars
         after_pis after_varctxt after_vars
         stmt_ws env ipl_after ip_before source
         Href Hflat Hsource Hpref Hbel_before Hlen_before.
  pose proof
    (domain_partition_refinement_parent_stmt
       (before_pis, before_varctxt, before_vars)
       (after_pis, after_varctxt, after_vars)
       stmt_ws
       (PolyLang.ip_nth ip_before)
       source
       Href Hsource)
    as Hstmt_part.
  unfold Refine.stmt_partition_refinement in Hstmt_part.
  destruct Hstmt_part as [Hpayloads [_ [Hcover _]]].
  destruct (Hcover (PolyLang.ip_index ip_before) (proj1 Hbel_before))
    as [piece [Hpiece_in Hpiece_dom]].
  assert (Hpayload_piece :
            Refine.payload_eq_except_domain source piece).
  {
    eapply Forall_forall; eauto.
  }
  destruct (child_in_children_for_parent_inv
              (PolyLang.ip_nth ip_before) after_pis stmt_ws piece Hpiece_in)
    as [n [w [Hafter_nth [Hw Hparent]]]].
  set (ip_after := set_ip_nth n ip_before).
  assert (Hbel_after : PolyLang.belongs_to ip_after piece).
  {
    apply (proj1 (belongs_to_set_ip_nth_iff n ip_before piece)).
    unfold PolyLang.belongs_to in *.
    unfold Refine.payload_eq_except_domain in Hpayload_piece.
    destruct Hpayload_piece as
        [Hdepth_eq [Hinstr_eq [Hsched_eq [Hwitness_eq
          [Htf_eq [Hatf_eq [Hwacc_eq Hracc_eq]]]]]]].
    destruct Hbel_before as [Hdom_before [Htf_before [Hts_before [Hinstr_before Hdepth_before]]]].
    repeat split.
    - exact Hpiece_dom.
    - unfold PolyLang.current_transformation_of,
             PolyLang.current_env_dim_of,
             PolyLang.current_transformation_at,
             PolyLang.current_transformation_for_witness in *.
      rewrite <- Hwitness_eq.
      rewrite <- Htf_eq.
      exact Htf_before.
    - rewrite <- Hsched_eq. exact Hts_before.
    - rewrite <- Hinstr_eq. exact Hinstr_before.
    - rewrite <- Hdepth_eq. exact Hdepth_before.
  }
  assert (Hlen_after :
            length (PolyLang.ip_index ip_after) =
            (length env + PolyLang.pi_depth piece)%nat).
  {
    unfold ip_after, set_ip_nth.
    simpl.
    unfold Refine.payload_eq_except_domain in Hpayload_piece.
    destruct Hpayload_piece as [Hdepth_eq _].
    rewrite <- Hdepth_eq.
    exact Hlen_before.
  }
  assert (Hin_after : In ip_after ipl_after).
  {
    eapply Extractor.flatten_instrs_in_intro; eauto.
  }
  unfold before_ipl_from_after.
  apply in_map_iff.
  exists ip_after.
  split.
  - unfold ip_after, before_of_after_point, before_parent_nth, set_ip_nth.
    simpl.
    rewrite Hw.
    rewrite Hparent.
    destruct ip_before.
    reflexivity.
  - exact Hin_after.
Qed.

End ISSSemantics.
