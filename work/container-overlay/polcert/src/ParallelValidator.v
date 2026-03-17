Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Base.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import AffineValidator.
Require Import Linalg.
Require Import ListExt.
Require Import Misc.
Require Import PolyBase.
Require Import PointWitness.
Require Import Result.
Require Import PolIRs.

Module ParallelValidator (PolIRs : POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module ILSema := PolyLang.ILSema.
Module Instr := PolIRs.Instr.
Module AffineCore := AffineValidator PolIRs.

Record parallel_plan := {
  target_dim : nat
}.

Record parallel_cert := {
  certified_dim : nat
}.

Definition pprog_pis (pp : PolyLang.t) : list PolyLang.PolyInstr :=
  let '(pis, _, _) := pp in pis.

Definition pprog_varctxt (pp : PolyLang.t) : list Instr.ident :=
  let '(_, varctxt, _) := pp in varctxt.

Definition current_coord_schedule_row
  (env_dim depth i : nat) : list Z * Z :=
  (resize (env_dim + depth) (V0 (env_dim + i) ++ [1%Z]), 0%Z).

Definition current_coord_old_schedule
  (env_dim depth d : nat) : list (list Z * Z) :=
  [current_coord_schedule_row env_dim depth d].

Definition current_coord_prefix_schedule
  (env_dim depth d : nat) : list (list Z * Z) :=
  map (current_coord_schedule_row env_dim depth) (seq 0 d).

Definition parallel_old_pi
  (env_dim d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      current_coord_old_schedule env_dim pi.(PolyLang.pi_depth) d;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_new_pi
  (env_dim d : nat) (pi : PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule :=
      current_coord_prefix_schedule env_dim pi.(PolyLang.pi_depth) d;
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess)
  |}.

Definition parallel_old_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  ((List.map (parallel_old_pi (Datatypes.length varctxt) d) pis, varctxt), vars).

Definition parallel_new_pprog
  (pp : PolyLang.t) (d : nat) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  ((List.map (parallel_new_pi (Datatypes.length varctxt) d) pis, varctxt), vars).

Definition check_current_view_pinstrb (pi : PolyLang.PolyInstr) : bool :=
  match pi.(PolyLang.pi_point_witness) with
  | PSWIdentity d' => Nat.eqb d' pi.(PolyLang.pi_depth)
  | _ => false
  end.

Definition check_current_view_pprogb (pp : PolyLang.t) : bool :=
  forallb check_current_view_pinstrb (pprog_pis pp).

Definition all_pinstrs_cover_dimb (d : nat) (pp : PolyLang.t) : bool :=
  forallb (fun pi => Nat.ltb d pi.(PolyLang.pi_depth)) (pprog_pis pp).

Definition env_dim_of (ip : PolyLang.InstrPoint) : nat :=
  Nat.sub (Datatypes.length ip.(PolyLang.ip_index)) ip.(PolyLang.ip_depth).

Definition env_prefix_of (ip : PolyLang.InstrPoint) : list Z :=
  firstn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition current_coords_of (ip : PolyLang.InstrPoint) : list Z :=
  skipn (env_dim_of ip) ip.(PolyLang.ip_index).

Definition same_env_of (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  env_prefix_of ip1 = env_prefix_of ip2.

Definition same_prefix_before
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  firstn d (current_coords_of ip1) = firstn d (current_coords_of ip2).

Definition different_dim_at
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  nth_error (current_coords_of ip1) d <>
  nth_error (current_coords_of ip2) d.

Definition same_parallel_slice
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint) : Prop :=
  same_env_of ip1 ip2 /\
  same_prefix_before d ip1 ip2 /\
  different_dim_at d ip1 ip2.

Lemma eq_except_sched_preserves_same_parallel_slice :
  forall d ip1 ip1' ip2 ip2',
    PolyLang.eq_except_sched ip1 ip1' ->
    PolyLang.eq_except_sched ip2 ip2' ->
    same_parallel_slice d ip1 ip2 ->
    same_parallel_slice d ip1' ip2'.
Proof.
  intros d ip1 ip1' ip2 ip2' Heq1 Heq2 Hslice.
  unfold PolyLang.eq_except_sched in Heq1, Heq2.
  unfold same_parallel_slice in *.
  destruct Heq1 as (_ & Hidx1 & _ & _ & Hdepth1).
  destruct Heq2 as (_ & Hidx2 & _ & _ & Hdepth2).
  destruct Hslice as (Henv & Hprefix & Hdiff).
  repeat split.
  - unfold same_env_of, env_prefix_of, env_dim_of in *; simpl in *.
    rewrite <- Hidx1, <- Hidx2, <- Hdepth1, <- Hdepth2.
    exact Henv.
  - unfold same_prefix_before, current_coords_of, env_dim_of in *; simpl in *.
    rewrite <- Hidx1, <- Hidx2, <- Hdepth1, <- Hdepth2.
    exact Hprefix.
  - unfold different_dim_at, current_coords_of, env_dim_of in *; simpl in *.
    rewrite <- Hidx1, <- Hidx2, <- Hdepth1, <- Hdepth2.
    exact Hdiff.
Qed.

Lemma instr_point_sema_eq_except_sched_iff :
  forall ip1 ip2 st1 st2,
    PolyLang.eq_except_sched ip1 ip2 ->
    ILSema.instr_point_sema ip1 st1 st2 <->
    ILSema.instr_point_sema ip2 st1 st2.
Proof.
  intros ip1 ip2 st1 st2 Heq.
  unfold PolyLang.eq_except_sched in Heq.
  destruct Heq as (_ & Hidx & Htf & Hins & _).
  split; intro Hsema; inversion Hsema as [wcs rcs Hsem]; subst.
  - econstructor.
    rewrite <- Hidx, <- Htf, <- Hins.
    exact Hsem.
  - econstructor.
    rewrite Hidx, Htf, Hins.
    exact Hsem.
Qed.

Lemma eq_except_sched_symm :
  forall ip1 ip2,
    PolyLang.eq_except_sched ip1 ip2 ->
    PolyLang.eq_except_sched ip2 ip1.
Proof.
  intros ip1 ip2 Heq.
  unfold PolyLang.eq_except_sched in *.
  destruct Heq as (Hnth & Hidx & Htf & Hins & Hdepth).
  repeat split; symmetry; assumption.
Qed.

Lemma permutable_eq_except_sched :
  forall ip1 ip1' ip2 ip2',
    PolyLang.eq_except_sched ip1 ip1' ->
    PolyLang.eq_except_sched ip2 ip2' ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.Permutable ip1' ip2'.
Proof.
  intros ip1 ip1' ip2 ip2' Heq1 Heq2 Hperm.
  unfold ILSema.Permutable in *.
  intros st1 Halias.
  specialize (Hperm st1 Halias).
  destruct Hperm as [Hfwd Hbwd].
  split.
  - intros st2' st3 Hs1 Hs2.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2' Heq1) Hs1) as Hs1'.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip2 ip2' st2' st3 Heq2) Hs2) as Hs2'.
    destruct (Hfwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2'' Heq2)); exact Ht1.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip1 ip1' st2'' st3' Heq1)); exact Ht2.
  - intros st2' st3 Hs1 Hs2.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip2 ip2' st1 st2' Heq2) Hs1) as Hs1'.
    pose proof (proj2 (instr_point_sema_eq_except_sched_iff ip1 ip1' st2' st3 Heq1) Hs2) as Hs2'.
    destruct (Hbwd _ _ Hs1' Hs2') as (st2'' & st3' & Ht1 & Ht2 & Heq).
    exists st2'', st3'. repeat split; auto.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip1 ip1' st1 st2'' Heq1)); exact Ht1.
    + apply (proj1 (instr_point_sema_eq_except_sched_iff ip2 ip2' st2'' st3' Heq2)); exact Ht2.
Qed.

Definition parallel_safe_dim (pp : PolyLang.t) (d : nat) : Prop :=
  forall envv ipl tau1 tau2,
    Datatypes.length envv = Datatypes.length (pprog_varctxt pp) ->
    PolyLang.flatten_instrs envv (pprog_pis pp) ipl ->
    In tau1 ipl ->
    In tau2 ipl ->
    same_parallel_slice d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.

Definition parallel_cert_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim pp cert.(certified_dim).

Lemma current_coord_schedule_row_cols :
  forall env_dim depth i,
    Datatypes.length (fst (current_coord_schedule_row env_dim depth i)) =
    (env_dim + depth)%nat.
Proof.
  intros env_dim depth i.
  unfold current_coord_schedule_row.
  simpl.
  rewrite resize_length.
  reflexivity.
Qed.

Lemma exact_listzzs_cols_current_coord_old_schedule :
  forall env_dim depth d,
    exact_listzzs_cols (env_dim + depth)%nat
      (current_coord_old_schedule env_dim depth d).
Proof.
  intros env_dim depth d listz z listzz Hin Heq.
  simpl in Hin.
  destruct Hin as [Hin | []].
  subst listzz.
  inversion Heq; subst.
  apply current_coord_schedule_row_cols.
Qed.

Lemma exact_listzzs_cols_current_coord_prefix_schedule :
  forall env_dim depth d,
    exact_listzzs_cols (env_dim + depth)%nat
      (current_coord_prefix_schedule env_dim depth d).
Proof.
  intros env_dim depth d listz z listzz Hin Heq.
  unfold current_coord_prefix_schedule in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hi _]].
  subst listzz.
  inversion Heq; subst.
  apply current_coord_schedule_row_cols.
Qed.

Lemma eqdom_parallel_old_pi :
  forall env_dim d pi,
    PolyLang.eqdom_pinstr pi (parallel_old_pi env_dim d pi).
Proof.
  intros env_dim d pi.
  unfold PolyLang.eqdom_pinstr, parallel_old_pi.
  repeat split; reflexivity.
Qed.

Lemma eqdom_parallel_new_pi :
  forall env_dim d pi,
    PolyLang.eqdom_pinstr pi (parallel_new_pi env_dim d pi).
Proof.
  intros env_dim d pi.
  unfold PolyLang.eqdom_pinstr, parallel_new_pi.
  repeat split; reflexivity.
Qed.

Lemma eqdom_parallel_old_new_pi :
  forall env_dim d pi,
    PolyLang.eqdom_pinstr
      (parallel_old_pi env_dim d pi)
      (parallel_new_pi env_dim d pi).
Proof.
  intros env_dim d pi.
  unfold PolyLang.eqdom_pinstr, parallel_old_pi, parallel_new_pi.
  repeat split; reflexivity.
Qed.

Lemma rel_list_eqdom_parallel_old :
  forall env_dim d pis,
    rel_list PolyLang.eqdom_pinstr pis (List.map (parallel_old_pi env_dim d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_old_pi.
    + exact IH.
Qed.

Lemma rel_list_eqdom_parallel_new :
  forall env_dim d pis,
    rel_list PolyLang.eqdom_pinstr pis (List.map (parallel_new_pi env_dim d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_new_pi.
    + exact IH.
Qed.

Lemma rel_list_eqdom_parallel_old_new :
  forall env_dim d pis,
    rel_list PolyLang.eqdom_pinstr
      (List.map (parallel_old_pi env_dim d) pis)
      (List.map (parallel_new_pi env_dim d) pis).
Proof.
  induction pis as [|pi pis IH]; simpl.
  - constructor.
  - constructor.
    + apply eqdom_parallel_old_new_pi.
    + exact IH.
Qed.

Lemma check_current_view_pinstrb_sound :
  forall pi,
    check_current_view_pinstrb pi = true ->
    pi.(PolyLang.pi_point_witness) = PSWIdentity pi.(PolyLang.pi_depth).
Proof.
  intros pi Hcheck.
  unfold check_current_view_pinstrb in Hcheck.
  destruct (PolyLang.pi_point_witness pi); simpl in Hcheck; try discriminate.
  apply Nat.eqb_eq in Hcheck.
  subst.
  reflexivity.
Qed.

Lemma all_pinstrs_cover_dimb_sound :
  forall pp d pi,
    all_pinstrs_cover_dimb d pp = true ->
    In pi (pprog_pis pp) ->
    (d < pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pp d pi Hcheck Hin.
  unfold all_pinstrs_cover_dimb, pprog_pis in Hcheck.
  eapply forallb_forall in Hcheck; eauto.
  apply Nat.ltb_lt in Hcheck.
  exact Hcheck.
Qed.

Lemma wf_pinstr_affine_parallel_old_pi :
  forall env vars env_dim d pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    env_dim = Datatypes.length env ->
    PolyLang.wf_pinstr_affine env vars (parallel_old_pi env_dim d pi).
Proof.
  intros env vars env_dim d pi Hwf Henvdim.
  unfold PolyLang.wf_pinstr_affine in *.
  destruct Hwf as [Hwf [Hid Hacc]].
  unfold PolyLang.wf_pinstr in *.
  destruct Hwf as
    (Hcur & Hcols_le & Hpoly_nrl & Hsched_nrl &
     Hpoly & Htf & Hacc_tf & Hsched & Hw & Hr).
  subst env_dim.
  split.
  - unfold parallel_old_pi.
    simpl.
    repeat split.
    + exact Hcur.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + exact Hpoly.
    + exact Htf.
    + exact Hacc_tf.
    + apply exact_listzzs_cols_current_coord_old_schedule.
    + exact Hw.
    + exact Hr.
  - split; [exact Hid | exact Hacc].
Qed.

Lemma wf_pinstr_affine_parallel_new_pi :
  forall env vars env_dim d pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    env_dim = Datatypes.length env ->
    PolyLang.wf_pinstr_affine env vars (parallel_new_pi env_dim d pi).
Proof.
  intros env vars env_dim d pi Hwf Henvdim.
  unfold PolyLang.wf_pinstr_affine in *.
  destruct Hwf as [Hwf [Hid Hacc]].
  unfold PolyLang.wf_pinstr in *.
  destruct Hwf as
    (Hcur & Hcols_le & Hpoly_nrl & Hsched_nrl &
     Hpoly & Htf & Hacc_tf & Hsched & Hw & Hr).
  subst env_dim.
  split.
  - unfold parallel_new_pi.
    simpl.
    repeat split.
    + exact Hcur.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + unfold PolyLang.pinstr_current_dim. simpl. lia.
    + exact Hpoly.
    + exact Htf.
    + exact Hacc_tf.
    + eapply exact_listzzs_cols_current_coord_prefix_schedule.
    + exact Hw.
    + exact Hr.
  - split; [exact Hid | exact Hacc].
Qed.

Lemma nth_error_map_inv :
  forall A B (f : A -> B) l n y,
    nth_error (List.map f l) n = Some y ->
    exists x,
      nth_error l n = Some x /\
      f x = y.
Proof.
  intros A B f l.
  induction l as [|x l IH]; intros n y Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n as [|n']; simpl in Hnth.
    + inversion Hnth; subst. exists x. split; reflexivity.
    + eapply IH in Hnth.
      destruct Hnth as [x' [Hnth Heq]].
      exists x'. split; simpl; eauto.
Qed.

Lemma nth_error_map_fwd :
  forall A B (f : A -> B) l n x,
    nth_error l n = Some x ->
    nth_error (List.map f l) n = Some (f x).
Proof.
  intros A B f l.
  induction l as [|y l IH]; intros n x Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n as [|n']; simpl in *.
    + inversion Hnth; subst. reflexivity.
    + eapply IH. exact Hnth.
Qed.

Lemma flatten_instrs_member_inv :
  forall envv pis ipl ip,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip pi /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros envv pis ipl ip Hflat Hin.
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct ((proj1 Hmem) Hin) as [pi [Hnth [_ [Hbel Hlen]]]].
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma dot_product_v0_app_1_nth :
  forall n xs,
    dot_product (V0 n ++ [1%Z]) xs = nth n xs 0%Z.
Proof.
  induction n as [|n IH]; intros xs.
  - destruct xs as [|x xs]; simpl; [reflexivity|].
    destruct xs; simpl; lia.
  - destruct xs as [|x xs]; simpl.
    + reflexivity.
    + apply IH.
Qed.

Lemma dot_product_select_coord :
  forall cols n xs,
    (S n <= cols)%nat ->
    dot_product (resize cols (V0 n ++ [1%Z])) xs = nth n xs 0%Z.
Proof.
  intros cols n xs Hle.
  assert (Hresize :
    resize cols (V0 n ++ [1%Z]) =
    (V0 n ++ [1%Z]) ++ repeat 0%Z (cols - S n)).
  {
    rewrite resize_app_le.
    2: {
      unfold V0.
      rewrite repeat_length.
      lia.
    }
    replace (Datatypes.length (V0 n)) with n.
    2: {
      unfold V0.
      rewrite repeat_length.
      reflexivity.
    }
    replace (cols - n)%nat with (S (cols - S n)) by lia.
    simpl.
    rewrite resize_null_repeat by reflexivity.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hresize.
  rewrite dot_product_app_left.
  rewrite dot_product_repeat_zero_left.
  replace (Datatypes.length (V0 n ++ [1%Z])) with (S n).
  2: {
    replace (Datatypes.length (V0 n ++ [1%Z]))
      with (Datatypes.length (V0 n) + Datatypes.length [1%Z])%nat.
    2: {
      rewrite app_length.
      reflexivity.
    }
    unfold V0.
    rewrite repeat_length.
    simpl.
    lia.
  }
  rewrite dot_product_v0_app_1_nth.
  rewrite nth_resize.
  assert ((n <? S n)%nat = true) as Hlt.
  { apply Nat.ltb_lt. lia. }
  rewrite Hlt.
  lia.
Qed.

Lemma affine_product_current_coord_old_schedule :
  forall env_dim depth d idx,
    (d < depth)%nat ->
    affine_product (current_coord_old_schedule env_dim depth d) idx =
    [nth (env_dim + d)%nat idx 0%Z].
Proof.
  intros env_dim depth d idx Hd.
  unfold current_coord_old_schedule, affine_product.
  simpl.
  unfold current_coord_schedule_row.
  simpl.
  rewrite Z.add_0_r.
  f_equal.
  eapply dot_product_select_coord.
  lia.
Qed.

Lemma seq_shift_succ :
  forall start len,
    seq (S start) len = List.map S (seq start len).
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma map_nth_seq_firstn :
  forall d l,
    (d <= Datatypes.length l)%nat ->
    List.map (fun i => nth i l 0%Z) (seq 0 d) = firstn d l.
Proof.
  induction d as [|d IH]; intros l Hlen.
  - reflexivity.
  - destruct l as [|x l]; [inversion Hlen|].
    simpl.
    rewrite seq_shift_succ.
    simpl.
    f_equal.
    rewrite List.map_map.
    change
      (List.map (fun i : nat => nth i l 0%Z) (seq 0 d) = firstn d l).
    apply IH.
    simpl in Hlen.
    lia.
Qed.

Lemma affine_product_current_coord_prefix_schedule :
  forall env_dim depth d idx,
    (d <= depth)%nat ->
    Datatypes.length idx = (env_dim + depth)%nat ->
    affine_product (current_coord_prefix_schedule env_dim depth d) idx =
    firstn d (skipn env_dim idx).
Proof.
  intros env_dim depth d idx Hd Hlen.
  unfold current_coord_prefix_schedule, affine_product.
  rewrite List.map_map.
  transitivity (List.map (fun i => nth (env_dim + i)%nat idx 0%Z) (seq 0 d)).
  - apply List.map_ext_in.
    intros i Hin.
    apply in_seq in Hin.
    destruct Hin as [_ Hub].
    unfold current_coord_schedule_row.
    simpl.
    rewrite Z.add_0_r.
    rewrite dot_product_select_coord by lia.
    reflexivity.
  - transitivity (List.map (fun i => nth i (skipn env_dim idx) 0%Z) (seq 0 d)).
    + apply List.map_ext_in.
      intros i Hin.
      rewrite nth_skipn.
      reflexivity.
    + apply map_nth_seq_firstn.
      rewrite skipn_length.
      lia.
Qed.

Lemma flatten_parallel_old_member_inv :
  forall pis varctxt vars d envv ipl ip,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_old_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip (parallel_old_pi (Datatypes.length varctxt) d pi) /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pis varctxt vars d envv ipl ip Hflat Hin.
  unfold parallel_old_pprog, pprog_pis in Hflat.
  simpl in Hflat.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi_old [Hnth_old [Hbel Hlen]]].
  eapply nth_error_map_inv in Hnth_old.
  destruct Hnth_old as [pi [Hnth Heq]].
  subst pi_old.
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma flatten_parallel_new_member_inv :
  forall pis varctxt vars d envv ipl ip,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_new_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    exists pi,
      nth_error pis ip.(PolyLang.ip_nth) = Some pi /\
      PolyLang.belongs_to ip (parallel_new_pi (Datatypes.length varctxt) d pi) /\
      Datatypes.length ip.(PolyLang.ip_index) =
        (Datatypes.length envv + pi.(PolyLang.pi_depth))%nat.
Proof.
  intros pis varctxt vars d envv ipl ip Hflat Hin.
  unfold parallel_new_pprog, pprog_pis in Hflat.
  simpl in Hflat.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi_new [Hnth_new [Hbel Hlen]]].
  eapply nth_error_map_inv in Hnth_new.
  destruct Hnth_new as [pi [Hnth Heq]].
  subst pi_new.
  exists pi.
  split; [exact Hnth |].
  split; [exact Hbel | exact Hlen].
Qed.

Lemma member_parallel_old_timestamp :
  forall pis varctxt vars d envv ipl ip pi,
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_old_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    (d < pi.(PolyLang.pi_depth))%nat ->
    ip.(PolyLang.ip_time_stamp) =
    [nth (Datatypes.length varctxt + d)%nat ip.(PolyLang.ip_index) 0%Z].
Proof.
  intros pis varctxt vars d envv ipl ip pi Hflat Hin Hnth Hd.
  destruct (flatten_parallel_old_member_inv _ _ _ _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel _]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [Hts _]]].
  rewrite Hts.
  eapply affine_product_current_coord_old_schedule.
  exact Hd.
Qed.

Lemma member_parallel_new_timestamp :
  forall pis varctxt vars d envv ipl ip pi,
    Datatypes.length envv = Datatypes.length varctxt ->
    PolyLang.flatten_instrs envv
      (pprog_pis (parallel_new_pprog (pis, varctxt, vars) d)) ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    (d <= pi.(PolyLang.pi_depth))%nat ->
    ip.(PolyLang.ip_time_stamp) =
    firstn d (skipn (Datatypes.length varctxt) ip.(PolyLang.ip_index)).
Proof.
  intros pis varctxt vars d envv ipl ip pi Henvlen Hflat Hin Hnth Hd.
  destruct (flatten_parallel_new_member_inv _ _ _ _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel Hlen]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [Hts _]]].
  rewrite Hts.
  rewrite Henvlen in Hlen.
  eapply affine_product_current_coord_prefix_schedule; eauto.
Qed.

Lemma old_new_of_ext_eq_except_sched :
  forall ip_ext,
    PolyLang.eq_except_sched (PolyLang.old_of_ext ip_ext) (PolyLang.new_of_ext ip_ext).
Proof.
  intros ip_ext.
  unfold PolyLang.eq_except_sched, PolyLang.old_of_ext, PolyLang.new_of_ext.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma rel_list_eq_except_sched_member :
  forall ipl ipl' tau,
    rel_list PolyLang.eq_except_sched ipl ipl' ->
    In tau ipl ->
    exists tau',
      In tau' ipl' /\
      PolyLang.eq_except_sched tau tau'.
Proof.
  intros ipl ipl' tau Hrel Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hnth].
  pose proof
    (proj1 (rel_list_nth _ _ _ n ipl ipl' Hrel) (ex_intro _ tau Hnth))
    as [tau' Hnth'].
  exists tau'. split.
  - eapply nth_error_In. exact Hnth'.
  - eapply rel_list_implies_rel_nth; eauto.
Qed.

Lemma in_old_of_ext_list_inv :
  forall ipl_ext tau,
    In tau (PolyLang.old_of_ext_list ipl_ext) ->
    exists ip_ext,
      In ip_ext ipl_ext /\
      PolyLang.old_of_ext ip_ext = tau.
Proof.
  intros ipl_ext tau Hin.
  unfold PolyLang.old_of_ext_list in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [ip_ext [Heq Hin_ext]].
  exists ip_ext. split; auto.
Qed.

Lemma in_new_of_ext_list_inv :
  forall ipl_ext tau,
    In tau (PolyLang.new_of_ext_list ipl_ext) ->
    exists ip_ext,
      In ip_ext ipl_ext /\
      PolyLang.new_of_ext ip_ext = tau.
Proof.
  intros ipl_ext tau Hin.
  unfold PolyLang.new_of_ext_list in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [ip_ext [Heq Hin_ext]].
  exists ip_ext. split; auto.
Qed.

Lemma env_dim_of_flat_member :
  forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    env_dim_of ip = Datatypes.length envv.
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin)
    as [pi' [Hnth' [Hbel Hlen]]].
  rewrite Hnth in Hnth'. inversion Hnth'. subst pi'.
  unfold PolyLang.belongs_to in Hbel.
  destruct Hbel as [_ [_ [_ [_ Hdepth]]]].
  unfold env_dim_of.
  rewrite Hlen, Hdepth.
  lia.
Qed.

Lemma current_coords_of_flat_member :
  forall envv pis ipl ip pi,
    PolyLang.flatten_instrs envv pis ipl ->
    In ip ipl ->
    nth_error pis ip.(PolyLang.ip_nth) = Some pi ->
    current_coords_of ip = skipn (Datatypes.length envv) ip.(PolyLang.ip_index).
Proof.
  intros envv pis ipl ip pi Hflat Hin Hnth.
  unfold current_coords_of.
  rewrite (env_dim_of_flat_member _ _ _ _ _ Hflat Hin Hnth).
  reflexivity.
Qed.

Lemma lex_compare_singleton_lt :
  forall z1 z2,
    (z1 < z2)%Z ->
    lex_compare [z1] [z2] = Lt.
Proof.
  intros z1 z2 Hlt.
  simpl.
  destruct (z1 ?= z2) eqn:Hcmp; simpl.
  - apply Z.compare_eq_iff in Hcmp. lia.
  - reflexivity.
  - apply Z.compare_gt_iff in Hcmp. lia.
Qed.

Definition check_pprog_parallel_currentb
  (pp : PolyLang.t) (plan : parallel_plan) : imp bool :=
  let d := plan.(target_dim) in
  if Nat.ltb d (PolyLang.pprog_current_dim pp)
     && check_current_view_pprogb pp
     && all_pinstrs_cover_dimb d pp
  then AffineCore.validate (parallel_old_pprog pp d) (parallel_new_pprog pp d)
  else pure false.

Definition checked_parallelize_current
  (pp : PolyLang.t) (plan : parallel_plan) : imp (result parallel_cert) :=
  BIND ok <- check_pprog_parallel_currentb pp plan -;
  if ok
  then pure (Okk {| certified_dim := plan.(target_dim) |})
  else pure (Err "Parallel validation failed").

Lemma check_pprog_parallel_currentb_true_inv :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    (target_dim plan < PolyLang.pprog_current_dim pp)%nat /\
    check_current_view_pprogb pp = true /\
    all_pinstrs_cover_dimb (target_dim plan) pp = true /\
    mayReturn
      (AffineCore.validate
         (parallel_old_pprog pp plan.(target_dim))
         (parallel_new_pprog pp plan.(target_dim)))
      true.
Proof.
  intros pp plan Hret.
  unfold check_pprog_parallel_currentb in Hret.
  destruct
    ((Nat.ltb (target_dim plan) (PolyLang.pprog_current_dim pp)
        && check_current_view_pprogb pp
        && all_pinstrs_cover_dimb (target_dim plan) pp)%bool) eqn:Hguard.
  - apply andb_true_iff in Hguard.
    destruct Hguard as [Hguard1 Hcover].
    apply andb_true_iff in Hguard1.
    destruct Hguard1 as [Hlt Hcur].
    split.
    + apply Nat.ltb_lt. exact Hlt.
    + split; [exact Hcur |].
      split; [exact Hcover | exact Hret].
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

Lemma check_pprog_parallel_currentb_sound :
  forall pp plan,
    mayReturn (check_pprog_parallel_currentb pp plan) true ->
    parallel_safe_dim pp plan.(target_dim).
Proof.
  intros [[pis varctxt] vars] [d] Hcheck.
  simpl in *.
  pose proof
    (check_pprog_parallel_currentb_true_inv
       ((pis, varctxt), vars) {| target_dim := d |} Hcheck)
    as (_ & _ & Hcover & Hval).
  unfold parallel_safe_dim.
  intros envv ipl tau1 tau2 Henvlen Hflat Hin1 Hin2 Hslice.
  simpl in *.
  pose proof
    (PolyLang.eqdom_pinstrs_implies_flatten_instrs_exists
       pis
       (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
       ipl envv
       (rel_list_eqdom_parallel_old (Datatypes.length varctxt) d pis)
       Hflat)
    as [ipl_old Hflat_old].
  pose proof
    (PolyLang.eqdom_pinstrs_implies_flatten_instrs_exists
       pis
       (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
       ipl envv
       (rel_list_eqdom_parallel_new (Datatypes.length varctxt) d pis)
       Hflat)
    as [ipl_new Hflat_new].
  pose proof
    (PolyLang.eqdom_pinstrs_implies_flatten_instr_nth_rel'
       pis
       (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
       ipl envv ipl_old
       (rel_list_eqdom_parallel_old (Datatypes.length varctxt) d pis)
       Hflat Hflat_old)
    as Hrel_old.
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin1)
    as [pi1 [Hnth1 [Hbel1 Hlen1]]].
  destruct (flatten_instrs_member_inv _ _ _ _ Hflat Hin2)
    as [pi2 [Hnth2 [Hbel2 Hlen2]]].
  assert (Hinpi1 : In pi1 pis).
  { eapply nth_error_In. exact Hnth1. }
  assert (Hinpi2 : In pi2 pis).
  { eapply nth_error_In. exact Hnth2. }
  pose proof
    (all_pinstrs_cover_dimb_sound ((pis, varctxt), vars) d pi1 Hcover Hinpi1)
    as Hd1.
  pose proof
    (all_pinstrs_cover_dimb_sound ((pis, varctxt), vars) d pi2 Hcover Hinpi2)
    as Hd2.
  destruct (rel_list_eq_except_sched_member _ _ _ Hrel_old Hin1)
    as [tau1_old [Hin1_old Heq1]].
  destruct (rel_list_eq_except_sched_member _ _ _ Hrel_old Hin2)
    as [tau2_old [Hin2_old Heq2]].
  assert (Hslice_old : same_parallel_slice d tau1_old tau2_old).
  {
    eapply eq_except_sched_preserves_same_parallel_slice; eauto.
  }
  pose proof Heq1 as Heq1_full.
  pose proof Heq2 as Heq2_full.
  destruct Heq1 as (Hnth_eq1 & _ & _ & _ & _).
  destruct Heq2 as (Hnth_eq2 & _ & _ & _ & _).
  assert (Hnth1_old : nth_error pis tau1_old.(PolyLang.ip_nth) = Some pi1).
  { rewrite <- Hnth_eq1. exact Hnth1. }
  assert (Hnth2_old : nth_error pis tau2_old.(PolyLang.ip_nth) = Some pi2).
  { rewrite <- Hnth_eq2. exact Hnth2. }
  assert
    (Hnth1_old_map :
       nth_error (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
         tau1_old.(PolyLang.ip_nth) =
       Some (parallel_old_pi (Datatypes.length varctxt) d pi1)).
  { rewrite <- Hnth_eq1. apply nth_error_map_fwd. exact Hnth1. }
  assert
    (Hnth2_old_map :
       nth_error (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
         tau2_old.(PolyLang.ip_nth) =
       Some (parallel_old_pi (Datatypes.length varctxt) d pi2)).
  { rewrite <- Hnth_eq2. apply nth_error_map_fwd. exact Hnth2. }
  pose proof
    (member_parallel_old_timestamp
       pis varctxt vars d envv ipl_old tau1_old pi1
       Hflat_old Hin1_old Hnth1_old Hd1)
    as Hts1_old.
  pose proof
    (member_parallel_old_timestamp
       pis varctxt vars d envv ipl_old tau2_old pi2
       Hflat_old Hin2_old Hnth2_old Hd2)
    as Hts2_old.
  pose proof
    (AffineCore.validate_implies_permutability
       (parallel_old_pprog ((pis, varctxt), vars) d)
       (parallel_new_pprog ((pis, varctxt), vars) d)
       varctxt varctxt envv vars vars
       (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
       (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
       ipl_old ipl_new true Hval eq_refl eq_refl eq_refl (eq_sym Henvlen)
       Hflat_old Hflat_new)
    as Hperm_data.
  destruct Hperm_data as [ipl_ext [Hnewext [Holdext Hperm_ext]]].
  pose proof Hin1_old as Hin1_old_flat.
  pose proof Hin2_old as Hin2_old_flat.
  rewrite <- Holdext in Hin1_old, Hin2_old.
  destruct (in_old_of_ext_list_inv _ _ Hin1_old)
    as [tau1_ext [Hin1_ext Hold1]].
  destruct (in_old_of_ext_list_inv _ _ Hin2_old)
    as [tau2_ext [Hin2_ext Hold2]].
  assert (Hslice_ext_old :
    same_parallel_slice d (PolyLang.old_of_ext tau1_ext) (PolyLang.old_of_ext tau2_ext)).
  {
    rewrite Hold1, Hold2.
    exact Hslice_old.
  }
  pose proof (old_new_of_ext_eq_except_sched tau1_ext) as Hext_eq1.
  pose proof (old_new_of_ext_eq_except_sched tau2_ext) as Hext_eq2.
  assert (Hslice_new :
    same_parallel_slice d (PolyLang.new_of_ext tau1_ext) (PolyLang.new_of_ext tau2_ext)).
  {
    eapply eq_except_sched_preserves_same_parallel_slice; eauto.
  }
  destruct Hext_eq1 as (Hnth_ext1 & _ & _ & _ & _).
  destruct Hext_eq2 as (Hnth_ext2 & _ & _ & _ & _).
  assert (Hin1_new : In (PolyLang.new_of_ext tau1_ext) ipl_new).
  { rewrite <- Hnewext. unfold PolyLang.new_of_ext_list. apply in_map. exact Hin1_ext. }
  assert (Hin2_new : In (PolyLang.new_of_ext tau2_ext) ipl_new).
  { rewrite <- Hnewext. unfold PolyLang.new_of_ext_list. apply in_map. exact Hin2_ext. }
  assert
    (Hnth1_new :
       nth_error pis (PolyLang.ip_nth (PolyLang.new_of_ext tau1_ext)) = Some pi1).
  {
    rewrite <- Hnth_ext1.
    rewrite Hold1.
    exact Hnth1_old.
  }
  assert
    (Hnth2_new :
       nth_error pis (PolyLang.ip_nth (PolyLang.new_of_ext tau2_ext)) = Some pi2).
  {
    rewrite <- Hnth_ext2.
    rewrite Hold2.
    exact Hnth2_old.
  }
  pose proof
    (member_parallel_new_timestamp
       pis varctxt vars d envv ipl_new (PolyLang.new_of_ext tau1_ext) pi1
       Henvlen Hflat_new Hin1_new Hnth1_new (Nat.lt_le_incl _ _ Hd1))
    as Hts1_new.
  pose proof
    (member_parallel_new_timestamp
       pis varctxt vars d envv ipl_new (PolyLang.new_of_ext tau2_ext) pi2
       Henvlen Hflat_new Hin2_new Hnth2_new (Nat.lt_le_incl _ _ Hd2))
    as Hts2_new.
  assert
    (Hnth1_new_map :
       nth_error (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
         (PolyLang.ip_nth (PolyLang.new_of_ext tau1_ext)) =
       Some (parallel_new_pi (Datatypes.length varctxt) d pi1)).
  {
    rewrite <- Hnth_ext1.
    rewrite Hold1.
    apply nth_error_map_fwd.
    exact Hnth1_old.
  }
  assert
    (Hnth2_new_map :
       nth_error (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
         (PolyLang.ip_nth (PolyLang.new_of_ext tau2_ext)) =
       Some (parallel_new_pi (Datatypes.length varctxt) d pi2)).
  {
    rewrite <- Hnth_ext2.
    rewrite Hold2.
    apply nth_error_map_fwd.
    exact Hnth2_old.
  }
  pose proof
    (current_coords_of_flat_member
       envv
       (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
       ipl_old tau1_old
       (parallel_old_pi (Datatypes.length varctxt) d pi1)
       Hflat_old Hin1_old_flat Hnth1_old_map)
    as Hcur1_old.
  pose proof
    (current_coords_of_flat_member
       envv
       (List.map (parallel_old_pi (Datatypes.length varctxt) d) pis)
       ipl_old tau2_old
       (parallel_old_pi (Datatypes.length varctxt) d pi2)
       Hflat_old Hin2_old_flat Hnth2_old_map)
    as Hcur2_old.
  pose proof
    (current_coords_of_flat_member
       envv
       (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
       ipl_new (PolyLang.new_of_ext tau1_ext)
       (parallel_new_pi (Datatypes.length varctxt) d pi1)
       Hflat_new Hin1_new Hnth1_new_map)
    as Hcur1_new.
  pose proof
    (current_coords_of_flat_member
       envv
       (List.map (parallel_new_pi (Datatypes.length varctxt) d) pis)
       ipl_new (PolyLang.new_of_ext tau2_ext)
       (parallel_new_pi (Datatypes.length varctxt) d pi2)
       Hflat_new Hin2_new Hnth2_new_map)
    as Hcur2_new.
  destruct Hslice_old as (_ & Hprefix_old & Hdiff_old).
  destruct Hslice_new as (_ & Hprefix_new & _).
  unfold different_dim_at in Hdiff_old.
  unfold same_prefix_before in Hprefix_new.
  rewrite Hcur1_old, Hcur2_old in Hdiff_old.
  rewrite Hcur1_new, Hcur2_new in Hprefix_new.
  pose proof Heq1_full as Heq1_idx.
  pose proof Heq2_full as Heq2_idx.
  destruct Heq1_idx as (_ & Hidx_eq1 & _ & _ & _).
  destruct Heq2_idx as (_ & Hidx_eq2 & _ & _ & _).
  assert
    (Hlen1_old_full :
       Datatypes.length tau1_old.(PolyLang.ip_index) =
       (Datatypes.length envv + PolyLang.pi_depth pi1)%nat).
  { rewrite <- Hidx_eq1. exact Hlen1. }
  assert
    (Hlen2_old_full :
       Datatypes.length tau2_old.(PolyLang.ip_index) =
       (Datatypes.length envv + PolyLang.pi_depth pi2)%nat).
  { rewrite <- Hidx_eq2. exact Hlen2. }
  assert
    (Hneq_coord :
       nth (Datatypes.length envv + d)%nat tau1_old.(PolyLang.ip_index) 0%Z <>
       nth (Datatypes.length envv + d)%nat tau2_old.(PolyLang.ip_index) 0%Z).
  {
    intro Heq.
    apply Hdiff_old.
    rewrite <- !nth_error_skipn.
    replace (d + Datatypes.length envv)%nat with (Datatypes.length envv + d)%nat by lia.
    change
      (nth_error tau1_old.(PolyLang.ip_index) (Datatypes.length envv + d) =
       nth_error tau2_old.(PolyLang.ip_index) (Datatypes.length envv + d)).
    rewrite nth_error_nth' with
        (d := 0%Z)
        (n := (Datatypes.length envv + d)%nat)
        (l := PolyLang.ILSema.ip_index tau1_old).
    2: { rewrite Hlen1_old_full. lia. }
    rewrite nth_error_nth' with
        (d := 0%Z)
        (n := (Datatypes.length envv + d)%nat)
        (l := PolyLang.ILSema.ip_index tau2_old).
    2: { rewrite Hlen2_old_full. lia. }
    now rewrite Heq.
  }
  assert
    (Hnew_eq :
       PolyLang.ip_time_stamp (PolyLang.new_of_ext tau1_ext) =
       PolyLang.ip_time_stamp (PolyLang.new_of_ext tau2_ext)).
  {
    replace (Datatypes.length varctxt)%nat with (Datatypes.length envv)%nat in Hts1_new
      by (rewrite <- Henvlen; reflexivity).
    replace (Datatypes.length varctxt)%nat with (Datatypes.length envv)%nat in Hts2_new
      by (rewrite <- Henvlen; reflexivity).
    rewrite Hts1_new, Hts2_new.
    exact Hprefix_new.
  }
  destruct
    (Z_lt_ge_dec
       (nth (Datatypes.length envv + d)%nat tau1_old.(PolyLang.ip_index) 0%Z)
       (nth (Datatypes.length envv + d)%nat tau2_old.(PolyLang.ip_index) 0%Z))
    as [Hlt12 | Hge12].
  - assert (PolyLang.instr_point_ext_old_sched_lt tau1_ext tau2_ext) as Hold_lt.
    {
      unfold PolyLang.instr_point_ext_old_sched_lt.
      change
        (lex_compare
           (PolyLang.ip_time_stamp (PolyLang.old_of_ext tau1_ext))
           (PolyLang.ip_time_stamp (PolyLang.old_of_ext tau2_ext)) = Lt).
      rewrite Hold1, Hold2.
      rewrite Hts1_old, Hts2_old.
      rewrite Henvlen in Hlt12.
      apply lex_compare_singleton_lt.
      exact Hlt12.
    }
    assert (PolyLang.instr_point_ext_new_sched_ge tau1_ext tau2_ext) as Hnew_ge.
    {
      unfold PolyLang.instr_point_ext_new_sched_ge.
      left.
      change
        (lex_compare
           (PolyLang.ip_time_stamp (PolyLang.new_of_ext tau1_ext))
           (PolyLang.ip_time_stamp (PolyLang.new_of_ext tau2_ext)) = Eq).
      rewrite Hnew_eq.
      apply lex_compare_reflexive.
    }
    eapply permutable_eq_except_sched.
    + apply eq_except_sched_symm. exact Heq1_full.
    + apply eq_except_sched_symm. exact Heq2_full.
    + unfold PolyLang.Permutable_ext.
      rewrite <- Hold1, <- Hold2.
      eapply Hperm_ext; eauto.
  - assert
      (Hgt21 :
         (nth (Datatypes.length envv + d)%nat tau2_old.(PolyLang.ip_index) 0%Z <
          nth (Datatypes.length envv + d)%nat tau1_old.(PolyLang.ip_index) 0%Z)%Z).
    { lia. }
    assert (PolyLang.instr_point_ext_old_sched_lt tau2_ext tau1_ext) as Hold_lt.
    {
      unfold PolyLang.instr_point_ext_old_sched_lt.
      change
        (lex_compare
           (PolyLang.ip_time_stamp (PolyLang.old_of_ext tau2_ext))
           (PolyLang.ip_time_stamp (PolyLang.old_of_ext tau1_ext)) = Lt).
      rewrite Hold1, Hold2.
      rewrite Hts1_old, Hts2_old.
      rewrite Henvlen in Hgt21.
      apply lex_compare_singleton_lt.
      exact Hgt21.
    }
    assert (PolyLang.instr_point_ext_new_sched_ge tau2_ext tau1_ext) as Hnew_ge.
    {
      unfold PolyLang.instr_point_ext_new_sched_ge.
      left.
      change
        (lex_compare
           (PolyLang.ip_time_stamp (PolyLang.new_of_ext tau2_ext))
           (PolyLang.ip_time_stamp (PolyLang.new_of_ext tau1_ext)) = Eq).
      rewrite Hnew_eq.
      apply lex_compare_reflexive.
    }
    eapply permutable_eq_except_sched.
    + apply eq_except_sched_symm. exact Heq1_full.
    + apply eq_except_sched_symm. exact Heq2_full.
    + assert (Hperm_rev : PolyLang.Permutable_ext tau2_ext tau1_ext).
      {
        eapply Hperm_ext; eauto.
      }
      pose proof (PolyLang.Permutable_ext_symm _ _ Hperm_rev) as Hperm_fwd.
      unfold PolyLang.Permutable_ext in Hperm_fwd.
      rewrite Hold1, Hold2 in Hperm_fwd.
      exact Hperm_fwd.
Qed.

Lemma checked_parallelize_current_sound :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    parallel_cert_sound pp cert.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  unfold parallel_cert_sound.
  simpl.
  eapply check_pprog_parallel_currentb_sound.
  exact Hcheck.
Qed.

Lemma checked_parallelize_current_implies_dim_in_range :
  forall pp plan cert,
    mayReturn (checked_parallelize_current pp plan) (Okk cert) ->
    (certified_dim cert < PolyLang.pprog_current_dim pp)%nat.
Proof.
  intros pp plan cert Hchecked.
  unfold checked_parallelize_current in Hchecked.
  apply mayReturn_bind in Hchecked.
  destruct Hchecked as [ok [Hcheck Hret]].
  destruct ok;
    [apply mayReturn_pure in Hret
    | apply mayReturn_pure in Hret; discriminate].
  inversion Hret; subst; clear Hret.
  simpl.
  destruct (check_pprog_parallel_currentb_true_inv pp plan Hcheck)
    as (Hlt & _).
  exact Hlt.
Qed.

End ParallelValidator.
