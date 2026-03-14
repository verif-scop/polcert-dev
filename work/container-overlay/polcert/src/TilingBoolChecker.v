Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import PolyBase.
Require Import PolyLang.
Require Import PointWitness.
Require Import TilingWitness.
Require Import TilingRelation.
Require Import InstrTy.

Module TilingBoolChecker (Instr: INSTR).

Module Tiling := TilingRelation Instr.
Module PL := Tiling.PL.
Module Ty := Instr.Ty.

Fixpoint ctxt_eqb (l1 l2: list Instr.ident): bool :=
  match l1, l2 with
  | id1 :: l1', id2 :: l2' =>
      Instr.ident_eqb id1 id2 && ctxt_eqb l1' l2'
  | [], [] => true
  | _, _ => false
  end.

Lemma ctxt_eqb_eq :
  forall l1 l2,
    ctxt_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|x xs IH]; intros l2; split; intro H.
  - destruct l2; simpl in H; try discriminate; reflexivity.
  - subst. reflexivity.
  - destruct l2 as [|y ys]; simpl in H; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Heq Htl].
    apply Instr.ident_eqb_eq in Heq.
    apply IH in Htl.
    subst. reflexivity.
  - inversion H; subst.
    simpl.
    apply andb_true_iff.
    split.
    + apply Instr.ident_eqb_eq. reflexivity.
    + apply IH. reflexivity.
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

Definition check_tile_link_positiveb (link: tile_link) : bool :=
  Z.ltb 0 (tl_tile_size link).

Fixpoint check_well_formed_tile_linksb
    (prefix_dim point_dim: nat) (links: list tile_link) : bool :=
  match links with
  | [] => true
  | link :: links' =>
      Nat.eqb (List.length (ae_var_coeffs (tl_expr link))) (prefix_dim + point_dim) &&
      check_well_formed_tile_linksb (S prefix_dim) point_dim links'
  end.

Definition check_statement_tiling_witnessb
    (param_dim: nat) (w: statement_tiling_witness) : bool :=
  check_well_formed_tile_linksb 0 (stw_point_dim w) (stw_links w) &&
  forallb
    (fun link =>
       Nat.eqb (List.length (ae_param_coeffs (tl_expr link))) param_dim &&
       check_tile_link_positiveb link)
    (stw_links w).

Lemma check_well_formed_tile_linksb_sound :
  forall prefix_dim point_dim links,
    check_well_formed_tile_linksb prefix_dim point_dim links = true ->
    well_formed_tile_links prefix_dim point_dim links.
Proof.
  intros prefix_dim point_dim links.
  revert prefix_dim point_dim.
  induction links as [|link links' IH]; intros prefix_dim point_dim Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hlen Hrest].
    split.
    + apply Nat.eqb_eq. exact Hlen.
    + apply IH. exact Hrest.
Qed.

Lemma forallb_link_params_positive_sound :
  forall param_dim links,
    forallb
      (fun link =>
         Nat.eqb (List.length (ae_param_coeffs (tl_expr link))) param_dim &&
         check_tile_link_positiveb link)
      links = true ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = param_dim /\
         0 < tl_tile_size link)
      links.
Proof.
  intros param_dim links.
  induction links as [|link links' IH]; intro Hcheck.
  - constructor.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    apply andb_true_iff in Hhd.
    destruct Hhd as [Hparam Hpos].
    constructor.
    + split.
      * apply Nat.eqb_eq. exact Hparam.
      * apply Z.ltb_lt. exact Hpos.
    + apply IH. exact Htl.
Qed.

Lemma check_statement_tiling_witnessb_sound :
  forall param_dim w,
    check_statement_tiling_witnessb param_dim w = true ->
    Tiling.wf_statement_tiling_witness_with_param_dim param_dim w /\
    Forall (fun link => 0 < tl_tile_size link) (stw_links w).
Proof.
  intros param_dim w Hcheck.
  unfold Tiling.wf_statement_tiling_witness_with_param_dim,
         check_statement_tiling_witnessb in *.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hwf Hrest].
  pose proof (check_well_formed_tile_linksb_sound 0 (stw_point_dim w) (stw_links w) Hwf)
    as Hwf_links.
  pose proof (forallb_link_params_positive_sound param_dim (stw_links w) Hrest)
    as Hparam_pos.
  split.
  - split.
    + exact Hwf_links.
    + eapply Forall_impl; [| exact Hparam_pos].
      intros link [Hparam _].
      exact Hparam.
  - eapply Forall_impl; [| exact Hparam_pos].
    intros link [_ Hpos].
    exact Hpos.
Qed.

Definition check_pinstr_tiling_compiledb
    (env_size param_dim: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  let cw := Tiling.compiled_pinstr_tiling_witness w in
  check_statement_tiling_witnessb param_dim w &&
  Nat.eqb (stw_point_dim w) (PL.pi_depth before) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr before) &&
  Nat.eqb (PL.pi_depth after) (PL.pi_depth before + List.length (stw_links w)) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PSWTiling (Tiling.ptw_statement_witness cw)) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (Tiling.pad_transformation_after_env
       (Tiling.ptw_added_dims cw) env_size (PL.pi_transformation before)) &&
  listzzs_strict_eqb
    (PL.pi_access_transformation after)
    (Tiling.pad_transformation_after_env
       (Tiling.ptw_added_dims cw) env_size (PL.pi_access_transformation before)) &&
  listzzs_strict_eqb
    (PL.pi_poly after)
    (Tiling.ptw_link_domain cw ++
     Tiling.lifted_base_domain_after_env env_size cw (PL.pi_poly before)) &&
  access_list_strict_eqb
    (PL.pi_waccess after)
    (Tiling.lifted_accesses_after_env env_size cw (PL.pi_waccess before)) &&
  access_list_strict_eqb
    (PL.pi_raccess after)
    (Tiling.lifted_accesses_after_env env_size cw (PL.pi_raccess before)).

Definition check_pinstr_tiling_sourceb
    (env_size param_dim: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : bool :=
  let cw := Tiling.compiled_pinstr_tiling_witness w in
  check_statement_tiling_witnessb param_dim w &&
  Nat.eqb (stw_point_dim w) (PL.pi_depth before) &&
  point_space_witness_eqb
    (PL.pi_point_witness before)
    (PSWIdentity (PL.pi_depth before)) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr before) &&
  Nat.eqb (PL.pi_depth after) (PL.pi_depth before + List.length (stw_links w)) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PSWTiling (Tiling.ptw_statement_witness cw)) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (PL.pi_transformation before) &&
  listzzs_strict_eqb
    (PL.pi_access_transformation after)
    (PL.pi_access_transformation before) &&
  listzzs_strict_eqb
    (PL.pi_poly after)
    (Tiling.ptw_link_domain cw ++
     Tiling.lifted_base_domain_after_env env_size cw (PL.pi_poly before)) &&
  access_list_strict_eqb
    (PL.pi_waccess after)
    (PL.pi_waccess before) &&
  access_list_strict_eqb
    (PL.pi_raccess after)
    (PL.pi_raccess before).

Lemma check_pinstr_tiling_compiledb_sound :
  forall env_size param_dim before after w,
    check_pinstr_tiling_compiledb env_size param_dim before after w = true ->
    Tiling.tiling_rel_pinstr_structure_compiled env_size before after w /\
    Tiling.wf_statement_tiling_witness_with_param_dim param_dim w /\
    Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
    stw_point_dim w = PL.pi_depth before.
Proof.
  intros env_size param_dim before after w Hcheck.
  unfold check_pinstr_tiling_compiledb in Hcheck.
  set (cw := Tiling.compiled_pinstr_tiling_witness w) in *.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hracc].
  destruct Hcheck as [Hcheck Hwacc].
  destruct Hcheck as [Hcheck Hdom].
  destruct Hcheck as [Hcheck Hacc_tf].
  destruct Hcheck as [Hcheck Htf].
  destruct Hcheck as [Hcheck Hwitness].
  destruct Hcheck as [Hcheck Hdepth].
  destruct Hcheck as [Hcheck Hinstr].
  destruct Hcheck as [Hwit Hpoint].
  pose proof (check_statement_tiling_witnessb_sound param_dim w Hwit)
    as [Hwf Hsizes].
  split.
  - unfold Tiling.tiling_rel_pinstr_structure_compiled,
           Tiling.tiling_rel_pinstr_structure.
    repeat split.
    + apply Instr.eqb_eq. exact Hinstr.
    + apply Nat.eqb_eq. exact Hdepth.
    + apply point_space_witness_eqb_eq. exact Hwitness.
    + apply listzzs_strict_eqb_eq. exact Htf.
    + apply listzzs_strict_eqb_eq. exact Hacc_tf.
    + apply listzzs_strict_eqb_eq. exact Hdom.
    + apply access_list_strict_eqb_eq. exact Hwacc.
    + apply access_list_strict_eqb_eq. exact Hracc.
  - split.
    + exact Hwf.
    + split.
      * exact Hsizes.
      * apply Nat.eqb_eq. exact Hpoint.
Qed.

Lemma check_pinstr_tiling_sourceb_sound :
  forall env_size param_dim before after w,
    check_pinstr_tiling_sourceb env_size param_dim before after w = true ->
    Tiling.tiling_rel_pinstr_structure_source
      env_size before after (Tiling.compiled_pinstr_tiling_witness w) /\
    PL.pi_point_witness before = PSWIdentity (PL.pi_depth before) /\
    Tiling.wf_statement_tiling_witness_with_param_dim param_dim w /\
    Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
    stw_point_dim w = PL.pi_depth before.
Proof.
  intros env_size param_dim before after w Hcheck.
  unfold check_pinstr_tiling_sourceb in Hcheck.
  set (cw := Tiling.compiled_pinstr_tiling_witness w) in *.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hracc].
  destruct Hcheck as [Hcheck Hwacc].
  destruct Hcheck as [Hcheck Hdom].
  destruct Hcheck as [Hcheck Hacc_tf].
  destruct Hcheck as [Hcheck Htf].
  destruct Hcheck as [Hcheck Hwitness].
  destruct Hcheck as [Hcheck Hdepth].
  destruct Hcheck as [Hcheck Hinstr].
  destruct Hcheck as [Hcheck Hbefore_witness].
  destruct Hcheck as [Hwit Hpoint].
  pose proof (check_statement_tiling_witnessb_sound param_dim w Hwit)
    as [Hwf Hsizes].
  split.
  - unfold Tiling.tiling_rel_pinstr_structure_source.
    repeat split.
    + apply Instr.eqb_eq. exact Hinstr.
    + apply Nat.eqb_eq. exact Hdepth.
    + apply point_space_witness_eqb_eq. exact Hwitness.
    + apply listzzs_strict_eqb_eq. exact Htf.
    + apply listzzs_strict_eqb_eq. exact Hacc_tf.
    + apply listzzs_strict_eqb_eq. exact Hdom.
    + apply access_list_strict_eqb_eq. exact Hwacc.
    + apply access_list_strict_eqb_eq. exact Hracc.
  - split.
    + apply point_space_witness_eqb_eq. exact Hbefore_witness.
    + split.
      * exact Hwf.
      * split.
        -- exact Hsizes.
        -- apply Nat.eqb_eq. exact Hpoint.
Qed.

Fixpoint check_pinstr_list_tiling_compiledb
    (env_size param_dim: nat)
    (before after: list PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before, after, ws with
  | [], [], [] => true
  | before_pi :: before', after_pi :: after', w :: ws' =>
      check_pinstr_tiling_compiledb env_size param_dim before_pi after_pi w &&
      check_pinstr_list_tiling_compiledb env_size param_dim before' after' ws'
  | _, _, _ => false
  end.

Fixpoint check_pinstr_list_tiling_sourceb
    (env_size param_dim: nat)
    (before after: list PL.PolyInstr)
    (ws: list statement_tiling_witness) : bool :=
  match before, after, ws with
  | [], [], [] => true
  | before_pi :: before', after_pi :: after', w :: ws' =>
      check_pinstr_tiling_sourceb env_size param_dim before_pi after_pi w &&
      check_pinstr_list_tiling_sourceb env_size param_dim before' after' ws'
  | _, _, _ => false
  end.

Lemma check_pinstr_list_tiling_compiledb_sound :
  forall env_size param_dim before after ws,
    check_pinstr_list_tiling_compiledb env_size param_dim before after ws = true ->
    Tiling.tiling_rel_pinstr_list
      env_size before after (List.map Tiling.compiled_pinstr_tiling_witness ws) /\
    Forall (Tiling.wf_statement_tiling_witness_with_param_dim param_dim) ws /\
    Forall (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w)) ws /\
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi) before ws.
Proof.
  induction before as [|before_pi before' IHbefore]; intros after ws Hcheck.
  - destruct after, ws; simpl in Hcheck; try discriminate.
    repeat split; constructor.
  - destruct after as [|after_pi after'], ws as [|w ws']; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    pose proof (check_pinstr_tiling_compiledb_sound _ _ _ _ _ Hhd)
      as [Hrel_hd [Hwf_hd [Hsizes_hd Hdepth_hd]]].
    pose proof (IHbefore _ _ Htl)
      as [Hrel_tl [Hwf_tl [Hsizes_tl Hdepth_tl]]].
    split.
    + simpl. split.
      * exact Hrel_hd.
      * exact Hrel_tl.
    + split.
      * constructor; assumption.
      * split.
        -- constructor; assumption.
        -- constructor; assumption.
Qed.

Lemma check_pinstr_list_tiling_sourceb_sound :
  forall env_size param_dim before after ws,
    check_pinstr_list_tiling_sourceb env_size param_dim before after ws = true ->
    Tiling.tiling_rel_pinstr_list_source
      env_size before after (List.map Tiling.compiled_pinstr_tiling_witness ws) /\
    Forall
      (fun before_pi =>
         PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi))
      before /\
    Forall (Tiling.wf_statement_tiling_witness_with_param_dim param_dim) ws /\
    Forall (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w)) ws /\
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi) before ws.
Proof.
  induction before as [|before_pi before' IHbefore]; intros after ws Hcheck.
  - destruct after, ws; simpl in Hcheck; try discriminate.
    repeat split; constructor.
  - destruct after as [|after_pi after'], ws as [|w ws']; simpl in Hcheck; try discriminate.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhd Htl].
    pose proof (check_pinstr_tiling_sourceb_sound _ _ _ _ _ Hhd)
      as [Hrel_hd [Hbefore_hd [Hwf_hd [Hsizes_hd Hdepth_hd]]]].
    pose proof (IHbefore _ _ Htl)
      as [Hrel_tl [Hbefore_tl [Hwf_tl [Hsizes_tl Hdepth_tl]]]].
    split.
    + simpl. split.
      * exact Hrel_hd.
      * exact Hrel_tl.
    + split.
      * constructor; assumption.
      * split.
        -- constructor; assumption.
        -- split.
           ++ constructor; assumption.
           ++ constructor; assumption.
Qed.

Definition check_pprog_tiling_compiledb
    (before after: PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  ctxt_eqb before_ctxt after_ctxt &&
  ctxt_ty_eqb before_vars after_vars &&
  check_pinstr_list_tiling_compiledb
    (List.length before_ctxt)
    (List.length before_ctxt)
    before_pis after_pis ws.

Definition check_pprog_tiling_sourceb
    (before after: PL.t)
    (ws: list statement_tiling_witness) : bool :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  ctxt_eqb before_ctxt after_ctxt &&
  ctxt_ty_eqb before_vars after_vars &&
  check_pinstr_list_tiling_sourceb
    (List.length before_ctxt)
    (List.length before_ctxt)
    before_pis after_pis ws.

Lemma check_pprog_tiling_compiledb_sound :
  forall before after ws,
    check_pprog_tiling_compiledb before after ws = true ->
    Tiling.tiling_rel_pprog_structure_compiled before after ws /\
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (let '(_, before_ctxt, _) := before in List.length before_ctxt))
      ws /\
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws /\
    let '(before_pis, _, _) := before in
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi) before_pis ws.
Proof.
  intros before after ws Hcheck.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  unfold check_pprog_tiling_compiledb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hctxt Hvars] Hlist].
  apply ctxt_eqb_eq in Hctxt.
  apply ctxt_ty_eqb_eq in Hvars.
  pose proof
    (check_pinstr_list_tiling_compiledb_sound
       (List.length before_ctxt) (List.length before_ctxt)
       before_pis after_pis ws Hlist)
    as [Hrel [Hwf [Hsizes Hdepths]]].
  split.
  - unfold Tiling.tiling_rel_pprog_structure_compiled,
           Tiling.tiling_rel_pprog_structure.
    simpl.
    split; [exact Hctxt|].
    split; [exact Hvars|].
    exact Hrel.
  - split; [exact Hwf|].
    split; [exact Hsizes| exact Hdepths].
Qed.

Lemma check_pprog_tiling_sourceb_sound :
  forall before after ws,
    check_pprog_tiling_sourceb before after ws = true ->
    Tiling.tiling_rel_pprog_structure_source before after
      (List.map Tiling.compiled_pinstr_tiling_witness ws) /\
    let '(before_pis, _, _) := before in
    Forall
      (fun before_pi =>
         PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi))
      before_pis /\
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (let '(_, before_ctxt, _) := before in List.length before_ctxt))
      ws /\
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws /\
    let '(before_pis, _, _) := before in
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi) before_pis ws.
Proof.
  intros before after ws Hcheck.
  destruct before as [[before_pis before_ctxt] before_vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  unfold check_pprog_tiling_sourceb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hctxt Hvars] Hlist].
  apply ctxt_eqb_eq in Hctxt.
  apply ctxt_ty_eqb_eq in Hvars.
  pose proof
    (check_pinstr_list_tiling_sourceb_sound
       (List.length before_ctxt) (List.length before_ctxt)
       before_pis after_pis ws Hlist)
    as [Hrel [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  split.
  - unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    split; [exact Hctxt|].
    split; [exact Hvars|].
    exact Hrel.
  - split; [exact Hbefore_ids|].
    split; [exact Hwf|].
    split; [exact Hsizes| exact Hdepths].
Qed.

End TilingBoolChecker.
