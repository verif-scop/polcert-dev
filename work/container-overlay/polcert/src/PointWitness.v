Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Linalg.
Require Import PolyBase.
Require Import TilingWitness.

Import ListNotations.

Inductive point_space_witness :=
| PSWIdentity (point_dim: nat)
| PSWTiling (w: statement_tiling_witness)
| PSWInsertAfterEnv (added_dim: nat) (inner: point_space_witness)
| PSWInsertAtEnd (added_dim: nat) (inner: point_space_witness).

Fixpoint list_Z_eqb (xs ys: list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Z.eqb x y && list_Z_eqb xs' ys'
  | _, _ => false
  end.

Definition affine_expr_eqb (e1 e2: affine_expr) : bool :=
  list_Z_eqb e1.(ae_var_coeffs) e2.(ae_var_coeffs) &&
  list_Z_eqb e1.(ae_param_coeffs) e2.(ae_param_coeffs) &&
  Z.eqb e1.(ae_const) e2.(ae_const).

Definition tile_link_eqb (l1 l2: tile_link) : bool :=
  affine_expr_eqb l1.(tl_expr) l2.(tl_expr) &&
  Z.eqb l1.(tl_tile_size) l2.(tl_tile_size).

Fixpoint tile_link_list_eqb (ls1 ls2: list tile_link) : bool :=
  match ls1, ls2 with
  | [], [] => true
  | l1 :: ls1', l2 :: ls2' => tile_link_eqb l1 l2 && tile_link_list_eqb ls1' ls2'
  | _, _ => false
  end.

Definition statement_tiling_witness_eqb
    (w1 w2: statement_tiling_witness) : bool :=
  Nat.eqb w1.(stw_point_dim) w2.(stw_point_dim) &&
  tile_link_list_eqb w1.(stw_links) w2.(stw_links).

Fixpoint point_space_witness_eqb
    (pw1 pw2: point_space_witness) : bool :=
  match pw1, pw2 with
  | PSWIdentity d1, PSWIdentity d2 => Nat.eqb d1 d2
  | PSWTiling w1, PSWTiling w2 => statement_tiling_witness_eqb w1 w2
  | PSWInsertAfterEnv d1 pw1', PSWInsertAfterEnv d2 pw2' =>
      Nat.eqb d1 d2 && point_space_witness_eqb pw1' pw2'
  | PSWInsertAtEnd d1 pw1', PSWInsertAtEnd d2 pw2' =>
      Nat.eqb d1 d2 && point_space_witness_eqb pw1' pw2'
  | _, _ => false
  end.

Fixpoint witness_added_dims (pw: point_space_witness) : nat :=
  match pw with
  | PSWIdentity _ => 0
  | PSWTiling w => List.length (stw_links w)
  | PSWInsertAfterEnv added_dim inner => (added_dim + witness_added_dims inner)%nat
  | PSWInsertAtEnd added_dim inner => (added_dim + witness_added_dims inner)%nat
  end.

Fixpoint witness_base_point_dim (pw: point_space_witness) : nat :=
  match pw with
  | PSWIdentity point_dim => point_dim
  | PSWTiling w => stw_point_dim w
  | PSWInsertAfterEnv _ inner => witness_base_point_dim inner
  | PSWInsertAtEnd _ inner => witness_base_point_dim inner
  end.

Definition witness_current_point_dim (pw: point_space_witness) : nat :=
  (witness_base_point_dim pw + witness_added_dims pw)%nat.

Definition identity_affine_row
    (total_cols pos: nat) : list Z * Z :=
  (repeat 0%Z pos ++ [1%Z] ++ repeat 0%Z (total_cols - pos - 1), 0%Z).

Fixpoint identity_affine_rows_from
    (total_cols pos count: nat) : Transformation :=
  match count with
  | O => []
  | S count' =>
      identity_affine_row total_cols pos ::
      identity_affine_rows_from total_cols (S pos) count'
  end.

Fixpoint point_witness_projection
    (env_dim: nat) (pw: point_space_witness) : Transformation :=
  match pw with
  | PSWIdentity point_dim =>
      let total_cols := (env_dim + point_dim)%nat in
      firstn env_dim (identity_affine_rows_from total_cols 0 total_cols) ++
      identity_affine_rows_from total_cols env_dim point_dim
  | PSWTiling w =>
      let total_cols := (env_dim + witness_current_point_dim (PSWTiling w))%nat in
      firstn env_dim (identity_affine_rows_from total_cols 0 total_cols) ++
      identity_affine_rows_from
        total_cols
        (env_dim + witness_added_dims (PSWTiling w))%nat
        (witness_base_point_dim (PSWTiling w))
  | PSWInsertAfterEnv added_dim inner =>
      map (fun '(coeffs, rhs) =>
             (resize env_dim coeffs ++ repeat 0%Z added_dim ++ skipn env_dim coeffs, rhs))
          (point_witness_projection env_dim inner)
  | PSWInsertAtEnd added_dim inner =>
      map (fun '(coeffs, rhs) =>
             (resize (length coeffs + added_dim) coeffs, rhs))
          (point_witness_projection env_dim inner)
  end.

Fixpoint projected_base_point_of_current
    (env: list Z) (pw: point_space_witness) (current: list Z) : list Z :=
  match pw with
  | PSWIdentity _ =>
      firstn (length env) current ++ skipn (length env) current
  | PSWTiling _ =>
      firstn (length env) current ++
      skipn (length env + witness_added_dims pw)%nat current
  | PSWInsertAfterEnv added_dim inner =>
      projected_base_point_of_current
        env
        inner
        (firstn (length env) current ++
         skipn (length env + added_dim)%nat current)
  | PSWInsertAtEnd added_dim inner =>
      projected_base_point_of_current
        env
        inner
        (firstn (length current - added_dim)%nat current)
  end.

Definition related_by_point_witness (env: list Z)
  (pw: point_space_witness) (base current: list Z) : Prop :=
  projected_base_point_of_current env pw current = base /\
  length base = (length env + witness_base_point_dim pw)%nat /\
  length current = (length env + witness_current_point_dim pw)%nat.

Definition project_base_point (env: list Z) (pw: point_space_witness)
    (base current: list Z) : Prop :=
  related_by_point_witness env pw base current.

Definition src_args_of
    (tf: Transformation)
    (base: list Z) : list Z :=
  affine_product tf base.

Definition acc_args_of_tiled
    (pw: point_space_witness)
    (env base current: list Z) : Prop :=
  related_by_point_witness env pw base current.

Definition related_src_acc_by_witness
    (env: list Z)
    (pw: point_space_witness)
    (tf: Transformation)
    (src_args current: list Z) : Prop :=
  exists base,
    related_by_point_witness env pw base current /\
    src_args = src_args_of tf base.

Lemma projected_base_point_of_current_identity :
  forall env point_dim current,
    List.length current = (length env + point_dim)%nat ->
    projected_base_point_of_current env (PSWIdentity point_dim) current = current.
Proof.
  intros env point_dim current Hlen.
  unfold projected_base_point_of_current; simpl.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma projected_base_point_of_current_eval_tiled :
  forall env w point params,
    projected_base_point_of_current
      env
      (PSWTiling w)
      (eval_statement_tiling_witness_with_env env w point params) =
    env ++ point.
Proof.
  intros env w point params.
  pose proof (eval_tile_links_length [] point params (stw_links w)) as Hlen_links.
  unfold projected_base_point_of_current.
  unfold eval_statement_tiling_witness_with_env, eval_statement_tiling_witness, lift_point.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  rewrite skipn_app.
  rewrite skipn_all2.
  2:{ lia. }
  simpl.
  replace ((length env + length (stw_links w) - length env)%nat)
    with (length (stw_links w)) by lia.
  rewrite skipn_app.
  rewrite <- Hlen_links at 1.
  rewrite skipn_all.
  rewrite Hlen_links.
  rewrite Nat.sub_diag.
  simpl.
  reflexivity.
Qed.

Lemma related_by_point_witness_projects :
  forall env pw base current,
    related_by_point_witness env pw base current ->
    projected_base_point_of_current env pw current = base.
Proof.
  intros env pw base current [Hproj _].
  exact Hproj.
Qed.

Lemma related_by_point_witness_base_length :
  forall env pw base current,
    related_by_point_witness env pw base current ->
    length base = (length env + witness_base_point_dim pw)%nat.
Proof.
  intros env pw base current [_ [Hlen _]].
  exact Hlen.
Qed.

Lemma related_by_point_witness_current_length :
  forall env pw base current,
    related_by_point_witness env pw base current ->
    length current = (length env + witness_current_point_dim pw)%nat.
Proof.
  intros env pw base current [_ [_ Hlen]].
  exact Hlen.
Qed.

Lemma related_by_point_witness_src_args :
  forall env pw tf base current,
    related_by_point_witness env pw base current ->
    src_args_of tf (projected_base_point_of_current env pw current) =
    src_args_of tf base.
Proof.
  intros env pw tf base current Hrel.
  unfold src_args_of.
  rewrite related_by_point_witness_projects with (base := base); auto.
Qed.

Lemma list_Z_eqb_eq :
  forall xs ys,
    list_Z_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys H.
  - destruct ys; simpl in *; congruence.
  - destruct ys as [|y ys]; simpl in *; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hxy Htl].
    apply Z.eqb_eq in Hxy.
    apply IH in Htl.
    subst. reflexivity.
Qed.

Lemma affine_expr_eqb_eq :
  forall e1 e2,
    affine_expr_eqb e1 e2 = true ->
    e1 = e2.
Proof.
  intros [v1 p1 c1] [v2 p2 c2] H.
  unfold affine_expr_eqb in H.
  simpl in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[Hv Hp] Hc].
  apply list_Z_eqb_eq in Hv.
  apply list_Z_eqb_eq in Hp.
  apply Z.eqb_eq in Hc.
  subst. reflexivity.
Qed.

Lemma tile_link_eqb_eq :
  forall l1 l2,
    tile_link_eqb l1 l2 = true ->
    l1 = l2.
Proof.
  intros [e1 t1] [e2 t2] H.
  unfold tile_link_eqb in H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H as [He Ht].
  apply affine_expr_eqb_eq in He.
  apply Z.eqb_eq in Ht.
  subst. reflexivity.
Qed.

Lemma tile_link_list_eqb_eq :
  forall ls1 ls2,
    tile_link_list_eqb ls1 ls2 = true ->
    ls1 = ls2.
Proof.
  induction ls1 as [|l1 ls1 IH]; intros ls2 H.
  - destruct ls2; simpl in *; congruence.
  - destruct ls2 as [|l2 ls2]; simpl in *; try discriminate.
    apply andb_true_iff in H.
    destruct H as [Hhd Htl].
    apply tile_link_eqb_eq in Hhd.
    apply IH in Htl.
    subst. reflexivity.
Qed.

Lemma statement_tiling_witness_eqb_eq :
  forall w1 w2,
    statement_tiling_witness_eqb w1 w2 = true ->
    w1 = w2.
Proof.
  intros [d1 ls1] [d2 ls2] H.
  unfold statement_tiling_witness_eqb in H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H as [Hd Hls].
  apply Nat.eqb_eq in Hd.
  apply tile_link_list_eqb_eq in Hls.
  subst. reflexivity.
Qed.

Lemma point_space_witness_eqb_eq :
  forall pw1 pw2,
    point_space_witness_eqb pw1 pw2 = true ->
    pw1 = pw2.
Proof.
  induction pw1 as [d1|w1|added1 inner1 IH|added1 inner1 IH]; intros pw2 H;
    destruct pw2; simpl in H; try discriminate.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply statement_tiling_witness_eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H.
    destruct H as [Hd Hinner].
    apply Nat.eqb_eq in Hd.
    apply IH in Hinner.
    subst. reflexivity.
  - apply andb_true_iff in H.
    destruct H as [Hd Hinner].
    apply Nat.eqb_eq in Hd.
    apply IH in Hinner.
    subst. reflexivity.
Qed.
