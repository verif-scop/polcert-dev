Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Record affine_expr := {
  ae_var_coeffs : list Z;
  ae_param_coeffs : list Z;
  ae_const : Z;
}.

Fixpoint dot_product (xs ys: list Z) : Z :=
  match xs, ys with
  | x :: xs', y :: ys' => x * y + dot_product xs' ys'
  | _, _ => 0
  end.

Definition eval_affine (expr: affine_expr) (vars params: list Z) : Z :=
  dot_product expr.(ae_var_coeffs) vars +
  dot_product expr.(ae_param_coeffs) params +
  expr.(ae_const).

Definition affine_row_holds (row: affine_expr) (vars params: list Z) : Prop :=
  0 <= eval_affine row vars params.

Definition insert_zeros_at (added_dims env_size: nat) (coeffs: list Z) : list Z :=
  firstn env_size coeffs ++ repeat 0 added_dims ++ skipn env_size coeffs.

Definition lift_base_row (tile_prefix_len: nat) (row: affine_expr) : affine_expr :=
  {|
    ae_var_coeffs := repeat 0 tile_prefix_len ++ row.(ae_var_coeffs);
    ae_param_coeffs := row.(ae_param_coeffs);
    ae_const := row.(ae_const);
  |}.

Definition lift_base_row_after_env
    (env_size added_dims: nat) (row: affine_expr) : affine_expr :=
  {|
    ae_var_coeffs := insert_zeros_at added_dims env_size row.(ae_var_coeffs);
    ae_param_coeffs := row.(ae_param_coeffs);
    ae_const := row.(ae_const);
  |}.

Record access_row := {
  ar_output_coeffs : list Z;
  ar_input_coeffs : list Z;
  ar_param_coeffs : list Z;
  ar_const : Z;
}.

Definition eval_access_row
    (row: access_row) (outputs inputs params: list Z) : Z :=
  dot_product row.(ar_output_coeffs) outputs +
  dot_product row.(ar_input_coeffs) inputs +
  dot_product row.(ar_param_coeffs) params +
  row.(ar_const).

Definition access_row_holds
    (row: access_row) (outputs inputs params: list Z) : Prop :=
  0 <= eval_access_row row outputs inputs params.

Definition lift_access_row (tile_prefix_len: nat) (row: access_row) : access_row :=
  {|
    ar_output_coeffs := row.(ar_output_coeffs);
    ar_input_coeffs := repeat 0 tile_prefix_len ++ row.(ar_input_coeffs);
    ar_param_coeffs := row.(ar_param_coeffs);
    ar_const := row.(ar_const);
  |}.

Definition lift_access_row_after_env
    (env_size added_dims: nat) (row: access_row) : access_row :=
  {|
    ar_output_coeffs := row.(ar_output_coeffs);
    ar_input_coeffs := insert_zeros_at added_dims env_size row.(ar_input_coeffs);
    ar_param_coeffs := row.(ar_param_coeffs);
    ar_const := row.(ar_const);
  |}.

Record tile_link := {
  tl_expr : affine_expr;
  tl_tile_size : Z;
}.

Record tile_trace_step := {
  tts_link : tile_link;
  tts_env : list Z;
  tts_parent : Z;
}.

Record statement_tiling_witness := {
  stw_point_dim : nat;
  stw_links : list tile_link;
}.

Definition eval_tile_parent (link: tile_link) (vars params: list Z) : Z :=
  Z.div (eval_affine link.(tl_expr) vars params) link.(tl_tile_size).

Definition tile_link_interval_holds (link: tile_link) (vars params: list Z) (parent: Z) : Prop :=
  tl_tile_size link * parent <= eval_affine (tl_expr link) vars params <
  tl_tile_size link * (parent + 1).

Definition lower_link_row_value (link: tile_link) (vars params: list Z) (parent: Z) : Z :=
  eval_affine (tl_expr link) vars params - tl_tile_size link * parent.

Definition upper_link_row_value (link: tile_link) (vars params: list Z) (parent: Z) : Z :=
  tl_tile_size link * (parent + 1) - 1 - eval_affine (tl_expr link) vars params.

Definition lower_link_row_holds (link: tile_link) (vars params: list Z) (parent: Z) : Prop :=
  0 <= lower_link_row_value link vars params parent.

Definition upper_link_row_holds (link: tile_link) (vars params: list Z) (parent: Z) : Prop :=
  0 <= upper_link_row_value link vars params parent.

Lemma eval_tile_parent_interval:
  forall link vars params,
    0 < tl_tile_size link ->
    tile_link_interval_holds link vars params (eval_tile_parent link vars params).
Proof.
  intros link vars params Hsize.
  unfold tile_link_interval_holds, eval_tile_parent.
  set (value := eval_affine (tl_expr link) vars params).
  assert (Hdiv: value = tl_tile_size link * (value / tl_tile_size link) + value mod tl_tile_size link).
  { apply Z_div_mod_eq; lia. }
  assert (Hmod_lo: 0 <= value mod tl_tile_size link).
  { apply Z.mod_pos_bound; lia. }
  assert (Hmod_hi: value mod tl_tile_size link < tl_tile_size link).
  { apply Z.mod_pos_bound; lia. }
  set (q := value / tl_tile_size link).
  set (r := value mod tl_tile_size link).
  split.
  - rewrite Hdiv. unfold q, r. lia.
  - rewrite Hdiv. unfold q, r. lia.
Qed.

Lemma interval_implies_lower_link_row:
  forall link vars params parent,
    tile_link_interval_holds link vars params parent ->
    lower_link_row_holds link vars params parent.
Proof.
  intros link vars params parent Hinterval.
  unfold tile_link_interval_holds, lower_link_row_holds, lower_link_row_value in *.
  lia.
Qed.

Lemma interval_implies_upper_link_row:
  forall link vars params parent,
    tile_link_interval_holds link vars params parent ->
    upper_link_row_holds link vars params parent.
Proof.
  intros link vars params parent Hinterval.
  unfold tile_link_interval_holds, upper_link_row_holds, upper_link_row_value in *.
  lia.
Qed.

Lemma lower_upper_rows_imply_interval:
  forall link vars params parent,
    lower_link_row_holds link vars params parent ->
    upper_link_row_holds link vars params parent ->
    tile_link_interval_holds link vars params parent.
Proof.
  intros link vars params parent Hlower Hupper.
  unfold lower_link_row_holds, lower_link_row_value in Hlower.
  unfold upper_link_row_holds, upper_link_row_value in Hupper.
  unfold tile_link_interval_holds.
  lia.
Qed.

Lemma tile_link_interval_unique:
  forall link vars params parent1 parent2,
    0 < tl_tile_size link ->
    tile_link_interval_holds link vars params parent1 ->
    tile_link_interval_holds link vars params parent2 ->
    parent1 = parent2.
Proof.
  intros link vars params parent1 parent2 Hsize Hint1 Hint2.
  unfold tile_link_interval_holds in *.
  nia.
Qed.

Lemma lower_upper_rows_imply_eval_tile_parent:
  forall link vars params parent,
    0 < tl_tile_size link ->
    lower_link_row_holds link vars params parent ->
    upper_link_row_holds link vars params parent ->
    parent = eval_tile_parent link vars params.
Proof.
  intros link vars params parent Hsize Hlower Hupper.
  apply tile_link_interval_unique with (link := link) (vars := vars) (params := params).
  - exact Hsize.
  - apply lower_upper_rows_imply_interval; assumption.
  - apply eval_tile_parent_interval; assumption.
Qed.

Fixpoint eval_tile_links (prefix point params: list Z) (links: list tile_link) : list Z :=
  match links with
  | [] => prefix
  | link :: links' =>
      let env := prefix ++ point in
      let tile := eval_tile_parent link env params in
      eval_tile_links (prefix ++ [tile]) point params links'
  end.

Fixpoint eval_tile_trace (prefix point params: list Z) (links: list tile_link) : list tile_trace_step :=
  match links with
  | [] => []
  | link :: links' =>
      let env := prefix ++ point in
      let tile := eval_tile_parent link env params in
      {| tts_link := link; tts_env := env; tts_parent := tile |} ::
      eval_tile_trace (prefix ++ [tile]) point params links'
  end.

Definition lift_point (point params: list Z) (links: list tile_link) : list Z :=
  eval_tile_links [] point params links ++ point.

Fixpoint well_formed_tile_links (prefix_dim point_dim: nat) (links: list tile_link) : Prop :=
  match links with
  | [] => True
  | link :: links' =>
      length (ae_var_coeffs (tl_expr link)) = (prefix_dim + point_dim)%nat /\
      well_formed_tile_links (S prefix_dim) point_dim links'
  end.

Definition well_formed_statement_tiling_witness (w: statement_tiling_witness) : Prop :=
  well_formed_tile_links 0 w.(stw_point_dim) w.(stw_links).

Definition eval_statement_tiling_witness
    (w: statement_tiling_witness) (point params: list Z) : list Z :=
  lift_point point params w.(stw_links).

Lemma eval_tile_links_length:
  forall prefix point params links,
    length (eval_tile_links prefix point params links) = (length prefix + length links)%nat.
Proof.
  intros prefix point params links.
  revert prefix point params.
  induction links as [|link links IH]; intros prefix point params; simpl.
  - lia.
  - rewrite IH. rewrite app_length. simpl. lia.
Qed.

Lemma dot_product_repeat_zero_app:
  forall n prefix suffix coeffs,
    length prefix = n ->
    dot_product (repeat 0 n ++ coeffs) (prefix ++ suffix) = dot_product coeffs suffix.
Proof.
  intros n prefix.
  revert n.
  induction prefix as [|x prefix IH]; intros n suffix coeffs Hlen.
  - destruct n; simpl in *.
    + reflexivity.
    + discriminate.
  - destruct n; simpl in *.
    + discriminate.
    + inversion Hlen as [Hlen']; subst n.
      simpl.
      exact (IH (length prefix) suffix coeffs eq_refl).
Qed.

Lemma dot_product_app_exact:
  forall xs1 xs2 ys1 ys2,
    length xs1 = length ys1 ->
    dot_product (xs1 ++ xs2) (ys1 ++ ys2) =
    dot_product xs1 ys1 + dot_product xs2 ys2.
Proof.
  induction xs1 as [|x xs1 IH]; intros xs2 ys1 ys2 Hlen.
  - destruct ys1; simpl in *; [lia|discriminate].
  - destruct ys1 as [|y ys1]; simpl in *; [discriminate|].
    inversion Hlen as [Hlen'].
    simpl.
    rewrite IH by exact Hlen'.
    lia.
Qed.

Lemma dot_product_cons_singleton:
  forall x xs y ys,
    dot_product (x :: xs) (y :: ys) =
    dot_product [x] [y] + dot_product xs ys.
Proof.
  intros.
  simpl.
  lia.
Qed.

Lemma dot_product_split_firstn_skipn:
  forall coeffs prefix point,
    length coeffs = (length prefix + length point)%nat ->
    dot_product coeffs (prefix ++ point) =
    dot_product (firstn (length prefix) coeffs) prefix +
    dot_product (skipn (length prefix) coeffs) point.
Proof.
  intros coeffs prefix point Hlen.
  assert (Hpre:
    length (firstn (length prefix) coeffs) = length prefix).
  { rewrite firstn_length. lia. }
  rewrite <- (firstn_skipn (length prefix) coeffs) at 1.
  apply dot_product_app_exact.
  exact Hpre.
Qed.

Lemma dot_product_repeat_zero_exact:
  forall n ys,
    length ys = n ->
    dot_product (repeat 0 n) ys = 0.
Proof.
  intros n ys.
  revert n.
  induction ys as [|y ys IH]; intros m Hlen.
  - destruct m; simpl in *; lia.
  - destruct m; simpl in *; [discriminate|].
    inversion Hlen as [Hlen']; subst m.
    simpl.
    rewrite IH by reflexivity.
    lia.
Qed.

Lemma dot_product_insert_zeros_at:
  forall coeffs env middle tail env_size added_dims,
    length env = env_size ->
    length middle = added_dims ->
    (env_size <= length coeffs)%nat ->
    dot_product (insert_zeros_at added_dims env_size coeffs) (env ++ middle ++ tail) =
    dot_product coeffs (env ++ tail).
Proof.
  intros coeffs env middle tail env_size added_dims Henv Hmid Hcoeff.
  unfold insert_zeros_at.
  assert (Hfirstlen: length (firstn env_size coeffs) = env_size).
  { rewrite firstn_length. lia. }
  replace (firstn env_size coeffs ++ repeat 0 added_dims ++ skipn env_size coeffs)
    with ((firstn env_size coeffs ++ repeat 0 added_dims) ++ skipn env_size coeffs)
    by now rewrite app_assoc.
  replace (env ++ middle ++ tail) with ((env ++ middle) ++ tail)
    by now rewrite app_assoc.
  rewrite dot_product_app_exact
    with (xs1 := firstn env_size coeffs ++ repeat 0 added_dims)
         (ys1 := env ++ middle)
         (xs2 := skipn env_size coeffs)
         (ys2 := tail).
  2:{
    rewrite !app_length, Hfirstlen, repeat_length, Henv, Hmid.
    lia.
  }
  rewrite dot_product_app_exact
    with (xs1 := firstn env_size coeffs)
         (ys1 := env)
         (xs2 := repeat 0 added_dims)
         (ys2 := middle).
  2:{
    rewrite Hfirstlen, Henv.
    reflexivity.
  }
  rewrite dot_product_repeat_zero_exact by exact Hmid.
  assert (Hsplit:
    dot_product coeffs (env ++ tail) =
    dot_product (firstn env_size coeffs) env +
    dot_product (skipn env_size coeffs) tail).
  {
    rewrite <- (firstn_skipn env_size coeffs) at 1.
    rewrite dot_product_app_exact
      with (xs1 := firstn env_size coeffs)
           (ys1 := env)
           (xs2 := skipn env_size coeffs)
           (ys2 := tail).
    2:{
      rewrite Hfirstlen, Henv.
      reflexivity.
    }
    reflexivity.
  }
  rewrite Hsplit.
  lia.
Qed.

Lemma eval_lift_base_row:
  forall prefix point params row,
    eval_affine (lift_base_row (length prefix) row) (prefix ++ point) params =
    eval_affine row point params.
Proof.
  intros prefix point params row.
  unfold eval_affine, lift_base_row.
  simpl.
  rewrite dot_product_repeat_zero_app with (prefix := prefix) (suffix := point) (coeffs := ae_var_coeffs row).
  - lia.
  - reflexivity.
Qed.

Lemma lift_base_row_sound:
  forall prefix point params row,
    affine_row_holds row point params ->
    affine_row_holds (lift_base_row (length prefix) row) (prefix ++ point) params.
Proof.
  intros prefix point params row Hrow.
  unfold affine_row_holds in *.
  rewrite eval_lift_base_row.
  exact Hrow.
Qed.

Lemma eval_lift_access_row:
  forall prefix outputs point params row,
    eval_access_row (lift_access_row (length prefix) row) outputs (prefix ++ point) params =
    eval_access_row row outputs point params.
Proof.
  intros prefix outputs point params row.
  unfold eval_access_row, lift_access_row.
  simpl.
  rewrite dot_product_repeat_zero_app with (prefix := prefix) (suffix := point) (coeffs := ar_input_coeffs row).
  - lia.
  - reflexivity.
Qed.

Lemma lift_access_row_sound:
  forall prefix outputs point params row,
    access_row_holds row outputs point params ->
    access_row_holds (lift_access_row (length prefix) row) outputs (prefix ++ point) params.
Proof.
  intros prefix outputs point params row Hrow.
  unfold access_row_holds in *.
  rewrite eval_lift_access_row.
  exact Hrow.
Qed.

Lemma lift_point_suffix:
  forall point params links,
    skipn (length links) (lift_point point params links) = point.
Proof.
  intros point params links.
  unfold lift_point.
  remember (eval_tile_links [] point params links) as tiles eqn:Htiles.
  assert (Hlen: length tiles = length links).
  { subst tiles. rewrite eval_tile_links_length. simpl. reflexivity. }
  rewrite <- Hlen.
  rewrite skipn_app.
  rewrite Nat.sub_diag.
  rewrite skipn_all.
  simpl.
  reflexivity.
Qed.

Lemma eval_tile_trace_sound:
  forall prefix point params links step,
    In step (eval_tile_trace prefix point params links) ->
    0 < tl_tile_size (tts_link step) ->
    tile_link_interval_holds (tts_link step) (tts_env step) params (tts_parent step).
Proof.
  intros prefix point params links.
  revert prefix point params.
  induction links as [|link links IH]; intros prefix point params step Hin Hsize; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl.
      apply eval_tile_parent_interval; assumption.
    + apply IH with (prefix := prefix ++ [eval_tile_parent link (prefix ++ point) params])
                    (point := point) (params := params) (step := step) in Hin; auto.
Qed.

Definition tile_trace_step_rows_hold (step: tile_trace_step) (params: list Z) : Prop :=
  lower_link_row_holds (tts_link step) (tts_env step) params (tts_parent step) /\
  upper_link_row_holds (tts_link step) (tts_env step) params (tts_parent step).

Fixpoint tile_trace_rows_hold (trace: list tile_trace_step) (params: list Z) : Prop :=
  match trace with
  | [] => True
  | step :: trace' =>
      tile_trace_step_rows_hold step params /\ tile_trace_rows_hold trace' params
  end.

Lemma eval_tile_trace_rows_hold:
  forall prefix point params links,
    (forall link, In link links -> 0 < tl_tile_size link) ->
    tile_trace_rows_hold (eval_tile_trace prefix point params links) params.
Proof.
  intros prefix point params links.
  revert prefix point params.
  induction links as [|link links IH]; intros prefix point params Hsizes; simpl.
  - exact I.
  - split.
    + unfold tile_trace_step_rows_hold.
      split.
      * apply interval_implies_lower_link_row.
        apply eval_tile_parent_interval.
        apply Hsizes. simpl. auto.
      * apply interval_implies_upper_link_row.
        apply eval_tile_parent_interval.
        apply Hsizes. simpl. auto.
    + apply IH.
      intros link' Hin.
      apply Hsizes.
      simpl. auto.
Qed.

Lemma eval_statement_tiling_witness_suffix:
  forall w point params,
    skipn (length w.(stw_links)) (eval_statement_tiling_witness w point params) = point.
Proof.
  intros. unfold eval_statement_tiling_witness.
  apply lift_point_suffix.
Qed.

Definition statement_tiling_rows_hold
    (w: statement_tiling_witness) (point params: list Z) : Prop :=
  tile_trace_rows_hold (eval_tile_trace [] point params w.(stw_links)) params.

Lemma eval_statement_tiling_rows_hold:
  forall w point params,
    (forall link, In link w.(stw_links) -> 0 < tl_tile_size link) ->
    statement_tiling_rows_hold w point params.
Proof.
  intros w point params Hsizes.
  unfold statement_tiling_rows_hold.
  apply eval_tile_trace_rows_hold.
  exact Hsizes.
Qed.

Lemma eval_statement_tiling_base_row_sound:
  forall w row point params,
    affine_row_holds row point params ->
    affine_row_holds
      (lift_base_row (length w.(stw_links)) row)
      (eval_statement_tiling_witness w point params)
      params.
Proof.
  intros w row point params Hrow.
  unfold eval_statement_tiling_witness, lift_point.
  replace (length (stw_links w)) with (length (eval_tile_links [] point params (stw_links w))).
  2:{
    rewrite eval_tile_links_length.
    simpl.
    reflexivity.
  }
  apply lift_base_row_sound.
  exact Hrow.
Qed.

Lemma eval_statement_tiling_access_row_sound:
  forall w row outputs point params,
    access_row_holds row outputs point params ->
    access_row_holds
      (lift_access_row (length w.(stw_links)) row)
      outputs
      (eval_statement_tiling_witness w point params)
      params.
Proof.
  intros w row outputs point params Hrow.
  unfold eval_statement_tiling_witness, lift_point.
  replace (length (stw_links w)) with (length (eval_tile_links [] point params (stw_links w))).
  2:{
    rewrite eval_tile_links_length.
    simpl.
    reflexivity.
  }
  apply lift_access_row_sound.
  exact Hrow.
Qed.

Lemma eval_statement_tiling_base_rows_sound:
  forall w rows point params,
    Forall (fun row => affine_row_holds row point params) rows ->
    Forall
      (fun row =>
         affine_row_holds row (eval_statement_tiling_witness w point params) params)
      (map (lift_base_row (length w.(stw_links))) rows).
Proof.
  intros w rows point params Hrows.
  induction Hrows as [|row rows Hrow Hrows IH]; simpl.
  - constructor.
  - constructor.
    + apply eval_statement_tiling_base_row_sound.
      exact Hrow.
    + exact IH.
Qed.

Lemma eval_statement_tiling_access_rows_sound:
  forall w rows outputs point params,
    Forall (fun row => access_row_holds row outputs point params) rows ->
    Forall
      (fun row =>
         access_row_holds row outputs (eval_statement_tiling_witness w point params) params)
      (map (lift_access_row (length w.(stw_links))) rows).
Proof.
  intros w rows outputs point params Hrows.
  induction Hrows as [|row rows Hrow Hrows IH]; simpl.
  - constructor.
  - constructor.
    + apply eval_statement_tiling_access_row_sound.
      exact Hrow.
    + exact IH.
Qed.

Theorem statement_tiling_core_sound:
  forall w base_rows access_rows outputs point params,
    (forall link, In link w.(stw_links) -> 0 < tl_tile_size link) ->
    Forall (fun row => affine_row_holds row point params) base_rows ->
    Forall (fun row => access_row_holds row outputs point params) access_rows ->
    statement_tiling_rows_hold w point params /\
    Forall
      (fun row =>
         affine_row_holds row (eval_statement_tiling_witness w point params) params)
      (map (lift_base_row (length w.(stw_links))) base_rows) /\
    Forall
      (fun row =>
         access_row_holds row outputs (eval_statement_tiling_witness w point params) params)
      (map (lift_access_row (length w.(stw_links))) access_rows).
Proof.
  intros w base_rows access_rows outputs point params Hsizes Hbase Haccess.
  split.
  - apply eval_statement_tiling_rows_hold.
    exact Hsizes.
  - split.
    + apply eval_statement_tiling_base_rows_sound.
      exact Hbase.
    + apply eval_statement_tiling_access_rows_sound.
      exact Haccess.
Qed.

Definition eval_statement_tiling_witness_with_env
    (env: list Z) (w: statement_tiling_witness) (point params: list Z) : list Z :=
  env ++ eval_statement_tiling_witness w point params.

Lemma eval_lift_base_row_after_env:
  forall env w row point params,
    (length env <= length (ae_var_coeffs row))%nat ->
    eval_affine
      (lift_base_row_after_env (length env) (length w.(stw_links)) row)
      (eval_statement_tiling_witness_with_env env w point params)
      params =
    eval_affine row (env ++ point) params.
Proof.
  intros env w row point params Henv.
  unfold eval_affine, lift_base_row_after_env, eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness, lift_point.
  simpl.
  rewrite dot_product_insert_zeros_at
    with (env := env)
         (middle := eval_tile_links [] point params (stw_links w))
         (tail := point)
         (env_size := length env)
         (added_dims := length (stw_links w)).
  - lia.
  - reflexivity.
  - rewrite eval_tile_links_length. simpl. reflexivity.
  - exact Henv.
Qed.

Lemma lift_base_row_after_env_sound:
  forall env w row point params,
    (length env <= length (ae_var_coeffs row))%nat ->
    affine_row_holds row (env ++ point) params ->
    affine_row_holds
      (lift_base_row_after_env (length env) (length w.(stw_links)) row)
      (eval_statement_tiling_witness_with_env env w point params)
      params.
Proof.
  intros env w row point params Henv Hrow.
  unfold affine_row_holds in *.
  rewrite eval_lift_base_row_after_env by exact Henv.
  exact Hrow.
Qed.

Lemma eval_lift_access_row_after_env:
  forall env w row outputs point params,
    (length env <= length (ar_input_coeffs row))%nat ->
    eval_access_row
      (lift_access_row_after_env (length env) (length w.(stw_links)) row)
      outputs
      (eval_statement_tiling_witness_with_env env w point params)
      params =
    eval_access_row row outputs (env ++ point) params.
Proof.
  intros env w row outputs point params Henv.
  unfold eval_access_row, lift_access_row_after_env, eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness, lift_point.
  simpl.
  rewrite dot_product_insert_zeros_at
    with (env := env)
         (middle := eval_tile_links [] point params (stw_links w))
         (tail := point)
         (env_size := length env)
         (added_dims := length (stw_links w)).
  - lia.
  - reflexivity.
  - rewrite eval_tile_links_length. simpl. reflexivity.
  - exact Henv.
Qed.

Lemma lift_access_row_after_env_sound:
  forall env w row outputs point params,
    (length env <= length (ar_input_coeffs row))%nat ->
    access_row_holds row outputs (env ++ point) params ->
    access_row_holds
      (lift_access_row_after_env (length env) (length w.(stw_links)) row)
      outputs
      (eval_statement_tiling_witness_with_env env w point params)
      params.
Proof.
  intros env w row outputs point params Henv Hrow.
  unfold access_row_holds in *.
  rewrite eval_lift_access_row_after_env by exact Henv.
  exact Hrow.
Qed.
