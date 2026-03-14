Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Lia.
Require Import Sorting.Sorted.
Require Import Sorting.Permutation.
Require Import SetoidList.
Require Import SelectionSort.
Import ListNotations.

Require Import PolyBase.
Require Import PolyLang.
Require Import PointWitness.
Require Import TilingWitness.
Require Import TilingList.
Require Import InstrTy.
Require Import Linalg.
Require Import LinalgExt.
Require Import Misc.
Require Import Base.

Module TilingRelation (Instr: INSTR).

Module PL := PolyLang Instr.

Definition lift_constraint_after_env
    (added_dims env_size: nat) (c: list Z * Z) : list Z * Z :=
  PL.insert_zeros_constraint added_dims env_size c.

Definition lift_affine_function_after_env
    (added_dims env_size: nat) (f: AffineFunction) : AffineFunction :=
  List.map (lift_constraint_after_env added_dims env_size) f.

Definition identity_affine_row
    (total_cols pos: nat) : list Z * Z :=
  (repeat 0%Z pos ++ [1%Z] ++ repeat 0%Z (total_cols - pos - 1), 0%Z).

Fixpoint identity_affine_rows_from
    (total_cols pos count: nat) : AffineFunction :=
  match count with
  | O => []
  | S count' =>
      identity_affine_row total_cols pos ::
      identity_affine_rows_from total_cols (S pos) count'
  end.

Definition pad_transformation_after_env
    (added_dims env_size: nat) (f: AffineFunction) : AffineFunction :=
  let lifted := lift_affine_function_after_env added_dims env_size f in
  let total_cols :=
    match lifted with
    | [] => (env_size + added_dims)%nat
    | (coeffs, _) :: _ => List.length coeffs
    end in
  firstn env_size lifted ++
  identity_affine_rows_from total_cols env_size added_dims ++
  skipn env_size lifted.

Definition lift_access_after_env
    (added_dims env_size: nat) (a: AccessFunction) : AccessFunction :=
  let '(arr, aff) := a in
  (arr, lift_affine_function_after_env added_dims env_size aff).

Definition lift_schedule_after_env
    (added_dims env_size: nat) (s: Schedule) : Schedule :=
  lift_affine_function_after_env added_dims env_size s.

Record pinstr_tiling_witness := {
  ptw_added_dims : nat;
  ptw_statement_witness : statement_tiling_witness;
  ptw_link_domain : Domain;
}.

Definition wf_pinstr_tiling_witness (w: pinstr_tiling_witness) : Prop :=
  ptw_added_dims w = List.length (stw_links (ptw_statement_witness w)).

Definition wf_statement_tiling_witness_with_param_dim
    (param_dim: nat) (w: statement_tiling_witness) : Prop :=
  well_formed_statement_tiling_witness w /\
  Forall
    (fun link =>
       List.length (ae_param_coeffs (tl_expr link)) = param_dim)
    (stw_links w).

Lemma app_singleton_cons :
  forall (xs: list Z) (x: Z) (ys: list Z),
    xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  intros xs x ys.
  induction xs as [|h xs IH]; simpl.
  - reflexivity.
  - f_equal.
    exact IH.
Qed.

Lemma NoDup_map_on :
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

Lemma Forall_nth_error :
  forall (A: Type) (P: A -> Prop) xs n x0,
    Forall P xs ->
    List.nth_error xs n = Some x0 ->
    P x0.
Proof.
  intros A P xs n x0 Hforall Hnth.
  eapply Forall_forall.
  - exact Hforall.
  - eapply nth_error_In; eauto.
Qed.

Lemma Forall2_nth_error :
  forall (A B: Type) (P: A -> B -> Prop) xs ys n x0 y0,
    Forall2 P xs ys ->
    List.nth_error xs n = Some x0 ->
    List.nth_error ys n = Some y0 ->
    P x0 y0.
Proof.
  intros A B P xs ys n x0 y0 Hforall2.
  revert n x0 y0.
  induction Hforall2; intros n x0 y0 Hnthx Hnthy.
  - destruct n; inversion Hnthx.
  - destruct n.
    + simpl in *.
      inversion Hnthx; inversion Hnthy; subst; assumption.
    + simpl in *.
      eapply IHHforall2; eauto.
Qed.

Lemma nth_error_map_some :
  forall (A B: Type) (f: A -> B) xs n x,
    List.nth_error xs n = Some x ->
    List.nth_error (List.map f xs) n = Some (f x).
Proof.
  intros A B f xs.
  induction xs as [|xhd xtl IH]; intros n x Hnth.
  - destruct n; inversion Hnth.
  - destruct n.
    + simpl in *. inversion Hnth. reflexivity.
    + simpl in *. eapply IH; eauto.
Qed.

Definition eval_pinstr_tiling_index_with_env
    (env point params: list Z) (w: pinstr_tiling_witness) : list Z :=
  eval_statement_tiling_witness_with_env env (ptw_statement_witness w) point params.

Definition compile_ge_affine_row_to_constraint (row: affine_expr) : constraint :=
  (mult_vector (-1) (ae_param_coeffs row ++ ae_var_coeffs row), ae_const row).

Definition lower_link_affine_row_after_env
    (prefix_len suffix_len: nat) (link: tile_link) : affine_expr :=
  {|
    ae_var_coeffs :=
      firstn prefix_len (ae_var_coeffs (tl_expr link)) ++
      [-(tl_tile_size link)] ++
      repeat 0 suffix_len ++
      skipn prefix_len (ae_var_coeffs (tl_expr link));
    ae_param_coeffs := ae_param_coeffs (tl_expr link);
    ae_const := ae_const (tl_expr link);
  |}.

Definition upper_link_affine_row_after_env
    (prefix_len suffix_len: nat) (link: tile_link) : affine_expr :=
  {|
    ae_var_coeffs :=
      mult_vector (-1) (firstn prefix_len (ae_var_coeffs (tl_expr link))) ++
      [tl_tile_size link] ++
      repeat 0 suffix_len ++
      mult_vector (-1) (skipn prefix_len (ae_var_coeffs (tl_expr link)));
    ae_param_coeffs := mult_vector (-1) (ae_param_coeffs (tl_expr link));
    ae_const := tl_tile_size link - 1 - ae_const (tl_expr link);
  |}.

Definition lower_link_constraint_after_env
    (prefix_len suffix_len: nat) (link: tile_link) : constraint :=
  compile_ge_affine_row_to_constraint
    (lower_link_affine_row_after_env prefix_len suffix_len link).

Definition upper_link_constraint_after_env
    (prefix_len suffix_len: nat) (link: tile_link) : constraint :=
  compile_ge_affine_row_to_constraint
    (upper_link_affine_row_after_env prefix_len suffix_len link).

Fixpoint compile_link_domain_after_env_from
    (prefix_len: nat) (links: list tile_link) : Domain :=
  match links with
  | [] => []
  | link :: links' =>
      lower_link_constraint_after_env prefix_len (List.length links') link ::
      upper_link_constraint_after_env prefix_len (List.length links') link ::
      compile_link_domain_after_env_from (S prefix_len) links'
  end.

Definition compile_link_domain_after_env
    (w: statement_tiling_witness) : Domain :=
  compile_link_domain_after_env_from 0 (stw_links w).

Definition lifted_base_domain_after_env
    (env_size: nat) (w: pinstr_tiling_witness) (dom: Domain) : Domain :=
  List.map
    (lift_constraint_after_env (ptw_added_dims w) env_size)
    dom.

Definition lifted_accesses_after_env
    (env_size: nat) (w: pinstr_tiling_witness) (accs: list AccessFunction)
    : list AccessFunction :=
  List.map (lift_access_after_env (ptw_added_dims w) env_size) accs.

Definition tiling_rel_pinstr_structure
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: pinstr_tiling_witness) : Prop :=
  PL.pi_instr after = PL.pi_instr before /\
  PL.pi_depth after = (PL.pi_depth before + ptw_added_dims w)%nat /\
  PL.pi_point_witness after = PSWTiling (ptw_statement_witness w) /\
  PL.pi_transformation after =
    pad_transformation_after_env
      (ptw_added_dims w) env_size (PL.pi_transformation before) /\
  PL.pi_access_transformation after =
    pad_transformation_after_env
      (ptw_added_dims w) env_size (PL.pi_access_transformation before) /\
  PL.pi_poly after =
    ptw_link_domain w ++
    lifted_base_domain_after_env env_size w (PL.pi_poly before) /\
  PL.pi_waccess after =
    lifted_accesses_after_env env_size w (PL.pi_waccess before) /\
  PL.pi_raccess after =
    lifted_accesses_after_env env_size w (PL.pi_raccess before).

Definition tiling_rel_pinstr_structure_source
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: pinstr_tiling_witness) : Prop :=
  PL.pi_instr after = PL.pi_instr before /\
  PL.pi_depth after = (PL.pi_depth before + ptw_added_dims w)%nat /\
  PL.pi_point_witness after = PSWTiling (ptw_statement_witness w) /\
  PL.pi_transformation after =
    PL.pi_transformation before /\
  PL.pi_access_transformation after =
    PL.pi_access_transformation before /\
  PL.pi_poly after =
    ptw_link_domain w ++
    lifted_base_domain_after_env env_size w (PL.pi_poly before) /\
  PL.pi_waccess after =
    PL.pi_waccess before /\
  PL.pi_raccess after =
    PL.pi_raccess before.

Definition source_view_of_tiled_pinstr
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: pinstr_tiling_witness) : PL.PolyInstr := {|
  PL.pi_depth := PL.pi_depth after;
  PL.pi_instr := PL.pi_instr after;
  PL.pi_poly := PL.pi_poly after;
  PL.pi_schedule := PL.pi_schedule after;
  PL.pi_point_witness := PSWTiling (ptw_statement_witness w);
  PL.pi_transformation := PL.pi_transformation before;
  PL.pi_access_transformation := PL.pi_access_transformation before;
  PL.pi_waccess := PL.pi_waccess before;
  PL.pi_raccess := PL.pi_raccess before;
|}.

Fixpoint source_view_of_tiled_pinstrs
    (env_size: nat)
    (before after: list PL.PolyInstr)
    (ws: list pinstr_tiling_witness) : list PL.PolyInstr :=
  match before, after, ws with
  | before_pi :: before', after_pi :: after', w :: ws' =>
      source_view_of_tiled_pinstr env_size before_pi after_pi w ::
      source_view_of_tiled_pinstrs env_size before' after' ws'
  | _, _, _ => []
  end.

Fixpoint tiling_rel_pinstr_list
    (env_size: nat)
    (before after: list PL.PolyInstr)
    (ws: list pinstr_tiling_witness) : Prop :=
  match before, after, ws with
  | [], [], [] => True
  | pi1 :: before', pi2 :: after', w :: ws' =>
      tiling_rel_pinstr_structure env_size pi1 pi2 w /\
      tiling_rel_pinstr_list env_size before' after' ws'
  | _, _, _ => False
  end.

Fixpoint tiling_rel_pinstr_list_source
    (env_size: nat)
    (before after: list PL.PolyInstr)
    (ws: list pinstr_tiling_witness) : Prop :=
  match before, after, ws with
  | [], [], [] => True
  | pi1 :: before', pi2 :: after', w :: ws' =>
      tiling_rel_pinstr_structure_source env_size pi1 pi2 w /\
      tiling_rel_pinstr_list_source env_size before' after' ws'
  | _, _, _ => False
  end.

Definition tiling_rel_pprog_structure
    (before after: PL.t)
    (ws: list pinstr_tiling_witness) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  tiling_rel_pinstr_list (List.length before_ctxt) before_pis after_pis ws.

Definition tiling_rel_pprog_structure_source
    (before after: PL.t)
    (ws: list pinstr_tiling_witness) : Prop :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, after_ctxt, after_vars) := after in
  before_ctxt = after_ctxt /\
  before_vars = after_vars /\
  tiling_rel_pinstr_list_source (List.length before_ctxt) before_pis after_pis ws.

Definition witness_matches_compiled_link_domain
    (w: pinstr_tiling_witness) : Prop :=
  ptw_link_domain w = compile_link_domain_after_env (ptw_statement_witness w).

Definition compiled_pinstr_tiling_witness
    (w: statement_tiling_witness) : pinstr_tiling_witness :=
  {|
    ptw_added_dims := List.length (stw_links w);
    ptw_statement_witness := w;
    ptw_link_domain := compile_link_domain_after_env w;
  |}.

Definition source_view_of_tiled_pprog
    (before after: PL.t)
    (ws: list statement_tiling_witness) : PL.t :=
  let '(before_pis, before_ctxt, before_vars) := before in
  let '(after_pis, _, _) := after in
  (source_view_of_tiled_pinstrs
     (List.length before_ctxt)
     before_pis after_pis
     (List.map compiled_pinstr_tiling_witness ws),
   before_ctxt,
   before_vars).

Definition tiling_rel_pinstr_structure_compiled
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : Prop :=
  tiling_rel_pinstr_structure
    env_size before after (compiled_pinstr_tiling_witness w).

Definition current_src_transformation_of_pinstr
    (env_size: nat) (pi: PL.PolyInstr) : Transformation :=
  PL.current_transformation_at env_size pi.

Definition compose_tiling_pinstr_ext
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : PL.PolyInstr_ext := {|
  PL.pi_depth_ext := PL.pi_depth after;
  PL.pi_instr_ext := PL.pi_instr after;
  PL.pi_poly_ext := PL.pi_poly after;
  PL.pi_point_witness_ext := PL.pi_point_witness after;
  PL.pi_transformation_ext := current_src_transformation_of_pinstr env_size after;
  PL.pi_access_transformation_ext := current_src_transformation_of_pinstr env_size after;
  PL.pi_schedule1_ext :=
    lift_schedule_after_env (List.length (stw_links w)) env_size (PL.pi_schedule before);
  PL.pi_schedule2_ext := PL.pi_schedule after;
  PL.pi_waccess_ext := PL.pi_waccess after;
  PL.pi_raccess_ext := PL.pi_raccess after;
|}.

Definition retiled_old_pinstr
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : PL.PolyInstr := {|
  PL.pi_depth := PL.pi_depth after;
  PL.pi_instr := PL.pi_instr after;
  PL.pi_poly := PL.pi_poly after;
  PL.pi_schedule :=
    lift_schedule_after_env (List.length (stw_links w)) env_size (PL.pi_schedule before);
  PL.pi_point_witness := PSWTiling w;
  PL.pi_transformation := PL.pi_transformation after;
  PL.pi_access_transformation := PL.pi_access_transformation after;
  PL.pi_waccess := PL.pi_waccess after;
  PL.pi_raccess := PL.pi_raccess after;
|}.

Definition compose_tiling_instr_point_ext
    (nth: nat)
    (env point: list Z)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness) : PL.InstrPoint_ext :=
  let index :=
    eval_pinstr_tiling_index_with_env
      env point env (compiled_pinstr_tiling_witness w) in
  let after_tf := current_src_transformation_of_pinstr (List.length env) after in
  {|
    PL.ip_nth_ext := nth;
    PL.ip_index_ext := index;
    PL.ip_transformation_ext := after_tf;
    PL.ip_access_transformation_ext := after_tf;
    PL.ip_time_stamp1_ext :=
      affine_product
        (lift_schedule_after_env (List.length (stw_links w)) (List.length env)
           (PL.pi_schedule before))
        index;
    PL.ip_time_stamp2_ext :=
      affine_product (PL.pi_schedule after) index;
    PL.ip_instruction_ext := PL.pi_instr after;
    PL.ip_depth_ext := PL.pi_depth after;
  |}.

Definition tiling_rel_pprog_structure_compiled
    (before after: PL.t)
    (ws: list statement_tiling_witness) : Prop :=
  tiling_rel_pprog_structure before after (List.map compiled_pinstr_tiling_witness ws).

Lemma tiling_rel_pinstr_list_lengths :
  forall env_size before after ws,
    tiling_rel_pinstr_list env_size before after ws ->
    List.length before = List.length after /\
    List.length after = List.length ws.
Proof.
  induction before as [|before_pi before']; intros after ws Hrel;
    destruct after as [|after_pi after']; destruct ws as [|w ws'];
    simpl in Hrel; try contradiction.
  - split; reflexivity.
  - destruct Hrel as [_ Htl].
    specialize (IHbefore' _ _ Htl).
    destruct IHbefore' as [Hlen_after Hlen_ws].
    split; simpl; lia.
Qed.

Lemma tiling_rel_pinstr_list_source_lengths :
  forall env_size before after ws,
    tiling_rel_pinstr_list_source env_size before after ws ->
    List.length before = List.length after /\
    List.length after = List.length ws.
Proof.
  induction before as [|before_pi before']; intros after ws Hrel;
    destruct after as [|after_pi after']; destruct ws as [|w ws'];
    simpl in Hrel; try contradiction.
  - split; reflexivity.
  - destruct Hrel as [_ Htl].
    specialize (IHbefore' _ _ Htl).
    destruct IHbefore' as [Hlen_after Hlen_ws].
    split; simpl; lia.
Qed.

Lemma tiling_rel_pprog_structure_compiled_lengths :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars) ws ->
    List.length before_pis = List.length after_pis /\
    List.length after_pis = List.length ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hprog.
  unfold tiling_rel_pprog_structure_compiled,
         tiling_rel_pprog_structure in Hprog.
  simpl in Hprog.
  destruct Hprog as [_ [_ Hrel]].
  pose proof (tiling_rel_pinstr_list_lengths _ _ _ _ Hrel)
    as [Hlen_after Hlen_ws].
  split.
  - exact Hlen_after.
  - rewrite List.map_length in Hlen_ws.
    exact Hlen_ws.
Qed.

Lemma tiling_rel_pprog_structure_source_lengths :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars) ws ->
    List.length before_pis = List.length after_pis /\
    List.length after_pis = List.length ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hprog.
  unfold tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [_ [_ Hrel]].
  eapply tiling_rel_pinstr_list_source_lengths; eauto.
Qed.

Lemma tiling_rel_pinstr_list_app_singleton_inv :
  forall env_size before after ws before_pi after_pi w,
    tiling_rel_pinstr_list
      env_size
      (before ++ [before_pi])
      (after ++ [after_pi])
      (ws ++ [w]) ->
    tiling_rel_pinstr_list env_size before after ws.
Proof.
  induction before as [|before_hd before_tl IH];
    intros after ws before_pi after_pi w Hrel.
  - pose proof (tiling_rel_pinstr_list_lengths _ _ _ _ Hrel)
      as [Hlen_after Hlen_ws].
    rewrite !app_length in Hlen_after.
    simpl in Hlen_after.
    rewrite !app_length in Hlen_ws.
    simpl in Hlen_ws.
    assert (List.length after = 0)%nat as Hafter_len by lia.
    assert (List.length ws = 0)%nat as Hws_len by lia.
    apply length_zero_iff_nil in Hafter_len.
    apply length_zero_iff_nil in Hws_len.
    subst.
    exact I.
  - pose proof (tiling_rel_pinstr_list_lengths _ _ _ _ Hrel)
      as [Hlen_after Hlen_ws].
    rewrite !app_length in Hlen_after.
    simpl in Hlen_after.
    rewrite !app_length in Hlen_ws.
    simpl in Hlen_ws.
    destruct after as [|after_hd after_tl].
    + exfalso.
      destruct before_tl as [|before_hd' before_tl']; simpl in Hlen_after;
        discriminate.
    + destruct ws as [|w_hd w_tl].
      * exfalso.
        destruct after_tl as [|after_hd' after_tl']; simpl in Hlen_ws;
          discriminate.
      * simpl in Hrel.
        destruct Hrel as [Hhd Htl].
        split.
        -- exact Hhd.
        -- eapply IH; exact Htl.
Qed.

Lemma tiling_rel_pinstr_list_source_app_singleton_inv :
  forall env_size before after ws before_pi after_pi w,
    tiling_rel_pinstr_list_source
      env_size
      (before ++ [before_pi])
      (after ++ [after_pi])
      (ws ++ [w]) ->
    tiling_rel_pinstr_list_source env_size before after ws.
Proof.
  induction before as [|before_hd before_tl IH];
    intros after ws before_pi after_pi w Hrel.
  - pose proof (tiling_rel_pinstr_list_source_lengths _ _ _ _ Hrel)
      as [Hlen_after Hlen_ws].
    rewrite !app_length in Hlen_after.
    simpl in Hlen_after.
    rewrite !app_length in Hlen_ws.
    simpl in Hlen_ws.
    assert (List.length after = 0)%nat as Hafter_len by lia.
    assert (List.length ws = 0)%nat as Hws_len by lia.
    apply length_zero_iff_nil in Hafter_len.
    apply length_zero_iff_nil in Hws_len.
    subst.
    exact I.
  - pose proof (tiling_rel_pinstr_list_source_lengths _ _ _ _ Hrel)
      as [Hlen_after Hlen_ws].
    rewrite !app_length in Hlen_after.
    simpl in Hlen_after.
    rewrite !app_length in Hlen_ws.
    simpl in Hlen_ws.
    destruct after as [|after_hd after_tl].
    + exfalso.
      destruct before_tl as [|before_hd' before_tl']; simpl in Hlen_after;
        discriminate.
    + destruct ws as [|w_hd w_tl].
      * exfalso.
        destruct after_tl as [|after_hd' after_tl']; simpl in Hlen_ws;
          discriminate.
      * simpl in Hrel.
        destruct Hrel as [Hhd Htl].
        split.
        -- exact Hhd.
        -- eapply IH; exact Htl.
Qed.

Lemma tiling_rel_pprog_structure_compiled_app_singleton_inv :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws
         before_pi after_pi w,
    tiling_rel_pprog_structure_compiled
      (before_pis ++ [before_pi], before_ctxt, before_vars)
      (after_pis ++ [after_pi], after_ctxt, after_vars)
      (ws ++ [w]) ->
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws
         before_pi after_pi w Hprog.
  unfold tiling_rel_pprog_structure_compiled,
         tiling_rel_pprog_structure in *.
  simpl in *.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  rewrite map_app in Hrel.
  split; [exact Hctxt|].
  split; [exact Hvars|].
  eapply
    (tiling_rel_pinstr_list_app_singleton_inv
       (List.length before_ctxt)
       before_pis after_pis
       (List.map compiled_pinstr_tiling_witness ws)
       before_pi after_pi
       (compiled_pinstr_tiling_witness w)).
  exact Hrel.
Qed.

Lemma tiling_rel_pprog_structure_source_app_singleton_inv :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws
         before_pi after_pi w,
    tiling_rel_pprog_structure_source
      (before_pis ++ [before_pi], before_ctxt, before_vars)
      (after_pis ++ [after_pi], after_ctxt, after_vars)
      (ws ++ [w]) ->
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws
         before_pi after_pi w Hprog.
  unfold tiling_rel_pprog_structure_source in *.
  simpl in Hprog |- *.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  split; [exact Hctxt|].
  split; [exact Hvars|].
  eapply
    (tiling_rel_pinstr_list_source_app_singleton_inv
       (List.length before_ctxt)
       before_pis after_pis
       (ws)
       before_pi after_pi
       w).
  exact Hrel.
Qed.

Lemma Forall2_app_singleton_inv :
  forall (A B: Type) (P: A -> B -> Prop) xs ys x y,
    Forall2 P (xs ++ [x]) (ys ++ [y]) ->
    Forall2 P xs ys /\ P x y.
Proof.
  intros A B P xs ys x y Hforall2.
  apply Forall2_app_inv_r in Hforall2.
  destruct Hforall2 as [xs' [xy [Hhead [Htail Hsplit]]]].
  simpl in Htail.
  inversion Htail; subst; clear Htail.
  match goal with
  | H : Forall2 _ _ [] |- _ => inversion H; subst; clear H
  end.
  apply app_inj_tail in Hsplit.
  destruct Hsplit as [Hxs Hx].
  subst.
  split.
  - exact Hhead.
  - assumption.
Qed.

Lemma lift_affine_function_after_env_eval:
  forall added_dims env_size f env tiles iters,
    length env = env_size ->
    length tiles = added_dims ->
    affine_product
      (lift_affine_function_after_env added_dims env_size f)
      (env ++ tiles ++ iters) =
    affine_product f (env ++ iters).
Proof.
  intros added_dims env_size f env tiles iters Henv Htiles.
  subst env_size.
  unfold lift_affine_function_after_env.
  rewrite PL.affine_product_skipn.
  rewrite resize_app by reflexivity.
  rewrite skipn_app_le by lia.
  replace (added_dims + length env - length env)%nat with added_dims by lia.
  rewrite skipn_app by exact Htiles.
  reflexivity.
Qed.

Lemma wf_compiled_pinstr_tiling_witness:
  forall w,
    wf_pinstr_tiling_witness (compiled_pinstr_tiling_witness w).
Proof.
  intros w.
  unfold wf_pinstr_tiling_witness, compiled_pinstr_tiling_witness.
  simpl.
  reflexivity.
Qed.

Lemma compiled_pinstr_tiling_witness_matches:
  forall w,
    witness_matches_compiled_link_domain
      (compiled_pinstr_tiling_witness w).
Proof.
  intros w.
  unfold witness_matches_compiled_link_domain, compiled_pinstr_tiling_witness.
  simpl.
  reflexivity.
Qed.

Lemma lift_access_after_env_exact_cell:
  forall added_dims env_size acc env tiles iters,
    length env = env_size ->
    length tiles = added_dims ->
    exact_cell (lift_access_after_env added_dims env_size acc) (env ++ tiles ++ iters) =
    exact_cell acc (env ++ iters).
Proof.
  intros added_dims env_size [arr aff] env tiles iters Henv Htiles.
  simpl.
  f_equal.
  apply lift_affine_function_after_env_eval; assumption.
Qed.

Lemma lift_constraint_after_env_satisfies:
  forall added_dims env_size c env tiles iters,
    length env = env_size ->
    length tiles = added_dims ->
    satisfies_constraint
      (env ++ tiles ++ iters)
      (lift_constraint_after_env added_dims env_size c) =
    satisfies_constraint (env ++ iters) c.
Proof.
  intros added_dims env_size [coeffs rhs] env tiles iters Henv Htiles.
  subst env_size.
  unfold lift_constraint_after_env, satisfies_constraint.
  simpl.
  rewrite dot_product_commutative.
  rewrite PL.insert_zeros_product_skipn.
  rewrite resize_app by reflexivity.
  rewrite skipn_app_le by lia.
  replace (added_dims + length env - length env)%nat with added_dims by lia.
  rewrite skipn_app by exact Htiles.
  rewrite dot_product_commutative.
  reflexivity.
Qed.

Lemma tiling_dot_product_eq_linalg_dot_product:
  forall xs ys,
    TilingWitness.dot_product xs ys = Linalg.dot_product xs ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys].
    + reflexivity.
    + simpl.
      rewrite IH.
      lia.
Qed.

Lemma compile_ge_affine_row_to_constraint_sound:
  forall vars params row,
    List.length params = List.length (ae_param_coeffs row) ->
    affine_row_holds row vars params ->
    satisfies_constraint
      (params ++ vars)
      (compile_ge_affine_row_to_constraint row) = true.
Proof.
  intros vars params row Hparams Hrow.
  unfold affine_row_holds in Hrow.
  unfold compile_ge_affine_row_to_constraint, satisfies_constraint.
  simpl.
  rewrite mult_vector_app.
  rewrite dot_product_commutative.
  rewrite dot_product_app.
  2:{ rewrite mult_vector_length. symmetry. exact Hparams. }
  rewrite dot_product_mult_left.
  rewrite dot_product_mult_left.
  apply Z.leb_le.
  unfold eval_affine in Hrow.
  repeat rewrite tiling_dot_product_eq_linalg_dot_product in Hrow.
  replace ((-1) * Linalg.dot_product (ae_param_coeffs row) params)%Z
    with (- Linalg.dot_product (ae_param_coeffs row) params)%Z by lia.
  replace ((-1) * Linalg.dot_product (ae_var_coeffs row) vars)%Z
    with (- Linalg.dot_product (ae_var_coeffs row) vars)%Z by lia.
  nia.
Qed.

Lemma compile_ge_affine_row_to_constraint_complete:
  forall vars params row,
    List.length params = List.length (ae_param_coeffs row) ->
    satisfies_constraint
      (params ++ vars)
      (compile_ge_affine_row_to_constraint row) = true ->
    affine_row_holds row vars params.
Proof.
  intros vars params row Hparams Hsat.
  unfold affine_row_holds.
  unfold compile_ge_affine_row_to_constraint, satisfies_constraint in Hsat.
  simpl in Hsat.
  rewrite mult_vector_app in Hsat.
  rewrite dot_product_commutative in Hsat.
  rewrite dot_product_app in Hsat.
  2:{ rewrite mult_vector_length. symmetry. exact Hparams. }
  rewrite dot_product_mult_left in Hsat.
  rewrite dot_product_mult_left in Hsat.
  apply Z.leb_le in Hsat.
  unfold eval_affine.
  repeat rewrite tiling_dot_product_eq_linalg_dot_product.
  replace ((-1) * Linalg.dot_product (ae_param_coeffs row) params)%Z
    with (- Linalg.dot_product (ae_param_coeffs row) params)%Z in Hsat by lia.
  replace ((-1) * Linalg.dot_product (ae_var_coeffs row) vars)%Z
    with (- Linalg.dot_product (ae_var_coeffs row) vars)%Z in Hsat by lia.
  nia.
Qed.

Lemma tiling_dot_product_mult_left:
  forall k xs ys,
    TilingWitness.dot_product (mult_vector k xs) ys =
    k * TilingWitness.dot_product xs ys.
Proof.
  intros k xs ys.
  repeat rewrite tiling_dot_product_eq_linalg_dot_product.
  apply dot_product_mult_left.
Qed.

Lemma eval_lower_link_affine_row_after_env:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    eval_affine
      (lower_link_affine_row_after_env (List.length prefix) (List.length suffix) link)
      (prefix ++ parent :: suffix ++ point)
      env =
    lower_link_row_value link (prefix ++ point) env parent.
Proof.
  intros env prefix suffix point link parent Hlen.
  unfold eval_affine, lower_link_affine_row_after_env, lower_link_row_value.
  simpl.
  assert (Hpre:
    List.length (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) =
    List.length prefix).
  { rewrite firstn_length. lia. }
  rewrite TilingWitness.dot_product_app_exact
    with (xs1 := firstn (List.length prefix) (ae_var_coeffs (tl_expr link)))
         (ys1 := prefix)
         (xs2 := (-(tl_tile_size link)) ::
                 repeat 0 (List.length suffix) ++
                 skipn (List.length prefix) (ae_var_coeffs (tl_expr link)))
         (ys2 := parent :: suffix ++ point).
  2:{ exact Hpre. }
  rewrite TilingWitness.dot_product_cons_singleton.
  rewrite TilingWitness.dot_product_app_exact
    with (xs1 := repeat 0 (List.length suffix))
         (ys1 := suffix)
         (xs2 := skipn (List.length prefix) (ae_var_coeffs (tl_expr link)))
         (ys2 := point).
  2:{ rewrite repeat_length. reflexivity. }
  rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
  replace
    (TilingWitness.dot_product (ae_var_coeffs (tl_expr link)) (prefix ++ point))
    with
    (TilingWitness.dot_product
       (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) prefix +
     TilingWitness.dot_product
       (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))) point).
  2:{
    symmetry.
    apply TilingWitness.dot_product_split_firstn_skipn.
    exact Hlen.
  }
  simpl.
  unfold eval_affine.
  simpl.
  replace
    (TilingWitness.dot_product (ae_var_coeffs (tl_expr link)) (prefix ++ point))
    with
    (TilingWitness.dot_product
       (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) prefix +
     TilingWitness.dot_product
       (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))) point).
  2:{
    symmetry.
    apply TilingWitness.dot_product_split_firstn_skipn.
    exact Hlen.
  }
  nia.
Qed.

Lemma lower_link_affine_row_after_env_sound:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    lower_link_row_holds link (prefix ++ point) env parent ->
    affine_row_holds
      (lower_link_affine_row_after_env (List.length prefix) (List.length suffix) link)
      (prefix ++ parent :: suffix ++ point)
      env.
Proof.
  intros env prefix suffix point link parent Hlen Hrow.
  unfold affine_row_holds in *.
  rewrite eval_lower_link_affine_row_after_env by exact Hlen.
  exact Hrow.
Qed.

Lemma lower_link_constraint_after_env_sound:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length env ->
    lower_link_row_holds link (prefix ++ point) env parent ->
    satisfies_constraint
      (env ++ prefix ++ parent :: suffix ++ point)
      (lower_link_constraint_after_env (List.length prefix) (List.length suffix) link) = true.
Proof.
  intros env prefix suffix point link parent Hvars Hparams Hrow.
  unfold lower_link_constraint_after_env.
  apply compile_ge_affine_row_to_constraint_sound.
  - simpl. symmetry. exact Hparams.
  - apply lower_link_affine_row_after_env_sound; assumption.
Qed.

Lemma eval_upper_link_affine_row_after_env:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    eval_affine
      (upper_link_affine_row_after_env (List.length prefix) (List.length suffix) link)
      (prefix ++ parent :: suffix ++ point)
      env =
    upper_link_row_value link (prefix ++ point) env parent.
Proof.
  intros env prefix suffix point link parent Hlen.
  unfold eval_affine, upper_link_affine_row_after_env, upper_link_row_value.
  simpl.
  assert (Hpre:
    List.length (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) =
    List.length prefix).
  { rewrite firstn_length. lia. }
  rewrite TilingWitness.dot_product_app_exact
    with (xs1 := mult_vector (-1) (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))))
         (ys1 := prefix)
         (xs2 := (tl_tile_size link) ::
                 repeat 0 (List.length suffix) ++
                 mult_vector (-1)
                   (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))))
         (ys2 := parent :: suffix ++ point).
  2:{ rewrite mult_vector_length. exact Hpre. }
  rewrite tiling_dot_product_mult_left.
  rewrite TilingWitness.dot_product_cons_singleton.
  rewrite TilingWitness.dot_product_app_exact
    with (xs1 := repeat 0 (List.length suffix))
         (ys1 := suffix)
         (xs2 := mult_vector (-1)
                  (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))))
         (ys2 := point).
  2:{ rewrite repeat_length. reflexivity. }
  rewrite TilingWitness.dot_product_repeat_zero_exact by reflexivity.
  rewrite tiling_dot_product_mult_left.
  rewrite tiling_dot_product_mult_left.
  replace
    (TilingWitness.dot_product [tl_tile_size link] [parent])
    with (tl_tile_size link * parent)%Z.
  2:{ simpl. lia. }
  replace
    (TilingWitness.dot_product (ae_var_coeffs (tl_expr link)) (prefix ++ point))
    with
    (TilingWitness.dot_product
       (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) prefix +
     TilingWitness.dot_product
       (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))) point).
  2:{
    symmetry.
    apply TilingWitness.dot_product_split_firstn_skipn.
    exact Hlen.
  }
  unfold eval_affine.
  simpl.
  replace
    (TilingWitness.dot_product (ae_var_coeffs (tl_expr link)) (prefix ++ point))
    with
    (TilingWitness.dot_product
       (firstn (List.length prefix) (ae_var_coeffs (tl_expr link))) prefix +
     TilingWitness.dot_product
       (skipn (List.length prefix) (ae_var_coeffs (tl_expr link))) point).
  2:{
    symmetry.
    apply TilingWitness.dot_product_split_firstn_skipn.
    exact Hlen.
  }
  nia.
Qed.

Lemma upper_link_affine_row_after_env_sound:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    upper_link_row_holds link (prefix ++ point) env parent ->
    affine_row_holds
      (upper_link_affine_row_after_env (List.length prefix) (List.length suffix) link)
      (prefix ++ parent :: suffix ++ point)
      env.
Proof.
  intros env prefix suffix point link parent Hlen Hrow.
  unfold affine_row_holds in *.
  rewrite eval_upper_link_affine_row_after_env by exact Hlen.
  exact Hrow.
Qed.

Lemma upper_link_constraint_after_env_sound:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length env ->
    upper_link_row_holds link (prefix ++ point) env parent ->
    satisfies_constraint
      (env ++ prefix ++ parent :: suffix ++ point)
      (upper_link_constraint_after_env (List.length prefix) (List.length suffix) link) = true.
Proof.
  intros env prefix suffix point link parent Hvars Hparams Hrow.
  unfold upper_link_constraint_after_env.
  apply compile_ge_affine_row_to_constraint_sound.
  - simpl. rewrite mult_vector_length. symmetry. exact Hparams.
  - apply upper_link_affine_row_after_env_sound; assumption.
Qed.

Lemma lower_link_constraint_after_env_complete:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length env ->
    satisfies_constraint
      (env ++ prefix ++ parent :: suffix ++ point)
      (lower_link_constraint_after_env (List.length prefix) (List.length suffix) link) = true ->
    lower_link_row_holds link (prefix ++ point) env parent.
Proof.
  intros env prefix suffix point link parent Hvars Hparams Hsat.
  unfold lower_link_constraint_after_env in Hsat.
  apply compile_ge_affine_row_to_constraint_complete in Hsat.
  2:{ simpl. symmetry. exact Hparams. }
  unfold affine_row_holds in Hsat.
  rewrite eval_lower_link_affine_row_after_env in Hsat by exact Hvars.
  exact Hsat.
Qed.

Lemma upper_link_constraint_after_env_complete:
  forall env prefix suffix point link parent,
    List.length (ae_var_coeffs (tl_expr link)) =
      (List.length prefix + List.length point)%nat ->
    List.length (ae_param_coeffs (tl_expr link)) = List.length env ->
    satisfies_constraint
      (env ++ prefix ++ parent :: suffix ++ point)
      (upper_link_constraint_after_env (List.length prefix) (List.length suffix) link) = true ->
    upper_link_row_holds link (prefix ++ point) env parent.
Proof.
  intros env prefix suffix point link parent Hvars Hparams Hsat.
  unfold upper_link_constraint_after_env in Hsat.
  apply compile_ge_affine_row_to_constraint_complete in Hsat.
  2:{ simpl. rewrite mult_vector_length. symmetry. exact Hparams. }
  unfold affine_row_holds in Hsat.
  rewrite eval_upper_link_affine_row_after_env in Hsat by exact Hvars.
  exact Hsat.
Qed.

Lemma eval_tile_links_app_suffix:
  forall prefix point params links,
    exists suffix,
      eval_tile_links prefix point params links = prefix ++ suffix.
Proof.
  intros prefix point params links.
  revert prefix point params.
  induction links as [|link links IH]; intros prefix point params; simpl.
  - exists []. now rewrite app_nil_r.
  - set (parent := eval_tile_parent link (prefix ++ point) params).
    destruct (IH (prefix ++ [parent]) point params) as [suffix Hsuffix].
    exists (parent :: suffix).
    rewrite Hsuffix.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma compile_link_domain_after_env_from_sound:
  forall params prefix point links prefix_len,
    prefix_len = List.length prefix ->
    well_formed_tile_links prefix_len (List.length point) links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      links ->
    Forall (fun link => 0 < tl_tile_size link) links ->
    in_poly
      (params ++ eval_tile_links prefix point params links ++ point)
      (compile_link_domain_after_env_from prefix_len links) = true.
Proof.
  intros params prefix point links.
  revert prefix.
  induction links as [|link links IH]; intros prefix prefix_len Hprefix_len Hwf Hparams Hsizes; simpl.
  - reflexivity.
  - subst prefix_len.
    destruct Hwf as [Hvars Hwf].
    pose proof (Forall_inv Hparams) as Hparam.
    pose proof (Forall_inv_tail Hparams) as Hparams'.
    pose proof (Forall_inv Hsizes) as Hsize.
    pose proof (Forall_inv_tail Hsizes) as Hsizes'.
    set (parent := eval_tile_parent link (prefix ++ point) params).
    destruct (eval_tile_links_app_suffix (prefix ++ [parent]) point params links)
      as [suffix Hsuffix].
    rewrite Hsuffix.
    rewrite app_assoc.
    assert (Hsuffix_len: List.length suffix = List.length links).
    {
      apply (f_equal (@List.length Z)) in Hsuffix.
      rewrite eval_tile_links_length in Hsuffix.
      rewrite !app_length in Hsuffix.
      simpl in Hsuffix.
      lia.
    }
    assert (Hlower:
      satisfies_constraint
        (params ++ prefix ++ parent :: suffix ++ point)
        (lower_link_constraint_after_env (List.length prefix) (List.length links) link) = true).
    {
      replace (List.length links) with (List.length suffix) by exact Hsuffix_len.
      apply lower_link_constraint_after_env_sound.
      - exact Hvars.
      - exact Hparam.
      - apply interval_implies_lower_link_row.
        apply eval_tile_parent_interval.
        exact Hsize.
    }
    assert (Hupper:
      satisfies_constraint
        (params ++ prefix ++ parent :: suffix ++ point)
        (upper_link_constraint_after_env (List.length prefix) (List.length links) link) = true).
    {
      replace (List.length links) with (List.length suffix) by exact Hsuffix_len.
      apply upper_link_constraint_after_env_sound.
      - exact Hvars.
      - exact Hparam.
      - apply interval_implies_upper_link_row.
        apply eval_tile_parent_interval.
        exact Hsize.
    }
    assert (Hlifted_eq:
      ((params ++ (prefix ++ [parent]) ++ suffix) ++ point) =
      params ++ prefix ++ parent :: suffix ++ point).
    {
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      simpl.
      reflexivity.
    }
    assert (Hlower_goal:
      satisfies_constraint
        ((params ++ (prefix ++ [parent]) ++ suffix) ++ point)
        (lower_link_constraint_after_env (List.length prefix) (List.length links) link) = true).
    {
      rewrite Hlifted_eq.
      exact Hlower.
    }
    assert (Hupper_goal:
      satisfies_constraint
        ((params ++ (prefix ++ [parent]) ++ suffix) ++ point)
        (upper_link_constraint_after_env (List.length prefix) (List.length links) link) = true).
    {
      rewrite Hlifted_eq.
      exact Hupper.
    }
    rewrite Hlower_goal.
    rewrite Hupper_goal.
    simpl.
    rewrite <- Hsuffix.
    rewrite <- app_assoc.
    apply IH.
    + rewrite app_length.
      simpl.
      lia.
    + exact Hwf.
    + exact Hparams'.
    + exact Hsizes'.
Qed.

Theorem compile_link_domain_after_env_sound:
  forall params point w,
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim (List.length params) w ->
    Forall (fun link => 0 < tl_tile_size link) (stw_links w) ->
    in_poly
      (eval_statement_tiling_witness_with_env params w point params)
      (compile_link_domain_after_env w) = true.
Proof.
  intros params point w Hpoint Hwf Hsizes.
  destruct Hwf as [Hwf Hparams].
  unfold well_formed_statement_tiling_witness in Hwf.
  rewrite <- Hpoint in Hwf.
  unfold compile_link_domain_after_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  apply compile_link_domain_after_env_from_sound.
  - reflexivity.
  - exact Hwf.
  - exact Hparams.
  - exact Hsizes.
Qed.

Theorem compile_link_domain_after_env_from_complete:
  forall params prefix added point links,
    List.length added = List.length links ->
    well_formed_tile_links (List.length prefix) (List.length point) links ->
    Forall
      (fun link =>
         List.length (ae_param_coeffs (tl_expr link)) = List.length params)
      links ->
    Forall (fun link => 0 < tl_tile_size link) links ->
    in_poly
      (params ++ prefix ++ added ++ point)
      (compile_link_domain_after_env_from (List.length prefix) links) = true ->
    prefix ++ added = eval_tile_links prefix point params links.
Proof.
  intros params prefix added point links.
  revert prefix added.
  induction links as [|link links IH]; intros prefix added Hadded Hwf Hparams Hsizes Hin.
  - destruct added as [|x added]; simpl in *.
    + now rewrite app_nil_r.
    + discriminate.
  - destruct added as [|parent suffix]; simpl in Hadded.
    + discriminate.
    + destruct Hwf as [Hvars Hwf].
      pose proof (Forall_inv Hparams) as Hparam.
      pose proof (Forall_inv_tail Hparams) as Hparams'.
      pose proof (Forall_inv Hsizes) as Hsize.
      pose proof (Forall_inv_tail Hsizes) as Hsizes'.
      unfold in_poly in Hin.
      simpl in Hin.
      apply andb_true_iff in Hin as [Hlower Hin].
      simpl in Hin.
      apply andb_true_iff in Hin as [Hupper Hrest].
      assert (Hparent:
        parent = eval_tile_parent link (prefix ++ point) params).
      {
        apply lower_upper_rows_imply_eval_tile_parent.
        - exact Hsize.
        - eapply lower_link_constraint_after_env_complete; eauto.
        - eapply upper_link_constraint_after_env_complete; eauto.
      }
      assert (Hrest':
        in_poly
          (params ++ (prefix ++ [parent]) ++ suffix ++ point)
          (compile_link_domain_after_env_from (List.length (prefix ++ [parent])) links) = true).
      {
        assert (Hvec:
          params ++ (prefix ++ [parent]) ++ suffix ++ point =
          params ++ prefix ++ parent :: suffix ++ point).
        {
          replace (params ++ (prefix ++ [parent]) ++ suffix ++ point)
            with (params ++ prefix ++ [parent] ++ suffix ++ point)
            by (repeat rewrite app_assoc; reflexivity).
          remember (params ++ prefix) as pre eqn:Hpre.
          induction pre as [|x pre IHpre]; simpl.
          - reflexivity.
          - f_equal; exact IHpre.
        }
        replace (List.length (prefix ++ [parent])) with (S (List.length prefix))
          by (rewrite app_length; simpl; lia).
        rewrite Hvec.
        exact Hrest.
      }
      assert (Hrec:
        (prefix ++ [parent]) ++ suffix =
        eval_tile_links (prefix ++ [parent]) point params links).
      {
        apply IH.
        - lia.
        - replace (List.length (prefix ++ [parent])) with (S (List.length prefix))
            by (rewrite app_length; simpl; lia).
          exact Hwf.
        - exact Hparams'.
        - exact Hsizes'.
        - exact Hrest'.
      }
      simpl.
      rewrite Hparent in Hrec.
      rewrite <- app_singleton_cons in Hrec.
      rewrite Hparent.
      exact Hrec.
Qed.

Theorem compile_link_domain_after_env_complete:
  forall params point w added,
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim (List.length params) w ->
    Forall (fun link => 0 < tl_tile_size link) (stw_links w) ->
    in_poly
      (params ++ added ++ point)
      (compile_link_domain_after_env w) = true ->
    added = eval_tile_links [] point params (stw_links w).
Proof.
  intros params point w added Hadded Hpoint Hwf Hsizes Hin.
  destruct Hwf as [Hwf Hparams].
  unfold well_formed_statement_tiling_witness in Hwf.
  rewrite <- Hpoint in Hwf.
  unfold compile_link_domain_after_env in Hin.
  specialize
    (compile_link_domain_after_env_from_complete
       params [] added point (stw_links w)
       Hadded Hwf Hparams Hsizes Hin) as Hcomplete.
  simpl in Hcomplete.
  exact Hcomplete.
Qed.

Lemma lifted_base_domain_after_env_in_poly:
  forall added_dims env_size dom env tiles iters,
    length env = env_size ->
    length tiles = added_dims ->
    in_poly
      (env ++ tiles ++ iters)
      (List.map (lift_constraint_after_env added_dims env_size) dom) =
    in_poly (env ++ iters) dom.
Proof.
  intros added_dims env_size dom.
  induction dom as [|c dom IH]; intros env tiles iters Henv Htiles; simpl.
  - reflexivity.
  - rewrite lift_constraint_after_env_satisfies by assumption.
    rewrite IH by assumption.
    reflexivity.
Qed.

Theorem tiling_rel_pinstr_structure_domain_decompose:
  forall env before after w tiles iters,
    tiling_rel_pinstr_structure (length env) before after w ->
    length tiles = ptw_added_dims w ->
    in_poly (env ++ tiles ++ iters) (PL.pi_poly after) =
    (in_poly (env ++ tiles ++ iters) (ptw_link_domain w) &&
     in_poly (env ++ iters) (PL.pi_poly before)).
Proof.
  intros env before after w tiles iters Hrel Htiles.
  destruct Hrel as [_ [_ [_ [_ [_ [Hpoly _]]]]]].
  rewrite Hpoly.
  rewrite in_poly_app.
  f_equal.
  unfold lifted_base_domain_after_env.
  apply lifted_base_domain_after_env_in_poly; auto.
Qed.

Theorem tiling_rel_pinstr_structure_domain_lifted_compiled:
  forall params before after w point,
    tiling_rel_pinstr_structure (List.length params) before after w ->
    witness_matches_compiled_link_domain w ->
    wf_pinstr_tiling_witness w ->
    List.length point = stw_point_dim (ptw_statement_witness w) ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) (ptw_statement_witness w) ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links (ptw_statement_witness w)) ->
    in_poly (params ++ point) (PL.pi_poly before) = true ->
    in_poly
      (eval_pinstr_tiling_index_with_env params point params w)
      (PL.pi_poly after) = true.
Proof.
  intros params before after w point Hrel Hcompiled Hwf Hpoint_dim Hwf_stmt Hsizes Hbefore.
  unfold eval_pinstr_tiling_index_with_env.
  destruct Hrel as [_ [_ [_ [_ [_ [Hpoly _]]]]]].
  rewrite Hpoly.
  rewrite in_poly_app.
  rewrite Hcompiled.
  rewrite
    (compile_link_domain_after_env_sound
       params point (ptw_statement_witness w)).
  2:{ exact Hpoint_dim. }
  2:{ exact Hwf_stmt. }
  2:{ exact Hsizes. }
  rewrite andb_true_l.
  unfold eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  unfold lifted_base_domain_after_env.
  rewrite
    (lifted_base_domain_after_env_in_poly
       (ptw_added_dims w)
       (List.length params)
       (PL.pi_poly before)
       params
       (eval_tile_links [] point params (stw_links (ptw_statement_witness w)))
       point).
  2:{ reflexivity. }
  2:{
    rewrite eval_tile_links_length.
    simpl.
    unfold wf_pinstr_tiling_witness in Hwf.
    lia.
  }
  exact Hbefore.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_domain_lifted:
  forall params before after w point,
    tiling_rel_pinstr_structure_compiled (List.length params) before after w ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (params ++ point) (PL.pi_poly before) = true ->
    in_poly
      (eval_pinstr_tiling_index_with_env
         params point params (compiled_pinstr_tiling_witness w))
      (PL.pi_poly after) = true.
Proof.
  intros params before after w point Hrel Hpoint_dim Hwf_stmt Hsizes Hbefore.
  eapply tiling_rel_pinstr_structure_domain_lifted_compiled.
  - exact Hrel.
  - apply compiled_pinstr_tiling_witness_matches.
  - apply wf_compiled_pinstr_tiling_witness.
  - exact Hpoint_dim.
  - exact Hwf_stmt.
  - exact Hsizes.
  - exact Hbefore.
Qed.

Theorem tiling_rel_pinstr_structure_source_domain_lifted:
  forall params before after w point,
    tiling_rel_pinstr_structure_source
      (List.length params) before after (compiled_pinstr_tiling_witness w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (params ++ point) (PL.pi_poly before) = true ->
    in_poly
      (eval_pinstr_tiling_index_with_env
         params point params (compiled_pinstr_tiling_witness w))
      (PL.pi_poly after) = true.
Proof.
  intros params before after w point Hrel Hpoint_dim Hwf_stmt Hsizes Hbefore.
  unfold eval_pinstr_tiling_index_with_env.
  unfold compiled_pinstr_tiling_witness.
  simpl.
  unfold tiling_rel_pinstr_structure_source in Hrel.
  unfold compiled_pinstr_tiling_witness in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [Hpoly _]]]]]].
  rewrite Hpoly.
  rewrite in_poly_app.
  rewrite
    (compile_link_domain_after_env_sound
       params point w).
  2:{ exact Hpoint_dim. }
  2:{ exact Hwf_stmt. }
  2:{ exact Hsizes. }
  rewrite andb_true_l.
  change
    (in_poly
       (params ++ eval_tile_links [] point params (stw_links w) ++ point)
       (lifted_base_domain_after_env
          (List.length params)
          (compiled_pinstr_tiling_witness w)
          (PL.pi_poly before)) = true).
  unfold lifted_base_domain_after_env.
  unfold compiled_pinstr_tiling_witness.
  simpl.
  change
    (in_poly
       (params ++ eval_tile_links [] point params (stw_links w) ++ point)
       (List.map
          (lift_constraint_after_env
             (List.length (stw_links w))
             (List.length params))
          (PL.pi_poly before)) = true).
  rewrite
    (lifted_base_domain_after_env_in_poly
       (List.length (stw_links w))
       (List.length params)
       (PL.pi_poly before)
       params
       (eval_tile_links [] point params (stw_links w))
       point).
  2:{ reflexivity. }
  2:{ rewrite eval_tile_links_length; reflexivity. }
  exact Hbefore.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_domain_complete:
  forall params before after w added point,
    tiling_rel_pinstr_structure_compiled (List.length params) before after w ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (params ++ added ++ point) (PL.pi_poly after) = true ->
    added = eval_tile_links [] point params (stw_links w) /\
    in_poly (params ++ point) (PL.pi_poly before) = true.
Proof.
  intros params before after w added point Hrel Hadded Hpoint_dim Hwf_stmt Hsizes Hafter.
  unfold tiling_rel_pinstr_structure_compiled,
         compiled_pinstr_tiling_witness in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [Hpoly _]]]]]].
  rewrite Hpoly in Hafter.
  rewrite in_poly_app in Hafter.
  apply andb_true_iff in Hafter as [Hlink Hbase].
  split.
  - eapply compile_link_domain_after_env_complete; eauto.
  - unfold lifted_base_domain_after_env in Hbase.
    simpl in Hbase.
    rewrite
      (lifted_base_domain_after_env_in_poly
         (List.length (stw_links w))
         (List.length params)
         (PL.pi_poly before)
         params
         added
         point) in Hbase.
    + exact Hbase.
    + reflexivity.
    + exact Hadded.
Qed.

Theorem tiling_rel_pinstr_structure_source_domain_complete:
  forall params before after w added point,
    tiling_rel_pinstr_structure_source (List.length params) before after w ->
    wf_pinstr_tiling_witness w ->
    witness_matches_compiled_link_domain w ->
    List.length added = List.length (stw_links (ptw_statement_witness w)) ->
    List.length point = stw_point_dim (ptw_statement_witness w) ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) (ptw_statement_witness w) ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links (ptw_statement_witness w)) ->
    in_poly (params ++ added ++ point) (PL.pi_poly after) = true ->
    added = eval_tile_links [] point params (stw_links (ptw_statement_witness w)) /\
    in_poly (params ++ point) (PL.pi_poly before) = true.
Proof.
  intros params before after w added point Hrel Hwf Hmatch Hadded Hpoint_dim Hwf_stmt Hsizes Hafter.
  destruct Hrel as [_ [_ [_ [_ [_ [Hpoly _]]]]]].
  rewrite Hpoly in Hafter.
  rewrite in_poly_app in Hafter.
  apply andb_true_iff in Hafter as [Hlink Hbase].
  split.
  - rewrite Hmatch in Hlink.
    eapply compile_link_domain_after_env_complete; eauto.
  - unfold lifted_base_domain_after_env in Hbase.
    unfold wf_pinstr_tiling_witness in Hwf.
    rewrite Hwf in Hbase.
    change
      (in_poly
         (params ++ added ++ point)
         (List.map
            (lift_constraint_after_env
               (List.length (stw_links (ptw_statement_witness w)))
               (List.length params))
            (PL.pi_poly before)) = true) in Hbase.
    rewrite
      (lifted_base_domain_after_env_in_poly
         (List.length (stw_links (ptw_statement_witness w)))
         (List.length params)
         (PL.pi_poly before)
         params
         added
         point) in Hbase.
    + exact Hbase.
    + reflexivity.
    + exact Hadded.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_index_complete:
  forall params before after w added point,
    tiling_rel_pinstr_structure_compiled (List.length params) before after w ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (params ++ added ++ point) (PL.pi_poly after) = true ->
    params ++ added ++ point =
    eval_pinstr_tiling_index_with_env
      params point params (compiled_pinstr_tiling_witness w).
Proof.
  intros params before after w added point Hrel Hadded Hpoint_dim Hwf_stmt Hsizes Hafter.
  pose proof
    (tiling_rel_pinstr_structure_compiled_domain_complete
       params before after w added point
       Hrel Hadded Hpoint_dim Hwf_stmt Hsizes Hafter) as [Hadded_eq _].
  unfold eval_pinstr_tiling_index_with_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  rewrite Hadded_eq.
  reflexivity.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_domain_iff:
  forall params before after w added point,
    tiling_rel_pinstr_structure_compiled (List.length params) before after w ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    (in_poly (params ++ added ++ point) (PL.pi_poly after) = true <->
     added = eval_tile_links [] point params (stw_links w) /\
     in_poly (params ++ point) (PL.pi_poly before) = true).
Proof.
  intros params before after w added point Hrel Hadded Hpoint_dim Hwf_stmt Hsizes.
  split.
  - intros Hafter.
    eapply tiling_rel_pinstr_structure_compiled_domain_complete; eauto.
  - intros [Hadded_eq Hbefore].
    subst added.
    replace (params ++ eval_tile_links [] point params (stw_links w) ++ point)
      with
        (eval_pinstr_tiling_index_with_env
           params point params (compiled_pinstr_tiling_witness w))
      by reflexivity.
    eapply tiling_rel_pinstr_structure_compiled_domain_lifted; eauto.
Qed.

Lemma tiling_rel_pinstr_list_compiled_nth :
  forall env_size before_pis after_pis ws n before_pi after_pi w,
    tiling_rel_pinstr_list
      env_size before_pis after_pis (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    tiling_rel_pinstr_structure_compiled env_size before_pi after_pi w.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_hd before_tl IH];
    intros after_pis ws n before_pi after_pi w Hrel Hbefore Hafter Hwitness.
  - destruct n; inversion Hbefore.
  - destruct after_pis as [|after_hd after_tl], ws as [|w_hd w_tl];
      simpl in Hrel; try contradiction.
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hwitness; subst.
      destruct Hrel as [Hhd _].
      exact Hhd.
    + destruct Hrel as [_ Htl].
      eapply IH; eauto.
Qed.

Lemma tiling_rel_pinstr_list_source_nth :
  forall env_size before_pis after_pis ws n before_pi after_pi w,
    tiling_rel_pinstr_list_source env_size before_pis after_pis ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    tiling_rel_pinstr_structure_source env_size before_pi after_pi w.
Proof.
  intros env_size before_pis.
  induction before_pis as [|before_hd before_tl IH];
    intros after_pis ws n before_pi after_pi w Hrel Hbefore Hafter Hwitness.
  - destruct n; inversion Hbefore.
  - destruct after_pis as [|after_hd after_tl], ws as [|w_hd w_tl];
      simpl in Hrel; try contradiction.
    destruct n as [|n].
    + inversion Hbefore; inversion Hafter; inversion Hwitness; subst.
      destruct Hrel as [Hhd _].
      exact Hhd.
    + destruct Hrel as [_ Htl].
      eapply IH; eauto.
Qed.

Theorem tiling_rel_pprog_structure_compiled_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    tiling_rel_pinstr_structure_compiled
      (List.length before_ctxt) before_pi after_pi w.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w Hrel Hbefore Hafter Hwitness.
  unfold tiling_rel_pprog_structure_compiled,
         tiling_rel_pprog_structure in Hrel.
  simpl in Hrel.
  destruct Hrel as [Hctxt [Hvars Hpis]].
  subst after_ctxt after_vars.
  eapply tiling_rel_pinstr_list_compiled_nth; eauto.
Qed.

Theorem tiling_rel_pprog_structure_source_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt) before_pi after_pi w.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w Hrel Hbefore Hafter Hwitness.
  unfold tiling_rel_pprog_structure_source in Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ Hpins]].
  eapply tiling_rel_pinstr_list_source_nth; eauto.
Qed.

Theorem tiling_rel_pprog_structure_compiled_domain_iff_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         params added point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length params = List.length before_ctxt ->
    List.length added = List.length (stw_links w) ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length params) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    (in_poly (params ++ added ++ point) (PL.pi_poly after_pi) = true <->
     added = eval_tile_links [] point params (stw_links w) /\
     in_poly (params ++ point) (PL.pi_poly before_pi) = true).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         params added point
         Hprog Hbefore_nth Hafter_nth Hw_nth Hparams_len
         Hadded Hpoint_dim Hwf_stmt Hsizes.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Hparams_len in Hstmt.
  eapply tiling_rel_pinstr_structure_compiled_domain_iff; eauto.
Qed.

Theorem tiling_rel_pinstr_structure_waccess_exact_cells:
  forall env before after w tiles iters,
    tiling_rel_pinstr_structure (length env) before after w ->
    length tiles = ptw_added_dims w ->
    List.map
      (fun acc => exact_cell acc (env ++ tiles ++ iters))
      (PL.pi_waccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ iters))
      (PL.pi_waccess before).
Proof.
  intros env before after w tiles iters Hrel Htiles.
  destruct Hrel as [_ [_ [_ [_ [_ [_ [Hwacc _]]]]]]].
  rewrite Hwacc.
  unfold lifted_accesses_after_env.
  rewrite map_map.
  apply map_ext.
  intros acc.
  apply lift_access_after_env_exact_cell; auto.
Qed.

Theorem tiling_rel_pinstr_structure_raccess_exact_cells:
  forall env before after w tiles iters,
    tiling_rel_pinstr_structure (length env) before after w ->
    length tiles = ptw_added_dims w ->
    List.map
      (fun acc => exact_cell acc (env ++ tiles ++ iters))
      (PL.pi_raccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ iters))
      (PL.pi_raccess before).
Proof.
  intros env before after w tiles iters Hrel Htiles.
  destruct Hrel as [_ [_ [_ [_ [_ [_ [_ Hracc]]]]]]].
  rewrite Hracc.
  unfold lifted_accesses_after_env.
  rewrite map_map.
  apply map_ext.
  intros acc.
  apply lift_access_after_env_exact_cell; auto.
Qed.

Lemma tiling_rel_pinstr_structure_source_of_tiled :
  forall env_size before after w,
    tiling_rel_pinstr_structure env_size before after w ->
    tiling_rel_pinstr_structure_source
      env_size before (source_view_of_tiled_pinstr env_size before after w) w.
Proof.
  intros env_size before after w Hrel.
  destruct Hrel as
      [Hinstr [Hdepth [Hwitness [Htf [Hacc_tf [Hdom [Hwacc Hracc]]]]]]].
  unfold tiling_rel_pinstr_structure_source, source_view_of_tiled_pinstr.
  simpl.
  repeat split; auto.
Qed.

Theorem tiling_rel_pinstr_structure_source_transformation_lifted:
  forall env before after w point params,
    tiling_rel_pinstr_structure_source (length env) before after w ->
    wf_pinstr_tiling_witness w ->
    List.length point = stw_point_dim (ptw_statement_witness w) ->
    PL.current_src_args_of after
      (eval_pinstr_tiling_index_with_env env point params w) =
    affine_product
      (PL.pi_transformation before)
      (env ++ point).
Proof.
  intros env before after w point params Hrel Hwf Hpoint_len.
  destruct Hrel as [_ [_ [Hwitness [Htf _]]]].
  unfold PL.current_src_args_of, PL.current_src_args_at, PL.current_env_dim_of,
         PL.current_transformation_at, PL.current_transformation_for_witness.
  rewrite Hwitness.
  rewrite Htf.
  simpl.
  assert (Henv_dim :
    (List.length (eval_pinstr_tiling_index_with_env env point params w) -
     witness_current_point_dim (PSWTiling (ptw_statement_witness w)))%nat =
    List.length env).
  {
    assert (Hidx_len :
      List.length (eval_pinstr_tiling_index_with_env env point params w) =
      (List.length env +
       witness_current_point_dim (PSWTiling (ptw_statement_witness w)))%nat).
    {
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      repeat rewrite app_length.
      simpl.
      rewrite eval_tile_links_length.
      rewrite Hpoint_len.
      unfold witness_current_point_dim, witness_added_dims, witness_base_point_dim.
      change
        ((List.length env +
          (List.length (@nil Z) +
           List.length (stw_links (ptw_statement_witness w)) +
           stw_point_dim (ptw_statement_witness w)))%nat =
         (List.length env +
          (stw_point_dim (ptw_statement_witness w) +
           List.length (stw_links (ptw_statement_witness w))))%nat).
      remember (List.length env) as a.
      remember (List.length (stw_links (ptw_statement_witness w))) as b.
      remember (stw_point_dim (ptw_statement_witness w)) as c.
      simpl.
      lia.
    }
    rewrite Hidx_len.
    lia.
  }
  rewrite Henv_dim.
  unfold eval_pinstr_tiling_index_with_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  simpl.
  apply
    (lift_affine_function_after_env_eval
       (List.length (stw_links (ptw_statement_witness w)))
       (List.length env)
       (PL.pi_transformation before)
       env
       (eval_tile_links [] point params (stw_links (ptw_statement_witness w)))
       point).
  - reflexivity.
  - rewrite eval_tile_links_length.
    simpl.
    reflexivity.
Qed.

Theorem tiling_rel_pinstr_structure_source_instr_semantics_lifted_iff:
  forall env before after w point params wcs rcs st1 st2,
    tiling_rel_pinstr_structure_source (length env) before after w ->
    wf_pinstr_tiling_witness w ->
    List.length point = stw_point_dim (ptw_statement_witness w) ->
    Instr.instr_semantics
      (PL.pi_instr after)
      (PL.current_src_args_of after
         (eval_pinstr_tiling_index_with_env env point params w))
      wcs rcs st1 st2 <->
    Instr.instr_semantics
      (PL.pi_instr before)
      (affine_product
         (PL.pi_transformation before)
         (env ++ point))
      wcs rcs st1 st2.
Proof.
  intros env before after w point params wcs rcs st1 st2 Hrel Hwf Hpoint_len.
  pose proof Hrel as Hrel0.
  destruct Hrel as [Hinstr _].
  rewrite (tiling_rel_pinstr_structure_source_transformation_lifted
             env before after w point params Hrel0 Hwf Hpoint_len).
  split; intro Hsem.
  - rewrite Hinstr in Hsem. exact Hsem.
  - rewrite <- Hinstr in Hsem. exact Hsem.
Qed.

Theorem tiling_rel_pinstr_structure_waccess_lifted:
  forall env before after w point params,
    tiling_rel_pinstr_structure (length env) before after w ->
    wf_pinstr_tiling_witness w ->
    List.map
      (fun acc => exact_cell acc (eval_pinstr_tiling_index_with_env env point params w))
      (PL.pi_waccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_waccess before).
Proof.
  intros env before after w point params Hrel Hwf.
  unfold eval_pinstr_tiling_index_with_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  eapply tiling_rel_pinstr_structure_waccess_exact_cells; eauto.
  rewrite eval_tile_links_length.
  simpl.
  unfold wf_pinstr_tiling_witness in Hwf.
  lia.
Qed.

Theorem tiling_rel_pinstr_structure_raccess_lifted:
  forall env before after w point params,
    tiling_rel_pinstr_structure (length env) before after w ->
    wf_pinstr_tiling_witness w ->
    List.map
      (fun acc => exact_cell acc (eval_pinstr_tiling_index_with_env env point params w))
      (PL.pi_raccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_raccess before).
Proof.
  intros env before after w point params Hrel Hwf.
  unfold eval_pinstr_tiling_index_with_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  eapply tiling_rel_pinstr_structure_raccess_exact_cells; eauto.
  rewrite eval_tile_links_length.
  simpl.
  unfold wf_pinstr_tiling_witness in Hwf.
  lia.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_waccess_lifted:
  forall env before after w point params,
    tiling_rel_pinstr_structure_compiled (length env) before after w ->
    List.map
      (fun acc =>
         exact_cell acc
           (eval_pinstr_tiling_index_with_env
              env point params (compiled_pinstr_tiling_witness w)))
      (PL.pi_waccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_waccess before).
Proof.
  intros env before after w point params Hrel.
  eapply tiling_rel_pinstr_structure_waccess_lifted.
  - exact Hrel.
  - apply wf_compiled_pinstr_tiling_witness.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_raccess_lifted:
  forall env before after w point params,
    tiling_rel_pinstr_structure_compiled (length env) before after w ->
    List.map
      (fun acc =>
         exact_cell acc
           (eval_pinstr_tiling_index_with_env
              env point params (compiled_pinstr_tiling_witness w)))
      (PL.pi_raccess after) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_raccess before).
Proof.
  intros env before after w point params Hrel.
  eapply tiling_rel_pinstr_structure_raccess_lifted.
  - exact Hrel.
  - apply wf_compiled_pinstr_tiling_witness.
Qed.

Theorem tiling_rel_pprog_structure_compiled_waccess_lifted_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.map
      (fun acc =>
         exact_cell acc
           (eval_pinstr_tiling_index_with_env
              env point env (compiled_pinstr_tiling_witness w)))
      (PL.pi_waccess after_pi) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_waccess before_pi).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  cbn in Hstmt.
  rewrite <- Henv_len in Hstmt.
  eapply tiling_rel_pinstr_structure_compiled_waccess_lifted; eauto.
Qed.

Theorem tiling_rel_pprog_structure_compiled_raccess_lifted_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.map
      (fun acc =>
         exact_cell acc
           (eval_pinstr_tiling_index_with_env
              env point env (compiled_pinstr_tiling_witness w)))
      (PL.pi_raccess after_pi) =
    List.map
      (fun acc => exact_cell acc (env ++ point))
      (PL.pi_raccess before_pi).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  eapply tiling_rel_pinstr_structure_compiled_raccess_lifted; eauto.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_old_schedule_lifted :
  forall env before after w point,
    tiling_rel_pinstr_structure_compiled (length env) before after w ->
    affine_product
      (lift_schedule_after_env (List.length (stw_links w)) (List.length env)
         (PL.pi_schedule before))
      (eval_pinstr_tiling_index_with_env
         env point env (compiled_pinstr_tiling_witness w)) =
    affine_product
      (PL.pi_schedule before)
      (env ++ point).
Proof.
  intros env before after w point Hrel.
  unfold eval_pinstr_tiling_index_with_env,
         eval_statement_tiling_witness_with_env,
         eval_statement_tiling_witness,
         lift_point.
  apply lift_affine_function_after_env_eval.
  - reflexivity.
  - rewrite eval_tile_links_length. simpl. reflexivity.
Qed.

Theorem tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    affine_product
      (PL.pi_schedule1_ext
         (compose_tiling_pinstr_ext (List.length env) before_pi after_pi w))
      (PL.ip_index_ext
         (compose_tiling_instr_point_ext n env point before_pi after_pi w)) =
    affine_product
      (PL.pi_schedule before_pi)
      (env ++ point).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  unfold compose_tiling_pinstr_ext, compose_tiling_instr_point_ext.
  simpl.
  eapply tiling_rel_pinstr_structure_compiled_old_schedule_lifted; eauto.
Qed.

Theorem tiling_rel_pprog_structure_compiled_belongs_to_ext_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (env ++ point) (PL.pi_poly before_pi) = true ->
    PL.belongs_to_ext
      (compose_tiling_instr_point_ext n env point before_pi after_pi w)
      (compose_tiling_pinstr_ext (List.length env) before_pi after_pi w).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hpoint_dim Hwf_stmt Hsizes Hbefore_dom.
  unfold PL.belongs_to_ext, compose_tiling_instr_point_ext, compose_tiling_pinstr_ext.
  simpl.
  repeat split; try reflexivity.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  eapply tiling_rel_pinstr_structure_compiled_domain_lifted; eauto.
Qed.

Definition tiled_added_part
    (env_size added_dims: nat) (idx: list Z) : list Z :=
  firstn added_dims (skipn env_size idx).

Definition tiled_point_part
    (env_size added_dims: nat) (idx: list Z) : list Z :=
  skipn (env_size + added_dims) idx.

Definition before_index_of_retiled_old
    (env_size added_dims: nat) (idx: list Z) : list Z :=
  firstn env_size idx ++ tiled_point_part env_size added_dims idx.

Definition before_of_retiled_old_point
    (env_size added_dims: nat)
    (before: PL.PolyInstr)
    (ip_old: PL.InstrPoint) : PL.InstrPoint :=
  let idx_before := before_index_of_retiled_old env_size added_dims (PL.ip_index ip_old) in
  {|
    PL.ip_nth := PL.ip_nth ip_old;
    PL.ip_index := idx_before;
    PL.ip_transformation := PL.current_transformation_of before idx_before;
    PL.ip_time_stamp := affine_product (PL.pi_schedule before) idx_before;
    PL.ip_instruction := PL.pi_instr before;
    PL.ip_depth := PL.pi_depth before;
  |}.

Definition before_ipl_from_retiled_old
    (env_size added_dims: nat)
    (before: PL.PolyInstr)
    (ipl_old: list PL.InstrPoint) : list PL.InstrPoint :=
  List.map (before_of_retiled_old_point env_size added_dims before) ipl_old.

Definition before_of_retiled_old_point_source
    (env_size added_dims: nat)
    (before: PL.PolyInstr)
    (ip_old: PL.InstrPoint) : PL.InstrPoint :=
  let idx_before := before_index_of_retiled_old env_size added_dims (PL.ip_index ip_old) in
  {|
    PL.ip_nth := PL.ip_nth ip_old;
    PL.ip_index := idx_before;
    PL.ip_transformation := PL.pi_transformation before;
    PL.ip_time_stamp := affine_product (PL.pi_schedule before) idx_before;
    PL.ip_instruction := PL.pi_instr before;
    PL.ip_depth := PL.pi_depth before;
  |}.

Definition before_ipl_from_retiled_old_source
    (env_size added_dims: nat)
    (before: PL.PolyInstr)
    (ipl_old: list PL.InstrPoint) : list PL.InstrPoint :=
  List.map (before_of_retiled_old_point_source env_size added_dims before) ipl_old.

Lemma before_of_retiled_old_point_eq_source_if_identity :
  forall env_size added_dims before ip_old,
    PL.pi_point_witness before = PSWIdentity (PL.pi_depth before) ->
    before_of_retiled_old_point env_size added_dims before ip_old =
    before_of_retiled_old_point_source env_size added_dims before ip_old.
Proof.
  intros env_size added_dims before ip_old Hwit.
  destruct ip_old as [nth idx tf ts instr depth].
  unfold before_of_retiled_old_point, before_of_retiled_old_point_source.
  simpl.
  unfold PL.current_transformation_of, PL.current_transformation_at.
  rewrite Hwit.
  simpl.
  reflexivity.
Qed.

Definition before_of_retiled_old_pprog_point
    (env_size: nat)
    (before_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (ip_old: PL.InstrPoint) : PL.InstrPoint :=
  match List.nth_error before_pis (PL.ip_nth ip_old),
        List.nth_error ws (PL.ip_nth ip_old) with
  | Some before, Some w =>
      before_of_retiled_old_point env_size (List.length (stw_links w)) before ip_old
  | _, _ => ip_old
  end.

Definition before_ipl_from_retiled_old_pprog
    (env_size: nat)
    (before_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (ipl_old: list PL.InstrPoint) : list PL.InstrPoint :=
  List.map (before_of_retiled_old_pprog_point env_size before_pis ws) ipl_old.

Definition before_of_retiled_old_pprog_point_source
    (env_size: nat)
    (before_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (ip_old: PL.InstrPoint) : PL.InstrPoint :=
  match List.nth_error before_pis (PL.ip_nth ip_old),
        List.nth_error ws (PL.ip_nth ip_old) with
  | Some before, Some w =>
      before_of_retiled_old_point_source
        env_size (List.length (stw_links w)) before ip_old
  | _, _ => ip_old
  end.

Definition before_ipl_from_retiled_old_pprog_source
    (env_size: nat)
    (before_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (ipl_old: list PL.InstrPoint) : list PL.InstrPoint :=
  List.map (before_of_retiled_old_pprog_point_source env_size before_pis ws) ipl_old.

Lemma before_of_retiled_old_pprog_point_app_head :
  forall env_size before_pis ws before_pi w ip_old,
    List.length before_pis = List.length ws ->
    (PL.ip_nth ip_old < List.length before_pis)%nat ->
    before_of_retiled_old_pprog_point
      env_size (before_pis ++ [before_pi]) (ws ++ [w]) ip_old =
    before_of_retiled_old_pprog_point
      env_size before_pis ws ip_old.
Proof.
  intros env_size before_pis ws before_pi w ip_old Hlen Hlt.
  unfold before_of_retiled_old_pprog_point.
  rewrite List.nth_error_app1 by lia.
  rewrite List.nth_error_app1 by lia.
  reflexivity.
Qed.

Lemma before_of_retiled_old_pprog_point_app_tail :
  forall env_size before_pis ws before_pi w ip_old,
    List.length before_pis = List.length ws ->
    PL.ip_nth ip_old = List.length before_pis ->
    before_of_retiled_old_pprog_point
      env_size (before_pis ++ [before_pi]) (ws ++ [w]) ip_old =
    before_of_retiled_old_point
      env_size (List.length (stw_links w)) before_pi ip_old.
Proof.
  intros env_size before_pis ws before_pi w ip_old Hlen Hnth.
  unfold before_of_retiled_old_pprog_point.
  rewrite Hnth.
  rewrite List.nth_error_app2 by lia.
  rewrite Nat.sub_diag.
  simpl.
  rewrite List.nth_error_app2 by lia.
  rewrite Hlen.
  rewrite Nat.sub_diag.
  simpl.
  reflexivity.
Qed.

Lemma before_ipl_from_retiled_old_pprog_app :
  forall env_size before_pis ws before_pi w ipl_old_h ipl_old_t,
    before_ipl_from_retiled_old_pprog
      env_size (before_pis ++ [before_pi]) (ws ++ [w]) (ipl_old_h ++ ipl_old_t) =
    before_ipl_from_retiled_old_pprog
      env_size (before_pis ++ [before_pi]) (ws ++ [w]) ipl_old_h ++
    before_ipl_from_retiled_old_pprog
      env_size (before_pis ++ [before_pi]) (ws ++ [w]) ipl_old_t.
Proof.
  intros.
  unfold before_ipl_from_retiled_old_pprog.
  rewrite map_app.
  reflexivity.
Qed.

Definition instr_point_np_key (ip: PL.InstrPoint) : list Z :=
  Z.of_nat (PL.ip_nth ip) :: PL.ip_index ip.

Definition instr_point_np_ltb (ip1 ip2: PL.InstrPoint) : bool :=
  comparison_eqb
    (lex_compare (instr_point_np_key ip1) (instr_point_np_key ip2))
    Lt.

Definition instr_point_np_eqb (ip1 ip2: PL.InstrPoint) : bool :=
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
    PL.np_eq ip1 ip2.
Proof.
  intros [nth1 idx1 tf1 ts1 instr1 dep1]
         [nth2 idx2 tf2 ts2 instr2 dep2].
  unfold instr_point_np_eqb, instr_point_np_key, PL.np_eq.
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
    PL.np_lt ip1 ip2.
Proof.
  intros [nth1 idx1 tf1 ts1 instr1 dep1]
         [nth2 idx2 tf2 ts2 instr2 dep2].
  unfold instr_point_np_ltb, instr_point_np_key, PL.np_lt.
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
    NoDupA PL.np_eq ipl ->
    Sorted PL.np_lt ipl.
Proof.
  assert (Hhd_strict :
    forall a tail,
      HdRel
        (fun x y =>
           combine_leb instr_point_np_ltb instr_point_np_eqb x y = true)
        a tail ->
      ~ InA PL.np_eq a tail ->
      HdRel PL.np_lt a tail).
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

Lemma before_of_retiled_old_point_prefix :
  forall env before added_dims ip_old,
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    firstn
      (List.length env)
      (PL.ip_index
         (before_of_retiled_old_point
            (List.length env) added_dims before ip_old)) = env.
Proof.
  intros env before added_dims ip_old Hpref.
  unfold before_of_retiled_old_point, before_index_of_retiled_old.
  simpl.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite Nat.min_id.
  rewrite Hpref.
  simpl.
  rewrite Nat.sub_diag.
  rewrite firstn_O.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma before_index_of_retiled_old_length :
  forall (env idx: list Z) (before: PL.PolyInstr) (w: statement_tiling_witness),
    stw_point_dim w = PL.pi_depth before ->
    List.length idx =
      (List.length env + List.length (stw_links w) + stw_point_dim w)%nat ->
    List.length
      (before_index_of_retiled_old
         (List.length env) (List.length (stw_links w)) idx) =
    (List.length env + PL.pi_depth before)%nat.
Proof.
  intros env idx before w Hpoint_depth Hidx_len.
  unfold before_index_of_retiled_old.
  rewrite app_length.
  rewrite firstn_length.
  unfold tiled_point_part.
  rewrite skipn_length.
  rewrite Nat.min_l by lia.
  rewrite Hpoint_depth in Hidx_len.
  lia.
Qed.

Lemma before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext :
  forall n env point before after w,
    before_of_retiled_old_point
      (List.length env) (List.length (stw_links w)) before
      (PL.old_of_ext
         (compose_tiling_instr_point_ext n env point before after w)) =
    {|
      PL.ip_nth := n;
      PL.ip_index := env ++ point;
      PL.ip_transformation :=
        PL.current_transformation_of before (env ++ point);
      PL.ip_time_stamp := affine_product (PL.pi_schedule before) (env ++ point);
      PL.ip_instruction := PL.pi_instr before;
      PL.ip_depth := PL.pi_depth before;
    |}.
Proof.
  intros n env point before after w.
  assert (Hidx :
    before_index_of_retiled_old
      (List.length env)
      (List.length (stw_links w))
      (eval_pinstr_tiling_index_with_env
         env point env (compiled_pinstr_tiling_witness w)) =
    env ++ point).
  {
    unfold before_index_of_retiled_old.
    unfold eval_pinstr_tiling_index_with_env,
           eval_statement_tiling_witness_with_env,
           eval_statement_tiling_witness,
           lift_point.
    rewrite firstn_app.
    rewrite firstn_all2 by reflexivity.
    rewrite Nat.sub_diag.
    simpl.
    assert (Htiled :
      tiled_point_part
        (List.length env)
        (List.length (stw_links w))
        (env ++ (eval_tile_links [] point env (stw_links w) ++ point)) = point).
    {
      remember (stw_links w) as links eqn:Hlinks.
      unfold tiled_point_part.
      rewrite skipn_app_le by lia.
      assert (Hsub :
        (List.length env + List.length links - List.length env)%nat =
        List.length links).
      {
        lia.
      }
      rewrite Hsub.
      simpl.
      apply skipn_eval_tile_links_suffix.
    }
    rewrite Htiled.
    repeat rewrite app_nil_r.
    reflexivity.
  }
  unfold before_of_retiled_old_point, PL.old_of_ext, compose_tiling_instr_point_ext.
  simpl.
  rewrite Hidx.
  reflexivity.
Qed.

Lemma tiled_added_part_length :
  forall idx env_size added_dims point_dim,
    List.length idx = (env_size + added_dims + point_dim)%nat ->
    List.length (tiled_added_part env_size added_dims idx) = added_dims.
Proof.
  intros idx env_size added_dims point_dim Hlen.
  unfold tiled_added_part.
  rewrite firstn_length.
  rewrite skipn_length.
  lia.
Qed.

Lemma tiled_point_part_length :
  forall idx env_size added_dims point_dim,
    List.length idx = (env_size + added_dims + point_dim)%nat ->
    List.length (tiled_point_part env_size added_dims idx) = point_dim.
Proof.
  intros idx env_size added_dims point_dim Hlen.
  unfold tiled_point_part.
  rewrite skipn_length.
  lia.
Qed.

Lemma tiled_index_split :
  forall idx env_size added_dims,
    idx =
    firstn env_size idx ++
    tiled_added_part env_size added_dims idx ++
    tiled_point_part env_size added_dims idx.
Proof.
  intros idx env_size added_dims.
  unfold tiled_added_part, tiled_point_part.
  rewrite <- firstn_skipn with (n := env_size) (l := idx) at 1.
  f_equal.
  rewrite <- firstn_skipn with (n := added_dims) (l := skipn env_size idx) at 1.
  f_equal.
  rewrite skipn_skipn.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Theorem tiling_rel_pprog_structure_compiled_before_of_retiled_old_point_belongs_to_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.belongs_to
      ip_old
      (retiled_old_pinstr (List.length env) before_pi after_pi w) ->
    List.length (PL.ip_index ip_old) =
    (List.length env + PL.pi_depth after_pi)%nat ->
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    PL.belongs_to
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before_pi ip_old)
      before_pi.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hbel_old Hidx_len Hpref.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  pose proof Hstmt as Hstmt_depth.
  destruct Hstmt_depth as [_ [Hdepth_eq _]].
  destruct Hbel_old as [Hafter_dom [_ [_ [_ _]]]].
  unfold retiled_old_pinstr in Hafter_dom.
  simpl in Hafter_dom.
  set (added := tiled_added_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  set (point := tiled_point_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  assert (Hadded_len : List.length added = List.length (stw_links w)).
  {
    subst added.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hpoint_len : List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hidx_split :
    PL.ip_index ip_old = env ++ added ++ point).
  {
    subst added point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_old) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old)).
    - eapply tiled_index_split.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Hbefore_dom :
    in_poly (env ++ point) (PL.pi_poly before_pi) = true).
  {
    pose proof
      (tiling_rel_pinstr_structure_compiled_domain_complete
         env before_pi after_pi w added point
         Hstmt Hadded_len Hpoint_len Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split in Hafter_dom.
    specialize (Hcomplete Hafter_dom).
    tauto.
  }
  unfold PL.belongs_to, before_of_retiled_old_point, before_index_of_retiled_old.
  simpl.
  split.
  - rewrite Hpref.
    exact Hbefore_dom.
  - split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
Qed.

Theorem tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.belongs_to
      ip_old
      (retiled_old_pinstr (List.length env) before_pi after_pi w) ->
    List.length (PL.ip_index ip_old) =
    (List.length env + PL.pi_depth after_pi)%nat ->
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    PL.belongs_to
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before_pi ip_old)
      before_pi.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hbel_old Hidx_len Hpref.
  assert (Hstmt :
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt)
      before_pi after_pi (compiled_pinstr_tiling_witness w)).
  {
    eapply tiling_rel_pprog_structure_source_nth; eauto.
    eapply nth_error_map_some; exact Hw_nth.
  }
  rewrite <- Henv_len in Hstmt.
  assert (Hstmt_old :
    tiling_rel_pinstr_structure_source
      (List.length env)
      before_pi
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      (compiled_pinstr_tiling_witness w)).
  {
    destruct Hstmt as
        [Hinstr_stmt
         [Hdepth_stmt
         [Hwitness_stmt
         [Htf_stmt
         [Hacc_tf_stmt
         [Hpoly_stmt
         [Hwacc_stmt Hracc_stmt]]]]]]].
    unfold tiling_rel_pinstr_structure_source, retiled_old_pinstr.
    simpl.
    repeat split; auto.
  }
  pose proof Hstmt as Hstmt_depth.
  destruct Hstmt_depth as [_ [Hdepth_eq _]].
  destruct Hbel_old as [Hafter_dom [_ [_ [_ _]]]].
  unfold retiled_old_pinstr in Hafter_dom.
  simpl in Hafter_dom.
  set (added := tiled_added_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  set (point := tiled_point_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  assert (Hadded_len : List.length added = List.length (stw_links w)).
  {
    subst added.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hpoint_len : List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hidx_split :
    PL.ip_index ip_old = env ++ added ++ point).
  {
    subst added point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_old) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old)).
    - eapply tiled_index_split.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Hbefore_dom :
    in_poly (env ++ point) (PL.pi_poly before_pi) = true).
  {
    pose proof
      (tiling_rel_pinstr_structure_source_domain_complete
         env before_pi after_pi (compiled_pinstr_tiling_witness w) added point
         Hstmt
         (wf_compiled_pinstr_tiling_witness w)
         (compiled_pinstr_tiling_witness_matches w)
         Hadded_len Hpoint_len Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split in Hafter_dom.
    specialize (Hcomplete Hafter_dom).
    tauto.
  }
  unfold PL.belongs_to, before_of_retiled_old_point, before_index_of_retiled_old.
  simpl.
  split.
  - rewrite Hpref.
    exact Hbefore_dom.
  - split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
Qed.

Theorem tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective :
  forall env before after w ip1 ip2,
    tiling_rel_pinstr_structure_source (List.length env) before after w ->
    wf_pinstr_tiling_witness w ->
    witness_matches_compiled_link_domain w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) (ptw_statement_witness w) ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links (ptw_statement_witness w)) ->
    stw_point_dim (ptw_statement_witness w) = PL.pi_depth before ->
    PL.belongs_to
      ip1
      (retiled_old_pinstr
         (List.length env) before after (ptw_statement_witness w)) ->
    List.length (PL.ip_index ip1) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip1) = env ->
    PL.belongs_to
      ip2
      (retiled_old_pinstr
         (List.length env) before after (ptw_statement_witness w)) ->
    List.length (PL.ip_index ip2) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip2) = env ->
    before_of_retiled_old_point
      (List.length env)
      (List.length (stw_links (ptw_statement_witness w)))
      before ip1 =
    before_of_retiled_old_point
      (List.length env)
      (List.length (stw_links (ptw_statement_witness w)))
      before ip2 ->
    ip1 = ip2.
Proof.
  intros env before after w ip1 ip2
         Hrel Hwf Hmatch Hwf_stmt Hsizes Hpoint_depth
         Hbel1 Hidx_len1 Hpref1
         Hbel2 Hidx_len2 Hpref2
         Heq_before.
  pose proof Hrel as Hrel_depth.
  destruct Hrel_depth as [_ [Hdepth_eq _]].
  destruct Hbel1 as [Hafter_dom1 [Htf1 [Hts1 [Hinstr1 Hdep1]]]].
  destruct Hbel2 as [Hafter_dom2 [Htf2 [Hts2 [Hinstr2 Hdep2]]]].
  unfold retiled_old_pinstr in Hafter_dom1, Hafter_dom2, Htf1, Htf2, Hts1, Hts2,
    Hinstr1, Hinstr2, Hdep1, Hdep2.
  simpl in Hafter_dom1, Hafter_dom2, Htf1, Htf2, Hts1, Hts2, Hinstr1, Hinstr2,
    Hdep1, Hdep2.
  set (added1 := tiled_added_part
                   (List.length env)
                   (List.length (stw_links (ptw_statement_witness w)))
                   (PL.ip_index ip1)).
  set (point1 := tiled_point_part
                   (List.length env)
                   (List.length (stw_links (ptw_statement_witness w)))
                   (PL.ip_index ip1)).
  set (added2 := tiled_added_part
                   (List.length env)
                   (List.length (stw_links (ptw_statement_witness w)))
                   (PL.ip_index ip2)).
  set (point2 := tiled_point_part
                   (List.length env)
                   (List.length (stw_links (ptw_statement_witness w)))
                   (PL.ip_index ip2)).
  assert (Hadded_len1 :
    List.length added1 = List.length (stw_links (ptw_statement_witness w))).
  {
    subst added1.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip1) =
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) +
       PL.pi_depth before)%nat).
    {
      rewrite Hidx_len1, Hdepth_eq.
      unfold wf_pinstr_tiling_witness in Hwf.
      rewrite Hwf.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hpoint_len1 :
    List.length point1 = stw_point_dim (ptw_statement_witness w)).
  {
    subst point1.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip1) =
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) +
       PL.pi_depth before)%nat).
    {
      rewrite Hidx_len1, Hdepth_eq.
      unfold wf_pinstr_tiling_witness in Hwf.
      rewrite Hwf.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hadded_len2 :
    List.length added2 = List.length (stw_links (ptw_statement_witness w))).
  {
    subst added2.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip2) =
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) +
       PL.pi_depth before)%nat).
    {
      rewrite Hidx_len2, Hdepth_eq.
      unfold wf_pinstr_tiling_witness in Hwf.
      rewrite Hwf.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hpoint_len2 :
    List.length point2 = stw_point_dim (ptw_statement_witness w)).
  {
    subst point2.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip2) =
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) +
       PL.pi_depth before)%nat).
    {
      rewrite Hidx_len2, Hdepth_eq.
      unfold wf_pinstr_tiling_witness in Hwf.
      rewrite Hwf.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hidx_split1 :
    PL.ip_index ip1 = env ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length env) (PL.ip_index ip1) ++
       tiled_added_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip1) ++
       tiled_point_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip1)).
    - eapply tiled_index_split.
    - rewrite Hpref1.
      reflexivity.
  }
  assert (Hidx_split2 :
    PL.ip_index ip2 = env ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length env) (PL.ip_index ip2) ++
       tiled_added_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip2) ++
       tiled_point_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip2)).
    - eapply tiled_index_split.
    - rewrite Hpref2.
      reflexivity.
  }
  assert (Hpoint_eq : point1 = point2).
  {
    assert (Hidx_before_eq :
      before_index_of_retiled_old
        (List.length env)
        (List.length (stw_links (ptw_statement_witness w)))
        (PL.ip_index ip1) =
      before_index_of_retiled_old
        (List.length env)
        (List.length (stw_links (ptw_statement_witness w)))
        (PL.ip_index ip2)).
    {
      exact (f_equal PL.ip_index Heq_before).
    }
    unfold before_index_of_retiled_old in Hidx_before_eq.
    subst point1 point2.
    rewrite Hpref1 in Hidx_before_eq.
    rewrite Hpref2 in Hidx_before_eq.
    eapply app_inv_head in Hidx_before_eq.
    exact Hidx_before_eq.
  }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 env (stw_links (ptw_statement_witness w))).
  {
    pose proof
      (tiling_rel_pinstr_structure_source_domain_complete
         env before after w added1 point1
         Hrel Hwf Hmatch Hadded_len1 Hpoint_len1 Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 env (stw_links (ptw_statement_witness w))).
  {
    pose proof
      (tiling_rel_pinstr_structure_source_domain_complete
         env before after w added2 point2
         Hrel Hwf Hmatch Hadded_len2 Hpoint_len2 Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  assert (Hadded_eq : added1 = added2).
  {
    rewrite Hadded_eq1, Hadded_eq2, Hpoint_eq.
    reflexivity.
  }
  assert (Hidx_eq : PL.ip_index ip1 = PL.ip_index ip2).
  {
    rewrite Hidx_split1, Hidx_split2, Hadded_eq, Hpoint_eq.
    reflexivity.
  }
  assert (Hnth_eq : PL.ip_nth ip1 = PL.ip_nth ip2).
  {
    exact (f_equal PL.ip_nth Heq_before).
  }
  assert (Hts_eq : PL.ip_time_stamp ip1 = PL.ip_time_stamp ip2).
  {
    rewrite Hts1, Hts2, Hidx_eq.
    reflexivity.
  }
  assert (Htf_eq : PL.ip_transformation ip1 = PL.ip_transformation ip2).
  {
    rewrite Htf1, Htf2, Hidx_eq.
    reflexivity.
  }
  assert (Hinstr_eq : PL.ip_instruction ip1 = PL.ip_instruction ip2).
  {
    rewrite Hinstr1, Hinstr2.
    reflexivity.
  }
  assert (Hdep_eq : PL.ip_depth ip1 = PL.ip_depth ip2).
  {
    rewrite Hdep1, Hdep2.
    reflexivity.
  }
  destruct ip1 as [nth1 idx1 tfm1 ts1 instr1 dep1].
  destruct ip2 as [nth2 idx2 tfm2 ts2 instr2 dep2].
  simpl in *.
  rewrite Hnth_eq, Hidx_eq, Htf_eq, Hts_eq, Hinstr_eq, Hdep_eq.
  reflexivity.
Qed.

Lemma before_ipl_from_retiled_old_forward_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    In ip_before
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old) ->
    firstn (List.length env) (PL.ip_index ip_before) = env /\
    PL.belongs_to ip_before before_pi /\
    PL.ip_nth ip_before = n /\
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old Hip_before_in.
  unfold before_ipl_from_retiled_old in Hip_before_in.
  apply in_map_iff in Hip_before_in.
  destruct Hip_before_in as [ip_old [Hip_before_eq Hip_old_in]].
  subst ip_before.
  assert (Hstmt :
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt)
      before_pi after_pi (compiled_pinstr_tiling_witness w)).
  {
    eapply tiling_rel_pprog_structure_source_nth; eauto.
    eapply nth_error_map_some; exact Hw_nth.
  }
  rewrite <- Henv_len in Hstmt.
  destruct Hstmt as [_ [Hdepth_eq _]].
  destruct Hflat_old as [Hpref_old [Hmem_old [_ _]]].
  specialize (Hmem_old ip_old).
  destruct Hmem_old as [Hfwd _].
  specialize (Hfwd Hip_old_in).
  destruct Hfwd as [Hpref_ip_old [Hbel_old [Hnth_old Hlen_old]]].
  split.
  - eapply before_of_retiled_old_point_prefix.
    exact Hpref_ip_old.
  - split.
    + eapply tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth; eauto.
    + split.
      * simpl. exact Hnth_old.
      * eapply before_index_of_retiled_old_length; eauto.
        rewrite Hpoint_depth.
        unfold retiled_old_pinstr in Hlen_old.
        simpl in Hlen_old.
        cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq.
        replace (PL.pi_depth after_pi)
          with
          (PL.pi_depth before_pi + List.length (stw_links w))%nat
          in Hlen_old by exact Hdepth_eq.
        replace
          (List.length env +
           (PL.pi_depth before_pi + List.length (stw_links w)))%nat
          with
          (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat
          in Hlen_old by lia.
        exact Hlen_old.
Qed.

Theorem tiling_rel_pinstr_structure_source_before_of_retiled_old_sched_le_iff :
  forall env before after w ip1 ip2,
    tiling_rel_pinstr_structure_source (List.length env) before after w ->
    wf_pinstr_tiling_witness w ->
    stw_point_dim (ptw_statement_witness w) = PL.pi_depth before ->
    PL.belongs_to
      ip1
      (retiled_old_pinstr
         (List.length env) before after (ptw_statement_witness w)) ->
    List.length (PL.ip_index ip1) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip1) = env ->
    PL.belongs_to
      ip2
      (retiled_old_pinstr
         (List.length env) before after (ptw_statement_witness w)) ->
    List.length (PL.ip_index ip2) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip2) = env ->
    (PL.instr_point_sched_le ip1 ip2 <->
     PL.instr_point_sched_le
       (before_of_retiled_old_point
          (List.length env)
          (List.length (stw_links (ptw_statement_witness w)))
          before ip1)
       (before_of_retiled_old_point
          (List.length env)
          (List.length (stw_links (ptw_statement_witness w)))
          before ip2)).
Proof.
  intros env before after w ip1 ip2
         Hrel Hwf Hpoint_depth
         Hbel1 Hidx_len1 Hpref1
         Hbel2 Hidx_len2 Hpref2.
  assert (Hts1 :
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ip1) =
    PL.ip_time_stamp ip1).
  {
    pose proof Hrel as Hrel_depth1.
    destruct Hrel_depth1 as [_ [Hdepth_eq1 _]].
    destruct Hbel1 as [_ [_ [Hts_old1 [_ _]]]].
    set (added1 := tiled_added_part
                    (List.length env)
                    (List.length (stw_links (ptw_statement_witness w)))
                    (PL.ip_index ip1)).
    set (point1 := tiled_point_part
                    (List.length env)
                    (List.length (stw_links (ptw_statement_witness w)))
                    (PL.ip_index ip1)).
    assert (Hidx_split1 :
      PL.ip_index ip1 = env ++ added1 ++ point1).
    {
      subst added1 point1.
      transitivity
        (firstn (List.length env) (PL.ip_index ip1) ++
         tiled_added_part
           (List.length env)
           (List.length (stw_links (ptw_statement_witness w)))
           (PL.ip_index ip1) ++
         tiled_point_part
           (List.length env)
           (List.length (stw_links (ptw_statement_witness w)))
           (PL.ip_index ip1)).
      - eapply tiled_index_split.
      - rewrite Hpref1. reflexivity.
    }
    assert (Hadded_len1 :
      List.length added1 = List.length (stw_links (ptw_statement_witness w))).
    {
      subst added1.
      assert (Hidx_len_split1 :
        List.length (PL.ip_index ip1) =
        (List.length env +
         List.length (stw_links (ptw_statement_witness w)) +
         PL.pi_depth before)%nat).
      {
        rewrite Hidx_len1, Hdepth_eq1.
        unfold wf_pinstr_tiling_witness in Hwf.
        rewrite Hwf.
        lia.
      }
      eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
      exact Hidx_len_split1.
    }
    assert (Hpoint_part_eval1 :
      tiled_point_part
        (List.length env)
        (List.length (stw_links (ptw_statement_witness w)))
        (env ++ added1 ++ point1) = point1).
    {
      unfold tiled_point_part.
      rewrite skipn_app_le by lia.
      replace
        (List.length env +
         List.length (stw_links (ptw_statement_witness w)) -
         List.length env)%nat
        with (List.length (stw_links (ptw_statement_witness w))) by lia.
      rewrite skipn_app by exact Hadded_len1.
      reflexivity.
    }
    unfold before_of_retiled_old_point, before_index_of_retiled_old.
    simpl.
    rewrite Hpref1.
    rewrite Hts_old1.
    rewrite Hidx_split1.
    rewrite Hpoint_part_eval1.
    symmetry.
    eapply lift_affine_function_after_env_eval; eauto.
  }
  assert (Hts2 :
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ip2) =
    PL.ip_time_stamp ip2).
  {
    pose proof Hrel as Hrel_depth2.
    destruct Hrel_depth2 as [_ [Hdepth_eq2 _]].
    destruct Hbel2 as [_ [_ [Hts_old2 [_ _]]]].
    set (added2 := tiled_added_part
                    (List.length env)
                    (List.length (stw_links (ptw_statement_witness w)))
                    (PL.ip_index ip2)).
    set (point2 := tiled_point_part
                    (List.length env)
                    (List.length (stw_links (ptw_statement_witness w)))
                    (PL.ip_index ip2)).
    assert (Hidx_split2 :
      PL.ip_index ip2 = env ++ added2 ++ point2).
    {
      subst added2 point2.
      transitivity
        (firstn (List.length env) (PL.ip_index ip2) ++
         tiled_added_part
           (List.length env)
           (List.length (stw_links (ptw_statement_witness w)))
           (PL.ip_index ip2) ++
         tiled_point_part
           (List.length env)
           (List.length (stw_links (ptw_statement_witness w)))
           (PL.ip_index ip2)).
      - eapply tiled_index_split.
      - rewrite Hpref2. reflexivity.
    }
    assert (Hadded_len2 :
      List.length added2 = List.length (stw_links (ptw_statement_witness w))).
    {
      subst added2.
      assert (Hidx_len_split2 :
        List.length (PL.ip_index ip2) =
        (List.length env +
         List.length (stw_links (ptw_statement_witness w)) +
         PL.pi_depth before)%nat).
      {
        rewrite Hidx_len2, Hdepth_eq2.
        unfold wf_pinstr_tiling_witness in Hwf.
        rewrite Hwf.
        lia.
      }
      eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
      exact Hidx_len_split2.
    }
    assert (Hpoint_part_eval2 :
      tiled_point_part
        (List.length env)
        (List.length (stw_links (ptw_statement_witness w)))
        (env ++ added2 ++ point2) = point2).
    {
      unfold tiled_point_part.
      rewrite skipn_app_le by lia.
      replace
        (List.length env +
         List.length (stw_links (ptw_statement_witness w)) -
         List.length env)%nat
        with (List.length (stw_links (ptw_statement_witness w))) by lia.
      rewrite skipn_app by exact Hadded_len2.
      reflexivity.
    }
    unfold before_of_retiled_old_point, before_index_of_retiled_old.
    simpl.
    rewrite Hpref2.
    rewrite Hts_old2.
    rewrite Hidx_split2.
    rewrite Hpoint_part_eval2.
    symmetry.
    eapply lift_affine_function_after_env_eval; eauto.
  }
  unfold PL.instr_point_sched_le.
  rewrite Hts1, Hts2.
  tauto.
Qed.

Lemma HdRel_before_of_retiled_old_preserved_source :
  forall env before after w ip ipl,
    tiling_rel_pinstr_structure_source (List.length env) before after w ->
    wf_pinstr_tiling_witness w ->
    stw_point_dim (ptw_statement_witness w) = PL.pi_depth before ->
    (forall ip',
      In ip' (ip :: ipl) ->
      PL.belongs_to
        ip'
        (retiled_old_pinstr
           (List.length env) before after (ptw_statement_witness w)) /\
      List.length (PL.ip_index ip') =
      (List.length env + PL.pi_depth after)%nat /\
      firstn (List.length env) (PL.ip_index ip') = env) ->
    HdRel PL.instr_point_sched_le ip ipl ->
    HdRel PL.instr_point_sched_le
      (before_of_retiled_old_point
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ip)
      (before_ipl_from_retiled_old
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ipl).
Proof.
  intros env before after w ip ipl
         Hrel Hwf Hpoint_depth Hprops Hhd.
  induction Hhd as [|b l Hle].
  - simpl. constructor.
  - simpl. constructor.
    destruct (Hprops b (or_intror (or_introl eq_refl)))
      as [Hbel_b [Hlen_b Hpref_b]].
    destruct (Hprops ip (or_introl eq_refl))
      as [Hbel_a [Hlen_a Hpref_a]].
    eapply (proj1
      (tiling_rel_pinstr_structure_source_before_of_retiled_old_sched_le_iff
         env before after w ip b
         Hrel Hwf Hpoint_depth
         Hbel_a Hlen_a Hpref_a
         Hbel_b Hlen_b Hpref_b)).
    exact Hle.
Qed.

Lemma before_of_retiled_old_sorted_sched_preserved_source :
  forall env before after w ipl,
    tiling_rel_pinstr_structure_source (List.length env) before after w ->
    wf_pinstr_tiling_witness w ->
    stw_point_dim (ptw_statement_witness w) = PL.pi_depth before ->
    (forall ip,
      In ip ipl ->
      PL.belongs_to
        ip
        (retiled_old_pinstr
           (List.length env) before after (ptw_statement_witness w)) /\
      List.length (PL.ip_index ip) =
      (List.length env + PL.pi_depth after)%nat /\
      firstn (List.length env) (PL.ip_index ip) = env) ->
    Sorted PL.instr_point_sched_le ipl ->
    Sorted PL.instr_point_sched_le
      (before_ipl_from_retiled_old
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ipl).
Proof.
  intros env before after w ipl
         Hrel Hwf Hpoint_depth Hprops Hsorted.
  induction Hsorted.
  - simpl. constructor.
  - simpl. constructor.
    + eapply IHHsorted.
      intros ip' Hip'.
      eapply Hprops.
      right; exact Hip'.
    + eapply HdRel_before_of_retiled_old_preserved_source; eauto.
Qed.

Lemma before_ipl_from_retiled_old_forward :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    In ip_before
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old) ->
    firstn (List.length env) (PL.ip_index ip_before) = env /\
    PL.belongs_to ip_before before_pi /\
    PL.ip_nth ip_before = n /\
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old Hip_before_in.
  unfold before_ipl_from_retiled_old in Hip_before_in.
  apply in_map_iff in Hip_before_in.
  destruct Hip_before_in as [ip_old [Hip_before_eq Hip_old_in]].
  subst ip_before.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  destruct Hstmt as [_ [Hdepth_eq _]].
  destruct Hflat_old as [Hpref_old [Hmem_old [_ _]]].
  specialize (Hmem_old ip_old).
  destruct Hmem_old as [Hfwd _].
  specialize (Hfwd Hip_old_in).
  destruct Hfwd as [Hpref_ip_old [Hbel_old [Hnth_old Hlen_old]]].
  split.
  - eapply before_of_retiled_old_point_prefix.
    exact Hpref_ip_old.
  - split.
    + eapply tiling_rel_pprog_structure_compiled_before_of_retiled_old_point_belongs_to_nth; eauto.
    + split.
      * simpl.
        exact Hnth_old.
      * eapply before_index_of_retiled_old_length; eauto.
        cbn [retiled_old_pinstr] in Hlen_old.
        cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq.
        rewrite Hpoint_depth.
        replace
          (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat
          with
          (List.length env + (PL.pi_depth before_pi + List.length (stw_links w)))%nat
          by lia.
        rewrite <- Hdepth_eq.
        exact Hlen_old.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_before_of_retiled_old_point_injective :
  forall env before after w ip1 ip2,
    tiling_rel_pinstr_structure_compiled (List.length env) before after w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before ->
    PL.belongs_to
      ip1
      (retiled_old_pinstr (List.length env) before after w) ->
    List.length (PL.ip_index ip1) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip1) = env ->
    PL.belongs_to
      ip2
      (retiled_old_pinstr (List.length env) before after w) ->
    List.length (PL.ip_index ip2) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip2) = env ->
    before_of_retiled_old_point
      (List.length env) (List.length (stw_links w)) before ip1 =
    before_of_retiled_old_point
      (List.length env) (List.length (stw_links w)) before ip2 ->
    ip1 = ip2.
Proof.
  intros env before after w ip1 ip2
         Hrel Hwf_stmt Hsizes Hpoint_depth
         Hbel1 Hidx_len1 Hpref1
         Hbel2 Hidx_len2 Hpref2
         Heq_before.
  pose proof Hrel as Hrel_depth.
  destruct Hrel_depth as [_ [Hdepth_eq _]].
  destruct Hbel1 as [Hafter_dom1 [Htf1 [Hts1 [Hinstr1 Hdep1]]]].
  destruct Hbel2 as [Hafter_dom2 [Htf2 [Hts2 [Hinstr2 Hdep2]]]].
  unfold retiled_old_pinstr in Hafter_dom1, Hafter_dom2, Htf1, Htf2, Hts1, Hts2, Hinstr1, Hinstr2, Hdep1, Hdep2.
  simpl in Hafter_dom1, Hafter_dom2, Htf1, Htf2, Hts1, Hts2, Hinstr1, Hinstr2, Hdep1, Hdep2.
  set (added1 := tiled_added_part (List.length env) (List.length (stw_links w))
                    (PL.ip_index ip1)).
  set (point1 := tiled_point_part (List.length env) (List.length (stw_links w))
                    (PL.ip_index ip1)).
  set (added2 := tiled_added_part (List.length env) (List.length (stw_links w))
                    (PL.ip_index ip2)).
  set (point2 := tiled_point_part (List.length env) (List.length (stw_links w))
                    (PL.ip_index ip2)).
  assert (Hadded_len1 : List.length added1 = List.length (stw_links w)).
  {
    subst added1.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip1) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len1, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hpoint_len1 : List.length point1 = stw_point_dim w).
  {
    subst point1.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip1) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len1, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hadded_len2 : List.length added2 = List.length (stw_links w)).
  {
    subst added2.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip2) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len2, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hpoint_len2 : List.length point2 = stw_point_dim w).
  {
    subst point2.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip2) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len2, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hidx_split1 :
    PL.ip_index ip1 = env ++ added1 ++ point1).
  {
    subst added1 point1.
    transitivity
      (firstn (List.length env) (PL.ip_index ip1) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip1) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip1)).
    - eapply tiled_index_split.
    - rewrite Hpref1.
      reflexivity.
  }
  assert (Hidx_split2 :
    PL.ip_index ip2 = env ++ added2 ++ point2).
  {
    subst added2 point2.
    transitivity
      (firstn (List.length env) (PL.ip_index ip2) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip2) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip2)).
    - eapply tiled_index_split.
    - rewrite Hpref2.
      reflexivity.
  }
  assert (Hpoint_eq : point1 = point2).
  {
    assert (Hidx_before_eq :
      before_index_of_retiled_old
        (List.length env) (List.length (stw_links w)) (PL.ip_index ip1) =
      before_index_of_retiled_old
        (List.length env) (List.length (stw_links w)) (PL.ip_index ip2)).
    {
      exact (f_equal PL.ip_index Heq_before).
    }
    unfold before_index_of_retiled_old in Hidx_before_eq.
    subst point1 point2.
    rewrite Hpref1 in Hidx_before_eq.
    rewrite Hpref2 in Hidx_before_eq.
    eapply app_inv_head in Hidx_before_eq.
    exact Hidx_before_eq.
  }
  assert (Hadded_eq1 :
    added1 = eval_tile_links [] point1 env (stw_links w)).
  {
    pose proof
      (tiling_rel_pinstr_structure_compiled_domain_complete
         env before after w added1 point1
         Hrel Hadded_len1 Hpoint_len1 Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split1 in Hafter_dom1.
    specialize (Hcomplete Hafter_dom1).
    tauto.
  }
  assert (Hadded_eq2 :
    added2 = eval_tile_links [] point2 env (stw_links w)).
  {
    pose proof
      (tiling_rel_pinstr_structure_compiled_domain_complete
         env before after w added2 point2
         Hrel Hadded_len2 Hpoint_len2 Hwf_stmt Hsizes) as Hcomplete.
    rewrite Hidx_split2 in Hafter_dom2.
    specialize (Hcomplete Hafter_dom2).
    tauto.
  }
  assert (Hadded_eq : added1 = added2).
  {
    rewrite Hadded_eq1.
    rewrite Hadded_eq2.
    rewrite Hpoint_eq.
    reflexivity.
  }
  assert (Hidx_eq : PL.ip_index ip1 = PL.ip_index ip2).
  {
    rewrite Hidx_split1.
    rewrite Hidx_split2.
    rewrite Hadded_eq.
    rewrite Hpoint_eq.
    reflexivity.
  }
  assert (Hnth_eq : PL.ip_nth ip1 = PL.ip_nth ip2).
  {
    exact (f_equal PL.ip_nth Heq_before).
  }
  assert (Hts_eq : PL.ip_time_stamp ip1 = PL.ip_time_stamp ip2).
  {
    rewrite Hts1, Hts2.
    rewrite Hidx_eq.
    reflexivity.
  }
  assert (Htf_eq : PL.ip_transformation ip1 = PL.ip_transformation ip2).
  {
    rewrite Htf1, Htf2, Hidx_eq.
    reflexivity.
  }
  assert (Hinstr_eq : PL.ip_instruction ip1 = PL.ip_instruction ip2).
  {
    rewrite Hinstr1, Hinstr2.
    reflexivity.
  }
  assert (Hdep_eq : PL.ip_depth ip1 = PL.ip_depth ip2).
  {
    rewrite Hdep1, Hdep2.
    reflexivity.
  }
  destruct ip1 as [nth1 idx1 tfm1 ts1 instr1 dep1].
  destruct ip2 as [nth2 idx2 tfm2 ts2 instr2 dep2].
  simpl in *.
  rewrite Hnth_eq, Hidx_eq, Htf_eq, Hts_eq, Hinstr_eq, Hdep_eq.
  reflexivity.
Qed.

Lemma before_ipl_from_retiled_old_nodup :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    NoDup
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  destruct Hflat_old as [Hpref_old [Hmem_old [Hnodup_old _]]].
  eapply NoDup_map_on.
  - exact Hnodup_old.
  - intros ip1 ip2 Hin1 Hin2 Heq.
    pose proof (Hpref_old ip1 Hin1) as Hpref1.
    pose proof (Hpref_old ip2 Hin2) as Hpref2.
    pose proof (Hmem_old ip1) as Hmem1.
    pose proof (Hmem_old ip2) as Hmem2.
    destruct Hmem1 as [Hfwd1 _].
    destruct Hmem2 as [Hfwd2 _].
    specialize (Hfwd1 Hin1).
    specialize (Hfwd2 Hin2).
    destruct Hfwd1 as [_ [Hbel1 [_ Hlen1]]].
    destruct Hfwd2 as [_ [Hbel2 [_ Hlen2]]].
    cbn [retiled_old_pinstr] in Hlen1, Hlen2.
    eapply tiling_rel_pinstr_structure_compiled_before_of_retiled_old_point_injective; eauto.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp :
  forall env before after w ip_old,
    tiling_rel_pinstr_structure_compiled (List.length env) before after w ->
    stw_point_dim w = PL.pi_depth before ->
    PL.belongs_to
      ip_old
      (retiled_old_pinstr (List.length env) before after w) ->
    List.length (PL.ip_index ip_old) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before ip_old) =
    PL.ip_time_stamp ip_old.
Proof.
  intros env before after w ip_old
         Hrel Hpoint_depth
         Hbel_old Hidx_len Hpref.
  pose proof Hrel as Hrel_depth.
  destruct Hrel_depth as [_ [Hdepth_eq _]].
  destruct Hbel_old as [_ [_ [Hts_old [_ _]]]].
  unfold retiled_old_pinstr in Hts_old.
  simpl in Hts_old.
  set (added := tiled_added_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  set (point := tiled_point_part (List.length env) (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  assert (Hadded_len : List.length added = List.length (stw_links w)).
  {
    subst added.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hpoint_len : List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hidx_split :
    PL.ip_index ip_old = env ++ added ++ point).
  {
    subst added point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_old) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old)).
    - eapply tiled_index_split.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Hpoint_part_eval :
    tiled_point_part
      (List.length env) (List.length (stw_links w))
      (env ++ added ++ point) = point).
  {
    unfold tiled_point_part.
    rewrite skipn_app_le by lia.
    replace
      (List.length env + List.length (stw_links w) - List.length env)%nat
      with (List.length (stw_links w)) by lia.
    rewrite skipn_app by exact Hadded_len.
    reflexivity.
  }
  unfold before_of_retiled_old_point, before_index_of_retiled_old.
  simpl.
  rewrite Hpref.
  rewrite Hts_old.
  rewrite Hidx_split.
  rewrite Hpoint_part_eval.
  symmetry.
  eapply lift_affine_function_after_env_eval; eauto.
Qed.

Theorem tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp :
  forall env before after w ip_old,
    tiling_rel_pinstr_structure_source (List.length env) before after w ->
    wf_pinstr_tiling_witness w ->
    stw_point_dim (ptw_statement_witness w) = PL.pi_depth before ->
    PL.belongs_to
      ip_old
      (retiled_old_pinstr (List.length env) before after (ptw_statement_witness w)) ->
    List.length (PL.ip_index ip_old) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         before ip_old) =
    PL.ip_time_stamp ip_old.
Proof.
  intros env before after w ip_old
         Hrel Hwf Hpoint_depth
         Hbel_old Hidx_len Hpref.
  pose proof Hrel as Hrel_depth.
  destruct Hrel_depth as [_ [Hdepth_eq _]].
  destruct Hbel_old as [_ [_ [Hts_old [_ _]]]].
  unfold retiled_old_pinstr in Hts_old.
  simpl in Hts_old.
  set (added := tiled_added_part
                  (List.length env)
                  (List.length (stw_links (ptw_statement_witness w)))
                  (PL.ip_index ip_old)).
  set (point := tiled_point_part
                  (List.length env)
                  (List.length (stw_links (ptw_statement_witness w)))
                  (PL.ip_index ip_old)).
  assert (Hadded_len :
    List.length added = List.length (stw_links (ptw_statement_witness w))).
  {
    subst added.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) +
       PL.pi_depth before)%nat).
    {
      rewrite Hidx_len, Hdepth_eq.
      unfold wf_pinstr_tiling_witness in Hwf.
      rewrite Hwf.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before).
    exact Hidx_len_split.
  }
  assert (Hidx_split :
    PL.ip_index ip_old =
    env ++ added ++ point).
  {
    subst added point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_old) ++
       tiled_added_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip_old) ++
       tiled_point_part
         (List.length env)
         (List.length (stw_links (ptw_statement_witness w)))
         (PL.ip_index ip_old)).
    - eapply tiled_index_split.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Hpoint_part_eval :
    tiled_point_part
      (List.length env)
      (List.length (stw_links (ptw_statement_witness w)))
      (env ++ added ++ point) = point).
  {
    unfold tiled_point_part.
    rewrite skipn_app_le by lia.
    replace
      (List.length env +
       List.length (stw_links (ptw_statement_witness w)) -
       List.length env)%nat
      with (List.length (stw_links (ptw_statement_witness w))) by lia.
    rewrite skipn_app by exact Hadded_len.
    reflexivity.
  }
  unfold before_of_retiled_old_point, before_index_of_retiled_old.
  simpl.
  rewrite Hpref.
  rewrite Hts_old.
  rewrite Hidx_split.
  rewrite Hpoint_part_eval.
  symmetry.
  eapply lift_affine_function_after_env_eval; eauto.
Qed.

Theorem tiling_rel_pinstr_structure_compiled_before_of_retiled_old_sched_le_iff :
  forall env before after w ip1 ip2,
    tiling_rel_pinstr_structure_compiled (List.length env) before after w ->
    stw_point_dim w = PL.pi_depth before ->
    PL.belongs_to
      ip1
      (retiled_old_pinstr (List.length env) before after w) ->
    List.length (PL.ip_index ip1) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip1) = env ->
    PL.belongs_to
      ip2
      (retiled_old_pinstr (List.length env) before after w) ->
    List.length (PL.ip_index ip2) =
    (List.length env + PL.pi_depth after)%nat ->
    firstn (List.length env) (PL.ip_index ip2) = env ->
    (PL.instr_point_sched_le ip1 ip2 <->
     PL.instr_point_sched_le
       (before_of_retiled_old_point
          (List.length env) (List.length (stw_links w)) before ip1)
       (before_of_retiled_old_point
          (List.length env) (List.length (stw_links w)) before ip2)).
Proof.
  intros env before after w ip1 ip2
         Hrel Hpoint_depth
         Hbel1 Hidx_len1 Hpref1
         Hbel2 Hidx_len2 Hpref2.
  assert (Hts1 :
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before ip1) =
    PL.ip_time_stamp ip1).
  {
    eapply tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp; eauto.
  }
  assert (Hts2 :
    PL.ip_time_stamp
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before ip2) =
    PL.ip_time_stamp ip2).
  {
    eapply tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp; eauto.
  }
  unfold PL.instr_point_sched_le.
  rewrite Hts1.
  rewrite Hts2.
  tauto.
Qed.

Lemma HdRel_before_of_retiled_old_preserved :
  forall env before after w ip ipl,
    tiling_rel_pinstr_structure_compiled (List.length env) before after w ->
    stw_point_dim w = PL.pi_depth before ->
    (forall ip',
      In ip' (ip :: ipl) ->
      PL.belongs_to
        ip'
        (retiled_old_pinstr (List.length env) before after w) /\
      List.length (PL.ip_index ip') =
      (List.length env + PL.pi_depth after)%nat /\
      firstn (List.length env) (PL.ip_index ip') = env) ->
    HdRel PL.instr_point_sched_le ip ipl ->
    HdRel PL.instr_point_sched_le
      (before_of_retiled_old_point
         (List.length env) (List.length (stw_links w)) before ip)
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before ipl).
Proof.
  intros env before after w ip ipl
         Hrel Hpoint_depth Hprops Hhd.
  induction Hhd as [| b l Hle].
  - simpl.
    constructor.
  - simpl.
    constructor.
    destruct (Hprops b (or_intror (or_introl eq_refl)))
      as [Hbel_b [Hlen_b Hpref_b]].
    destruct (Hprops ip (or_introl eq_refl))
      as [Hbel_a [Hlen_a Hpref_a]].
    eapply (proj1
      (tiling_rel_pinstr_structure_compiled_before_of_retiled_old_sched_le_iff
         env before after w ip b
         Hrel Hpoint_depth
         Hbel_a Hlen_a Hpref_a
         Hbel_b Hlen_b Hpref_b)).
    exact Hle.
Qed.

Lemma before_of_retiled_old_sorted_sched_preserved :
  forall env before after w ipl,
    tiling_rel_pinstr_structure_compiled (List.length env) before after w ->
    stw_point_dim w = PL.pi_depth before ->
    (forall ip,
      In ip ipl ->
      PL.belongs_to
        ip
        (retiled_old_pinstr (List.length env) before after w) /\
      List.length (PL.ip_index ip) =
      (List.length env + PL.pi_depth after)%nat /\
      firstn (List.length env) (PL.ip_index ip) = env) ->
    Sorted PL.instr_point_sched_le ipl ->
    Sorted PL.instr_point_sched_le
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before ipl).
Proof.
  intros env before after w ipl
         Hrel Hpoint_depth Hprops Hsorted.
  induction Hsorted.
  - simpl.
    constructor.
  - simpl.
    constructor.
    + eapply IHHsorted.
      intros ip' Hip'.
      eapply Hprops.
      right.
      exact Hip'.
    + eapply HdRel_before_of_retiled_old_preserved; eauto.
Qed.

Theorem tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old st1 st2,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi) ->
    PL.belongs_to
      ip_old
      (retiled_old_pinstr (List.length env) before_pi after_pi w) ->
    List.length (PL.ip_index ip_old) =
    (List.length env + PL.pi_depth after_pi)%nat ->
    firstn (List.length env) (PL.ip_index ip_old) = env ->
    (PL.ILSema.instr_point_sema ip_old st1 st2 <->
     PL.ILSema.instr_point_sema
       (before_of_retiled_old_point
          (List.length env) (List.length (stw_links w)) before_pi ip_old)
       st1 st2).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_old st1 st2
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hbefore_id Hbel_old Hidx_len Hpref.
  assert (Hstmt :
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt)
      before_pi after_pi (compiled_pinstr_tiling_witness w)).
  {
    eapply tiling_rel_pprog_structure_source_nth; eauto.
    eapply nth_error_map_some; exact Hw_nth.
  }
  rewrite <- Henv_len in Hstmt.
  assert (Hstmt_old :
    tiling_rel_pinstr_structure_source
      (List.length env)
      before_pi
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      (compiled_pinstr_tiling_witness w)).
  {
    destruct Hstmt as
        [Hinstr_stmt
         [Hdepth_stmt
         [Hwitness_stmt
         [Htf_stmt
         [Hacc_tf_stmt
         [Hpoly_stmt
         [Hwacc_stmt Hracc_stmt]]]]]]].
    unfold tiling_rel_pinstr_structure_source, retiled_old_pinstr.
    simpl.
    repeat split; auto.
  }
  pose proof Hstmt as Hstmt_depth.
  destruct Hstmt_depth as [_ [Hdepth_eq _]].
  destruct Hbel_old as [Hafter_dom [Htf_old [_ [Hinstr_old _]]]].
  unfold retiled_old_pinstr in Hafter_dom, Htf_old, Hinstr_old.
  simpl in Hafter_dom, Htf_old, Hinstr_old.
  set (added := tiled_added_part
                  (List.length env)
                  (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  set (point := tiled_point_part
                  (List.length env)
                  (List.length (stw_links w))
                  (PL.ip_index ip_old)).
  assert (Hadded_len : List.length added = List.length (stw_links w)).
  {
    subst added.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_added_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hpoint_len : List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    assert (Hidx_len_split :
      List.length (PL.ip_index ip_old) =
      (List.length env + List.length (stw_links w) + PL.pi_depth before_pi)%nat).
    {
      cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq |- *.
      rewrite Hidx_len, Hdepth_eq.
      lia.
    }
    eapply tiled_point_part_length with (point_dim := PL.pi_depth before_pi).
    exact Hidx_len_split.
  }
  assert (Hidx_split :
    PL.ip_index ip_old = env ++ added ++ point).
  {
    subst added point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_old) ++
       tiled_added_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old) ++
       tiled_point_part (List.length env) (List.length (stw_links w))
         (PL.ip_index ip_old)).
    - eapply tiled_index_split.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Heval_idx :
    eval_pinstr_tiling_index_with_env
      env point env (compiled_pinstr_tiling_witness w) =
    PL.ip_index ip_old).
  {
    pose proof
      (tiling_rel_pinstr_structure_source_domain_complete
         env before_pi after_pi (compiled_pinstr_tiling_witness w) added point
         Hstmt
         (wf_compiled_pinstr_tiling_witness w)
         (compiled_pinstr_tiling_witness_matches w)
         Hadded_len Hpoint_len Hwf_stmt Hsizes)
      as Hcomplete.
    rewrite Hidx_split in Hafter_dom.
    specialize (Hcomplete Hafter_dom).
    destruct Hcomplete as [Hadded_eq _].
    transitivity (env ++ added ++ point).
    - symmetry.
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      rewrite Hadded_eq.
      reflexivity.
    - symmetry.
      exact Hidx_split.
  }
  assert (Hpoint_eq :
    before_of_retiled_old_point
      (List.length env) (List.length (stw_links w)) before_pi ip_old =
    before_of_retiled_old_point_source
      (List.length env) (List.length (stw_links w)) before_pi ip_old).
  {
    eapply before_of_retiled_old_point_eq_source_if_identity.
    exact Hbefore_id.
  }
  split; intro Hsem.
  - inversion Hsem as [wcs rcs Hinst]; subst.
    rewrite Hpoint_eq.
    econstructor.
    unfold before_of_retiled_old_point_source, before_index_of_retiled_old.
    simpl.
    rewrite Hpref.
    rewrite Htf_old in Hinst.
    rewrite Hinstr_old in Hinst.
    rewrite <- Heval_idx in Hinst.
    eapply (proj1
      (tiling_rel_pinstr_structure_source_instr_semantics_lifted_iff
         env before_pi
         (retiled_old_pinstr (List.length env) before_pi after_pi w)
         (compiled_pinstr_tiling_witness w)
         point env wcs rcs st1 st2
         Hstmt_old (wf_compiled_pinstr_tiling_witness w) Hpoint_len)).
    exact Hinst.
  - rewrite Hpoint_eq in Hsem.
    inversion Hsem as [wcs rcs Hinst]; subst.
    econstructor.
    rewrite Htf_old.
    rewrite Hinstr_old.
    rewrite <- Heval_idx.
    unfold before_of_retiled_old_point_source, before_index_of_retiled_old in Hinst.
    simpl in Hinst.
    rewrite Hpref in Hinst.
    eapply (proj2
      (tiling_rel_pinstr_structure_source_instr_semantics_lifted_iff
         env before_pi
         (retiled_old_pinstr (List.length env) before_pi after_pi w)
         (compiled_pinstr_tiling_witness w)
         point env wcs rcs st1 st2
         Hstmt_old (wf_compiled_pinstr_tiling_witness w) Hpoint_len)).
    exact Hinst.
Qed.

Lemma before_of_retiled_old_list_semantics_preserved :
  forall env_size added_dims before ipl_old st1 st2,
    (forall ip s1 s2,
      In ip ipl_old ->
      (PL.ILSema.instr_point_sema ip s1 s2 <->
       PL.ILSema.instr_point_sema
         (before_of_retiled_old_point env_size added_dims before ip) s1 s2)) ->
    PL.ILSema.instr_point_list_semantics ipl_old st1 st2 ->
    PL.ILSema.instr_point_list_semantics
      (before_ipl_from_retiled_old env_size added_dims before ipl_old)
      st1 st2.
Proof.
  intros env_size added_dims before ipl_old st1 st2 Hequiv Hsema.
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

Lemma instr_point_list_semantics_map_preserved :
  forall (f: PL.InstrPoint -> PL.InstrPoint) ipl st1 st2,
    (forall ip s1 s2,
      In ip ipl ->
      (PL.ILSema.instr_point_sema ip s1 s2 <->
       PL.ILSema.instr_point_sema (f ip) s1 s2)) ->
    PL.ILSema.instr_point_list_semantics ipl st1 st2 ->
    PL.ILSema.instr_point_list_semantics (List.map f ipl) st1 st2.
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
  forall (f: PL.InstrPoint -> PL.InstrPoint) ip ipl,
    (forall ip',
      In ip' (ip :: ipl) ->
      PL.ip_time_stamp (f ip') = PL.ip_time_stamp ip') ->
    HdRel PL.instr_point_sched_le ip ipl ->
    HdRel PL.instr_point_sched_le (f ip) (List.map f ipl).
Proof.
  intros f ip ipl Hts Hhd.
  induction Hhd as [|b l Hle].
  - simpl.
    constructor.
  - simpl.
    constructor.
    unfold PL.instr_point_sched_le in *.
    rewrite (Hts ip (or_introl eq_refl)).
    rewrite (Hts b (or_intror (or_introl eq_refl))).
    exact Hle.
Qed.

Lemma sorted_sched_map_time_stamp_preserved :
  forall (f: PL.InstrPoint -> PL.InstrPoint) ipl,
    (forall ip,
      In ip ipl ->
      PL.ip_time_stamp (f ip) = PL.ip_time_stamp ip) ->
    Sorted PL.instr_point_sched_le ipl ->
    Sorted PL.instr_point_sched_le (List.map f ipl).
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

Theorem tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (env ++ point) (PL.pi_poly before_pi) = true ->
    PL.belongs_to
      (PL.old_of_ext
         (compose_tiling_instr_point_ext n env point before_pi after_pi w))
      (retiled_old_pinstr (List.length env) before_pi after_pi w).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hpoint_dim Hwf_stmt Hsizes Hbefore_dom.
  assert (Hstmt :
    tiling_rel_pinstr_structure_compiled
      (List.length env) before_pi after_pi w).
  {
    pose proof
      (tiling_rel_pprog_structure_compiled_nth
         before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt0.
    rewrite <- Henv_len in Hstmt0.
    exact Hstmt0.
  }
  unfold PL.belongs_to, PL.old_of_ext, compose_tiling_instr_point_ext, retiled_old_pinstr.
  simpl.
  split.
  - eapply tiling_rel_pinstr_structure_compiled_domain_lifted; eauto.
  - split.
    + unfold current_src_transformation_of_pinstr.
      unfold PL.current_transformation_of, PL.current_env_dim_of.
      cbn [retiled_old_pinstr].
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      destruct Hstmt as [_ [_ [Hwitness_after _]]].
      unfold PL.current_transformation_at, PL.current_transformation_for_witness.
      rewrite Hwitness_after.
      simpl.
      assert (Henv_dim_cur :
        (List.length (env ++ eval_tile_links [] point env (stw_links w) ++ point) -
         witness_current_point_dim (PSWTiling w))%nat =
        List.length env).
      {
        assert (Hidx_len :
          List.length (env ++ eval_tile_links [] point env (stw_links w) ++ point) =
          (List.length env + witness_current_point_dim (PSWTiling w))%nat).
        {
          repeat rewrite app_length.
          simpl.
          rewrite (eval_tile_links_length [] point env (stw_links w)).
          rewrite Hpoint_dim.
          unfold witness_current_point_dim, witness_added_dims, witness_base_point_dim.
          remember (List.length env) as a.
          remember (List.length (stw_links w)) as b.
          remember (stw_point_dim w) as c.
          simpl.
          lia.
        }
        rewrite Hidx_len.
        lia.
      }
      rewrite Henv_dim_cur.
      reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split; reflexivity.
Qed.

Theorem tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_before,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    firstn (List.length env) (PL.ip_index ip_before) = env ->
    PL.belongs_to ip_before before_pi ->
    PL.ip_nth ip_before = n ->
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat ->
    exists ip_old,
      ip_old =
        PL.old_of_ext
          (compose_tiling_instr_point_ext
             n env (skipn (List.length env) (PL.ip_index ip_before))
             before_pi after_pi w) /\
      PL.belongs_to
        ip_old
        (retiled_old_pinstr (List.length env) before_pi after_pi w) /\
      before_of_retiled_old_point
        (List.length env) (List.length (stw_links w)) before_pi ip_old =
      ip_before.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hpref Hbel_before Hnth_before Hlen_before.
  set (point := skipn (List.length env) (PL.ip_index ip_before)).
  assert (Hidx_before :
    PL.ip_index ip_before = env ++ point).
  {
    subst point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_before) ++
       skipn (List.length env) (PL.ip_index ip_before)).
    - symmetry.
      apply firstn_skipn.
    - rewrite Hpref.
      reflexivity.
  }
  assert (Hpoint_len :
    List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    rewrite skipn_length.
    lia.
  }
  destruct Hbel_before as
    [Hdom_before [Htf_before [Hts_before [Hinstr_before Hdepth_before]]]].
  exists
    (PL.old_of_ext
       (compose_tiling_instr_point_ext n env point before_pi after_pi w)).
  split.
  - reflexivity.
  - split.
    + eapply tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth; try eassumption.
      rewrite Hidx_before in Hdom_before.
      exact Hdom_before.
    + pose proof
        (before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext
           n env point before_pi after_pi w) as Hcanon.
      transitivity
        {|
          PL.ip_nth := n;
          PL.ip_index := env ++ point;
          PL.ip_transformation :=
            PL.current_transformation_of before_pi (env ++ point);
          PL.ip_time_stamp := affine_product (PL.pi_schedule before_pi) (env ++ point);
          PL.ip_instruction := PL.pi_instr before_pi;
          PL.ip_depth := PL.pi_depth before_pi;
        |}.
      * exact Hcanon.
      * destruct ip_before as [nth idx tf ts instr depth].
        simpl in *.
        rewrite <- Hnth_before.
        rewrite <- Hidx_before.
        rewrite Htf_before.
        rewrite Hts_before.
        rewrite Hinstr_before.
        rewrite Hdepth_before.
        reflexivity.
Qed.

Lemma before_ipl_from_retiled_old_backward :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    firstn (List.length env) (PL.ip_index ip_before) = env ->
    PL.belongs_to ip_before before_pi ->
    PL.ip_nth ip_before = n ->
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat ->
    In ip_before
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old Hpref_before Hbel_before Hnth_before Hlen_before.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  destruct Hstmt as [_ [Hdepth_eq _]].
  pose proof
    (tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       env ip_before
       Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
       Hwf_stmt Hsizes Hpoint_depth
       Hpref_before Hbel_before Hnth_before Hlen_before)
    as Hpreimage.
  destruct Hpreimage as [ip_old [Hip_old_eq [Hbel_old Hmap]]].
  destruct Hflat_old as [_ [Hmem_old _]].
  specialize (Hmem_old ip_old).
  destruct Hmem_old as [_ Hback].
  assert (Hip_old_in : In ip_old ipl_old).
  {
    apply Hback.
    subst ip_old.
    split.
    - unfold PL.old_of_ext, compose_tiling_instr_point_ext.
      simpl.
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      rewrite firstn_app.
      rewrite firstn_all2 by reflexivity.
      rewrite Nat.sub_diag.
      simpl.
      rewrite app_nil_r.
      reflexivity.
    - split.
      + exact Hbel_old.
      + split.
        * unfold PL.old_of_ext, compose_tiling_instr_point_ext.
          simpl.
          reflexivity.
        * unfold PL.old_of_ext, compose_tiling_instr_point_ext.
          simpl.
          unfold eval_pinstr_tiling_index_with_env,
                 eval_statement_tiling_witness_with_env,
                 eval_statement_tiling_witness,
                 lift_point.
          set (point := skipn (List.length env) (PL.ip_index ip_before)).
          assert (Hpoint_len : List.length point = stw_point_dim w).
          {
            subst point.
            rewrite Hpoint_depth.
            rewrite skipn_length.
            lia.
          }
          rewrite app_length.
          rewrite app_length.
          rewrite eval_tile_links_length.
          simpl.
          rewrite Hpoint_len.
          assert (Hsum :
            (List.length (stw_links w) + stw_point_dim w = PL.pi_depth after_pi)%nat).
          {
            cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_eq.
            rewrite Hpoint_depth.
            lia.
          }
          replace
            (List.length env + List.length (stw_links w) + stw_point_dim w)%nat
            with
            (List.length env + (List.length (stw_links w) + stw_point_dim w))%nat
            by lia.
          replace
            (List.length env + (List.length (stw_links w) + stw_point_dim w))%nat
            with
            (List.length env + PL.pi_depth after_pi)%nat.
          2: {
            rewrite Hsum.
            reflexivity.
          }
          cbn [retiled_old_pinstr].
          reflexivity.
  }
  unfold before_ipl_from_retiled_old.
  apply in_map_iff.
  exists ip_old.
  split; [exact Hmap|exact Hip_old_in].
Qed.

Theorem tiling_rel_pprog_structure_source_old_point_belongs_to_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (env ++ point) (PL.pi_poly before_pi) = true ->
    PL.belongs_to
      {|
        PL.ip_nth := n;
        PL.ip_index :=
          eval_pinstr_tiling_index_with_env
            env point env (compiled_pinstr_tiling_witness w);
        PL.ip_transformation :=
          PL.current_transformation_of
            (retiled_old_pinstr (List.length env) before_pi after_pi w)
            (eval_pinstr_tiling_index_with_env
               env point env (compiled_pinstr_tiling_witness w));
        PL.ip_time_stamp :=
          affine_product
            (lift_schedule_after_env
               (List.length (stw_links w))
               (List.length env)
               (PL.pi_schedule before_pi))
            (eval_pinstr_tiling_index_with_env
               env point env (compiled_pinstr_tiling_witness w));
        PL.ip_instruction := PL.pi_instr after_pi;
        PL.ip_depth := PL.pi_depth after_pi;
      |}
      (retiled_old_pinstr (List.length env) before_pi after_pi w).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hpoint_dim Hwf_stmt Hsizes Hbefore_dom.
  unfold PL.belongs_to, retiled_old_pinstr.
  simpl.
  split.
  - assert (Hstmt :
      tiling_rel_pinstr_structure_source
        (List.length before_ctxt)
        before_pi after_pi (compiled_pinstr_tiling_witness w)).
    {
      eapply tiling_rel_pprog_structure_source_nth; eauto.
      eapply nth_error_map_some; exact Hw_nth.
    }
    rewrite <- Henv_len in Hstmt.
    eapply tiling_rel_pinstr_structure_source_domain_lifted; eauto.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split; reflexivity.
Qed.

Theorem tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_before,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    firstn (List.length env) (PL.ip_index ip_before) = env ->
    PL.belongs_to ip_before before_pi ->
    PL.ip_nth ip_before = n ->
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat ->
    exists ip_old,
      PL.belongs_to
        ip_old
        (retiled_old_pinstr (List.length env) before_pi after_pi w) /\
      PL.ip_index ip_old =
      eval_pinstr_tiling_index_with_env
        env (skipn (List.length env) (PL.ip_index ip_before))
        env (compiled_pinstr_tiling_witness w) /\
      before_of_retiled_old_point
        (List.length env) (List.length (stw_links w)) before_pi ip_old =
      ip_before.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hpref Hbel_before Hnth_before Hlen_before.
  set (point := skipn (List.length env) (PL.ip_index ip_before)).
  assert (Hidx_before :
    PL.ip_index ip_before = env ++ point).
  {
    subst point.
    transitivity
      (firstn (List.length env) (PL.ip_index ip_before) ++
       skipn (List.length env) (PL.ip_index ip_before)).
    - symmetry. apply firstn_skipn.
    - rewrite Hpref. reflexivity.
  }
  assert (Hpoint_len :
    List.length point = stw_point_dim w).
  {
    subst point.
    rewrite Hpoint_depth.
    rewrite skipn_length.
    lia.
  }
  destruct Hbel_before as
    [Hdom_before [Htf_before [Hts_before [Hinstr_before Hdepth_before]]]].
  set (idx_old :=
    eval_pinstr_tiling_index_with_env env point env (compiled_pinstr_tiling_witness w)).
  exists
    {|
      PL.ip_nth := n;
      PL.ip_index := idx_old;
      PL.ip_transformation :=
        PL.current_transformation_of
          (retiled_old_pinstr (List.length env) before_pi after_pi w)
          idx_old;
      PL.ip_time_stamp :=
        affine_product
          (lift_schedule_after_env
             (List.length (stw_links w))
             (List.length env)
             (PL.pi_schedule before_pi))
          idx_old;
      PL.ip_instruction := PL.pi_instr after_pi;
      PL.ip_depth := PL.pi_depth after_pi;
    |}.
  split.
  - subst idx_old.
    eapply tiling_rel_pprog_structure_source_old_point_belongs_to_nth; eauto.
  - split.
    + subst idx_old point.
      reflexivity.
    + transitivity
      {|
        PL.ip_nth := n;
        PL.ip_index := env ++ point;
        PL.ip_transformation :=
          PL.current_transformation_of before_pi (env ++ point);
        PL.ip_time_stamp := affine_product (PL.pi_schedule before_pi) (env ++ point);
        PL.ip_instruction := PL.pi_instr before_pi;
        PL.ip_depth := PL.pi_depth before_pi;
      |}.
    * subst idx_old.
      unfold before_of_retiled_old_point, before_index_of_retiled_old.
      simpl.
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      rewrite firstn_app.
      rewrite firstn_all2 by reflexivity.
      rewrite Nat.sub_diag.
      simpl.
      assert (Htiled :
        tiled_point_part
          (List.length env)
          (List.length (stw_links w))
          (env ++ (eval_tile_links [] point env (stw_links w) ++ point)) = point).
      {
        remember (stw_links w) as links eqn:Hlinks.
        unfold tiled_point_part.
        rewrite skipn_app_le by lia.
        replace (List.length env + List.length links - List.length env)%nat
          with (List.length links) by lia.
        simpl.
        apply skipn_eval_tile_links_suffix.
      }
      rewrite Htiled.
      repeat rewrite app_nil_r.
      reflexivity.
    * destruct ip_before as [nth idx tf ts instr depth].
      simpl in *.
      rewrite <- Hnth_before.
      rewrite <- Hidx_before.
      rewrite Htf_before.
      rewrite Hts_before.
      rewrite Hinstr_before.
      rewrite Hdepth_before.
      reflexivity.
Qed.

Lemma before_ipl_from_retiled_old_backward_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    firstn (List.length env) (PL.ip_index ip_before) = env ->
    PL.belongs_to ip_before before_pi ->
    PL.ip_nth ip_before = n ->
    List.length (PL.ip_index ip_before) =
      (List.length env + PL.pi_depth before_pi)%nat ->
    In ip_before
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old ip_before
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old Hpref_before Hbel_before Hnth_before Hlen_before.
  pose proof
    (tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       env ip_before
       Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
       Hwf_stmt Hsizes Hpoint_depth
       Hpref_before Hbel_before Hnth_before Hlen_before)
    as Hpreimage.
  destruct Hpreimage as [ip_old [Hbel_old [Hidx_old Hmap]]].
  destruct Hflat_old as [_ [Hmem_old _]].
  specialize (Hmem_old ip_old).
  destruct Hmem_old as [_ Hback].
  assert (Hip_old_in : In ip_old ipl_old).
  {
    apply Hback.
    split.
    - rewrite Hidx_old.
      unfold eval_pinstr_tiling_index_with_env,
             eval_statement_tiling_witness_with_env,
             eval_statement_tiling_witness,
             lift_point.
      rewrite firstn_app.
      rewrite firstn_all2 by reflexivity.
      rewrite Nat.sub_diag.
      simpl.
      rewrite app_nil_r.
      reflexivity.
	    - split.
	      + exact Hbel_old.
	      + split.
	        * pose proof (f_equal PL.ip_nth Hmap) as Hnth_map.
	          simpl in Hnth_map.
	          rewrite Hnth_map.
	          exact Hnth_before.
	        * rewrite Hidx_old.
	          pose proof
	            (nth_error_map_some
	               statement_tiling_witness
	               pinstr_tiling_witness
	               compiled_pinstr_tiling_witness
	               ws n w Hw_nth)
	            as Hw_nth_compiled.
	          pose proof
	            (tiling_rel_pprog_structure_source_nth
	               before_pis before_ctxt before_vars
	               after_pis after_ctxt after_vars
	               (List.map compiled_pinstr_tiling_witness ws)
	               n before_pi after_pi
	               (compiled_pinstr_tiling_witness w)
	               Hprog Hbefore_nth Hafter_nth Hw_nth_compiled)
	            as Hstmt_src.
	          destruct Hstmt_src as [_ [Hdepth_after _]].
	          unfold eval_pinstr_tiling_index_with_env,
	                 eval_statement_tiling_witness_with_env,
	                 eval_statement_tiling_witness,
	                 lift_point.
	          repeat rewrite app_length.
	          rewrite eval_tile_links_length.
	          simpl.
	          rewrite skipn_length.
	          rewrite Hlen_before.
	          cbn [compiled_pinstr_tiling_witness ptw_added_dims] in Hdepth_after.
	          rewrite Hdepth_after.
	          lia.
  }
  unfold before_ipl_from_retiled_old.
  apply in_map_iff.
  exists ip_old.
  split; [exact Hmap|exact Hip_old_in].
Qed.

Lemma flatten_instr_nth_implies_ip_nth :
  forall env n pi ipl ip,
    PL.flatten_instr_nth env n pi ipl ->
    In ip ipl ->
    PL.ip_nth ip = n.
Proof.
  intros env n pi ipl ip Hflat Hin.
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct Hmem as [Hfwd _].
  specialize (Hfwd Hin).
  tauto.
Qed.

Theorem flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    exists ipl_before,
      ipl_before =
        SelectionSort instr_point_np_ltb instr_point_np_eqb
          (before_ipl_from_retiled_old
             (List.length env) (List.length (stw_links w)) before_pi ipl_old) /\
      PL.flatten_instr_nth env n before_pi ipl_before.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  set (raw_before :=
    before_ipl_from_retiled_old
      (List.length env) (List.length (stw_links w)) before_pi ipl_old).
  set (sorted_before :=
    SelectionSort instr_point_np_ltb instr_point_np_eqb raw_before).
  exists sorted_before.
  split; [reflexivity|].
  assert (Hperm_before :
    Permutation raw_before sorted_before).
  {
    subst sorted_before.
    eapply selection_sort_perm.
  }
  assert (Hnodup_raw :
    NoDup raw_before).
  {
    subst raw_before.
    eapply before_ipl_from_retiled_old_nodup; eauto.
  }
  assert (Hnodup_sorted :
    NoDup sorted_before).
  {
    eapply Permutation_NoDup; eauto.
  }
  assert (Hmem_sorted :
    forall ip,
      In ip sorted_before <->
      firstn (List.length env) (PL.ip_index ip) = env /\
      PL.belongs_to ip before_pi /\
      PL.ip_nth ip = n /\
      List.length (PL.ip_index ip) =
        (List.length env + PL.pi_depth before_pi)%nat).
  {
    intros ip.
    split; intro Hin.
    - eapply before_ipl_from_retiled_old_forward.
      + exact Hprog.
      + exact Hbefore_nth.
      + exact Hafter_nth.
      + exact Hw_nth.
      + exact Henv_len.
      + exact Hwf_stmt.
      + exact Hsizes.
      + exact Hpoint_depth.
      + exact Hflat_old.
      + eapply Permutation_in.
        * eapply Permutation_sym. exact Hperm_before.
        * exact Hin.
    - eapply Permutation_in.
      + exact Hperm_before.
      + {
          destruct Hin as [Hpref_before [Hbel_before [Hnth_before Hlen_before]]].
          eapply before_ipl_from_retiled_old_backward.
          - exact Hprog.
          - exact Hbefore_nth.
          - exact Hafter_nth.
          - exact Hw_nth.
          - exact Henv_len.
          - exact Hwf_stmt.
          - exact Hsizes.
          - exact Hpoint_depth.
          - exact Hflat_old.
          - exact Hpref_before.
          - exact Hbel_before.
          - exact Hnth_before.
          - exact Hlen_before.
        }
  }
  assert (HnodupA_sorted :
    NoDupA PL.np_eq sorted_before).
  {
    eapply PL.belongs_to_implies_NoDupA_np.
    - intros ip Hin.
      specialize (Hmem_sorted ip).
      destruct Hmem_sorted as [Hfwd _].
      specialize (Hfwd Hin).
      destruct Hfwd as [_ [Hbel [Hnth Hlen]]].
      destruct Hbel as [Hpoly [Htrans [Hts [Hinss Hdepth]]]].
      repeat split.
      + exact Hpoly.
      + exact Htrans.
      + exact Hts.
      + exact Hinss.
      + exact Hdepth.
      + exact Hnth.
      + exact Hlen.
    - exact Hnodup_sorted.
  }
  assert (Hsortedb :
    Sorted_b (combine_leb instr_point_np_ltb instr_point_np_eqb) sorted_before).
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
  - intros ip Hin.
    specialize (Hmem_sorted ip).
    tauto.
  - split.
    + exact Hmem_sorted.
    + split.
      * exact Hnodup_sorted.
      * eapply sortedb_instr_point_np_implies_sorted_np; eauto.
Qed.

Theorem flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    exists ipl_before,
      PL.flatten_instr_nth env n before_pi ipl_before /\
      Permutation
        ipl_before
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  set (raw_before :=
    before_ipl_from_retiled_old
      (List.length env) (List.length (stw_links w)) before_pi ipl_old).
  set (sorted_before :=
    SelectionSort instr_point_np_ltb instr_point_np_eqb raw_before).
  exists sorted_before.
  split.
  - subst sorted_before raw_before.
    assert (Hperm_before :
      Permutation
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old)
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply selection_sort_perm.
    }
    assert (Hnodup_raw :
      NoDup
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old)).
    {
      eapply before_ipl_from_retiled_old_nodup; eauto.
    }
    assert (Hnodup_sorted :
      NoDup
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply Permutation_NoDup; eauto.
    }
    assert (Hmem_sorted :
      forall ip,
        In ip
          (SelectionSort instr_point_np_ltb instr_point_np_eqb
             (before_ipl_from_retiled_old
                (List.length env) (List.length (stw_links w)) before_pi ipl_old)) <->
        firstn (List.length env) (PL.ip_index ip) = env /\
        PL.belongs_to ip before_pi /\
        PL.ip_nth ip = n /\
        List.length (PL.ip_index ip) =
          (List.length env + PL.pi_depth before_pi)%nat).
    {
      intros ip.
      split; intro Hin.
      - eapply before_ipl_from_retiled_old_forward.
        + exact Hprog.
        + exact Hbefore_nth.
        + exact Hafter_nth.
        + exact Hw_nth.
        + exact Henv_len.
        + exact Hwf_stmt.
        + exact Hsizes.
        + exact Hpoint_depth.
        + exact Hflat_old.
        + eapply Permutation_in.
          * eapply Permutation_sym. exact Hperm_before.
          * exact Hin.
      - eapply Permutation_in.
        + exact Hperm_before.
        + {
            destruct Hin as [Hpref_before [Hbel_before [Hnth_before Hlen_before]]].
            eapply before_ipl_from_retiled_old_backward.
            - exact Hprog.
            - exact Hbefore_nth.
            - exact Hafter_nth.
            - exact Hw_nth.
            - exact Henv_len.
            - exact Hwf_stmt.
            - exact Hsizes.
            - exact Hpoint_depth.
            - exact Hflat_old.
            - exact Hpref_before.
            - exact Hbel_before.
            - exact Hnth_before.
            - exact Hlen_before.
          }
    }
    assert (HnodupA_sorted :
      NoDupA PL.np_eq
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply PL.belongs_to_implies_NoDupA_np.
      - intros ip Hin.
        specialize (Hmem_sorted ip).
        destruct Hmem_sorted as [Hfwd _].
        specialize (Hfwd Hin).
        destruct Hfwd as [_ [Hbel [Hnth Hlen]]].
        destruct Hbel as [Hpoly [Htrans [Hts [Hinss Hdepth]]]].
        repeat split.
        + exact Hpoly.
        + exact Htrans.
        + exact Hts.
        + exact Hinss.
        + exact Hdepth.
        + exact Hnth.
        + exact Hlen.
      - exact Hnodup_sorted.
    }
    assert (Hsortedb :
      Sorted_b
        (combine_leb instr_point_np_ltb instr_point_np_eqb)
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
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
      specialize (Hmem_sorted ip).
      tauto.
    + split.
      * exact Hmem_sorted.
      * split.
        -- exact Hnodup_sorted.
        -- eapply sortedb_instr_point_np_implies_sorted_np; eauto.
  - subst sorted_before raw_before.
    eapply Permutation_sym.
    eapply selection_sort_perm.
Qed.

Theorem tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    List.length point = stw_point_dim w ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    in_poly (env ++ point) (PL.pi_poly before_pi) = true ->
    PL.belongs_to
      (PL.new_of_ext
         (compose_tiling_instr_point_ext n env point before_pi after_pi w))
      after_pi.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env point
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hpoint_dim Hwf_stmt Hsizes Hbefore_dom.
  pose proof
    (tiling_rel_pprog_structure_compiled_nth
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws n before_pi after_pi w
       Hprog Hbefore_nth Hafter_nth Hw_nth) as Hstmt.
  rewrite <- Henv_len in Hstmt.
  unfold PL.belongs_to, PL.new_of_ext, compose_tiling_instr_point_ext.
  simpl.
  split.
  - eapply tiling_rel_pinstr_structure_compiled_domain_lifted; eauto.
  - destruct Hstmt as [_ [_ [Hwitness_after _]]].
    split.
    + unfold current_src_transformation_of_pinstr.
      unfold PL.current_transformation_of, PL.current_env_dim_of.
      unfold PL.current_transformation_at, PL.current_transformation_for_witness.
      rewrite Hwitness_after.
      simpl.
      assert (Henv_dim_cur :
        (List.length
           (eval_pinstr_tiling_index_with_env env point env
              (compiled_pinstr_tiling_witness w)) -
         witness_current_point_dim (PSWTiling w))%nat =
        List.length env).
      {
        assert (Hidx_len :
          List.length
            (eval_pinstr_tiling_index_with_env env point env
               (compiled_pinstr_tiling_witness w)) =
          (List.length env + witness_current_point_dim (PSWTiling w))%nat).
        {
          unfold eval_pinstr_tiling_index_with_env,
                 eval_statement_tiling_witness_with_env,
                 eval_statement_tiling_witness,
                 lift_point.
          repeat rewrite app_length.
          simpl.
          rewrite eval_tile_links_length.
          rewrite Hpoint_dim.
          unfold witness_current_point_dim, witness_added_dims, witness_base_point_dim.
          remember (List.length env) as a.
          remember (List.length (stw_links w)) as b.
          remember (stw_point_dim w) as c.
          simpl.
          lia.
        }
        rewrite Hidx_len.
        lia.
      }
      rewrite Henv_dim_cur.
      reflexivity.
    + split; [reflexivity|].
      split; reflexivity.
Qed.

Definition retiled_old_of_after_point
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness)
    (ip_after: PL.InstrPoint) : PL.InstrPoint := {|
  PL.ip_nth := PL.ip_nth ip_after;
  PL.ip_index := PL.ip_index ip_after;
  PL.ip_transformation := PL.ip_transformation ip_after;
  PL.ip_time_stamp :=
    affine_product
      (lift_schedule_after_env (List.length (stw_links w)) env_size
         (PL.pi_schedule before))
      (PL.ip_index ip_after);
  PL.ip_instruction := PL.ip_instruction ip_after;
  PL.ip_depth := PL.ip_depth ip_after;
|}.

Definition after_point_of_retiled_old
    (after: PL.PolyInstr)
    (ip_old: PL.InstrPoint) : PL.InstrPoint := {|
  PL.ip_nth := PL.ip_nth ip_old;
  PL.ip_index := PL.ip_index ip_old;
  PL.ip_transformation := PL.ip_transformation ip_old;
  PL.ip_time_stamp :=
    affine_product (PL.pi_schedule after) (PL.ip_index ip_old);
  PL.ip_instruction := PL.ip_instruction ip_old;
  PL.ip_depth := PL.ip_depth ip_old;
|}.

Definition compose_tiling_instr_point_ext_from_after
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness)
    (ip_after: PL.InstrPoint) : PL.InstrPoint_ext := {|
  PL.ip_nth_ext := PL.ip_nth ip_after;
  PL.ip_index_ext := PL.ip_index ip_after;
  PL.ip_transformation_ext := PL.ip_transformation ip_after;
  PL.ip_access_transformation_ext := PL.ip_transformation ip_after;
  PL.ip_time_stamp1_ext :=
    affine_product
      (lift_schedule_after_env (List.length (stw_links w)) env_size
         (PL.pi_schedule before))
      (PL.ip_index ip_after);
  PL.ip_time_stamp2_ext := PL.ip_time_stamp ip_after;
  PL.ip_instruction_ext := PL.ip_instruction ip_after;
  PL.ip_depth_ext := PL.ip_depth ip_after;
|}.

Definition retiled_old_ipl_from_after
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness)
    (ipl_after: list PL.InstrPoint) : list PL.InstrPoint :=
  List.map (retiled_old_of_after_point env_size before after w) ipl_after.

Definition compose_tiling_ipl_ext_from_after
    (env_size: nat)
    (before after: PL.PolyInstr)
    (w: statement_tiling_witness)
    (ipl_after: list PL.InstrPoint) : list PL.InstrPoint_ext :=
  List.map (compose_tiling_instr_point_ext_from_after env_size before after w) ipl_after.

Fixpoint retiled_old_pinstrs
    (env_size: nat)
    (before_pis after_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness) : list PL.PolyInstr :=
  match before_pis, after_pis, ws with
  | before_pi :: before_pis', after_pi :: after_pis', w :: ws' =>
      retiled_old_pinstr env_size before_pi after_pi w ::
      retiled_old_pinstrs env_size before_pis' after_pis' ws'
  | _, _, _ => []
  end.

Fixpoint compose_tiling_pinstrs_ext_from_after
    (env_size: nat)
    (before_pis after_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness) : list PL.PolyInstr_ext :=
  match before_pis, after_pis, ws with
  | before_pi :: before_pis', after_pi :: after_pis', w :: ws' =>
      compose_tiling_pinstr_ext env_size before_pi after_pi w ::
      compose_tiling_pinstrs_ext_from_after env_size before_pis' after_pis' ws'
  | _, _, _ => []
  end.

Lemma retiled_old_of_after_point_preserves_np_fields :
  forall env_size before after w ip,
    PL.ip_nth (retiled_old_of_after_point env_size before after w ip) = PL.ip_nth ip /\
    PL.ip_index (retiled_old_of_after_point env_size before after w ip) = PL.ip_index ip.
Proof.
  intros. unfold retiled_old_of_after_point. simpl. auto.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_preserves_np_fields :
  forall env_size before after w ip,
    PL.ip_nth_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip) =
      PL.ip_nth ip /\
    PL.ip_index_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip) =
      PL.ip_index ip.
Proof.
  intros. unfold compose_tiling_instr_point_ext_from_after. simpl. auto.
Qed.

Lemma retiled_old_of_after_point_belongs_to :
  forall env_size before after w ip_after,
    PL.pi_point_witness after = PSWTiling w ->
    PL.belongs_to ip_after after ->
    PL.belongs_to
      (retiled_old_of_after_point env_size before after w ip_after)
      (retiled_old_pinstr env_size before after w).
Proof.
  intros env_size before after w ip_after Hwitness_after Hbel.
  unfold PL.belongs_to in *.
  unfold retiled_old_of_after_point, retiled_old_pinstr.
  simpl in *.
  destruct Hbel as (Hdom & Htf & Hts & Hinstr & Hdepth).
  split.
  - exact Hdom.
  - split.
    + unfold PL.current_transformation_of,
             PL.current_env_dim_of,
             PL.current_transformation_at,
             PL.current_transformation_for_witness in *.
      simpl in *.
      rewrite Hwitness_after in Htf.
      simpl in Htf.
      exact Htf.
    + split.
      * reflexivity.
      * split.
        -- exact Hinstr.
        -- exact Hdepth.
Qed.

Lemma after_point_of_retiled_old_belongs_to :
  forall env_size before after w ip_old,
    PL.pi_point_witness after = PSWTiling w ->
    PL.belongs_to ip_old (retiled_old_pinstr env_size before after w) ->
    PL.belongs_to
      (after_point_of_retiled_old after ip_old)
      after.
Proof.
  intros env_size before after w ip_old Hwitness_after Hbel.
  unfold PL.belongs_to in *.
  unfold after_point_of_retiled_old, retiled_old_pinstr in *.
  simpl in *.
  destruct Hbel as (Hdom & Htf & Hts & Hinstr & Hdepth).
  split.
  - exact Hdom.
  - split.
    + unfold PL.current_transformation_of,
             PL.current_env_dim_of,
             PL.current_transformation_at,
             PL.current_transformation_for_witness in *.
      simpl in *.
      rewrite Hwitness_after.
      simpl.
      exact Htf.
    + split.
      * reflexivity.
      * split.
        -- exact Hinstr.
        -- exact Hdepth.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_belongs_to_ext :
  forall env_size before after w ip_after,
    PL.pi_point_witness after = PSWTiling w ->
    witness_current_point_dim (PL.pi_point_witness after) = PL.pi_depth after ->
    List.length (PL.ip_index ip_after) = (env_size + PL.pi_depth after)%nat ->
    PL.belongs_to ip_after after ->
    PL.belongs_to_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip_after)
      (compose_tiling_pinstr_ext env_size before after w).
Proof.
  intros env_size before after w ip_after
         Hwitness_after Hwitdim Hlen Hbel.
  unfold PL.belongs_to in Hbel.
  unfold PL.belongs_to_ext.
  unfold compose_tiling_instr_point_ext_from_after, compose_tiling_pinstr_ext.
  simpl.
  destruct Hbel as (Hdom & Htf & Hts & Hinstr & Hdepth).
  assert (Henv_dim_cur :
    (List.length (PL.ip_index ip_after) -
     witness_current_point_dim (PL.pi_point_witness after))%nat =
    env_size).
  {
    rewrite Hlen.
    rewrite Hwitdim.
    lia.
  }
  split.
  - exact Hdom.
  - split.
    + unfold current_src_transformation_of_pinstr.
      unfold PL.current_transformation_of, PL.current_env_dim_of in Htf.
      rewrite Henv_dim_cur in Htf.
      exact Htf.
    + split.
      * unfold current_src_transformation_of_pinstr.
        unfold PL.current_transformation_of, PL.current_env_dim_of in Htf.
        rewrite Henv_dim_cur in Htf.
        exact Htf.
      * split.
        -- reflexivity.
        -- split.
          ++ exact Hts.
          ++ split.
            ** exact Hinstr.
            ** exact Hdepth.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_new_of_ext :
  forall env_size before after w ip_after,
    PL.new_of_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip_after) =
    ip_after.
Proof.
  intros.
  unfold PL.new_of_ext, compose_tiling_instr_point_ext_from_after.
  destruct ip_after.
  reflexivity.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_old_of_ext :
  forall env_size before after w ip_after,
    PL.old_of_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip_after) =
    retiled_old_of_after_point env_size before after w ip_after.
Proof.
  intros.
  unfold PL.old_of_ext, compose_tiling_instr_point_ext_from_after.
  unfold retiled_old_of_after_point.
  destruct ip_after.
  reflexivity.
Qed.

Definition after_matches_tiling_witness
    (after: PL.PolyInstr)
    (w: statement_tiling_witness) : Prop :=
  PL.pi_point_witness after = PSWTiling w /\
  witness_current_point_dim (PL.pi_point_witness after) = PL.pi_depth after.

Lemma retiled_old_of_after_point_after_inverse :
  forall env_size before after w ip_after,
    retiled_old_of_after_point env_size before after w
      (after_point_of_retiled_old after
         (retiled_old_of_after_point env_size before after w ip_after)) =
    retiled_old_of_after_point env_size before after w ip_after.
Proof.
  intros.
  unfold retiled_old_of_after_point, after_point_of_retiled_old.
  destruct ip_after.
  reflexivity.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_after_inverse :
  forall env_size before after w ip_ext,
    PL.belongs_to_ext ip_ext (compose_tiling_pinstr_ext env_size before after w) ->
    compose_tiling_instr_point_ext_from_after env_size before after w
      (PL.new_of_ext ip_ext) = ip_ext.
Proof.
  intros env_size before after w ip_ext Hbel.
  unfold PL.belongs_to_ext in Hbel.
  unfold compose_tiling_instr_point_ext_from_after, compose_tiling_pinstr_ext in *.
  unfold PL.new_of_ext in *.
  destruct ip_ext.
  simpl in *.
  destruct Hbel as (Hdom & Htf & Hts1 & Hts2 & Hinstr & Hdepth).
  subst.
  reflexivity.
Qed.

Lemma new_of_compose_tiling_ipl_ext_from_after :
  forall env_size before after w ipl_after,
    PL.new_of_ext_list
      (compose_tiling_ipl_ext_from_after env_size before after w ipl_after) =
    ipl_after.
Proof.
  intros.
  unfold compose_tiling_ipl_ext_from_after, PL.new_of_ext_list.
  induction ipl_after as [|ip ipl IH]; simpl.
  - reflexivity.
  - rewrite compose_tiling_instr_point_ext_from_after_new_of_ext.
    rewrite IH.
    reflexivity.
Qed.

Lemma old_of_compose_tiling_ipl_ext_from_after :
  forall env_size before after w ipl_after,
    PL.old_of_ext_list
      (compose_tiling_ipl_ext_from_after env_size before after w ipl_after) =
    retiled_old_ipl_from_after env_size before after w ipl_after.
Proof.
  intros.
  unfold compose_tiling_ipl_ext_from_after, PL.old_of_ext_list,
         retiled_old_ipl_from_after.
  induction ipl_after as [|ip ipl IH]; simpl.
  - reflexivity.
  - rewrite compose_tiling_instr_point_ext_from_after_old_of_ext.
    rewrite IH.
    reflexivity.
Qed.

Lemma retiled_old_pinstr_eqdom_after :
  forall env_size before after w,
    PL.pi_point_witness after = PSWTiling w ->
    PL.eqdom_pinstr (retiled_old_pinstr env_size before after w) after.
Proof.
  intros env_size before after w Hwitness_after.
  unfold PL.eqdom_pinstr, retiled_old_pinstr.
  simpl.
  repeat split; try reflexivity.
  symmetry.
  exact Hwitness_after.
Qed.

Lemma tiling_rel_pinstr_list_compiled_witnesses :
  forall env_size before_pis after_pis ws,
    tiling_rel_pinstr_list
      env_size before_pis after_pis (List.map compiled_pinstr_tiling_witness ws) ->
    Forall2
      (fun after_pi w => PL.pi_point_witness after_pi = PSWTiling w)
      after_pis ws.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hrel.
  - destruct after_pis, ws; simpl in *; try contradiction; constructor.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try contradiction.
    destruct ws as [|w ws']; simpl in *; try contradiction.
    destruct Hrel as [Hstmt Htl].
    destruct Hstmt as [_ [_ [Hwitness_after _]]].
    constructor.
    + simpl in Hwitness_after.
      exact Hwitness_after.
    + eapply IH.
      exact Htl.
Qed.

Lemma retiled_old_pinstrs_eqdom_after_rel_list :
  forall env_size before_pis after_pis ws,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    Forall2
      (fun after_pi w => PL.pi_point_witness after_pi = PSWTiling w)
      after_pis ws ->
    rel_list
      PL.eqdom_pinstr
      (retiled_old_pinstrs env_size before_pis after_pis ws)
      after_pis.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hlen_after Hlen_ws Hwits.
  - destruct after_pis, ws; simpl in *; try discriminate; constructor.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
    destruct ws as [|w ws']; simpl in *; try discriminate.
    inversion Hwits as [|after_pi' w' after_pis'' ws'' Hwitness_after Hwits']; subst.
    split.
    + apply retiled_old_pinstr_eqdom_after.
      exact Hwitness_after.
    + eapply IH; eauto; lia.
Qed.

Lemma tiling_rel_pprog_structure_compiled_retiled_old_eqdom :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    PL.eqdom_pprog
      (retiled_old_pinstrs (List.length before_ctxt) before_pis after_pis ws,
       before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars ws Hprog.
  unfold PL.eqdom_pprog.
  intros pil1 pil2 varctxt1 varctxt2 vars1 vars2 Hretiled Hafter.
  injection Hretiled as Hvars1 Hctxt1 Hpil1.
  injection Hafter as Hvars2 Hctxt2 Hpil2.
  subst pil1 pil2 varctxt1 varctxt2 vars1 vars2.
  unfold tiling_rel_pprog_structure_compiled,
         tiling_rel_pprog_structure in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  split.
  - exact Hctxt.
  - split.
    + exact Hvars.
    + split.
      * pose proof
          (tiling_rel_pinstr_list_lengths
             (List.length before_ctxt)
             before_pis after_pis
             (List.map compiled_pinstr_tiling_witness ws) Hrel)
          as [Hlen_after Hlen_ws].
        assert
          (Hlen_retiled :
             List.length
               (retiled_old_pinstrs
                  (List.length before_ctxt) before_pis after_pis ws) =
             List.length after_pis).
        {
          clear Hctxt Hvars Hrel.
          revert after_pis ws Hlen_after Hlen_ws.
          induction before_pis as [|before_pi before_pis' IH];
            intros after_pis ws Hlen_after Hlen_ws.
          - destruct after_pis, ws; simpl in *; try discriminate; reflexivity.
          - destruct after_pis as [|after_pi after_pis']; simpl in *;
              try discriminate.
            destruct ws as [|w ws']; simpl in *; try discriminate.
            f_equal.
            eapply IH; lia.
        }
        exact Hlen_retiled.
      * pose proof
          (tiling_rel_pinstr_list_lengths
             (List.length before_ctxt)
             before_pis after_pis
             (List.map compiled_pinstr_tiling_witness ws) Hrel)
          as [Hlen_after Hlen_ws].
        assert (Hlen_before_ws : List.length before_pis = List.length ws).
        {
          rewrite List.map_length in Hlen_ws.
          rewrite Hlen_after.
          exact Hlen_ws.
        }
        pose proof
          (tiling_rel_pinstr_list_compiled_witnesses
             (List.length before_ctxt)
             before_pis after_pis ws Hrel) as Hwits.
        eapply retiled_old_pinstrs_eqdom_after_rel_list; eauto.
Qed.

Lemma after_point_of_retiled_old_after_inverse :
  forall env_size before after w ip_after,
    PL.belongs_to ip_after after ->
    after_point_of_retiled_old after
      (retiled_old_of_after_point env_size before after w ip_after) = ip_after.
Proof.
  intros env_size before after w ip_after Hbel.
  unfold PL.belongs_to in Hbel.
  unfold after_point_of_retiled_old, retiled_old_of_after_point in *.
  destruct ip_after as [n idx tf ts instr depth].
  simpl in *.
  destruct Hbel as (_ & Htf & Hts & Hinstr & Hdepth).
  subst.
  reflexivity.
Qed.

Lemma retiled_old_of_after_point_injective_on_after_points :
  forall env_size before after w ip1 ip2,
    PL.belongs_to ip1 after ->
    PL.belongs_to ip2 after ->
    retiled_old_of_after_point env_size before after w ip1 =
    retiled_old_of_after_point env_size before after w ip2 ->
    ip1 = ip2.
Proof.
  intros env_size before after w ip1 ip2 Hbel1 Hbel2 Heq.
  apply (f_equal (after_point_of_retiled_old after)) in Heq.
  rewrite (after_point_of_retiled_old_after_inverse env_size before after w ip1 Hbel1) in Heq.
  rewrite (after_point_of_retiled_old_after_inverse env_size before after w ip2 Hbel2) in Heq.
  exact Heq.
Qed.

Lemma retiled_old_of_after_point_of_retiled_old :
  forall env_size before after w ip_old,
    PL.belongs_to ip_old (retiled_old_pinstr env_size before after w) ->
    retiled_old_of_after_point env_size before after w
      (after_point_of_retiled_old after ip_old) = ip_old.
Proof.
  intros env_size before after w ip_old Hbel.
  unfold PL.belongs_to in Hbel.
  unfold retiled_old_pinstr, retiled_old_of_after_point, after_point_of_retiled_old in *.
  destruct ip_old as [n idx tf ts instr depth].
  simpl in *.
  destruct Hbel as (_ & Htf & Hts & Hinstr & Hdepth).
  subst.
  reflexivity.
Qed.

Lemma retiled_old_ipl_from_after_nodup :
  forall env_size before after w ipl_after,
    (forall ip, In ip ipl_after -> PL.belongs_to ip after) ->
    NoDup ipl_after ->
    NoDup (retiled_old_ipl_from_after env_size before after w ipl_after).
Proof.
  intros env_size before after w ipl_after Hbel Hnodup.
  unfold retiled_old_ipl_from_after.
  induction Hnodup as [|ip ipl Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip' [Heq Hin']].
      assert (ip' = ip) as Hipeq.
      {
        eapply (retiled_old_of_after_point_injective_on_after_points
                  env_size before after w ip' ip).
        - apply Hbel. right. exact Hin'.
        - apply Hbel. left. reflexivity.
        - exact Heq.
      }
      subst.
      exfalso.
      apply Hnotin.
      exact Hin'.
    + apply IH.
      intros ip' Hin'.
      apply Hbel.
      right. exact Hin'.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_injective :
  forall env_size before after w ip1 ip2,
    compose_tiling_instr_point_ext_from_after env_size before after w ip1 =
    compose_tiling_instr_point_ext_from_after env_size before after w ip2 ->
    ip1 = ip2.
Proof.
  intros env_size before after w ip1 ip2 Heq.
  apply (f_equal PL.new_of_ext) in Heq.
  do 2 rewrite compose_tiling_instr_point_ext_from_after_new_of_ext in Heq.
  exact Heq.
Qed.

Lemma compose_tiling_ipl_ext_from_after_nodup :
  forall env_size before after w ipl_after,
    NoDup ipl_after ->
    NoDup (compose_tiling_ipl_ext_from_after env_size before after w ipl_after).
Proof.
  intros env_size before after w ipl_after Hnodup.
  unfold compose_tiling_ipl_ext_from_after.
  induction Hnodup as [|ip ipl Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip' [Heq Hin']].
      assert (ip' = ip) as Hipeq.
      {
        eapply compose_tiling_instr_point_ext_from_after_injective.
        exact Heq.
      }
      subst.
      exfalso.
      apply Hnotin.
      exact Hin'.
    + exact IH.
Qed.

Lemma compose_tiling_instr_point_ext_from_after_preserves_np_lt :
  forall env_size before after w ip1 ip2,
    PL.np_lt ip1 ip2 ->
    PL.np_lt_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip1)
      (compose_tiling_instr_point_ext_from_after env_size before after w ip2).
Proof.
  intros env_size before after w ip1 ip2 Hlt.
  unfold PL.np_lt, PL.np_lt_ext in *.
  destruct (compose_tiling_instr_point_ext_from_after_preserves_np_fields
              env_size before after w ip1) as [Hnth1 Hidx1].
  destruct (compose_tiling_instr_point_ext_from_after_preserves_np_fields
              env_size before after w ip2) as [Hnth2 Hidx2].
  rewrite Hnth1, Hidx1, Hnth2, Hidx2.
  exact Hlt.
Qed.

Lemma compose_tiling_ipl_ext_from_after_hdrel :
  forall env_size before after w ip ipl,
    HdRel PL.np_lt ip ipl ->
    HdRel
      PL.np_lt_ext
      (compose_tiling_instr_point_ext_from_after env_size before after w ip)
      (compose_tiling_ipl_ext_from_after env_size before after w ipl).
Proof.
  intros env_size before after w ip ipl Hhd.
  induction Hhd.
  - constructor.
  - simpl.
    constructor.
    eapply compose_tiling_instr_point_ext_from_after_preserves_np_lt.
    exact H.
Qed.

Lemma compose_tiling_ipl_ext_from_after_sorted :
  forall env_size before after w ipl_after,
    Sorted PL.np_lt ipl_after ->
    Sorted
      PL.np_lt_ext
      (compose_tiling_ipl_ext_from_after env_size before after w ipl_after).
Proof.
  intros env_size before after w ipl_after Hsorted.
  unfold compose_tiling_ipl_ext_from_after.
  induction Hsorted as [|ip ipl Hsorted IH Hhd]; simpl.
  - constructor.
  - constructor.
    + exact IH.
    + eapply compose_tiling_ipl_ext_from_after_hdrel.
      exact Hhd.
Qed.

Theorem flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old :
  forall envv nth before after w ipl_after,
    after_matches_tiling_witness after w ->
    PL.flatten_instr_nth envv nth after ipl_after ->
    PL.flatten_instr_nth
      envv nth
      (retiled_old_pinstr (List.length envv) before after w)
      (retiled_old_ipl_from_after (List.length envv) before after w ipl_after).
Proof.
  intros envv nth before after w ipl_after Hafter_wit Hflat.
  destruct Hafter_wit as [Hwitness_after Hwitdim_after].
  destruct Hflat as (Hprefix & Hmem & Hnodup & Hsorted).
  refine (conj _ (conj _ (conj _ _))).
  - intros ip_old Hin.
    unfold retiled_old_ipl_from_after in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip_after [Hip_old Hin_after]].
    subst ip_old.
    change
      (firstn (length envv) (PL.ip_index ip_after) = envv).
    eapply Hprefix.
    exact Hin_after.
  - intros ip_old.
    split; intro Hin.
    + unfold retiled_old_ipl_from_after in Hin.
      apply in_map_iff in Hin.
	      destruct Hin as [ip_after [Hip_old Hin_after]].
	      subst ip_old.
	      destruct (Hmem ip_after) as [Hfwd _].
	      specialize (Hfwd Hin_after).
	      destruct Hfwd as (Hpref & Hbel_after & Hnth & Hlen).
	      split; [exact Hpref|].
	      split.
	      * eapply retiled_old_of_after_point_belongs_to; eauto.
	      * split; [exact Hnth|].
	        exact Hlen.
	    + destruct Hin as (Hpref & Hbel_old & Hnth & Hlen).
	      assert (Hbel_after :
	        PL.belongs_to (after_point_of_retiled_old after ip_old) after).
	      {
	        eapply after_point_of_retiled_old_belongs_to; eauto.
	      }
      destruct (Hmem (after_point_of_retiled_old after ip_old)) as [_ Hback].
      assert (Hin_after :
        In (after_point_of_retiled_old after ip_old) ipl_after).
      {
        apply Hback.
        split; [exact Hpref|].
        split; [exact Hbel_after|].
        split; [exact Hnth|].
        exact Hlen.
      }
      unfold retiled_old_ipl_from_after.
      apply in_map_iff.
      exists (after_point_of_retiled_old after ip_old).
      split.
      * eapply retiled_old_of_after_point_of_retiled_old.
        exact Hbel_old.
      * exact Hin_after.
  - eapply retiled_old_ipl_from_after_nodup.
    + intros ip Hin.
      destruct (Hmem ip) as [Hfwd _].
      specialize (Hfwd Hin).
      tauto.
    + exact Hnodup.
  - unfold retiled_old_ipl_from_after.
    eapply PL.Sorted_ipl_map_np_sorted_np.
    + exact Hsorted.
    + intros ip.
      eapply retiled_old_of_after_point_preserves_np_fields.
Qed.

Theorem flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext :
  forall envv nth before after w ipl_after,
    after_matches_tiling_witness after w ->
    PL.flatten_instr_nth envv nth after ipl_after ->
    PL.flatten_instr_nth_ext
      envv nth
      (compose_tiling_pinstr_ext (List.length envv) before after w)
      (compose_tiling_ipl_ext_from_after (List.length envv) before after w ipl_after).
Proof.
  intros envv nth before after w ipl_after Hafter_wit Hflat.
  destruct Hafter_wit as [Hwitness_after Hwitdim_after].
  destruct Hflat as (Hprefix & Hmem & Hnodup & Hsorted).
  refine (conj _ (conj _ (conj _ _))).
  - intros ip_ext Hin.
    unfold compose_tiling_ipl_ext_from_after in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [ip_after [Hip_ext Hin_after]].
    subst ip_ext.
    change
      (firstn (length envv) (PL.ip_index ip_after) = envv).
    eapply Hprefix.
    exact Hin_after.
  - intros ip_ext.
    split; intro Hin.
	    + unfold compose_tiling_ipl_ext_from_after in Hin.
	      apply in_map_iff in Hin.
	      destruct Hin as [ip_after [Hip_ext Hin_after]].
	      subst ip_ext.
	      destruct (Hmem ip_after) as [Hfwd _].
	      specialize (Hfwd Hin_after).
	      destruct Hfwd as (Hpref & Hbel_after & Hnth & Hlen).
	      split; [exact Hpref|].
	      split.
	      * eapply compose_tiling_instr_point_ext_from_after_belongs_to_ext; eauto.
	      * split; [exact Hnth|].
	        exact Hlen.
    + destruct Hin as (Hpref & Hbel_ext & Hnth & Hlen).
      assert (Hbel_after :
        PL.belongs_to (PL.new_of_ext ip_ext) after).
	      {
	        unfold PL.belongs_to_ext in Hbel_ext.
	        unfold PL.belongs_to, compose_tiling_pinstr_ext in *.
	        unfold PL.new_of_ext in *.
	        destruct ip_ext.
	        simpl in *.
		        destruct Hbel_ext as (Hdom & Htf & Hacc_tf & Hts1 & Hts2 & Hinstr & Hdepth).
		        split.
		        - exact Hdom.
		        - split.
		          + unfold current_src_transformation_of_pinstr in Htf.
		            unfold PL.current_transformation_of, PL.current_env_dim_of.
		            assert (Henv_dim_cur :
		              (List.length ip_index_ext -
		               witness_current_point_dim (PL.pi_point_witness after))%nat =
		              List.length envv).
		            {
		              rewrite Hlen.
		              rewrite Hwitdim_after.
		              lia.
		            }
		            rewrite Henv_dim_cur.
		            exact Htf.
		          + split.
		            * exact Hts2.
		            * split.
	              -- exact Hinstr.
	              -- exact Hdepth.
	      }
      destruct (Hmem (PL.new_of_ext ip_ext)) as [_ Hback].
      assert (Hin_after :
        In (PL.new_of_ext ip_ext) ipl_after).
      {
        apply Hback.
        split; [exact Hpref|].
        split; [exact Hbel_after|].
        split; [exact Hnth|].
        exact Hlen.
      }
      unfold compose_tiling_ipl_ext_from_after.
      apply in_map_iff.
      exists (PL.new_of_ext ip_ext).
      split.
      * eapply compose_tiling_instr_point_ext_from_after_after_inverse.
        exact Hbel_ext.
      * exact Hin_after.
  - eapply compose_tiling_ipl_ext_from_after_nodup.
    exact Hnodup.
  - eapply compose_tiling_ipl_ext_from_after_sorted.
    exact Hsorted.
Qed.

Lemma nth_error_retiled_old_pinstrs :
  forall env_size before_pis after_pis ws n before_pi after_pi w,
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.nth_error
      (retiled_old_pinstrs env_size before_pis after_pis ws) n =
    Some (retiled_old_pinstr env_size before_pi after_pi w).
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws n before_pi after_pi w Hbefore Hafter Hw.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct after_pis as [|after_pi0 after_pis']; simpl in *.
    + destruct n; simpl in Hafter; discriminate.
    + destruct ws as [|w0 ws']; simpl in *.
      * destruct n; simpl in Hw; discriminate.
      * destruct n as [|n'].
        -- now inversion Hbefore; inversion Hafter; inversion Hw; subst.
        -- eapply IH; eauto.
Qed.

Lemma nth_error_compose_tiling_pinstrs_ext_from_after :
  forall env_size before_pis after_pis ws n before_pi after_pi w,
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.nth_error
      (compose_tiling_pinstrs_ext_from_after env_size before_pis after_pis ws) n =
    Some (compose_tiling_pinstr_ext env_size before_pi after_pi w).
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws n before_pi after_pi w Hbefore Hafter Hw.
  - destruct n; simpl in Hbefore; discriminate.
  - destruct after_pis as [|after_pi0 after_pis']; simpl in *.
    + destruct n; simpl in Hafter; discriminate.
    + destruct ws as [|w0 ws']; simpl in *.
      * destruct n; simpl in Hw; discriminate.
      * destruct n as [|n'].
        -- now inversion Hbefore; inversion Hafter; inversion Hw; subst.
        -- eapply IH; eauto.
Qed.

Lemma retiled_old_pinstrs_preserve_length :
  forall env_size before_pis after_pis ws,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    List.length (retiled_old_pinstrs env_size before_pis after_pis ws) =
    List.length before_pis.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hlen_after Hlen_ws.
  - destruct after_pis, ws; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
    destruct ws as [|w ws']; simpl in *; try discriminate.
    f_equal.
    eapply IH; lia.
Qed.

Lemma compose_tiling_pinstrs_ext_from_after_preserve_length :
  forall env_size before_pis after_pis ws,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    List.length
      (compose_tiling_pinstrs_ext_from_after env_size before_pis after_pis ws) =
    List.length before_pis.
Proof.
  induction before_pis as [|before_pi before_pis' IH];
    intros after_pis ws Hlen_after Hlen_ws.
  - destruct after_pis, ws; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi after_pis']; simpl in *; try discriminate.
    destruct ws as [|w ws']; simpl in *; try discriminate.
    f_equal.
    eapply IH; lia.
Qed.

Lemma retiled_old_pinstrs_app_singleton :
  forall env_size before_pis after_pis ws before_pi after_pi w,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    retiled_old_pinstrs
      env_size
      (before_pis ++ [before_pi])
      (after_pis ++ [after_pi])
      (ws ++ [w]) =
    retiled_old_pinstrs env_size before_pis after_pis ws ++
    [retiled_old_pinstr env_size before_pi after_pi w].
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws before_pi after_pi w Hlen_after Hlen_ws.
  - destruct after_pis, ws; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi0 after_pis']; simpl in *; try discriminate.
    destruct ws as [|w0 ws']; simpl in *; try discriminate.
    f_equal.
    eapply IH; lia.
Qed.

Lemma compose_tiling_pinstrs_ext_from_after_app_singleton :
  forall env_size before_pis after_pis ws before_pi after_pi w,
    List.length before_pis = List.length after_pis ->
    List.length before_pis = List.length ws ->
    compose_tiling_pinstrs_ext_from_after
      env_size
      (before_pis ++ [before_pi])
      (after_pis ++ [after_pi])
      (ws ++ [w]) =
    compose_tiling_pinstrs_ext_from_after env_size before_pis after_pis ws ++
    [compose_tiling_pinstr_ext env_size before_pi after_pi w].
Proof.
  induction before_pis as [|before_pi0 before_pis' IH];
    intros after_pis ws before_pi after_pi w Hlen_after Hlen_ws.
  - destruct after_pis, ws; simpl in *; try discriminate; reflexivity.
  - destruct after_pis as [|after_pi0 after_pis']; simpl in *; try discriminate.
    destruct ws as [|w0 ws']; simpl in *; try discriminate.
    f_equal.
    eapply IH; lia.
Qed.

Theorem flatten_instrs_after_implies_tiling_ext_exists :
  forall envv before_pis after_pis ws ipl_after,
    List.length before_pis = List.length after_pis ->
    List.length after_pis = List.length ws ->
    Forall2 after_matches_tiling_witness after_pis ws ->
    PL.flatten_instrs envv after_pis ipl_after ->
    exists ipl_old ipl_ext,
      PL.flatten_instrs
        envv
        (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
        ipl_old /\
      PL.flatten_instrs_ext
        envv
        (compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext /\
      PL.old_of_ext_list ipl_ext = ipl_old /\
      PL.new_of_ext_list ipl_ext = ipl_after.
Proof.
  induction before_pis using rev_ind;
    intros after_pis ws ipl_after Hlen_after Hlen_ws Hwits Hflat.
  - assert (after_pis = []) as Hafter_nil.
    {
      apply length_zero_iff_nil.
      symmetry.
      exact Hlen_after.
    }
    assert (ws = []) as Hws_nil.
    {
      apply length_zero_iff_nil.
      rewrite <- Hlen_ws.
      rewrite <- Hlen_after.
      reflexivity.
    }
    subst.
    eapply PL.flatten_instrs_nil_implies_nil in Hflat.
    subst ipl_after.
    exists [], [].
    split.
    + apply PL.flatten_instrs_nil.
    + split.
      * apply PL.flatten_instrs_ext_nil.
      * split; reflexivity.
  - rename x into before_pi.
    assert (exists after_pis' after_pi, after_pis = after_pis' ++ [after_pi]) as Hafter_split.
    {
      destruct after_pis as [|a after_pis0].
      - simpl in Hlen_after. rewrite app_length in Hlen_after. simpl in Hlen_after. lia.
      - exists (removelast (a :: after_pis0)), (last (a :: after_pis0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    assert (exists ws' w, ws = ws' ++ [w]) as Hws_split.
    {
      destruct ws as [|a ws0].
      - rewrite app_length in Hlen_after. simpl in Hlen_after.
        destruct after_pis; simpl in *; lia.
      - exists (removelast (a :: ws0)), (last (a :: ws0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    destruct Hafter_split as [after_pis' [after_pi Hafter_eq]].
    destruct Hws_split as [ws' [w Hws_eq]].
    rewrite Hafter_eq in Hlen_after, Hlen_ws, Hflat.
    rewrite Hws_eq in Hlen_ws.
    assert (Hwits_split :
      Forall2 after_matches_tiling_witness after_pis' ws' /\
      after_matches_tiling_witness after_pi w).
    {
      rewrite Hafter_eq, Hws_eq in Hwits.
      eapply Forall2_app_singleton_inv.
      exact Hwits.
    }
    destruct Hwits_split as [Hwits' Hwit_last].
    assert (Hlen_after' : List.length before_pis = List.length after_pis') by (rewrite !app_length in Hlen_after; simpl in Hlen_after; lia).
    assert (Hlen_ws' : List.length after_pis' = List.length ws') by (rewrite !app_length in Hlen_ws; simpl in Hlen_ws; lia).
    eapply PL.flatten_instrs_app_singleton_inv in Hflat.
    destruct Hflat as [ipl_after_h [ipl_after_t [Hflat_after_h [Hflat_after_t Hafter_ipl_eq]]]].
    destruct
        (IHbefore_pis after_pis' ws' ipl_after_h
           Hlen_after' Hlen_ws'
           Hwits' Hflat_after_h)
      as [ipl_old_h [ipl_ext_h [Hflat_old_h [Hflat_ext_h [Hold_h Hnew_h]]]]].
    assert (Hflat_old_t :
      PL.flatten_instr_nth
        envv
        (List.length
           (retiled_old_pinstrs (List.length envv) before_pis after_pis' ws'))
        (retiled_old_pinstr
           (List.length envv) before_pi after_pi w)
        (retiled_old_ipl_from_after
           (List.length envv) before_pi after_pi w ipl_after_t)).
	    {
	      pose proof
	        (flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old
	           envv (List.length after_pis') before_pi after_pi w ipl_after_t
	           Hwit_last
	           Hflat_after_t) as Htmp.
	      replace
	        (List.length
	           (retiled_old_pinstrs (List.length envv) before_pis after_pis' ws'))
	        with (List.length after_pis').
	      - exact Htmp.
      - assert (Hlen_old_builder :
            List.length
              (retiled_old_pinstrs (List.length envv) before_pis after_pis' ws') =
            List.length before_pis).
        {
          eapply retiled_old_pinstrs_preserve_length.
          - exact Hlen_after'.
          - lia.
        }
        rewrite Hlen_old_builder.
        symmetry.
        exact Hlen_after'.
    }
    assert (Hflat_ext_t :
      PL.flatten_instr_nth_ext
        envv
        (List.length
           (compose_tiling_pinstrs_ext_from_after
              (List.length envv) before_pis after_pis' ws'))
        (compose_tiling_pinstr_ext
           (List.length envv) before_pi after_pi w)
        (compose_tiling_ipl_ext_from_after
           (List.length envv) before_pi after_pi w ipl_after_t)).
	    {
	      pose proof
	        (flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext
	           envv (List.length after_pis') before_pi after_pi w ipl_after_t
	           Hwit_last
	           Hflat_after_t) as Htmp.
	      replace
	        (List.length
	           (compose_tiling_pinstrs_ext_from_after
              (List.length envv) before_pis after_pis' ws'))
        with (List.length after_pis').
      - exact Htmp.
      - assert (Hlen_ext_builder :
            List.length
              (compose_tiling_pinstrs_ext_from_after
                 (List.length envv) before_pis after_pis' ws') =
            List.length before_pis).
        {
          eapply compose_tiling_pinstrs_ext_from_after_preserve_length.
          - exact Hlen_after'.
          - lia.
        }
        rewrite Hlen_ext_builder.
        symmetry.
        exact Hlen_after'.
    }
    exists
      (ipl_old_h ++
       retiled_old_ipl_from_after
         (List.length envv) before_pi after_pi w ipl_after_t).
    exists
      (ipl_ext_h ++
       compose_tiling_ipl_ext_from_after
         (List.length envv) before_pi after_pi w ipl_after_t).
    split.
    + rewrite Hafter_eq.
      rewrite Hws_eq.
      rewrite retiled_old_pinstrs_app_singleton.
      * eapply PL.flatten_instrs_app_singleton; eauto.
      * exact Hlen_after'.
      * lia.
    + split.
      * rewrite Hafter_eq.
        rewrite Hws_eq.
        rewrite compose_tiling_pinstrs_ext_from_after_app_singleton.
        -- eapply PL.flatten_instrs_ext_app_singleton; eauto.
        -- exact Hlen_after'.
        -- lia.
      * split.
        -- unfold PL.old_of_ext_list in *.
           rewrite map_app.
           rewrite Hold_h.
           rewrite old_of_compose_tiling_ipl_ext_from_after.
           reflexivity.
        -- unfold PL.new_of_ext_list in *.
           rewrite map_app.
           rewrite Hnew_h.
           rewrite new_of_compose_tiling_ipl_ext_from_after.
           symmetry.
           exact Hafter_ipl_eq.
Qed.

Theorem flatten_instrs_retiled_old_implies_before_exists_perm :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    exists ipl_before,
      PL.flatten_instrs envv before_pis ipl_before /\
      Permutation
        ipl_before
        (before_ipl_from_retiled_old_pprog
           (List.length envv) before_pis ws ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths Hflat.
  pose proof
    (tiling_rel_pprog_structure_compiled_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars ws Hprog)
    as [Hlen_after Hlen_ws].
  revert after_pis after_ctxt after_vars ws Hprog Hlen_after Hlen_ws
         Hwf_ws Hsizes_ws Hdepths ipl_old Hflat.
  induction before_pis using rev_ind;
    intros after_pis after_ctxt after_vars ws
           Hprog Hlen_after Hlen_ws Hwf_ws Hsizes_ws Hdepths ipl_old Hflat.
  - assert (after_pis = []) as Hafter_nil.
    {
      apply length_zero_iff_nil.
      symmetry.
      exact Hlen_after.
    }
    assert (ws = []) as Hws_nil.
    {
      apply length_zero_iff_nil.
      rewrite <- Hlen_ws.
      rewrite <- Hlen_after.
      reflexivity.
    }
    subst.
    eapply PL.flatten_instrs_nil_implies_nil in Hflat.
    subst ipl_old.
    exists [].
    split.
    + apply PL.flatten_instrs_nil.
    + simpl.
      constructor.
  - rename x into before_pi.
    assert (exists after_pis' after_pi, after_pis = after_pis' ++ [after_pi])
      as Hafter_split.
    {
      destruct after_pis as [|a after_pis0].
      - rewrite app_length in Hlen_after. simpl in Hlen_after. lia.
      - exists (removelast (a :: after_pis0)), (last (a :: after_pis0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    assert (exists ws' w, ws = ws' ++ [w]) as Hws_split.
    {
      destruct ws as [|a ws0].
      - rewrite app_length in Hlen_after. simpl in Hlen_after.
        destruct after_pis; simpl in *; lia.
      - exists (removelast (a :: ws0)), (last (a :: ws0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    destruct Hafter_split as [after_pis' [after_pi Hafter_eq]].
    destruct Hws_split as [ws' [w Hws_eq]].
    rewrite Hafter_eq in Hlen_after, Hlen_ws, Hprog, Hflat.
    rewrite Hws_eq in Hlen_ws, Hprog.
    rewrite Hws_eq in Hwf_ws, Hsizes_ws, Hdepths.
    assert (Hlen_after' : List.length before_pis = List.length after_pis').
    {
      rewrite !app_length in Hlen_after.
      simpl in Hlen_after.
      lia.
    }
    assert (Hlen_ws' : List.length after_pis' = List.length ws').
    {
      rewrite !app_length in Hlen_ws.
      simpl in Hlen_ws.
      lia.
    }
    apply Forall_app in Hwf_ws.
    destruct Hwf_ws as [Hwf_ws_head Hwf_ws_tail].
    inversion Hwf_ws_tail as [|? ? Hwf_w Hwf_nil]; subst.
    apply Forall_app in Hsizes_ws.
    destruct Hsizes_ws as [Hsizes_ws_head Hsizes_ws_tail].
    inversion Hsizes_ws_tail as [|? ? Hsizes_w Hsizes_nil]; subst.
    pose proof
      (Forall2_app_singleton_inv
         PL.PolyInstr statement_tiling_witness
         (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
         before_pis ws' before_pi w Hdepths)
      as [Hdepths_head Hpoint_depth_last].
    pose proof
      (tiling_rel_pprog_structure_compiled_app_singleton_inv
         before_pis before_ctxt before_vars
         after_pis' after_ctxt after_vars ws'
         before_pi after_pi w Hprog)
      as Hprog_head.
    rewrite retiled_old_pinstrs_app_singleton in Hflat.
    2: exact Hlen_after'.
    2: lia.
    eapply PL.flatten_instrs_app_singleton_inv in Hflat.
    destruct Hflat as [ipl_old_h [ipl_old_t [Hflat_old_h [Hflat_old_t Hold_eq]]]].
    assert (Hretiled_head_len :
      List.length
        (retiled_old_pinstrs (List.length envv) before_pis after_pis' ws') =
      List.length before_pis).
    {
      eapply retiled_old_pinstrs_preserve_length.
      - exact Hlen_after'.
      - rewrite Hlen_after'.
        exact Hlen_ws'.
    }
    rewrite Hretiled_head_len in Hflat_old_t.
    destruct
      (IHbefore_pis after_pis' after_ctxt after_vars ws'
         Hprog_head Hlen_after' Hlen_ws'
         Hwf_ws_head Hsizes_ws_head Hdepths_head
         ipl_old_h Hflat_old_h)
      as [ipl_before_h [Hflat_before_h Hperm_before_h]].
    assert (Hbefore_last :
      List.nth_error (before_pis ++ [before_pi]) (List.length before_pis) =
      Some before_pi).
    {
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    assert (Hafter_last :
      List.nth_error (after_pis' ++ [after_pi]) (List.length before_pis) =
      Some after_pi).
    {
      rewrite Hlen_after'.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    assert (Hw_last :
      List.nth_error (ws' ++ [w]) (List.length before_pis) = Some w).
    {
      rewrite Hlen_after'.
      rewrite Hlen_ws'.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    destruct
      (flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm
         (before_pis ++ [before_pi]) before_ctxt before_vars
         (after_pis' ++ [after_pi]) after_ctxt after_vars
         (ws' ++ [w]) (List.length before_pis) before_pi after_pi w
         envv ipl_old_t
         Hprog Hbefore_last Hafter_last Hw_last Henv_len
         Hwf_w Hsizes_w Hpoint_depth_last Hflat_old_t)
      as [ipl_before_t [Hflat_before_t Hperm_before_t_local]].
    assert (Hhead_map_eq :
      before_ipl_from_retiled_old_pprog
        (List.length envv) before_pis ws' ipl_old_h =
      before_ipl_from_retiled_old_pprog
        (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_h).
    {
      unfold before_ipl_from_retiled_old_pprog.
      apply map_ext_in.
      intros ip Hin.
      symmetry.
      eapply before_of_retiled_old_pprog_point_app_head.
      - rewrite Hlen_after'.
        exact Hlen_ws'.
      - assert (Hip_lt :
            (PL.ip_nth ip <
             List.length
               (retiled_old_pinstrs
                  (List.length envv) before_pis after_pis' ws'))%nat).
        {
          eapply PL.flatten_instrs_ipl_n_lt_len; eauto.
        }
        rewrite Hretiled_head_len in Hip_lt.
        exact Hip_lt.
    }
    assert (Htail_map_eq :
      before_ipl_from_retiled_old
        (List.length envv) (List.length (stw_links w)) before_pi ipl_old_t =
      before_ipl_from_retiled_old_pprog
        (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_t).
    {
      unfold before_ipl_from_retiled_old, before_ipl_from_retiled_old_pprog.
      apply map_ext_in.
      intros ip Hin.
      symmetry.
      unfold before_of_retiled_old_pprog_point.
      rewrite (flatten_instr_nth_implies_ip_nth
                 envv (List.length before_pis)
                 (retiled_old_pinstr (List.length envv) before_pi after_pi w)
                 ipl_old_t ip Hflat_old_t Hin).
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      rewrite Hlen_after'.
      rewrite Hlen_ws'.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    exists (ipl_before_h ++ ipl_before_t).
    split.
    + eapply PL.flatten_instrs_app_singleton; eauto.
    + transitivity
        (before_ipl_from_retiled_old_pprog
           (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_h ++
         before_ipl_from_retiled_old_pprog
           (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_t).
      * rewrite <- Hhead_map_eq.
        rewrite <- Htail_map_eq.
        eapply Permutation_app; eauto.
      * rewrite <- before_ipl_from_retiled_old_pprog_app.
        rewrite <- Hold_eq.
        reflexivity.
Qed.

Theorem tiling_after_to_retiled_old_poly_correct :
  forall envv before_pis after_pis ws varctxt vars st1 st2,
    List.length before_pis = List.length after_pis ->
    List.length after_pis = List.length ws ->
    Forall2 after_matches_tiling_witness after_pis ws ->
    (forall ipl_ext tau1 tau2,
      PL.flatten_instrs_ext
        envv
        (compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      PL.Permutable_ext tau1 tau2) ->
    Instr.NonAlias st1 ->
    PL.poly_instance_list_semantics envv (after_pis, varctxt, vars) st1 st2 ->
    exists st2',
      PL.poly_instance_list_semantics
        envv
        (retiled_old_pinstrs (List.length envv) before_pis after_pis ws,
         varctxt, vars)
        st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros envv before_pis after_pis ws varctxt vars st1 st2
         Hlen_after Hlen_ws Hwits Hperm Halias Hsem.
  inversion Hsem as
    [envv' pprog pis varctxt' vars' st1' st2' ipl_after sorted_ipl_after
     Hpprog Hflat_after Hpermut_after Hsorted_after Hlist_after];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  destruct
    (flatten_instrs_after_implies_tiling_ext_exists
       envv before_pis pis ws ipl_after
       Hlen_after Hlen_ws Hwits Hflat_after)
    as [ipl_old [ipl_ext [Hflat_old [Hflat_ext [Hold_ext Hnew_ext0]]]]].
  pose proof
    (PL.permut_implies_ext_permut_new
       ipl_ext ipl_after sorted_ipl_after
       Hpermut_after Hnew_ext0)
    as Hperm_new.
  destruct Hperm_new as [sorted_new_ipl_ext [Hpermut_ext Hnew_ext]].
  remember
    (SelectionSort
       PL.instr_point_ext_old_sched_ltb
       PL.instr_point_ext_old_sched_eqb
       sorted_new_ipl_ext)
    as sorted_old_ipl_ext.
  remember (PL.old_of_ext_list sorted_old_ipl_ext) as sorted_ipl_old.
  symmetry in Heqsorted_old_ipl_ext.
  pose proof Heqsorted_old_ipl_ext as Hselsort_old_ext.
  eapply PL.selection_sort_instance_list_ext_implies_old_normal
    in Hselsort_old_ext.
  pose proof Hselsort_old_ext as Hselsort_old.
  eapply PL.selection_sort_instance_list_is_correct in Hselsort_old.
  destruct Hselsort_old as [Hpermut_old_ext Hsort_old_ext].
  assert (Base.Sorted_b PL.instr_point_ext_new_sched_leb sorted_new_ipl_ext)
    as Hsorted_new_ext.
  {
    eapply PL.sorted_ge_implies_ext_sorted_ge.
    rewrite Hnew_ext.
    exact Hsorted_after.
  }
  eapply PL.selection_sort_instance_list_ext_is_stable_permut
    in Heqsorted_old_ipl_ext.
  2: exact Hsorted_new_ext.
  assert
    (forall tau1 tau2 : PL.InstrPoint_ext,
      In tau1 sorted_new_ipl_ext ->
      In tau2 sorted_new_ipl_ext ->
      PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      PL.Permutable_ext tau1 tau2) as Hperm_sorted_new.
  {
    intros tau1 tau2 Hin1 Hin2 Hold Hnew.
    eapply (Hperm ipl_ext tau1 tau2).
    - exact Hflat_ext.
    - eapply Permutation_in.
      + eapply Permutation_sym. exact Hpermut_ext.
      + exact Hin1.
    - eapply Permutation_in.
      + eapply Permutation_sym. exact Hpermut_ext.
      + exact Hin2.
    - exact Hold.
    - exact Hnew.
  }
  pose proof
    (PL.stable_permut_ext_lists_are_equivalent
       sorted_new_ipl_ext sorted_old_ipl_ext
       Hperm_sorted_new Heqsorted_old_ipl_ext
       st1 Halias)
    as Hequiv.
  destruct Hequiv as [Hforward Hbackward].
  rewrite <- Hnew_ext in Hlist_after.
  rewrite <- PL.list_ext_old_new_equivalence in Hlist_after.
  pose proof (Hforward st2 Hlist_after) as Hold_sorted.
  destruct Hold_sorted as [st2' [Hlist_old_sorted Heqst]].
  exists st2'.
  split.
  - eapply PL.PolyPointListSema with
      (ipl := ipl_old)
      (sorted_ipl := sorted_ipl_old).
    + reflexivity.
    + exact Hflat_old.
    + remember (PL.old_of_ext_list sorted_new_ipl_ext) as sorted_new_old_ipl.
      transitivity sorted_new_old_ipl.
      * clear - Hpermut_ext Hold_ext Heqsorted_new_old_ipl.
        rewrite <- Hold_ext.
        rewrite Heqsorted_new_old_ipl.
        eapply PL.ext_permut_implies_permut_old.
        exact Hpermut_ext.
      * rewrite Heqsorted_ipl_old.
        exact Hpermut_old_ext.
    + rewrite Heqsorted_ipl_old.
      eapply PL.sortedb_lexorder_implies_sorted_lexorder.
      exact Hsort_old_ext.
    + rewrite Heqsorted_ipl_old.
      exact Hlist_old_sorted.
  - exact Heqst.
Qed.

Lemma flatten_instrs_retiled_old_member_nth_data :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip,
    tiling_rel_pprog_structure_compiled
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      ws ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    In ip ipl_old ->
    exists n before_pi after_pi w,
      List.nth_error before_pis n = Some before_pi /\
      List.nth_error after_pis n = Some after_pi /\
      List.nth_error ws n = Some w /\
      wf_statement_tiling_witness_with_param_dim (List.length envv) w /\
      Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
      stw_point_dim w = PL.pi_depth before_pi /\
      firstn (List.length envv) (PL.ip_index ip) = envv /\
      PL.belongs_to
        ip
        (retiled_old_pinstr (List.length envv) before_pi after_pi w) /\
      PL.ip_nth ip = n /\
      List.length (PL.ip_index ip) =
        (List.length envv + PL.pi_depth after_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths
         Hflat Hip_in.
  pose proof
    (tiling_rel_pprog_structure_compiled_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars ws Hprog)
    as [Hlen_after Hlen_ws].
  assert (Hretiled_len :
    List.length
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws) =
    List.length before_pis).
  {
    eapply retiled_old_pinstrs_preserve_length.
    - exact Hlen_after.
    - rewrite Hlen_after.
      exact Hlen_ws.
  }
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct Hmem as [Hfwd _].
  specialize (Hfwd Hip_in).
  destruct Hfwd as [pi0 [Hnth_retiled [Hpref_ip [Hbel_prog Hlen_ip]]]].
  set (n := PL.ip_nth ip).
  assert (Hn_lt_retiled :
    (n <
     List.length
       (retiled_old_pinstrs (List.length envv) before_pis after_pis ws))%nat).
  {
    subst n.
    eapply PL.nth_error_Some'.
    exact Hnth_retiled.
  }
  assert (Hn_lt_before : (n < List.length before_pis)%nat).
  {
    rewrite <- Hretiled_len.
    exact Hn_lt_retiled.
  }
  destruct (List.nth_error before_pis n) eqn:Hbefore_nth.
  2: {
    exfalso.
    eapply List.nth_error_None in Hbefore_nth.
    lia.
  }
  destruct (List.nth_error after_pis n) eqn:Hafter_nth.
  2: {
    exfalso.
    eapply List.nth_error_None in Hafter_nth.
    rewrite <- Hlen_after in Hafter_nth.
    lia.
  }
  destruct (List.nth_error ws n) eqn:Hw_nth.
  2: {
    exfalso.
    eapply List.nth_error_None in Hw_nth.
    rewrite <- Hlen_ws in Hw_nth.
    rewrite <- Hlen_after in Hw_nth.
    lia.
  }
  pose proof
    (nth_error_retiled_old_pinstrs
       (List.length envv) before_pis after_pis ws n
       p p0 s Hbefore_nth Hafter_nth Hw_nth)
    as Hnth_expected.
  unfold n in Hnth_expected.
  rewrite Hnth_retiled in Hnth_expected.
  inversion Hnth_expected; subst pi0.
  pose proof
    (Forall_nth_error _ _ _ _ _ Hwf_ws Hw_nth)
    as Hwf_w.
  pose proof
    (Forall_nth_error _ _ _ _ _ Hsizes_ws Hw_nth)
    as Hsizes_w.
  pose proof
    (Forall2_nth_error
       PL.PolyInstr statement_tiling_witness
       (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
       before_pis ws n p s
       Hdepths Hbefore_nth Hw_nth)
    as Hpoint_depth.
  exists n, p, p0, s.
  split.
  - exact Hbefore_nth.
  - split.
    + exact Hafter_nth.
    + split.
      * exact Hw_nth.
      * split.
        -- exact Hwf_w.
        -- split.
           ++ exact Hsizes_w.
           ++ split.
              ** exact Hpoint_depth.
              ** split.
                 --- exact Hpref_ip.
                 --- split.
                     +++ exact Hbel_prog.
                     +++ split.
                         *** unfold n. reflexivity.
                         *** cbn [retiled_old_pinstr] in Hlen_ip.
                             exact Hlen_ip.
Qed.

Lemma before_ipl_from_retiled_old_nodup_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    NoDup
      (before_ipl_from_retiled_old
         (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  assert (Hstmt :
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt)
      before_pi after_pi (compiled_pinstr_tiling_witness w)).
  {
    eapply tiling_rel_pprog_structure_source_nth; eauto.
    eapply nth_error_map_some; exact Hw_nth.
  }
  rewrite <- Henv_len in Hstmt.
  destruct Hflat_old as [Hpref_old [Hmem_old [Hnodup_old _]]].
  eapply NoDup_map_on.
  - exact Hnodup_old.
  - intros ip1 ip2 Hin1 Hin2 Heq.
    pose proof (Hpref_old ip1 Hin1) as Hpref1.
    pose proof (Hpref_old ip2 Hin2) as Hpref2.
    pose proof (Hmem_old ip1) as Hmem1.
    pose proof (Hmem_old ip2) as Hmem2.
    destruct Hmem1 as [Hfwd1 _].
    destruct Hmem2 as [Hfwd2 _].
    specialize (Hfwd1 Hin1).
    specialize (Hfwd2 Hin2).
    destruct Hfwd1 as [_ [Hbel1 [_ Hlen1]]].
    destruct Hfwd2 as [_ [Hbel2 [_ Hlen2]]].
    cbn [retiled_old_pinstr] in Hlen1, Hlen2.
    eapply tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective;
      eauto using wf_compiled_pinstr_tiling_witness,
                  compiled_pinstr_tiling_witness_matches.
Qed.

Theorem flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    exists ipl_before,
      ipl_before =
        SelectionSort instr_point_np_ltb instr_point_np_eqb
          (before_ipl_from_retiled_old
             (List.length env) (List.length (stw_links w)) before_pi ipl_old) /\
      PL.flatten_instr_nth env n before_pi ipl_before.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  set (raw_before :=
    before_ipl_from_retiled_old
      (List.length env) (List.length (stw_links w)) before_pi ipl_old).
  set (sorted_before :=
    SelectionSort instr_point_np_ltb instr_point_np_eqb raw_before).
  exists sorted_before.
  split; [reflexivity|].
  assert (Hperm_before :
    Permutation raw_before sorted_before).
  {
    subst sorted_before.
    eapply selection_sort_perm.
  }
  assert (Hnodup_raw :
    NoDup raw_before).
  {
    subst raw_before.
    eapply before_ipl_from_retiled_old_nodup_source; eauto.
  }
  assert (Hnodup_sorted :
    NoDup sorted_before).
  {
    eapply Permutation_NoDup; eauto.
  }
  assert (Hmem_sorted :
    forall ip,
      In ip sorted_before <->
      firstn (List.length env) (PL.ip_index ip) = env /\
      PL.belongs_to ip before_pi /\
      PL.ip_nth ip = n /\
      List.length (PL.ip_index ip) =
        (List.length env + PL.pi_depth before_pi)%nat).
  {
    intros ip.
    split; intro Hin.
    - eapply before_ipl_from_retiled_old_forward_source.
      + exact Hprog.
      + exact Hbefore_nth.
      + exact Hafter_nth.
      + exact Hw_nth.
      + exact Henv_len.
      + exact Hwf_stmt.
      + exact Hsizes.
      + exact Hpoint_depth.
      + exact Hflat_old.
      + eapply Permutation_in.
        * eapply Permutation_sym. exact Hperm_before.
        * exact Hin.
    - eapply Permutation_in.
      + exact Hperm_before.
      + {
          destruct Hin as [Hpref_before [Hbel_before [Hnth_before Hlen_before]]].
          eapply before_ipl_from_retiled_old_backward_source.
          - exact Hprog.
          - exact Hbefore_nth.
          - exact Hafter_nth.
          - exact Hw_nth.
          - exact Henv_len.
          - exact Hwf_stmt.
          - exact Hsizes.
          - exact Hpoint_depth.
          - exact Hflat_old.
          - exact Hpref_before.
          - exact Hbel_before.
          - exact Hnth_before.
          - exact Hlen_before.
        }
  }
  assert (HnodupA_sorted :
    NoDupA PL.np_eq sorted_before).
  {
    eapply PL.belongs_to_implies_NoDupA_np.
    - intros ip Hin.
      specialize (Hmem_sorted ip).
      destruct Hmem_sorted as [Hfwd _].
      specialize (Hfwd Hin).
      destruct Hfwd as [_ [Hbel [Hnth Hlen]]].
      destruct Hbel as [Hpoly [Htrans [Hts [Hinss Hdepth]]]].
      repeat split.
      + exact Hpoly.
      + exact Htrans.
      + exact Hts.
      + exact Hinss.
      + exact Hdepth.
      + exact Hnth.
      + exact Hlen.
    - exact Hnodup_sorted.
  }
  assert (Hsortedb :
    Sorted_b (combine_leb instr_point_np_ltb instr_point_np_eqb) sorted_before).
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
  - intros ip Hin.
    specialize (Hmem_sorted ip).
    tauto.
  - split.
    + exact Hmem_sorted.
    + split.
      * exact Hnodup_sorted.
      * eapply sortedb_instr_point_np_implies_sorted_np; eauto.
Qed.

Theorem flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.nth_error before_pis n = Some before_pi ->
    List.nth_error after_pis n = Some after_pi ->
    List.nth_error ws n = Some w ->
    List.length env = List.length before_ctxt ->
    wf_statement_tiling_witness_with_param_dim
      (List.length env) w ->
    Forall
      (fun link => 0 < tl_tile_size link)
      (stw_links w) ->
    stw_point_dim w = PL.pi_depth before_pi ->
    PL.flatten_instr_nth
      env n
      (retiled_old_pinstr (List.length env) before_pi after_pi w)
      ipl_old ->
    exists ipl_before,
      PL.flatten_instr_nth env n before_pi ipl_before /\
      Permutation
        ipl_before
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws n before_pi after_pi w
         env ipl_old
         Hprog Hbefore_nth Hafter_nth Hw_nth Henv_len
         Hwf_stmt Hsizes Hpoint_depth
         Hflat_old.
  set (raw_before :=
    before_ipl_from_retiled_old
      (List.length env) (List.length (stw_links w)) before_pi ipl_old).
  set (sorted_before :=
    SelectionSort instr_point_np_ltb instr_point_np_eqb raw_before).
  exists sorted_before.
  split.
  - subst sorted_before raw_before.
    assert (Hperm_before :
      Permutation
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old)
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply selection_sort_perm.
    }
    assert (Hnodup_raw :
      NoDup
        (before_ipl_from_retiled_old
           (List.length env) (List.length (stw_links w)) before_pi ipl_old)).
    {
      eapply before_ipl_from_retiled_old_nodup_source; eauto.
    }
    assert (Hnodup_sorted :
      NoDup
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply Permutation_NoDup; eauto.
    }
    assert (Hmem_sorted :
      forall ip,
        In ip
          (SelectionSort instr_point_np_ltb instr_point_np_eqb
             (before_ipl_from_retiled_old
                (List.length env) (List.length (stw_links w)) before_pi ipl_old)) <->
        firstn (List.length env) (PL.ip_index ip) = env /\
        PL.belongs_to ip before_pi /\
        PL.ip_nth ip = n /\
        List.length (PL.ip_index ip) =
          (List.length env + PL.pi_depth before_pi)%nat).
    {
      intros ip.
      split; intro Hin.
      - eapply before_ipl_from_retiled_old_forward_source.
        + exact Hprog.
        + exact Hbefore_nth.
        + exact Hafter_nth.
        + exact Hw_nth.
        + exact Henv_len.
        + exact Hwf_stmt.
        + exact Hsizes.
        + exact Hpoint_depth.
        + exact Hflat_old.
        + eapply Permutation_in.
          * eapply Permutation_sym. exact Hperm_before.
          * exact Hin.
      - eapply Permutation_in.
        + exact Hperm_before.
        + {
            destruct Hin as [Hpref_before [Hbel_before [Hnth_before Hlen_before]]].
            eapply before_ipl_from_retiled_old_backward_source.
            - exact Hprog.
            - exact Hbefore_nth.
            - exact Hafter_nth.
            - exact Hw_nth.
            - exact Henv_len.
            - exact Hwf_stmt.
            - exact Hsizes.
            - exact Hpoint_depth.
            - exact Hflat_old.
            - exact Hpref_before.
            - exact Hbel_before.
            - exact Hnth_before.
            - exact Hlen_before.
          }
    }
    assert (HnodupA_sorted :
      NoDupA PL.np_eq
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
      eapply PL.belongs_to_implies_NoDupA_np.
      - intros ip Hin.
        specialize (Hmem_sorted ip).
        destruct Hmem_sorted as [Hfwd _].
        specialize (Hfwd Hin).
        destruct Hfwd as [_ [Hbel [Hnth Hlen]]].
        destruct Hbel as [Hpoly [Htrans [Hts [Hinss Hdepth]]]].
        repeat split.
        + exact Hpoly.
        + exact Htrans.
        + exact Hts.
        + exact Hinss.
        + exact Hdepth.
        + exact Hnth.
        + exact Hlen.
      - exact Hnodup_sorted.
    }
    assert (Hsortedb :
      Sorted_b
        (combine_leb instr_point_np_ltb instr_point_np_eqb)
        (SelectionSort instr_point_np_ltb instr_point_np_eqb
           (before_ipl_from_retiled_old
              (List.length env) (List.length (stw_links w)) before_pi ipl_old))).
    {
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
      specialize (Hmem_sorted ip).
      tauto.
    + split.
      * exact Hmem_sorted.
      * split.
        -- exact Hnodup_sorted.
        -- eapply sortedb_instr_point_np_implies_sorted_np; eauto.
  - subst sorted_before raw_before.
    eapply Permutation_sym.
    eapply selection_sort_perm.
Qed.

Lemma flatten_instrs_retiled_old_member_nth_data_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    In ip ipl_old ->
    exists n before_pi after_pi w,
      List.nth_error before_pis n = Some before_pi /\
      List.nth_error after_pis n = Some after_pi /\
      List.nth_error ws n = Some w /\
      wf_statement_tiling_witness_with_param_dim (List.length envv) w /\
      Forall (fun link => 0 < tl_tile_size link) (stw_links w) /\
      stw_point_dim w = PL.pi_depth before_pi /\
      firstn (List.length envv) (PL.ip_index ip) = envv /\
      PL.belongs_to
        ip
        (retiled_old_pinstr (List.length envv) before_pi after_pi w) /\
      PL.ip_nth ip = n /\
      List.length (PL.ip_index ip) =
        (List.length envv + PL.pi_depth after_pi)%nat.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths
         Hflat Hip_in.
  pose proof
    (tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       (List.map compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after Hlen_ws_map].
  rewrite List.map_length in Hlen_ws_map.
  assert (Hretiled_len :
    List.length
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws) =
    List.length before_pis).
  {
    eapply retiled_old_pinstrs_preserve_length.
    - exact Hlen_after.
    - rewrite Hlen_after.
      exact Hlen_ws_map.
  }
  destruct Hflat as [_ [Hmem _]].
  specialize (Hmem ip).
  destruct Hmem as [Hfwd _].
  specialize (Hfwd Hip_in).
  destruct Hfwd as [pi0 [Hnth_retiled [Hpref_ip [Hbel_prog Hlen_ip]]]].
  set (n := PL.ip_nth ip).
  assert (Hn_lt_retiled :
    (n <
     List.length
       (retiled_old_pinstrs (List.length envv) before_pis after_pis ws))%nat).
  {
    subst n.
    eapply PL.nth_error_Some'.
    exact Hnth_retiled.
  }
  assert (Hn_lt_before : (n < List.length before_pis)%nat).
  {
    rewrite <- Hretiled_len.
    exact Hn_lt_retiled.
  }
  destruct (List.nth_error before_pis n) eqn:Hbefore_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hbefore_nth.
    lia.
  }
  destruct (List.nth_error after_pis n) eqn:Hafter_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hafter_nth.
    rewrite <- Hlen_after in Hafter_nth.
    lia.
  }
  destruct (List.nth_error ws n) eqn:Hw_nth.
  2:{
    exfalso.
    eapply List.nth_error_None in Hw_nth.
    rewrite <- Hlen_ws_map in Hw_nth.
    rewrite <- Hlen_after in Hw_nth.
    lia.
  }
  pose proof
    (nth_error_retiled_old_pinstrs
       (List.length envv) before_pis after_pis ws n
       p p0 s Hbefore_nth Hafter_nth Hw_nth)
    as Hnth_expected.
  unfold n in Hnth_expected.
  rewrite Hnth_retiled in Hnth_expected.
  inversion Hnth_expected; subst pi0.
  pose proof
    (Forall_nth_error _ _ _ _ _ Hwf_ws Hw_nth)
    as Hwf_w.
  pose proof
    (Forall_nth_error _ _ _ _ _ Hsizes_ws Hw_nth)
    as Hsizes_w.
  pose proof
    (Forall2_nth_error
       PL.PolyInstr statement_tiling_witness
       (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
       before_pis ws n p s
       Hdepths Hbefore_nth Hw_nth)
    as Hpoint_depth.
  exists n, p, p0, s.
  split.
  - exact Hbefore_nth.
  - split.
    + exact Hafter_nth.
    + split.
      * exact Hw_nth.
      * split.
        -- exact Hwf_w.
        -- split.
           ++ exact Hsizes_w.
           ++ split.
              ** exact Hpoint_depth.
              ** split.
                 --- exact Hpref_ip.
                 --- split.
                     +++ exact Hbel_prog.
                     +++ split.
                         *** unfold n. reflexivity.
                         *** cbn [retiled_old_pinstr] in Hlen_ip.
                             exact Hlen_ip.
Qed.

Theorem flatten_instrs_retiled_old_member_instr_semantics_iff_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip st1 st2,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    Forall
      (fun before_pi =>
         PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi))
      before_pis ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    In ip ipl_old ->
    (PL.ILSema.instr_point_sema ip st1 st2 <->
     PL.ILSema.instr_point_sema
       (before_of_retiled_old_pprog_point
          (List.length envv) before_pis ws ip)
       st1 st2).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip st1 st2
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths Hbefore_ids
         Hflat Hip_in.
  destruct
    (flatten_instrs_retiled_old_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws envv ipl_old ip
       Hprog Henv_len Hwf_ws Hsizes_ws Hdepths
       Hflat Hip_in)
    as [n [before_pi [after_pi [w Hmember]]]].
  destruct Hmember as
    [Hbefore_nth [Hafter_nth [Hw_nth
    [Hwf_w [Hsizes_w [Hpoint_depth
    [Hpref_ip [Hbel_prog [Hnth_ip Hlen_ip]]]]]]]]].
  pose proof
    (Forall_nth_error _ _ _ _ _ Hbefore_ids Hbefore_nth)
    as Hbefore_id.
  unfold before_of_retiled_old_pprog_point.
  rewrite Hnth_ip.
  rewrite Hbefore_nth.
  rewrite Hw_nth.
  eapply tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth; eauto.
Qed.

Theorem flatten_instrs_retiled_old_member_time_stamp_preserved_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    In ip ipl_old ->
    PL.ip_time_stamp
      (before_of_retiled_old_pprog_point
         (List.length envv) before_pis ws ip) =
    PL.ip_time_stamp ip.
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old ip
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths
         Hflat Hip_in.
  destruct
    (flatten_instrs_retiled_old_member_nth_data_source
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       ws envv ipl_old ip
       Hprog Henv_len Hwf_ws Hsizes_ws Hdepths
       Hflat Hip_in)
    as [n [before_pi [after_pi [w Hmember]]]].
  destruct Hmember as
    [Hbefore_nth [Hafter_nth [Hw_nth
    [Hwf_w [Hsizes_w [Hpoint_depth
    [Hpref_ip [Hbel_prog [Hnth_ip Hlen_ip]]]]]]]]].
  assert (Hstmt :
    tiling_rel_pinstr_structure_source
      (List.length before_ctxt)
      before_pi after_pi (compiled_pinstr_tiling_witness w)).
  {
    eapply tiling_rel_pprog_structure_source_nth; eauto.
    eapply nth_error_map_some; exact Hw_nth.
  }
  rewrite <- Henv_len in Hstmt.
  unfold before_of_retiled_old_pprog_point.
  rewrite Hnth_ip.
  rewrite Hbefore_nth.
  rewrite Hw_nth.
  eapply
    (tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp
       envv before_pi after_pi (compiled_pinstr_tiling_witness w) ip).
  - exact Hstmt.
  - exact (wf_compiled_pinstr_tiling_witness w).
  - cbn [compiled_pinstr_tiling_witness ptw_statement_witness].
    exact Hpoint_depth.
  - exact Hbel_prog.
  - exact Hlen_ip.
  - exact Hpref_ip.
Qed.

Theorem flatten_instrs_retiled_old_implies_before_exists_perm_source :
  forall before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old,
    tiling_rel_pprog_structure_source
      (before_pis, before_ctxt, before_vars)
      (after_pis, after_ctxt, after_vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.length envv = List.length before_ctxt ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.flatten_instrs
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws)
      ipl_old ->
    exists ipl_before,
      PL.flatten_instrs envv before_pis ipl_before /\
      Permutation
        ipl_before
        (before_ipl_from_retiled_old_pprog
           (List.length envv) before_pis ws ipl_old).
Proof.
  intros before_pis before_ctxt before_vars
         after_pis after_ctxt after_vars
         ws envv ipl_old
         Hprog Henv_len Hwf_ws Hsizes_ws Hdepths Hflat.
  pose proof
    (tiling_rel_pprog_structure_source_lengths
       before_pis before_ctxt before_vars
       after_pis after_ctxt after_vars
       (List.map compiled_pinstr_tiling_witness ws) Hprog)
    as [Hlen_after Hlen_ws_map].
  rewrite List.map_length in Hlen_ws_map.
  revert after_pis after_ctxt after_vars ws Hprog Hlen_after Hlen_ws_map
         Hwf_ws Hsizes_ws Hdepths ipl_old Hflat.
  induction before_pis using rev_ind;
    intros after_pis after_ctxt after_vars ws
           Hprog Hlen_after Hlen_ws
           Hwf_ws Hsizes_ws Hdepths ipl_old Hflat.
  - assert (after_pis = []) as Hafter_nil.
    {
      apply length_zero_iff_nil.
      symmetry.
      exact Hlen_after.
    }
    assert (ws = []) as Hws_nil.
    {
      apply length_zero_iff_nil.
      rewrite <- Hlen_ws.
      rewrite <- Hlen_after.
      reflexivity.
    }
    subst.
    eapply PL.flatten_instrs_nil_implies_nil in Hflat.
    subst ipl_old.
    exists [].
    split.
    + apply PL.flatten_instrs_nil.
    + simpl.
      constructor.
  - rename x into before_pi.
    assert (exists after_pis' after_pi, after_pis = after_pis' ++ [after_pi])
      as Hafter_split.
    {
      destruct after_pis as [|a after_pis0].
      - rewrite app_length in Hlen_after. simpl in Hlen_after. lia.
      - exists (removelast (a :: after_pis0)), (last (a :: after_pis0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    assert (exists ws' w, ws = ws' ++ [w]) as Hws_split.
    {
      destruct ws as [|a ws0].
      - rewrite app_length in Hlen_after. simpl in Hlen_after.
        destruct after_pis; simpl in *; lia.
      - exists (removelast (a :: ws0)), (last (a :: ws0) a).
        eapply app_removelast_last. intro Hnil. inversion Hnil.
    }
    destruct Hafter_split as [after_pis' [after_pi Hafter_eq]].
    destruct Hws_split as [ws' [w Hws_eq]].
    rewrite Hafter_eq in Hlen_after, Hlen_ws, Hprog, Hflat.
    rewrite Hws_eq in Hlen_ws, Hprog.
    rewrite Hws_eq in Hwf_ws, Hsizes_ws, Hdepths.
    rewrite map_app in Hprog.
    assert (Hlen_after' : List.length before_pis = List.length after_pis').
    {
      rewrite !app_length in Hlen_after.
      simpl in Hlen_after.
      lia.
    }
    assert (Hlen_ws' : List.length after_pis' = List.length ws').
    {
      rewrite !app_length in Hlen_ws.
      simpl in Hlen_ws.
      lia.
    }
    apply Forall_app in Hwf_ws.
    destruct Hwf_ws as [Hwf_ws_head Hwf_ws_tail].
    inversion Hwf_ws_tail as [|? ? Hwf_w Hwf_nil]; subst.
    apply Forall_app in Hsizes_ws.
    destruct Hsizes_ws as [Hsizes_ws_head Hsizes_ws_tail].
    inversion Hsizes_ws_tail as [|? ? Hsizes_w Hsizes_nil]; subst.
    pose proof
      (Forall2_app_singleton_inv
         PL.PolyInstr statement_tiling_witness
         (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
         before_pis ws' before_pi w Hdepths)
      as [Hdepths_head Hpoint_depth_last].
    pose proof
      (tiling_rel_pprog_structure_source_app_singleton_inv
         before_pis before_ctxt before_vars
         after_pis' after_ctxt after_vars
         (List.map compiled_pinstr_tiling_witness ws')
         before_pi after_pi
         (compiled_pinstr_tiling_witness w) Hprog)
      as Hprog_head.
    rewrite retiled_old_pinstrs_app_singleton in Hflat.
    2: exact Hlen_after'.
    2: lia.
    eapply PL.flatten_instrs_app_singleton_inv in Hflat.
    destruct Hflat as [ipl_old_h [ipl_old_t [Hflat_old_h [Hflat_old_t Hold_eq]]]].
    assert (Hretiled_head_len :
      List.length
        (retiled_old_pinstrs (List.length envv) before_pis after_pis' ws') =
      List.length before_pis).
    {
      eapply retiled_old_pinstrs_preserve_length.
      - exact Hlen_after'.
      - rewrite Hlen_after'.
        exact Hlen_ws'.
    }
    rewrite Hretiled_head_len in Hflat_old_t.
    destruct
      (IHbefore_pis after_pis' after_ctxt after_vars ws'
         Hprog_head Hlen_after' Hlen_ws'
         Hwf_ws_head Hsizes_ws_head Hdepths_head
         ipl_old_h Hflat_old_h)
      as [ipl_before_h [Hflat_before_h Hperm_before_h]].
    assert (Hbefore_last :
      List.nth_error (before_pis ++ [before_pi]) (List.length before_pis) =
      Some before_pi).
    {
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    assert (Hafter_last :
      List.nth_error (after_pis' ++ [after_pi]) (List.length before_pis) =
      Some after_pi).
    {
      rewrite Hlen_after'.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
	    assert (Hw_last :
	      List.nth_error (ws' ++ [w]) (List.length before_pis) = Some w).
	    {
	      rewrite Hlen_after'.
	      rewrite Hlen_ws'.
	      rewrite List.nth_error_app2 by lia.
	      rewrite Nat.sub_diag.
	      simpl.
	      reflexivity.
	    }
	    assert (Hprog_app :
	      tiling_rel_pprog_structure_source
	        (before_pis ++ [before_pi], before_ctxt, before_vars)
	        (after_pis' ++ [after_pi], after_ctxt, after_vars)
	        (List.map compiled_pinstr_tiling_witness (ws' ++ [w]))).
	    {
	      rewrite List.map_app.
	      simpl.
	      exact Hprog.
	    }
	    destruct
	      (flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm_source
	         (before_pis ++ [before_pi]) before_ctxt before_vars
	         (after_pis' ++ [after_pi]) after_ctxt after_vars
	         (ws' ++ [w]) (List.length before_pis) before_pi after_pi w
	         envv ipl_old_t
	         Hprog_app Hbefore_last Hafter_last Hw_last Henv_len
	         Hwf_w Hsizes_w Hpoint_depth_last Hflat_old_t)
	      as [ipl_before_t [Hflat_before_t Hperm_before_t_local]].
    assert (Hhead_map_eq :
      before_ipl_from_retiled_old_pprog
        (List.length envv) before_pis ws' ipl_old_h =
      before_ipl_from_retiled_old_pprog
        (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_h).
    {
      unfold before_ipl_from_retiled_old_pprog.
      apply map_ext_in.
      intros ip Hin.
      symmetry.
      eapply before_of_retiled_old_pprog_point_app_head.
      - rewrite Hlen_after'.
        exact Hlen_ws'.
      - assert (Hip_lt :
            (PL.ip_nth ip <
             List.length
               (retiled_old_pinstrs
                  (List.length envv) before_pis after_pis' ws'))%nat).
        {
          eapply PL.flatten_instrs_ipl_n_lt_len; eauto.
        }
        rewrite Hretiled_head_len in Hip_lt.
        exact Hip_lt.
    }
    assert (Htail_map_eq :
      before_ipl_from_retiled_old
        (List.length envv) (List.length (stw_links w)) before_pi ipl_old_t =
      before_ipl_from_retiled_old_pprog
        (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_t).
    {
      unfold before_ipl_from_retiled_old, before_ipl_from_retiled_old_pprog.
      apply map_ext_in.
      intros ip Hin.
      symmetry.
      unfold before_of_retiled_old_pprog_point.
      rewrite (flatten_instr_nth_implies_ip_nth
                 envv (List.length before_pis)
                 (retiled_old_pinstr (List.length envv) before_pi after_pi w)
                 ipl_old_t ip Hflat_old_t Hin).
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      rewrite Hlen_after'.
      rewrite Hlen_ws'.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    }
    exists (ipl_before_h ++ ipl_before_t).
    split.
    + eapply PL.flatten_instrs_app_singleton; eauto.
    + transitivity
        (before_ipl_from_retiled_old_pprog
           (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_h ++
         before_ipl_from_retiled_old_pprog
           (List.length envv) (before_pis ++ [before_pi]) (ws' ++ [w]) ipl_old_t).
      * rewrite <- Hhead_map_eq.
        rewrite <- Htail_map_eq.
        eapply Permutation_app; eauto.
      * rewrite <- before_ipl_from_retiled_old_pprog_app.
        rewrite <- Hold_eq.
        reflexivity.
Qed.

Theorem tiling_retiled_old_to_before_poly_correct_with_env_len_source :
  forall envv before_pis after_pis ws varctxt vars st1 st2,
    tiling_rel_pprog_structure_source
      (before_pis, varctxt, vars)
      (after_pis, varctxt, vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    List.length envv = List.length varctxt ->
    Forall
      (fun before_pi =>
         PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi))
      before_pis ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.poly_instance_list_semantics
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws,
       varctxt, vars)
      st1 st2 ->
    exists st2',
      PL.poly_instance_list_semantics
        envv
        (before_pis, varctxt, vars)
        st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros envv before_pis after_pis ws varctxt vars st1 st2
         Hprog Henv_len Hbefore_ids Hwf_ws Hsizes_ws Hdepths Hsem.
  inversion Hsem as
    [envv' pprog pis varctxt' vars' st1' st2'
     ipl_old sorted_ipl_old
     Hpprog Hflat_old Hpermut_old Hsorted_old Hlist_old];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  destruct
    (flatten_instrs_retiled_old_implies_before_exists_perm_source
       before_pis varctxt' vars'
       after_pis varctxt' vars'
       ws envv ipl_old
       Hprog Henv_len Hwf_ws Hsizes_ws Hdepths Hflat_old)
    as [ipl_before [Hflat_before Hperm_before_flat]].
  set (sorted_before :=
    before_ipl_from_retiled_old_pprog
      (List.length envv) before_pis ws sorted_ipl_old).
  assert (Hlist_before :
    PL.instr_point_list_semantics sorted_before st1 st2).
  {
    subst sorted_before.
    eapply instr_point_list_semantics_map_preserved.
    - intros ip s1 s2 Hin_sorted.
      eapply flatten_instrs_retiled_old_member_instr_semantics_iff_source; eauto.
      eapply Permutation_in.
      + eapply Permutation_sym.
        exact Hpermut_old.
      + exact Hin_sorted.
    - exact Hlist_old.
  }
  assert (Hsorted_before :
    Sorted PL.instr_point_sched_le sorted_before).
  {
    subst sorted_before.
    eapply sorted_sched_map_time_stamp_preserved.
    - intros ip Hin_sorted.
      eapply flatten_instrs_retiled_old_member_time_stamp_preserved_source; eauto.
      eapply Permutation_in.
      + eapply Permutation_sym.
        exact Hpermut_old.
      + exact Hin_sorted.
    - exact Hsorted_old.
  }
  assert (Hperm_before_sorted :
    Permutation ipl_before sorted_before).
  {
    subst sorted_before.
    transitivity
      (before_ipl_from_retiled_old_pprog
         (List.length envv) before_pis ws ipl_old).
    - exact Hperm_before_flat.
    - eapply Permutation_map.
      exact Hpermut_old.
  }
  exists st2.
  split.
  - eapply PL.PolyPointListSema with
      (ipl := ipl_before)
      (sorted_ipl := sorted_before).
    + reflexivity.
    + exact Hflat_before.
    + exact Hperm_before_sorted.
    + exact Hsorted_before.
    + exact Hlist_before.
  - eapply Instr.State.eq_refl.
Qed.

Theorem tiling_retiled_old_to_before_instance_correct_source :
  forall before_pis after_pis ws varctxt vars st1 st2,
    tiling_rel_pprog_structure_source
      (before_pis, varctxt, vars)
      (after_pis, varctxt, vars)
      (List.map compiled_pinstr_tiling_witness ws) ->
    Forall
      (fun before_pi =>
         PL.pi_point_witness before_pi = PSWIdentity (PL.pi_depth before_pi))
      before_pis ->
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length varctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => 0 < tl_tile_size link) (stw_links w))
      ws ->
    Forall2 (fun before_pi w => stw_point_dim w = PL.pi_depth before_pi)
      before_pis ws ->
    PL.instance_list_semantics
      (retiled_old_pinstrs (List.length varctxt) before_pis after_pis ws,
       varctxt, vars)
      st1 st2 ->
    exists st2',
      PL.instance_list_semantics
        (before_pis, varctxt, vars)
        st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros before_pis after_pis ws varctxt vars st1 st2
         Hprog Hbefore_ids Hwf_ws Hsizes_ws Hdepths Hinst.
  inversion Hinst as
    [pprog pis varctxt' vars' envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  pose proof (Instr.init_env_samelen varctxt' envv st1 Hinit) as Hlen_env.
  assert (Hwf_ws_env :
    Forall
      (wf_statement_tiling_witness_with_param_dim (List.length envv))
      ws).
  {
    rewrite <- Hlen_env.
    exact Hwf_ws.
  }
  assert (Hpoly_env :
    PL.poly_instance_list_semantics
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws,
       varctxt', vars')
      st1 st2).
  {
    rewrite <- Hlen_env.
    exact Hpoly.
  }
  destruct
    (tiling_retiled_old_to_before_poly_correct_with_env_len_source
       envv before_pis after_pis ws varctxt' vars' st1 st2
       Hprog (eq_sym Hlen_env) Hbefore_ids Hwf_ws_env Hsizes_ws Hdepths Hpoly_env)
    as [st2' [Hpoly_before Heq]].
  exists st2'.
  split.
  - econstructor.
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hpoly_before.
  - exact Heq.
Qed.

Definition tiling_retiled_old_to_before_poly_layer
    (envv: list Z)
    (before_pis after_pis: list PL.PolyInstr)
    (ws: list statement_tiling_witness)
    (varctxt: list PL.ident)
    (vars: list (PL.ident * PL.Ty.t)) : Prop :=
  forall st1 st_mid,
    PL.poly_instance_list_semantics
      envv
      (retiled_old_pinstrs (List.length envv) before_pis after_pis ws,
       varctxt, vars)
      st1 st_mid ->
    exists st2',
      PL.poly_instance_list_semantics
        envv
        (before_pis, varctxt, vars)
        st1 st2' /\
      Instr.State.eq st_mid st2'.

Theorem tiling_after_to_before_poly_correct_via_retiled_old :
  forall envv before_pis after_pis ws varctxt vars st1 st2,
    List.length before_pis = List.length after_pis ->
    List.length after_pis = List.length ws ->
    Forall2 after_matches_tiling_witness after_pis ws ->
    (forall ipl_ext tau1 tau2,
      PL.flatten_instrs_ext
        envv
        (compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      PL.Permutable_ext tau1 tau2) ->
    tiling_retiled_old_to_before_poly_layer
      envv before_pis after_pis ws varctxt vars ->
    Instr.NonAlias st1 ->
    PL.poly_instance_list_semantics envv (after_pis, varctxt, vars) st1 st2 ->
    exists st2',
      PL.poly_instance_list_semantics
        envv
        (before_pis, varctxt, vars)
        st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros envv before_pis after_pis ws varctxt vars st1 st2
         Hlen_after Hlen_ws Hwits Hperm Hlayer Halias Hafter.
  destruct
    (tiling_after_to_retiled_old_poly_correct
       envv before_pis after_pis ws varctxt vars st1 st2
       Hlen_after Hlen_ws Hwits Hperm Halias Hafter)
    as [st_mid [Hretiled Heq_mid]].
  destruct (Hlayer st1 st_mid Hretiled) as [st2' [Hbefore Heq_before]].
  exists st2'.
  split.
  - exact Hbefore.
  - eapply Instr.State.eq_trans.
    + exact Heq_mid.
    + exact Heq_before.
Qed.

Theorem tiling_after_to_before_instance_correct_via_retiled_old :
  forall before_pis after_pis ws varctxt vars st1 st2,
    List.length before_pis = List.length after_pis ->
    List.length after_pis = List.length ws ->
    Forall2 after_matches_tiling_witness after_pis ws ->
    (forall envv ipl_ext tau1 tau2,
      PL.flatten_instrs_ext
        envv
        (compose_tiling_pinstrs_ext_from_after
           (List.length envv) before_pis after_pis ws)
        ipl_ext ->
      In tau1 ipl_ext ->
      In tau2 ipl_ext ->
      PL.instr_point_ext_old_sched_lt tau1 tau2 ->
      PL.instr_point_ext_new_sched_ge tau1 tau2 ->
      PL.Permutable_ext tau1 tau2) ->
    (forall envv,
      tiling_retiled_old_to_before_poly_layer
        envv before_pis after_pis ws varctxt vars) ->
    PL.instance_list_semantics (after_pis, varctxt, vars) st1 st2 ->
    exists st2',
      PL.instance_list_semantics (before_pis, varctxt, vars) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros before_pis after_pis ws varctxt vars st1 st2
         Hlen_after Hlen_ws Hwits Hperm Hlayer Hinst_after.
  inversion Hinst_after as
    [pprog pis varctxt' vars' envv st1' st2'
     Hpprog Hcompat Halias Hinit Hpoly];
    subst.
  inversion Hpprog; subst; clear Hpprog.
  destruct
    (tiling_after_to_before_poly_correct_via_retiled_old
       envv before_pis pis ws varctxt' vars' st1 st2
       Hlen_after Hlen_ws Hwits
       (Hperm envv) (Hlayer envv) Halias Hpoly)
    as [st2'' [Hpoly_before Heq]].
  exists st2''.
  split.
  - econstructor.
    + reflexivity.
    + exact Hcompat.
    + exact Halias.
    + exact Hinit.
    + exact Hpoly_before.
  - exact Heq.
Qed.

End TilingRelation.
