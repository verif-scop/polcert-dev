Require Import Bool.
Require Import List.
Require Import Permutation.
Require Import SetoidList.
Require Import Sorting.Sorted.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import Base.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import Linalg.
Require Import LinalgExt.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import ASTGen.
Require Import CodeGen.
Require Import LoopCleanup.
Require Import LoopSingletonCleanup.
Require Import SelectionSort.
Require Import LibTactics.

Module PrepareCodegen (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module Loop := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module ASTGen := ASTGen PolIRs.
Module CodeGen := CodeGen PolIRs.
Module Cleanup := LoopSingletonCleanup PolIRs.

Definition resize_affine (cols: nat) (aff: list Z * Z) : list Z * Z :=
  let '(zs, c) := aff in
  (resize cols zs, c).

Definition resize_affine_list (cols: nat) (affs: list (list Z * Z)) : list (list Z * Z) :=
  map (resize_affine cols) affs.

Definition resize_access (cols: nat) (acc: AccessFunction) : AccessFunction :=
  let '(arrid, affs) := acc in
  (arrid, resize_affine_list cols affs).

Definition resize_access_list (cols: nat) (accs: list AccessFunction) : list AccessFunction :=
  map (resize_access cols) accs.

Definition source_cols (varctxt: list Instr.ident) (pi: PolyLang.PolyInstr) : nat :=
  length varctxt + pi.(PolyLang.pi_depth).

Definition codegen_target_dim (pp: PolyLang.t) : nat :=
  let '(_, _, vars) := pp in
  Nat.max (length vars) (PolyLang.pprog_current_dim pp).

Definition depth_tail_zero (env_dim cols: nat) (pi: PolyLang.PolyInstr) : Prop :=
  forall p,
    in_poly p pi.(PolyLang.pi_poly) = true ->
    is_null (skipn (env_dim + pi.(PolyLang.pi_depth)) (resize cols p)) = true.

Definition codegen_ready_pi (env_dim cols: nat) (pi: PolyLang.PolyInstr) : Prop :=
  (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat /\
  exact_listzzs_cols cols pi.(PolyLang.pi_poly) /\
  exact_listzzs_cols cols pi.(PolyLang.pi_schedule) /\
  exact_listzzs_cols cols pi.(PolyLang.pi_transformation) /\
  Forall (fun acc => let '(_, affs) := acc in exact_listzzs_cols cols affs) pi.(PolyLang.pi_waccess) /\
  Forall (fun acc => let '(_, affs) := acc in exact_listzzs_cols cols affs) pi.(PolyLang.pi_raccess) /\
  depth_tail_zero env_dim cols pi.

Definition codegen_ready_pprog_at (cols: nat) (pp: PolyLang.t) : Prop :=
  let '(pis, varctxt, vars) := pp in
  length varctxt <= cols /\
  forall pi, In pi pis -> codegen_ready_pi (length varctxt) cols pi.

Definition codegen_ready_pprog (pp: PolyLang.t) : Prop :=
  codegen_ready_pprog_at (codegen_target_dim pp) pp.

Definition codegen_wf_pprog_at (cols: nat) (pp: PolyLang.t) : Prop :=
  let '(pis, varctxt, vars) := pp in
  length varctxt <= cols /\
  ASTGen.pis_have_dimension pis cols /\
  (forall pi, In pi pis -> (poly_nrl pi.(PolyLang.pi_schedule) <= cols)%nat).

Definition codegen_wf_pprog (pp: PolyLang.t) : Prop :=
  codegen_wf_pprog_at (codegen_target_dim pp) pp.

Definition encode_depth_in_domain (env_dim cols: nat) (pi: PolyLang.PolyInstr) : Domain :=
  let src_cols := env_dim + pi.(PolyLang.pi_depth) in
  resize_affine_list cols pi.(PolyLang.pi_poly) ++
  resize_affine_list cols (PolyLang.make_null_poly src_cols (cols - src_cols)).

Definition prepare_pi (env_dim cols: nat) (pi: PolyLang.PolyInstr) : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := encode_depth_in_domain env_dim cols pi;
    PolyLang.pi_schedule := resize_affine_list cols pi.(PolyLang.pi_schedule);
    PolyLang.pi_point_witness :=
      PointWitness.PSWInsertAtEnd
        (cols - (env_dim + pi.(PolyLang.pi_depth)))%nat
        pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := resize_affine_list cols pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation :=
      resize_affine_list cols pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := resize_access_list cols pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := resize_access_list cols pi.(PolyLang.pi_raccess);
  |}.

Definition prepare_codegen (pp: PolyLang.t) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  let cols := codegen_target_dim pp in
  (map (prepare_pi (length varctxt) cols) pis, varctxt, vars).

Definition source_ip_of (env_dim n: nat) (pi: PolyLang.PolyInstr) (p: list Z)
  : PolyLang.InstrPoint :=
  let idx := resize (env_dim + pi.(PolyLang.pi_depth)) p in
  {|
    PolyLang.ip_nth := n;
    PolyLang.ip_index := idx;
    PolyLang.ip_transformation := PolyLang.current_transformation_of pi idx;
    PolyLang.ip_time_stamp :=
      affine_product pi.(PolyLang.pi_schedule)
                     idx;
    PolyLang.ip_instruction := pi.(PolyLang.pi_instr);
    PolyLang.ip_depth := pi.(PolyLang.pi_depth);
  |}.

Definition np_compare (ip1 ip2: PolyLang.InstrPoint) : comparison :=
  match Nat.compare ip1.(PolyLang.ip_nth) ip2.(PolyLang.ip_nth) with
  | Eq => lex_compare ip1.(PolyLang.ip_index) ip2.(PolyLang.ip_index)
  | c => c
  end.

Definition np_ltb (ip1 ip2: PolyLang.InstrPoint) : bool :=
  comparison_eqb (np_compare ip1 ip2) Lt.

Definition np_eqb (ip1 ip2: PolyLang.InstrPoint) : bool :=
  comparison_eqb (np_compare ip1 ip2) Eq.

Lemma exact_listzzs_cols_app:
  forall cols l1 l2,
    exact_listzzs_cols cols l1 ->
    exact_listzzs_cols cols l2 ->
    exact_listzzs_cols cols (l1 ++ l2).
Proof.
  intros cols l1 l2 H1 H2 listz z listzz Hin Heq.
  apply in_app_or in Hin.
  destruct Hin.
  - eapply H1; eauto.
  - eapply H2; eauto.
Qed.

Lemma resize_affine_list_exact_cols:
  forall cols affs,
    exact_listzzs_cols cols (resize_affine_list cols affs).
Proof.
  intros cols affs listz z listzz Hin Heq.
  unfold resize_affine_list in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[zs c] [Hc Hin]].
  inversion Hc; subst.
  inversion Heq; subst.
  rewrite resize_length.
  reflexivity.
Qed.

Lemma resize_access_list_exact_cols:
  forall cols accs,
    Forall (fun acc => let '(_, affs) := acc in exact_listzzs_cols cols affs)
           (resize_access_list cols accs).
Proof.
  intros cols accs.
  unfold resize_access_list.
  induction accs as [|[arrid affs] accs IH]; simpl.
  - constructor.
  - constructor.
    + simpl. apply resize_affine_list_exact_cols.
    + exact IH.
Qed.

Lemma exact_listzzs_cols_implies_poly_nrl_le:
  forall cols affs,
    exact_listzzs_cols cols affs ->
    (poly_nrl affs <= cols)%nat.
Proof.
  intros cols affs Hcols.
  apply (proj1 (poly_nrl_def cols affs)).
  intros [zs c] Hin.
  specialize (Hcols zs c (zs, c) Hin eq_refl).
  apply veq_sym.
  apply resize_eq.
  subst cols.
  apply le_n.
Qed.

Lemma resize_affine_satisfies_constraint:
  forall cols env aff,
    length env = cols ->
    satisfies_constraint env (resize_affine cols aff) =
    satisfies_constraint env aff.
Proof.
  intros cols env [v c] Hlen.
  unfold resize_affine, satisfies_constraint; simpl.
  rewrite dot_product_commutative.
  rewrite <- Hlen.
  rewrite dot_product_resize_left.
  rewrite dot_product_commutative.
  reflexivity.
Qed.

Lemma resize_affine_list_in_poly:
  forall cols env affs,
    length env = cols ->
    in_poly env (resize_affine_list cols affs) =
    in_poly env affs.
Proof.
  intros cols env affs Hlen.
  unfold in_poly, resize_affine_list.
  induction affs as [|aff affs IH]; simpl.
  - reflexivity.
  - rewrite resize_affine_satisfies_constraint.
    + rewrite IH; auto.
    + exact Hlen.
Qed.

Lemma encode_depth_in_domain_in_poly:
  forall env_dim cols pi p,
    exact_listzzs_cols (env_dim + pi.(PolyLang.pi_depth)) pi.(PolyLang.pi_poly) ->
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    let src_cols := env_dim + pi.(PolyLang.pi_depth) in
    in_poly p (encode_depth_in_domain env_dim cols pi) = true ->
    in_poly (resize src_cols p) pi.(PolyLang.pi_poly) = true /\
    is_null (skipn src_cols (resize cols p)) = true.
Proof.
  intros env_dim cols pi p Hpoly_exact Hsrcle src_cols Hin.
  unfold encode_depth_in_domain in Hin.
  unfold in_poly in Hin.
  rewrite forallb_app in Hin.
  apply andb_true_iff in Hin.
  destruct Hin as [Hdom Hnull].
  split.
  - assert (Hdom' : in_poly (resize cols p) (resize_affine_list cols pi.(PolyLang.pi_poly)) = true).
    {
      rewrite in_poly_nrlength with (n := cols).
      - exact Hdom.
      - eapply exact_listzzs_cols_implies_poly_nrl_le.
        apply resize_affine_list_exact_cols.
    }
    rewrite resize_affine_list_in_poly in Hdom' by (rewrite resize_length; reflexivity).
    assert (Hin_src : in_poly (resize src_cols (resize cols p)) pi.(PolyLang.pi_poly) = true).
    {
      rewrite in_poly_nrlength with (p := resize cols p) (n := src_cols).
      - exact Hdom'.
      - eapply exact_listzzs_cols_implies_poly_nrl_le.
        exact Hpoly_exact.
    }
    replace (resize src_cols (resize cols p)) with (resize src_cols p) in Hin_src.
    + exact Hin_src.
    + rewrite resize_resize by exact Hsrcle. reflexivity.
  - assert (Hnull' :
        in_poly (resize cols p)
                (resize_affine_list cols
                  (PolyLang.make_null_poly src_cols (cols - src_cols))) = true).
    {
      rewrite in_poly_nrlength with (n := cols).
      - exact Hnull.
      - eapply exact_listzzs_cols_implies_poly_nrl_le.
        apply resize_affine_list_exact_cols.
    }
    rewrite resize_affine_list_in_poly in Hnull' by (rewrite resize_length; reflexivity).
    assert (Hsplit: resize cols p =
      resize src_cols (resize cols p) ++
      skipn src_cols (resize cols p)).
    {
      apply same_length_eq.
      - rewrite app_length, skipn_length.
        rewrite !resize_length.
        replace (src_cols + (cols - src_cols)) with cols by lia.
        reflexivity.
      - apply veq_sym.
        apply resize_skipn_eq.
    }
    rewrite Hsplit in Hnull'.
    replace
      (resize src_cols (resize cols p) ++ skipn src_cols (resize cols p))
      with
      (resize src_cols (resize cols p) ++ skipn src_cols (resize cols p) ++ [])
      in Hnull'.
    2: { rewrite app_nil_r. reflexivity. }
    rewrite PolyLang.make_null_poly_correct in Hnull'.
    + exact Hnull'.
    + rewrite resize_length. reflexivity.
    + rewrite skipn_length, resize_length. lia.
Qed.

Lemma prepare_codegen_preserve_ctxt_vars:
  forall pis varctxt vars,
    prepare_codegen (pis, varctxt, vars) =
    (map (prepare_pi (length varctxt) (codegen_target_dim (pis, varctxt, vars))) pis,
     varctxt,
     vars).
Proof.
  intros. unfold prepare_codegen, codegen_target_dim. reflexivity.
Qed.

Lemma firstn_resize :
  forall n m p,
    (n <= m)%nat ->
    firstn n (resize m p) = resize n p.
Proof.
  induction n as [|n IH]; intros m p Hle; simpl.
  - reflexivity.
  - destruct m as [|m]; [lia|].
    destruct p as [|x p]; simpl.
    + rewrite IH by lia. reflexivity.
    + rewrite IH by lia. reflexivity.
Qed.

Lemma resize_affine_affine_product:
  forall src_cols cols affs p,
    exact_listzzs_cols src_cols affs ->
    (src_cols <= cols)%nat ->
    affine_product (resize_affine_list cols affs) p =
    affine_product affs (resize src_cols p).
Proof.
  intros src_cols cols affs p Hexact Hle.
  unfold affine_product, resize_affine_list.
  induction affs as [|[zs c] affs IH]; simpl.
  - reflexivity.
  - pose proof (Hexact zs c (zs, c) (or_introl eq_refl) eq_refl) as Hlenzs.
    f_equal.
    + erewrite dot_product_eq_compat_left.
      2: { apply resize_eq. lia. }
      rewrite <- Hlenzs.
      rewrite dot_product_resize_right.
      reflexivity.
    + apply IH.
      intros listz z listzz Hin Heq.
      eapply Hexact; eauto.
      right; exact Hin.
Qed.

Lemma prepare_pi_schedule_eval:
  forall env_dim cols pi p,
    exact_listzzs_cols (env_dim + pi.(PolyLang.pi_depth)) pi.(PolyLang.pi_schedule) ->
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    affine_product (prepare_pi env_dim cols pi).(PolyLang.pi_schedule) p =
    affine_product pi.(PolyLang.pi_schedule)
                   (resize (env_dim + pi.(PolyLang.pi_depth)) p).
Proof.
  intros. unfold prepare_pi; simpl.
  eapply resize_affine_affine_product; eauto.
Qed.

Lemma wf_pprog_affine_implies_source_cols_le :
  forall pis varctxt vars cols pi,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    In pi pis ->
    (length varctxt + pi.(PolyLang.pi_depth) <= cols)%nat.
Proof.
  intros pis varctxt vars cols pi Hwf Hdim_cols Hin.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi Hin) as Hwfpi.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [_ _].
  assert (Hpin :
    PolyLang.pinstr_current_dim varctxt pi <= cols).
  {
    eapply Nat.le_trans.
    - eapply PolyLang.pprog_current_dim_ge_pinstr; eauto.
    - exact Hdim_cols.
  }
  unfold PolyLang.pinstr_current_dim in Hpin.
  eapply Nat.le_trans.
  - apply Nat.le_max_l.
  - exact Hpin.
Qed.

Lemma fold_left_max_le_bound :
  forall ds init bound,
    init <= bound ->
    Forall (fun d => d <= bound)%nat ds ->
    List.fold_left Nat.max ds init <= bound.
Proof.
  induction ds as [|d ds IH]; intros init bound Hinit Hforall; simpl.
  - exact Hinit.
  - inversion Hforall; subst.
    eapply IH.
    + apply Nat.max_lub; assumption.
    + exact H2.
Qed.

Lemma wf_pprog_affine_implies_pprog_current_dim_le_target :
  forall pis varctxt vars,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars)
     <= codegen_target_dim (pis, varctxt, vars))%nat.
Proof.
  intros pis varctxt vars _.
  unfold codegen_target_dim.
  simpl.
  apply Nat.le_max_r.
Qed.

Lemma prepare_pi_transformation_eval:
  forall env_dim cols pi p,
    exact_listzzs_cols (env_dim + pi.(PolyLang.pi_depth)) pi.(PolyLang.pi_transformation) ->
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    affine_product (prepare_pi env_dim cols pi).(PolyLang.pi_transformation) p =
    affine_product pi.(PolyLang.pi_transformation)
                   (resize (env_dim + pi.(PolyLang.pi_depth)) p).
Proof.
  intros. unfold prepare_pi; simpl.
  eapply resize_affine_affine_product; eauto.
Qed.

Lemma prepare_pi_current_env_dim_in_dim_affine:
  forall env_dim cols pi,
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    pi.(PolyLang.pi_point_witness) = PointWitness.PSWIdentity pi.(PolyLang.pi_depth) ->
    PolyLang.current_env_dim_in_dim cols (prepare_pi env_dim cols pi).(PolyLang.pi_point_witness) = env_dim.
Proof.
  intros env_dim cols pi Hcols Hwit.
  unfold PolyLang.current_env_dim_in_dim.
  unfold prepare_pi; simpl.
  rewrite Hwit.
  unfold PointWitness.witness_current_point_dim,
    PointWitness.witness_base_point_dim,
    PointWitness.witness_added_dims.
  simpl.
  lia.
Qed.

Lemma prepare_pi_current_src_args_in_dim_affine:
  forall env_dim cols pi p,
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    pi.(PolyLang.pi_point_witness) = PointWitness.PSWIdentity pi.(PolyLang.pi_depth) ->
    p =v= resize cols p ->
    PolyLang.current_src_args_in_dim cols (prepare_pi env_dim cols pi) p =
    affine_product (prepare_pi env_dim cols pi).(PolyLang.pi_transformation) p.
Proof.
  intros env_dim cols pi p Hcols Hwit Hp.
  unfold PolyLang.current_src_args_in_dim, PolyLang.current_src_args_at.
  rewrite (prepare_pi_current_env_dim_in_dim_affine env_dim cols pi Hcols Hwit).
  unfold PolyLang.current_transformation_at, PolyLang.current_transformation_for_witness.
  unfold prepare_pi; simpl.
  rewrite Hwit.
  simpl.
  set (added := (cols - (env_dim + PolyLang.pi_depth pi))%nat).
  assert
    (Heq_affs :
      map
        (fun '(coeffs, rhs) =>
           (resize (length coeffs + added) coeffs, rhs))
        (resize_affine_list cols (PolyLang.pi_transformation pi)) =
      resize_affine_list (cols + added)
        (resize_affine_list cols (PolyLang.pi_transformation pi))).
  {
    unfold resize_affine_list.
    apply map_ext_in.
    intros [coeffs rhs] Hin.
    simpl.
    assert (Hcoeffs : length coeffs = cols).
    {
      eapply resize_affine_list_exact_cols; eauto.
    }
    rewrite Hcoeffs.
    reflexivity.
  }
  rewrite Heq_affs.
  rewrite (resize_affine_affine_product cols (cols + added)).
  - eapply affine_product_proper; [reflexivity|].
    apply veq_sym. exact Hp.
  - apply resize_affine_list_exact_cols.
  - lia.
Qed.

Lemma prepare_env_scan_true_implies_source_ip_props:
  forall pis varctxt vars cols envv n p pi,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    length envv = length varctxt ->
    nth_error pis n = Some pi ->
    PolyLang.env_scan
      (map (prepare_pi (length varctxt) cols) pis)
      envv cols n p = true ->
    let env_dim := length varctxt in
    let src_cols := env_dim + pi.(PolyLang.pi_depth) in
    let ip := source_ip_of env_dim n pi p in
    firstn env_dim ip.(PolyLang.ip_index) = envv /\
    PolyLang.belongs_to ip pi /\
    length ip.(PolyLang.ip_index) = src_cols /\
    is_eq p (resize cols p) = true /\
    is_null (skipn src_cols (resize cols p)) = true.
Proof.
  intros pis varctxt vars cols envv n p pi Hwf Hdim_cols Henvlen Hnth.
  pose proof (nth_error_In _ _ Hnth) as Hpi_in.
  assert (Hsrc_cols_le : (length varctxt + pi.(PolyLang.pi_depth) <= cols)%nat).
  {
    eapply wf_pprog_affine_implies_source_cols_le; eauto.
  }
  unfold PolyLang.env_scan.
  rewrite map_nth_error with (d := pi); auto.
  simpl.
  intros Hscan.
  apply andb_prop in Hscan.
  destruct Hscan as [Henv Hdom].
  apply andb_prop in Henv.
  destruct Henv as [Henv Hplen].
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi Hpi_in) as Hwfpi.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [Hwfpi [_ _]].
  unfold PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as
      [_ [_ [_ [_ [Hpoly_exact [Htf_exact [_ [Hsched_exact [_ _]]]]]]]]].
  pose proof
    (encode_depth_in_domain_in_poly
       (length varctxt) cols pi p Hpoly_exact
       Hsrc_cols_le
       Hdom)
    as Hprepared_dom.
  destruct Hprepared_dom as [Hsrcdom Htail].
  repeat split.
  - unfold source_ip_of. simpl.
    rewrite firstn_resize by lia.
    eapply same_length_eq.
    + rewrite resize_length. symmetry. exact Henvlen.
    + rewrite is_eq_commutative in Henv.
      rewrite Henvlen in Henv.
      exact Henv.
  - unfold PolyLang.belongs_to.
    unfold source_ip_of. simpl.
    repeat split; try reflexivity.
    exact Hsrcdom.
  - unfold source_ip_of. simpl. rewrite resize_length. reflexivity.
  - exact Hplen.
  - exact Htail.
Qed.

Lemma prepare_step_semantics_to_source_ip_sema:
  forall pis varctxt vars cols n p pi st1 st2 wcs rcs,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    nth_error pis n = Some pi ->
    p =v= resize cols p ->
    Instr.instr_semantics
      (prepare_pi (length varctxt) cols pi).(PolyLang.pi_instr)
      (PolyLang.current_src_args_in_dim cols (prepare_pi (length varctxt) cols pi) p)
      wcs rcs st1 st2 ->
    PolyLang.instr_point_sema (source_ip_of (length varctxt) n pi p) st1 st2.
Proof.
  intros pis varctxt vars cols n p pi st1 st2 wcs rcs Hwf Hdim_cols Hnth Hp Hsem.
  pose proof Hwf as Hwf_all.
  pose proof (nth_error_In _ _ Hnth) as Hpi_in.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi Hpi_in) as Hwfpi.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [Hwfpi [Hwit_eq _]].
  unfold PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as
      [Hwit_cur
       [Hcur_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hwacc Hracc]]]]]]]]].
  rewrite Hwit_eq in Htf_exact.
  simpl in Htf_exact.
  pose proof
    (wf_pprog_affine_implies_source_cols_le
       pis varctxt vars cols pi Hwf_all Hdim_cols Hpi_in)
    as Hcols_le_cols.
  rewrite prepare_pi_current_src_args_in_dim_affine in Hsem.
  2: exact Hcols_le_cols.
  2: exact Hwit_eq.
  2: exact Hp.
  rewrite (prepare_pi_transformation_eval (length varctxt) cols pi p) in Hsem.
  2: exact Htf_exact.
  2: lia.
  assert (Htf_cur :
    PolyLang.current_transformation_of pi
      (resize (length varctxt + PolyLang.pi_depth pi) p) =
    PolyLang.pi_transformation pi).
  {
    unfold PolyLang.current_transformation_of, PolyLang.current_transformation_at,
      PolyLang.current_env_dim_of.
    rewrite Hwit_eq.
    simpl.
    replace
      (length varctxt + PolyLang.pi_depth pi - PolyLang.pi_depth pi)%nat
      with (length varctxt) by lia.
    reflexivity.
  }
  econstructor.
  simpl.
  replace
    (affine_product
       (PolyLang.current_transformation_of pi
          (resize (length varctxt + PolyLang.pi_depth pi) p))
       (resize (length varctxt + PolyLang.pi_depth pi) p))
    with
      (affine_product
         (PolyLang.pi_transformation pi)
         (resize (length varctxt + PolyLang.pi_depth pi) p)).
  - exact Hsem.
  - rewrite Htf_cur. reflexivity.
Qed.

Lemma source_ip_of_nth :
  forall env_dim n pi p,
    PolyLang.ip_nth (source_ip_of env_dim n pi p) = n.
Proof. reflexivity. Qed.

Lemma source_ip_of_index_length :
  forall env_dim n pi p,
    length (PolyLang.ip_index (source_ip_of env_dim n pi p)) =
    env_dim + pi.(PolyLang.pi_depth).
Proof.
  intros. unfold source_ip_of. simpl. rewrite resize_length. reflexivity.
Qed.

Lemma source_ip_of_prefix :
  forall env_dim n pi p,
    firstn env_dim (PolyLang.ip_index (source_ip_of env_dim n pi p)) =
    resize env_dim p.
Proof.
  intros. unfold source_ip_of. simpl.
  apply firstn_resize. lia.
Qed.

Lemma np_ltb_iff :
  forall ip1 ip2,
    np_ltb ip1 ip2 = true <-> PolyLang.np_lt ip1 ip2.
Proof.
  intros ip1 ip2.
  unfold np_ltb, np_compare, PolyLang.np_lt.
  destruct (Nat.compare_spec (PolyLang.ip_nth ip1) (PolyLang.ip_nth ip2)) as [Heq|Hlt|Hgt].
  - rewrite comparison_eqb_iff_eq.
    split; intro H.
    + right. split; [exact Heq|exact H].
    + destruct H as [H|[Hnth Hlex]]; [lia|]. exact Hlex.
  - rewrite comparison_eqb_iff_eq.
    split; intro H.
    + left. lia.
    + destruct H as [H|[H _]]; [reflexivity|lia].
  - simpl. split; intro H.
    + discriminate.
    + destruct H as [H|[H _]]; lia.
Qed.

Lemma np_eqb_iff :
  forall ip1 ip2,
    np_eqb ip1 ip2 = true <-> PolyLang.np_eq ip1 ip2.
Proof.
  intros ip1 ip2.
  unfold np_eqb, np_compare, PolyLang.np_eq.
  destruct (Nat.compare_spec (PolyLang.ip_nth ip1) (PolyLang.ip_nth ip2)) as [Heq|Hlt|Hgt].
  - rewrite comparison_eqb_iff_eq. split; intro H.
    + split; [exact Heq|exact H].
    + destruct H as [_ Hlex]. exact Hlex.
  - simpl. split; intro H.
    + discriminate.
    + destruct H as [H _]. lia.
  - simpl. split; intro H.
    + discriminate.
    + destruct H as [H _]. lia.
Qed.

Lemma lex_compare_eq_is_eq:
  forall t1 t2,
    lex_compare t1 t2 = Eq ->
    is_eq t1 t2 = true.
Proof.
  assert (Hleft :
    forall t, lex_compare_nil t = Eq -> is_eq [] t = true).
  {
    intros t Hnil.
    destruct t as [|a t]; simpl in *; auto.
    destruct a; try discriminate.
    apply is_null_lex_compare_nil in Hnil.
    simpl. rewrite Hnil. reflexivity.
  }
  assert (Hright :
    forall t, CompOpp (lex_compare_nil t) = Eq -> is_eq t [] = true).
  {
    intros t Hnil.
    assert (Hnil' : lex_compare_nil t = Eq).
    {
      destruct (lex_compare_nil t) eqn:Hcmp; simpl in Hnil; try discriminate; reflexivity.
    }
    rewrite is_eq_commutative.
    eapply Hleft; eauto.
  }
  induction t1 as [|x t1 IH]; intros t2 Hcmp.
  - destruct t2 as [|y t2].
    + reflexivity.
    + eapply Hleft. exact Hcmp.
  - destruct t2 as [|y t2].
    + eapply Hright. exact Hcmp.
    + simpl in Hcmp.
      destruct (Z.compare x y) eqn:Hxy; try discriminate.
      apply Z.compare_eq_iff in Hxy. subst y. simpl.
      rewrite Z.eqb_refl.
      apply IH. exact Hcmp.
Qed.

Lemma np_eq_left_implies_lt :
  forall x y z,
    PolyLang.np_eq x y ->
    PolyLang.np_lt y z ->
    PolyLang.np_lt x z.
Proof.
  intros x y z Heq Hlt.
  destruct Heq as [Hnthxy Hidxxy].
  destruct Hlt as [Hlt|[Hnthyz Hidxyz]].
  - left. rewrite Hnthxy. exact Hlt.
  - right. split.
    + rewrite Hnthxy. exact Hnthyz.
    + erewrite lex_compare_left_eq.
      * exact Hidxyz.
      * apply lex_compare_eq_is_eq. exact Hidxxy.
Qed.

Lemma np_eq_right_implies_lt :
  forall x y z,
    PolyLang.np_lt x y ->
    PolyLang.np_eq y z ->
    PolyLang.np_lt x z.
Proof.
  intros x y z Hlt Heq.
  destruct Heq as [Hnthyz Hidxyz].
  destruct Hlt as [Hlt|[Hnthxy Hidxxy]].
  - left. rewrite Hnthyz in Hlt. exact Hlt.
  - right. split.
    + rewrite Hnthyz in Hnthxy. exact Hnthxy.
    + pose proof
        (lex_compare_right_eq
           (PolyLang.ip_index x)
           (PolyLang.ip_index y)
           (PolyLang.ip_index z)
           (lex_compare_eq_is_eq _ _ Hidxyz)) as Heq.
      rewrite Heq in Hidxxy.
      exact Hidxxy.
Qed.

Lemma np_ltb_trans :
  transitive np_ltb.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  apply np_ltb_iff in Hxy.
  apply np_ltb_iff in Hyz.
  apply np_ltb_iff.
  eapply PolyLang.np_lt_trans; eauto.
Qed.

Lemma np_eqb_refl :
  reflexive np_eqb.
Proof.
  intros x. apply np_eqb_iff. unfold PolyLang.np_eq. split; auto.
  apply lex_compare_reflexive.
Qed.

Lemma np_eqb_trans :
  transitive np_eqb.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  apply np_eqb_iff.
  destruct PolyLang.np_eq_equivalence as [_ Hsym Htrans].
  eapply Htrans.
  - apply np_eqb_iff. exact Hxy.
  - apply np_eqb_iff. exact Hyz.
Qed.

Lemma np_eqb_symm :
  symmetric np_eqb.
Proof.
  unfold symmetric.
  intros x y.
  destruct (np_eqb x y) eqn:Hxy, (np_eqb y x) eqn:Hyx; auto.
  - apply np_eqb_iff in Hxy.
    destruct PolyLang.np_eq_equivalence as [_ Hsym _].
    pose proof (proj2 (np_eqb_iff y x) (Hsym _ _ Hxy)) as Hyx'.
    rewrite Hyx' in Hyx. discriminate.
  - apply np_eqb_iff in Hyx.
    destruct PolyLang.np_eq_equivalence as [_ Hsym _].
    pose proof (proj2 (np_eqb_iff x y) (Hsym _ _ Hyx)) as Hxy'.
    rewrite Hxy' in Hxy. discriminate.
Qed.

Lemma np_cmp_total :
  total np_ltb np_eqb.
Proof.
  unfold total.
  intros x y.
  destruct (Nat.compare_spec (PolyLang.ip_nth x) (PolyLang.ip_nth y)) as [Heq|Hlt|Hgt].
  - subst.
    pose proof (lex_compare_total (PolyLang.ip_index x) (PolyLang.ip_index y)) as Htot.
    destruct Htot as [Hlt'|[Hgt'|Heq']].
    + left. apply (proj2 (np_ltb_iff x y)). right. split; [exact Heq|exact Hlt'].
    + right. left. apply (proj2 (np_ltb_iff y x)). right. split; [symmetry; exact Heq|exact Hgt'].
    + right. right. apply (proj2 (np_eqb_iff x y)). split; [exact Heq|exact Heq'].
  - left. apply (proj2 (np_ltb_iff x y)). left. exact Hlt.
  - right. left. apply (proj2 (np_ltb_iff y x)). left. exact Hgt.
Qed.

Lemma np_eqb_ltb_implies_ltb :
  eqb_ltb_implies_ltb np_ltb np_eqb.
Proof.
  unfold eqb_ltb_implies_ltb.
  intros x y z Heq Hlt.
  apply np_ltb_iff.
  eapply np_eq_left_implies_lt.
  - apply np_eqb_iff. exact Heq.
  - apply np_ltb_iff. exact Hlt.
Qed.

Lemma np_ltb_eqb_implies_ltb :
  ltb_eqb_implies_ltb np_ltb np_eqb.
Proof.
  unfold ltb_eqb_implies_ltb.
  intros x y z Hlt Heq.
  apply np_ltb_iff.
  eapply np_eq_right_implies_lt.
  - apply np_ltb_iff. exact Hlt.
  - apply np_eqb_iff. exact Heq.
Qed.

Lemma source_ip_of_eq_from_is_eq :
  forall env_dim n pi p q,
    is_eq p q = true ->
    source_ip_of env_dim n pi p = source_ip_of env_dim n pi q.
Proof.
  intros env_dim n [depth instr poly sched pw tf acc_tf wacc racc] p q Heq.
  unfold source_ip_of. simpl.
  assert (Hresize :
    resize (env_dim + depth) p = resize (env_dim + depth) q).
  {
    apply resize_eq_compat. exact Heq.
  }
  f_equal; try reflexivity.
  - exact Hresize.
  - rewrite Hresize. reflexivity.
  - rewrite Hresize. reflexivity.
Qed.

Lemma source_resize_eq_implies_prepare_eq :
  forall cols src_cols p q,
    (src_cols <= cols)%nat ->
    is_eq p (resize cols p) = true ->
    is_eq q (resize cols q) = true ->
    is_null (skipn src_cols (resize cols p)) = true ->
    is_null (skipn src_cols (resize cols q)) = true ->
    resize src_cols p = resize src_cols q ->
    is_eq p q = true.
Proof.
  intros cols src_cols p q Hle Hp Hq Htailp Htailq Hprefix.
  assert (Hfull :
    is_eq (resize cols p) (resize cols q) = true).
  {
    assert (Hsplitp :
      resize cols p =
      resize src_cols p ++ skipn src_cols (resize cols p)).
    {
      apply same_length_eq.
      - rewrite app_length, skipn_length, !resize_length. lia.
      - replace (resize src_cols p ++ skipn src_cols (resize cols p))
          with (resize src_cols (resize cols p) ++ skipn src_cols (resize cols p)).
        2: {
          rewrite resize_resize by exact Hle. reflexivity.
        }
        symmetry. apply resize_skipn_eq.
    }
    assert (Hsplitq :
      resize cols q =
      resize src_cols q ++ skipn src_cols (resize cols q)).
    {
      apply same_length_eq.
      - rewrite app_length, skipn_length, !resize_length. lia.
      - replace (resize src_cols q ++ skipn src_cols (resize cols q))
          with (resize src_cols (resize cols q) ++ skipn src_cols (resize cols q)).
        2: {
          rewrite resize_resize by exact Hle. reflexivity.
        }
        symmetry. apply resize_skipn_eq.
    }
    rewrite Hsplitp, Hsplitq.
    rewrite is_eq_app by (rewrite !resize_length; reflexivity).
    rewrite Hprefix.
    rewrite is_eq_reflexive. simpl.
    rewrite is_eq_is_null_left by exact Htailp.
    rewrite Htailq. reflexivity.
  }
  rewrite is_eq_veq.
  rewrite is_eq_veq in Hp.
  rewrite is_eq_veq in Hq.
  rewrite is_eq_veq in Hfull.
  eapply veq_transitive.
  - exact Hp.
  - eapply veq_transitive.
    + exact Hfull.
    + apply veq_sym. exact Hq.
Qed.

Lemma prepare_env_scan_true_source_ip_eq_implies_same_scan_key :
  forall pis varctxt vars cols envv n1 n2 p1 p2 pi1 pi2,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    length envv = length varctxt ->
    nth_error pis n1 = Some pi1 ->
    nth_error pis n2 = Some pi2 ->
    PolyLang.env_scan
      (map (prepare_pi (length varctxt) cols) pis)
      envv cols n1 p1 = true ->
    PolyLang.env_scan
      (map (prepare_pi (length varctxt) cols) pis)
      envv cols n2 p2 = true ->
    source_ip_of (length varctxt) n1 pi1 p1 =
    source_ip_of (length varctxt) n2 pi2 p2 ->
    n1 = n2 /\ pi1 = pi2 /\ is_eq p1 p2 = true.
Proof.
  intros pis varctxt vars cols envv n1 n2 p1 p2 pi1 pi2
         Hwf Hdim_cols Henvlen Hnth1 Hnth2 Hscan1 Hscan2 Heqip.
  pose proof Hwf as Hwf_all.
  assert (Hn : n1 = n2).
  {
    pose proof (f_equal PolyLang.ip_nth Heqip) as Hnth.
    simpl in Hnth. exact Hnth.
  }
  subst n2.
  assert (Hpi : pi1 = pi2) by congruence.
  subst pi2.
  pose proof
    (prepare_env_scan_true_implies_source_ip_props
       pis varctxt vars cols envv n1 p1 pi1
       Hwf Hdim_cols Henvlen Hnth1 Hscan1) as Hprops1.
  pose proof
    (prepare_env_scan_true_implies_source_ip_props
       pis varctxt vars cols envv n1 p2 pi1
       Hwf Hdim_cols Henvlen Hnth1 Hscan2) as Hprops2.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi1 (nth_error_In _ _ Hnth1)) as Hwfpi1.
  destruct Hprops1 as [_ [_ [_ [Hp1 Htail1]]]].
  destruct Hprops2 as [_ [_ [_ [Hp2 Htail2]]]].
  pose proof (f_equal PolyLang.ip_index Heqip) as Hidx.
  simpl in Hidx.
  pose proof (nth_error_In _ _ Hnth1) as Hpi1_in.
  split; [reflexivity|].
  split; [reflexivity|].
  eapply source_resize_eq_implies_prepare_eq
    with (cols := cols) (src_cols := length varctxt + pi1.(PolyLang.pi_depth)).
  - exact (wf_pprog_affine_implies_source_cols_le
             pis varctxt vars cols pi1 Hwf_all Hdim_cols Hpi1_in).
  - exact Hp1.
  - exact Hp2.
  - exact Htail1.
  - exact Htail2.
  - exact Hidx.
Qed.

Lemma source_ip_of_timestamp_prepare :
  forall pis varctxt vars cols n pi p,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    nth_error pis n = Some pi ->
    PolyLang.ip_time_stamp (source_ip_of (length varctxt) n pi p) =
    affine_product (prepare_pi (length varctxt) cols pi).(PolyLang.pi_schedule) p.
Proof.
  intros pis varctxt vars cols n pi p Hwf Hdim_cols Hnth.
  pose proof Hwf as Hwf_all.
  pose proof (nth_error_In _ _ Hnth) as Hpi_in.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi Hpi_in) as Hwfpi.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [Hwfpi _].
  unfold PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as
      [Hwit_cur
       [Hcur_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hwacc Hracc]]]]]]]]].
  unfold source_ip_of. simpl.
  symmetry.
  eapply prepare_pi_schedule_eval.
  - exact Hsched_exact.
  - exact (wf_pprog_affine_implies_source_cols_le
             pis varctxt vars cols pi Hwf_all Hdim_cols Hpi_in).
Qed.

Lemma selection_sort_np_is_correct:
  forall ipl1 ipl2,
    SelectionSort np_ltb np_eqb ipl1 = ipl2 ->
    Permutation ipl1 ipl2 /\
    Sorted_b (combine_leb np_ltb np_eqb) ipl2.
Proof.
  intros.
  eapply selection_sort_is_correct; eauto.
  - exact np_ltb_trans.
  - exact np_eqb_trans.
  - exact np_eqb_refl.
  - exact np_eqb_symm.
  - exact np_cmp_total.
  - exact np_eqb_ltb_implies_ltb.
  - exact np_ltb_eqb_implies_ltb.
Qed.

Lemma sortedb_np_nodup_implies_sorted_np :
  forall ipl,
    Sorted_b (combine_leb np_ltb np_eqb) ipl ->
    NoDupA PolyLang.np_eq ipl ->
    Sorted PolyLang.np_lt ipl.
Proof.
  intros ipl Hsorted.
  unfold Sorted_b in Hsorted.
  induction Hsorted; intros Hnodup.
  - constructor.
  - inversion Hnodup; subst.
    econstructor.
    + match goal with
      | Htail : NoDupA PolyLang.np_eq l |- _ =>
          apply IHHsorted; exact Htail
      end.
    + induction H.
      * constructor.
      * constructor.
        { unfold combine_leb in H.
          apply orb_prop in H.
          destruct H as [Hlt|Heq].
          - apply np_ltb_iff. exact Hlt.
          - exfalso.
            match goal with
            | Hnot : ~ InA PolyLang.np_eq a (b :: l) |- _ =>
                apply Hnot
            end.
            apply InA_alt.
            exists b. split.
            + apply np_eqb_iff. exact Heq.
            + left. reflexivity.
        }
Qed.

Lemma prepare_poly_semantics_collect :
  forall pis varctxt vars cols envv to_scan st1 st2,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    length envv = length varctxt ->
    PolyLang.poly_semantics
      cols
      to_scan
      (map (prepare_pi (length varctxt) cols) pis)
      st1 st2 ->
    (forall n p,
      to_scan n p = true ->
      PolyLang.env_scan
        (map (prepare_pi (length varctxt) cols) pis)
        envv cols n p = true) ->
    exists exec_ipl,
      PolyLang.instr_point_list_semantics exec_ipl st1 st2 /\
      Sorted PolyLang.instr_point_sched_le exec_ipl /\
      NoDup exec_ipl /\
      (forall ip,
        In ip exec_ipl <->
        exists n p pi,
          nth_error pis n = Some pi /\
          to_scan n p = true /\
          ip = source_ip_of (length varctxt) n pi p).
Proof.
  intros pis varctxt vars cols envv to_scan st1 st2 Hwf Hdim_cols Henvlen Hsem.
  intros Hsound.
  set (prep_pis := map (prepare_pi (length varctxt) cols) pis) in *.
  change (PolyLang.poly_semantics cols to_scan prep_pis st1 st2) in Hsem.
  change (forall n p, to_scan n p = true ->
            PolyLang.env_scan prep_pis envv cols n p = true) in Hsound.
  remember prep_pis as prep_pis0 eqn:Hprep_eq in Hsem.
  revert Hprep_eq.
  induction Hsem as
      [dim to_scan0 poly_instrs0 st0 Hdone
      | dim to_scan0 poly_instrs0 st1' st2' st3' wcs rcs poly_instr n p
          Hscanp Hnthprep Hmin Hstep Hrest IH];
    intros Hprep_eq.
  - exists (@nil PolyLang.InstrPoint).
    split.
    + constructor. apply Instr.State.eq_refl.
    + split.
      * constructor.
      * split.
        -- constructor.
        -- intros ip0.
           split.
           ++ intro Hin. inversion Hin.
           ++ intro Hin.
              destruct Hin as [n [p [pi [_ [Hscan _]]]]].
              specialize (Hdone n p). rewrite Hscan in Hdone. discriminate.
  - subst poly_instrs0.
    unfold prep_pis in Hnthprep, Hsound.
    destruct (nth_error pis n) eqn:Hsrcnth.
    2: {
      rewrite map_nth_error_none in Hnthprep; congruence.
    }
    assert (Hprep_pi :
      poly_instr = prepare_pi (length varctxt) dim p0).
    {
      rewrite map_nth_error with (d := p0) in Hnthprep; auto.
      inversion Hnthprep. reflexivity.
    }
    subst poly_instr.
    assert (Hscan_init :
      PolyLang.env_scan
        (map (prepare_pi (length varctxt) dim) pis)
        envv dim n p = true).
    {
      eapply Hsound. exact Hscanp.
    }
    assert (Hscan_vec : p =v= resize dim p).
    {
      unfold PolyLang.env_scan in Hscan_init.
      rewrite Hnthprep in Hscan_init.
      reflect.
      destruct Hscan_init as [[_ Hveq] _].
      exact Hveq.
    }
    assert (Hsound_scanned :
      forall n0 p1,
        PolyLang.scanned to_scan0 n p n0 p1 = true ->
        PolyLang.env_scan
          (map (prepare_pi (length varctxt) dim) pis)
          envv dim n0 p1 = true).
    {
      intros n0 p1 Hsc.
      unfold PolyLang.scanned in Hsc.
      apply andb_prop in Hsc.
      destruct Hsc as [Hto _].
      eapply Hsound. exact Hto.
    }
    destruct (IH Hdim_cols Hsound_scanned eq_refl)
      as [tail [Htailsem [Htailsorted [Htailnodup Htailin]]]].
    exists (source_ip_of (length varctxt) n p0 p :: tail).
    split.
    + econstructor.
      * eapply prepare_step_semantics_to_source_ip_sema.
        -- exact Hwf.
        -- exact Hdim_cols.
        -- exact Hsrcnth.
        -- exact Hscan_vec.
        -- exact Hstep.
      * exact Htailsem.
    + split.
      * econstructor.
        -- exact Htailsorted.
        -- destruct tail as [|ip tail].
           { constructor. }
           { constructor.
             destruct (Htailin ip) as [Hforw _].
             destruct (Hforw (or_introl eq_refl))
               as [n2 [p2 [pi2 [Hnth2 [Hscan2 Hip2]]]]].
             subst ip.
             destruct (PolyLang.instr_point_sched_cmp_total
                         (source_ip_of (length varctxt) n p0 p)
                         (source_ip_of (length varctxt) n2 pi2 p2))
               as [Hlt|[Hgt|Heq]].
             - left.
               unfold PolyLang.instr_point_sched_ltb in Hlt.
               apply comparison_eqb_iff_eq in Hlt.
               exact Hlt.
             - exfalso.
               assert (Hnthprep2 :
                 nth_error
                   (map (prepare_pi (length varctxt) dim) pis) n2 =
                 Some (prepare_pi (length varctxt) dim pi2)).
               {
                 rewrite map_nth_error with (d := pi2); auto.
               }
               assert (Hltprep :
                 lex_compare
                   (affine_product
                      (prepare_pi (length varctxt) dim pi2).(PolyLang.pi_schedule) p2)
                   (affine_product
                      (prepare_pi (length varctxt) dim p0).(PolyLang.pi_schedule) p)
                 = Lt).
               {
                 unfold PolyLang.instr_point_sched_ltb in Hgt.
                 apply comparison_eqb_iff_eq in Hgt.
                 rewrite <- (source_ip_of_timestamp_prepare pis varctxt vars dim n2 pi2 p2 Hwf Hdim_cols Hnth2).
                 rewrite <- (source_ip_of_timestamp_prepare pis varctxt vars dim n p0 p Hwf Hdim_cols Hsrcnth).
                 exact Hgt.
               }
               unfold PolyLang.scanned in Hscan2.
               apply andb_prop in Hscan2.
               destruct Hscan2 as [Hto2 _].
               specialize (Hmin n2 p2 (prepare_pi (length varctxt) dim pi2)
                             Hnthprep2 Hltprep).
               rewrite Hto2 in Hmin. discriminate.
             - right.
               unfold PolyLang.instr_point_sched_eqb in Heq.
               apply comparison_eqb_iff_eq in Heq.
               exact Heq.
           }
      * split.
        { constructor.
          - intro Hin.
            destruct (Htailin (source_ip_of (length varctxt) n p0 p)) as [Hforw _].
            destruct (Hforw Hin)
              as [n2 [p2 [pi2 [Hnth2 [Hscan2 Heqip]]]]].
            pose proof
              (prepare_env_scan_true_source_ip_eq_implies_same_scan_key
                 pis varctxt vars dim envv n n2 p p2 p0 pi2
                 Hwf Hdim_cols Henvlen Hsrcnth Hnth2 Hscan_init (Hsound_scanned _ _ Hscan2) Heqip)
              as [Hn [Hpi Heqp]].
            subst n2 pi2.
            unfold PolyLang.scanned in Hscan2.
            apply andb_prop in Hscan2.
            destruct Hscan2 as [_ Hneq].
            rewrite Heqp, Nat.eqb_refl in Hneq.
            simpl in Hneq. discriminate.
          - exact Htailnodup.
        }
        { intros ip0.
          split.
          - intro Hin.
            destruct Hin as [Hin|Hin].
            + subst ip0.
              exists n. exists p. exists p0.
              repeat split; auto.
            + destruct (Htailin ip0) as [Hforw _].
              destruct (Hforw Hin) as [n2 [p2 [pi2 [Hnth2 [Hscan2 Hip]]]]].
              exists n2. exists p2. exists pi2.
              split; [exact Hnth2|].
              split.
              * unfold PolyLang.scanned in Hscan2.
                apply andb_prop in Hscan2.
                tauto.
              * exact Hip.
          - intro Hin.
            destruct Hin as [n2 [p2 [pi2 [Hnth2 [Hscan2 Hip]]]]].
            destruct (Nat.eq_dec n2 n) as [Hnn|Hnn].
            + subst n2.
              assert (Hpi2 : pi2 = p0) by congruence.
              subst pi2.
              destruct (is_eq p p2) eqn:Heqp.
              * left.
                rewrite Hip.
                symmetry.
                eapply source_ip_of_eq_from_is_eq.
                rewrite is_eq_commutative. exact Heqp.
              * right.
                destruct (Htailin ip0) as [_ Hback].
                apply Hback.
                exists n. exists p2. exists p0.
                split; [exact Hsrcnth|].
                split.
                -- unfold PolyLang.scanned.
                   rewrite Hscan2.
                   rewrite Nat.eqb_refl, Heqp. simpl. reflexivity.
                -- exact Hip.
            + right.
              destruct (Htailin ip0) as [_ Hback].
              apply Hback.
              exists n2. exists p2. exists pi2.
              split; [exact Hnth2|].
              split.
              * unfold PolyLang.scanned.
                rewrite Hscan2.
                rewrite Nat.eqb_sym.
                apply Nat.eqb_neq in Hnn.
                rewrite Hnn.
                destruct (is_eq p p2); simpl; reflexivity.
              * exact Hip.
        }
Qed.

Theorem prepare_codegen_preserves_ready_at:
  forall pol,
    PolyLang.wf_pprog_affine pol ->
    codegen_ready_pprog_at (codegen_target_dim pol) (prepare_codegen pol).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [Hctxt Hwfpis].
  unfold codegen_ready_pprog_at, prepare_codegen, codegen_target_dim; simpl.
  split.
  - eapply Nat.le_trans.
    + exact Hctxt.
    + apply Nat.le_max_l.
  - intros pi Hin.
    apply in_map_iff in Hin.
    destruct Hin as [pi0 [Hpi Hin0]].
    subst pi.
    pose proof (Hwfpis pi0 Hin0) as Hwfpi.
    unfold PolyLang.wf_pinstr_affine in Hwfpi.
    destruct Hwfpi as [Hwfpi _].
    unfold PolyLang.wf_pinstr in Hwfpi.
    destruct Hwfpi as
        [Hwit_cur
         [Hcur_le
          [Hpoly_nrl
           [Hsched_nrl
            [Hpoly_exact
             [Htf_exact
              [Hacc_tf_exact
               [Hsched_exact [Hwacc Hracc]]]]]]]]].
    unfold codegen_ready_pi, prepare_pi, encode_depth_in_domain, depth_tail_zero; simpl.
    repeat split.
    + eapply Nat.le_trans.
      * exact Hcur_le.
      * eapply Nat.le_trans.
        -- eapply PolyLang.pprog_current_dim_ge_pinstr; exact Hin0.
        -- apply Nat.le_max_r.
    + eapply exact_listzzs_cols_app;
        [apply resize_affine_list_exact_cols | apply resize_affine_list_exact_cols].
    + apply resize_affine_list_exact_cols.
    + apply resize_affine_list_exact_cols.
    + apply resize_access_list_exact_cols.
    + apply resize_access_list_exact_cols.
    + intros p Hinpoly.
      assert (Hsrc_cols_le :
                (length varctxt + PolyLang.pi_depth pi0
                 <= Nat.max (length vars)
                      (PolyLang.pprog_current_dim (pis, varctxt, vars)))%nat).
      {
        eapply Nat.le_trans.
        - exact Hcur_le.
        - eapply Nat.le_trans.
          + eapply PolyLang.pprog_current_dim_ge_pinstr; exact Hin0.
          + apply Nat.le_max_r.
      }
      pose proof
        (encode_depth_in_domain_in_poly
           (length varctxt)
           (Nat.max (length vars)
              (PolyLang.pprog_current_dim (pis, varctxt, vars)))
           pi0 p Hpoly_exact Hsrc_cols_le Hinpoly)
        as [_ Htail].
      exact Htail.
Qed.

Lemma codegen_ready_pprog_implies_pprog_current_dim_eq_target :
  forall pp,
    codegen_ready_pprog pp ->
    PolyLang.pprog_current_dim pp = codegen_target_dim pp.
Proof.
  intros [[pis varctxt] vars] _.
  unfold codegen_ready_pprog, codegen_target_dim, PolyLang.pprog_current_dim.
  symmetry.
  apply Nat.max_r.
  apply PolyLang.fold_left_max_ge_init.
Qed.

Lemma wf_pinstr_affine_implies_pinstr_current_dim_eq_source_cols :
  forall env vars pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    PolyLang.pinstr_current_dim env pi = source_cols env pi.
Proof.
  intros env vars pi Hwf.
  unfold PolyLang.wf_pinstr_affine in Hwf.
  destruct Hwf as [Hwf _].
  unfold PolyLang.wf_pinstr in Hwf.
  destruct Hwf as
      [Hwit_cur
       [Hcols_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hwacc Hracc]]]]]]]]].
  pose proof (exact_listzzs_cols_implies_poly_nrl_le _ _ Hpoly_exact) as Hpoly_src.
  pose proof (exact_listzzs_cols_implies_poly_nrl_le _ _ Hsched_exact) as Hsched_src.
  unfold PolyLang.pinstr_current_dim, source_cols.
  simpl in *.
  rewrite Nat.max_l.
  - reflexivity.
  - apply Nat.max_lub; assumption.
Qed.

Lemma prepare_pi_pinstr_current_dim_ge_source_cols :
  forall env cols pi,
    source_cols env pi <= PolyLang.pinstr_current_dim env (prepare_pi (length env) cols pi).
Proof.
  intros env cols pi.
  unfold PolyLang.pinstr_current_dim, source_cols, prepare_pi.
  simpl.
  apply Nat.le_max_l.
Qed.

Lemma prepare_codegen_current_dim_ge_original :
  forall pol,
    PolyLang.wf_pprog_affine pol ->
    PolyLang.pprog_current_dim pol <= PolyLang.pprog_current_dim (prepare_codegen pol).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold PolyLang.pprog_current_dim, prepare_codegen, codegen_target_dim.
  simpl.
  apply fold_left_max_le_bound.
  - apply PolyLang.fold_left_max_ge_init.
  - apply Forall_forall.
    intros d Hin.
    apply in_map_iff in Hin.
    destruct Hin as [pi [Hd Hinpi]].
    subst d.
    unfold PolyLang.wf_pprog_affine in Hwf.
    destruct Hwf as [_ Hwfpis].
    pose proof (Hwfpis pi Hinpi) as Hwfpi.
    rewrite (wf_pinstr_affine_implies_pinstr_current_dim_eq_source_cols _ _ _ Hwfpi).
    eapply Nat.le_trans.
    + apply prepare_pi_pinstr_current_dim_ge_source_cols.
    + eapply PolyLang.pprog_current_dim_ge_pinstr.
      apply in_map.
      exact Hinpi.
Qed.

Lemma prepare_codegen_current_dim_le_target :
  forall pol,
    PolyLang.wf_pprog_affine pol ->
    PolyLang.pprog_current_dim (prepare_codegen pol) <= codegen_target_dim pol.
Proof.
  intros [[pis varctxt] vars] Hwf.
  pose proof (prepare_codegen_preserves_ready_at ((pis, varctxt), vars) Hwf) as Hready.
  unfold PolyLang.pprog_current_dim, prepare_codegen, codegen_target_dim in *.
  simpl in *.
  destruct Hready as [_ Hready].
  apply fold_left_max_le_bound.
  - apply Nat.le_max_l.
  - apply Forall_forall.
    intros d Hin.
    apply in_map_iff in Hin.
    destruct Hin as [pi [Hd Hinpi]].
    subst d.
    specialize (Hready pi Hinpi).
    destruct Hready as
        [Hsrc_cols_le
         [Hpoly_exact
          [Hsched_exact
           [_ [_ [_ _]]]]]].
    unfold PolyLang.pinstr_current_dim, prepare_pi.
    simpl.
    pose proof (exact_listzzs_cols_implies_poly_nrl_le _ _ Hpoly_exact) as Hpoly_nrl.
    pose proof (exact_listzzs_cols_implies_poly_nrl_le _ _ Hsched_exact) as Hsched_nrl.
    apply Nat.max_lub.
    + exact Hsrc_cols_le.
    + apply Nat.max_lub; assumption.
Qed.

Lemma prepare_codegen_target_dim_preserved :
  forall pol,
    PolyLang.wf_pprog_affine pol ->
    codegen_target_dim (prepare_codegen pol) = codegen_target_dim pol.
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold codegen_target_dim.
  simpl.
  pose proof (prepare_codegen_current_dim_ge_original ((pis, varctxt), vars) Hwf) as Hge.
  pose proof (prepare_codegen_current_dim_le_target ((pis, varctxt), vars) Hwf) as Hle.
  apply Nat.le_antisymm.
  - apply Nat.max_lub.
    + apply Nat.le_max_l.
    + exact Hle.
  - apply Nat.max_lub.
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * exact Hge.
      * apply Nat.le_max_r.
Qed.

Theorem prepare_codegen_preserves_wf_at:
  forall pol,
    PolyLang.wf_pprog_affine pol ->
    codegen_wf_pprog_at (codegen_target_dim pol) (prepare_codegen pol).
Proof.
  intros pol Hwf.
  pose proof (prepare_codegen_preserves_ready_at pol Hwf) as Hready.
  destruct pol as [[pis varctxt] vars].
  unfold codegen_ready_pprog_at, codegen_wf_pprog_at, prepare_codegen, codegen_target_dim in *.
  simpl in *.
  destruct Hready as [Hctxt Hready].
  repeat split.
  - exact Hctxt.
  - unfold ASTGen.pis_have_dimension.
    rewrite forallb_forall.
    intros pi Hin.
    specialize (Hready pi Hin).
    destruct Hready as [_ [Hpoly_exact _]].
    apply Nat.leb_le.
    eapply exact_listzzs_cols_implies_poly_nrl_le; eauto.
  - intros pi Hin.
    specialize (Hready pi Hin).
    destruct Hready as [_ [_ [Hsched_exact _]]].
    eapply exact_listzzs_cols_implies_poly_nrl_le; eauto.
Qed.

Lemma encode_depth_in_domain_from_source:
  forall env_dim cols pi p,
    exact_listzzs_cols (env_dim + pi.(PolyLang.pi_depth)) pi.(PolyLang.pi_poly) ->
    (env_dim + pi.(PolyLang.pi_depth) <= cols)%nat ->
    length p = env_dim + pi.(PolyLang.pi_depth) ->
    in_poly p pi.(PolyLang.pi_poly) = true ->
    in_poly p (encode_depth_in_domain env_dim cols pi) = true.
Proof.
  intros env_dim cols pi p Hpoly_exact Hsrcle Hplen Hsrcdom.
  unfold encode_depth_in_domain.
  assert (Hexact :
    exact_listzzs_cols cols
      (resize_affine_list cols pi.(PolyLang.pi_poly) ++
       resize_affine_list cols
         (PolyLang.make_null_poly (env_dim + pi.(PolyLang.pi_depth))
                                  (cols - (env_dim + pi.(PolyLang.pi_depth)))))).
  {
    apply exact_listzzs_cols_app.
    - apply resize_affine_list_exact_cols.
    - apply resize_affine_list_exact_cols.
  }
  pose proof (exact_listzzs_cols_implies_poly_nrl_le _ _ Hexact) as Hnrl.
  rewrite <- (in_poly_nrlength p _ cols Hnrl).
  unfold in_poly.
  rewrite forallb_app.
  apply andb_true_intro.
  split.
  - change (in_poly (resize cols p) (resize_affine_list cols pi.(PolyLang.pi_poly)) = true).
    rewrite resize_affine_list_in_poly by (rewrite resize_length; reflexivity).
    rewrite <- (in_poly_nrlength (resize cols p) pi.(PolyLang.pi_poly)
                                 (env_dim + pi.(PolyLang.pi_depth))).
    + rewrite resize_resize by exact Hsrcle.
      rewrite resize_length_eq by exact Hplen.
      exact Hsrcdom.
    + eapply exact_listzzs_cols_implies_poly_nrl_le; eauto.
  - change
      (in_poly (resize cols p)
         (resize_affine_list cols
            (PolyLang.make_null_poly (env_dim + pi.(PolyLang.pi_depth))
                                     (cols - (env_dim + pi.(PolyLang.pi_depth))))) = true).
    rewrite resize_affine_list_in_poly by (rewrite resize_length; reflexivity).
    replace (resize cols p)
      with (p ++ resize (cols - (env_dim + pi.(PolyLang.pi_depth))) nil).
    + replace (p ++ resize (cols - (env_dim + pi.(PolyLang.pi_depth))) nil)
        with (p ++ resize (cols - (env_dim + pi.(PolyLang.pi_depth))) nil ++ nil)
        by now rewrite app_nil_r.
      rewrite PolyLang.make_null_poly_correct with
        (p := p)
        (q := resize (cols - (env_dim + pi.(PolyLang.pi_depth))) nil)
        (r := nil).
      * autorewrite with vector. reflexivity.
      * exact Hplen.
      * rewrite resize_length. reflexivity.
    + replace (resize cols p) with (resize cols (p ++ nil)).
      2:{ now rewrite app_nil_r. }
      rewrite resize_app_le by (rewrite Hplen; exact Hsrcle).
      replace (cols - length p)%nat with (cols - (env_dim + pi.(PolyLang.pi_depth)))%nat by lia.
      reflexivity.
Qed.

Lemma source_ip_props_imply_prepare_env_scan_true:
  forall pis varctxt vars cols envv n pi ip,
    PolyLang.wf_pprog_affine (pis, varctxt, vars) ->
    (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat ->
    length envv = length varctxt ->
    nth_error pis n = Some pi ->
    firstn (length varctxt) (PolyLang.ip_index ip) = envv ->
    PolyLang.belongs_to ip pi ->
    length (PolyLang.ip_index ip) = length varctxt + pi.(PolyLang.pi_depth) ->
    PolyLang.env_scan
      (map (prepare_pi (length varctxt) cols) pis)
      envv cols n (PolyLang.ip_index ip) = true.
Proof.
  intros pis varctxt vars cols envv n pi ip Hwf Hdim_cols Henvlen Hnth Hpref Hbel Hlen.
  pose proof Hwf as Hwf_affine.
  unfold PolyLang.env_scan.
  rewrite map_nth_error with (d := pi); [| exact Hnth].
  simpl.
  unfold PolyLang.wf_pprog_affine in Hwf.
  destruct Hwf as [_ Hwfpis].
  pose proof (Hwfpis pi (nth_error_In _ _ Hnth)) as Hwfpi.
  pose proof
    (wf_pprog_affine_implies_source_cols_le
       pis varctxt vars cols pi Hwf_affine Hdim_cols (nth_error_In _ _ Hnth))
    as Hsrc_cols_le.
  unfold PolyLang.wf_pinstr_affine in Hwfpi.
  destruct Hwfpi as [Hwfpi _].
  unfold PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as
      [Hwit_cur
       [Hcur_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hwacc Hracc]]]]]]]]].
  destruct Hbel as [Hpoly _].
  apply andb_true_intro.
  split.
  {
    apply andb_true_intro.
    split.
    {
      assert (Hresize_pref :
        resize (length varctxt) (PolyLang.ip_index ip) = envv).
      {
        rewrite <- Hpref.
        rewrite <- (resize_length_eq (length varctxt + pi.(PolyLang.pi_depth))
                     (PolyLang.ip_index ip) Hlen) at 2.
        symmetry.
        apply firstn_resize.
        lia.
      }
      rewrite Henvlen.
      rewrite is_eq_commutative.
      rewrite Hresize_pref.
      apply is_eq_reflexive.
    }
    {
      rewrite is_eq_commutative.
      rewrite is_eq_veq.
      apply resize_eq.
      rewrite Hlen.
      exact Hsrc_cols_le.
    }
  }
  {
    eapply encode_depth_in_domain_from_source; eauto.
  }
Qed.

Lemma source_ip_of_self :
  forall env_dim n pi ip,
    PolyLang.ip_nth ip = n ->
    PolyLang.belongs_to ip pi ->
    length (PolyLang.ip_index ip) = env_dim + pi.(PolyLang.pi_depth) ->
    source_ip_of env_dim n pi (PolyLang.ip_index ip) = ip.
Proof.
  intros env_dim n pi [nth idx tf ts instr depth] Hnth Hbel Hlen.
  unfold PolyLang.belongs_to in Hbel.
  simpl in *.
  destruct Hbel as [Hpoly [Htf [Hts [Hinstr Hdepth]]]].
  subst nth instr depth.
  unfold source_ip_of. simpl.
  f_equal.
  - apply resize_length_eq. exact Hlen.
  - rewrite resize_length_eq by exact Hlen.
    symmetry. exact Htf.
  - rewrite resize_length_eq by exact Hlen.
    symmetry. exact Hts.
Qed.

Lemma source_like_points_imply_NoDupA_np :
  forall (pis: list PolyLang.PolyInstr)
         (varctxt: list PolyLang.ident)
         (envv: list Z)
         (ipl: list PolyLang.InstrPoint),
    (forall ip,
      In ip ipl ->
      exists n pi,
        nth_error pis n = Some pi /\
        firstn (length varctxt) (PolyLang.ip_index ip) = envv /\
        PolyLang.belongs_to ip pi /\
        PolyLang.ip_nth ip = n /\
        length (PolyLang.ip_index ip) = length varctxt + pi.(PolyLang.pi_depth)) ->
    NoDup ipl ->
    NoDupA PolyLang.np_eq ipl.
Proof.
  induction ipl as [|ip ipl IH]; intros Hmem Hnodup.
  - constructor.
  - constructor.
    + intro HinA.
      inversion Hnodup as [|? ? Hnotin Htailnodup]; subst.
      apply InA_alt in HinA.
      destruct HinA as [ip' [Hnpeq Hin]].
      destruct (Hmem ip ltac:(left; reflexivity))
        as [n [pi [Hnth [_ [Hbel [Hn Hlen]]]]]].
      destruct (Hmem ip' ltac:(right; exact Hin))
        as [n' [pi' [Hnth' [_ [Hbel' [Hn' Hlen']]]]]].
      unfold PolyLang.np_eq in Hnpeq.
      destruct Hnpeq as [Hnn Hidxcmp].
      rewrite Hn in Hnn.
      rewrite Hn' in Hnn.
      subst n'.
      assert (Hpi : pi = pi') by congruence.
      subst pi'.
      assert (Hidxeq :
        is_eq (PolyLang.ip_index ip) (PolyLang.ip_index ip') = true).
      {
        apply lex_compare_eq_is_eq.
        exact Hidxcmp.
      }
      pose proof (source_ip_of_self (length varctxt) n pi ip Hn Hbel Hlen) as Hip.
      pose proof (source_ip_of_self (length varctxt) n pi ip' Hn' Hbel' Hlen') as Hip'.
      assert (Hsrc :
        source_ip_of (length varctxt) n pi (PolyLang.ip_index ip) =
        source_ip_of (length varctxt) n pi (PolyLang.ip_index ip')).
      {
        apply source_ip_of_eq_from_is_eq.
        exact Hidxeq.
      }
      rewrite Hip in Hsrc.
      rewrite Hip' in Hsrc.
      subst ip'.
      contradiction.
    + apply IH.
      * intros ip' Hin.
        apply Hmem.
        right. exact Hin.
      * inversion Hnodup; subst; assumption.
Qed.

Theorem prepare_codegen_semantics_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    PolyLang.semantics (prepare_codegen pol) st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros [[pis varctxt] vars] st st' Hwf Hsem.
  pose proof (prepare_codegen_preserves_ready_at (pis, varctxt, vars) Hwf) as Hready.
  pose proof
    (prepare_codegen_target_dim_preserved ((pis, varctxt), vars) Hwf)
    as Hprepdim.
  assert (Hready' : codegen_ready_pprog (prepare_codegen (pis, varctxt, vars))).
  {
    unfold codegen_ready_pprog.
    rewrite Hprepdim.
    exact Hready.
  }
  pose proof
    (codegen_ready_pprog_implies_pprog_current_dim_eq_target
       (prepare_codegen (pis, varctxt, vars)) Hready')
    as Hprepcurdim.
  inversion Hsem as
      [pprog prep_pis varctxt' vars' envv st1 st2
         Hpprog Hcompat Hnalias Hinit Henvsem];
    subst.
  simpl in Hpprog.
  inversion Hpprog; subst prep_pis varctxt' vars'; clear Hpprog.
  rewrite Hprepcurdim in Henvsem.
  rewrite Hprepdim in Henvsem.
  pose proof (Instr.init_env_samelen varctxt envv st Hinit) as Henvlen.
  unfold PolyLang.env_poly_semantics in Henvsem.
  pose proof
    (wf_pprog_affine_implies_pprog_current_dim_le_target
       pis varctxt vars Hwf)
    as Hcurdim.
  set (cols := codegen_target_dim (pis, varctxt, vars)).
  assert (Hdim_cols :
            (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat).
  {
    exact Hcurdim.
  }
  destruct
    (prepare_poly_semantics_collect
       pis varctxt vars cols envv
       (PolyLang.env_scan
          (map (prepare_pi (length varctxt) cols) pis)
          envv cols)
       st st'
       Hwf Hdim_cols
       (eq_sym Henvlen) Henvsem (fun _ _ H => H))
    as [exec_ipl [Hexec_sem [Hexec_sched [Hexec_nodup Hexec_char]]]].
  set (ipl := SelectionSort np_ltb np_eqb exec_ipl).
  assert (Hsort :
    Permutation exec_ipl ipl /\
    Sorted_b (combine_leb np_ltb np_eqb) ipl).
  {
    unfold ipl.
    eapply selection_sort_np_is_correct.
    reflexivity.
  }
  destruct Hsort as [Hperm_exec Hsortedb].
  assert (Hipl_nodup : NoDup ipl).
  {
    eapply Permutation_NoDup; eauto.
  }
  assert (Hipl_source :
    forall ip,
      In ip ipl ->
      exists n pi,
        nth_error pis n = Some pi /\
        firstn (length varctxt) (PolyLang.ip_index ip) = envv /\
        PolyLang.belongs_to ip pi /\
        PolyLang.ip_nth ip = n /\
        length (PolyLang.ip_index ip) = length varctxt + pi.(PolyLang.pi_depth)).
  {
    intros ip Hin.
    assert (Hin_exec : In ip exec_ipl).
    {
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm_exec.
      - exact Hin.
    }
    destruct (Hexec_char ip) as [Hchar_forw _].
    destruct (Hchar_forw Hin_exec) as [n0 [p [pi [Hnth [Hscan Hip]]]]].
    subst ip.
    assert (Hprops :
      let env_dim := length varctxt in
      let src_cols := env_dim + pi.(PolyLang.pi_depth) in
      let ip0 := source_ip_of env_dim n0 pi p in
      firstn env_dim ip0.(PolyLang.ip_index) = envv /\
      PolyLang.belongs_to ip0 pi /\
      length ip0.(PolyLang.ip_index) = src_cols /\
      is_eq p (resize cols p) = true /\
      is_null (skipn src_cols (resize cols p)) = true).
    {
      refine
        (prepare_env_scan_true_implies_source_ip_props
           pis varctxt vars cols envv n0 p pi _ _ _ _ _).
      - exact Hwf.
      - exact Hdim_cols.
      - exact (eq_sym Henvlen).
      - exact Hnth.
      - exact Hscan.
    }
    destruct Hprops as [Hpref [Hbel [Hlen [_ _]]]].
    exists n0.
    exists pi.
    split; [exact Hnth|].
    split; [exact Hpref|].
    split; [exact Hbel|].
    split.
    - apply source_ip_of_nth.
    - exact Hlen.
  }
  assert (Hipl_nodupa : NoDupA PolyLang.np_eq ipl).
  {
    eapply source_like_points_imply_NoDupA_np; eauto.
  }
  assert (Hipl_sorted : Sorted PolyLang.np_lt ipl).
  {
    eapply sortedb_np_nodup_implies_sorted_np; eauto.
  }
  assert (Hflat : PolyLang.flatten_instrs envv pis ipl).
  {
    split.
    - intros ip Hin.
      destruct (Hipl_source ip Hin)
        as [n [pi [Hnth [Hpref [Hbel [Hn Hlen]]]]]].
      rewrite <- Henvlen.
      exact Hpref.
    - split.
      + intros ip.
        split.
        * intros Hin.
          destruct (Hipl_source ip Hin)
            as [n [pi [Hnth [Hpref [Hbel [Hn Hlen]]]]]].
          exists pi.
          rewrite Hn.
          split; [exact Hnth|].
          split.
          { rewrite <- Henvlen. exact Hpref. }
          split.
          { exact Hbel. }
          { rewrite <- Henvlen. exact Hlen. }
        * intros [pi [Hnth [Hpref [Hbel Hlen]]]].
          rewrite <- Henvlen in Hpref.
          rewrite <- Henvlen in Hlen.
          assert (Hscan :
            PolyLang.env_scan
              (map (prepare_pi (length varctxt) cols) pis)
              envv cols (PolyLang.ip_nth ip) (PolyLang.ip_index ip) = true).
          {
            eapply source_ip_props_imply_prepare_env_scan_true; eauto.
          }
          assert (Hin_exec : In ip exec_ipl).
          {
            destruct (Hexec_char ip) as [_ Hchar_back].
            apply Hchar_back.
            exists ip.(PolyLang.ip_nth).
            exists ip.(PolyLang.ip_index).
            exists pi.
            split; [exact Hnth|].
            split; [exact Hscan|].
            symmetry.
            eapply source_ip_of_self; eauto.
          }
          eapply Permutation_in.
          { exact Hperm_exec. }
          { exact Hin_exec. }
      + split.
        * exact Hipl_nodup.
        * exact Hipl_sorted.
  }
  eapply PolyLang.PIPSemaIntro with (envv := envv); eauto.
  eapply PolyLang.PolyPointListSema with (ipl := ipl) (sorted_ipl := exec_ipl).
  - reflexivity.
  - exact Hflat.
  - apply Permutation_sym. exact Hperm_exec.
  - exact Hexec_sched.
  - exact Hexec_sem.
Qed.

Definition prepared_codegen (pol: PolyLang.t) : imp Loop.t :=
  BIND loop <- CodeGen.codegen (prepare_codegen pol) -;
  pure (Cleanup.cleanup loop).

Theorem prepared_codegen_correct:
  forall pol st st',
    WHEN loop <- prepared_codegen pol THEN
    PolyLang.wf_pprog_affine pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros [[pis varctxt] vars] st st' loop Hcodegen Hwf Hloop.
  pose proof (prepare_codegen_preserves_ready_at (pis, varctxt, vars) Hwf) as Hready.
  pose proof
    (prepare_codegen_target_dim_preserved ((pis, varctxt), vars) Hwf)
    as Hprepdim.
  assert (Hready' : codegen_ready_pprog (prepare_codegen (pis, varctxt, vars))).
  {
    unfold codegen_ready_pprog.
    rewrite Hprepdim.
    exact Hready.
  }
  pose proof
    (codegen_ready_pprog_implies_pprog_current_dim_eq_target
       (prepare_codegen (pis, varctxt, vars)) Hready')
    as Hprepcurdim.
  pose proof (prepare_codegen_preserves_wf_at ((pis, varctxt), vars) Hwf) as Hcgwf.
  destruct Hcgwf as [Hctxt [Hdim Hsched]].
  set (es := length varctxt).
  set (n := codegen_target_dim (pis, varctxt, vars)).
  set (prep_pis := map (prepare_pi es n) pis).
  unfold prepared_codegen in Hcodegen.
  bind_imp_destruct Hcodegen loop_raw Hcodegen_raw.
  eapply mayReturn_pure in Hcodegen. subst loop.
  pose proof ((proj1 (Cleanup.cleanup_correct loop_raw st st')) Hloop) as Hloop_raw.
  unfold CodeGen.codegen in Hcodegen_raw. simpl in Hcodegen_raw.
  bind_imp_destruct Hcodegen_raw loop_stmt Hgen.
  eapply mayReturn_pure in Hcodegen_raw. subst loop_raw.
  inversion Hloop_raw. rename env into envv.
  inversion H; subst.
  assert (Hctxt' : (es <= n)%nat).
  { subst es n. exact Hctxt. }
  assert (Hdim' : ASTGen.pis_have_dimension prep_pis n).
  { subst prep_pis es n. exact Hdim. }
  assert (Hsched' : forall pi, In pi prep_pis -> (poly_nrl pi.(PolyLang.pi_schedule) <= n)%nat).
  { subst prep_pis es n. exact Hsched. }
  assert (Henvdim' :
    forall pi, In pi prep_pis ->
      PolyLang.current_env_dim_in_dim n pi.(PolyLang.pi_point_witness) = es).
  {
    intros pi Hin.
    pose proof Hwf as Hwf_affine.
    unfold prep_pis, es, n in *.
    apply in_map_iff in Hin.
    destruct Hin as [pi0 [Hpi Hin0]].
    subst pi.
    unfold PolyLang.wf_pprog_affine in Hwf_affine.
    destruct Hwf_affine as [_ Hwfpis].
    pose proof (Hwfpis pi0 Hin0) as Hwfpi.
    unfold PolyLang.wf_pinstr_affine in Hwfpi.
    destruct Hwfpi as [Hwfpi [Hwit _]].
    unfold PolyLang.wf_pinstr in Hwfpi.
    destruct Hwfpi as
      [Hwit_cur
       [Hcur_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hwacc Hracc]]]]]]]]].
    pose proof
      (wf_pprog_affine_implies_source_cols_le
         _ _ _ _ _
         Hwf
         (wf_pprog_affine_implies_pprog_current_dim_le_target _ _ _ Hwf)
         Hin0)
      as Hsrc_cols_le.
    apply prepare_pi_current_env_dim_in_dim_affine.
    exact Hsrc_cols_le.
    exact Hwit.
  }
  change
    (mayReturn
       (CodeGen.complete_generate_many
          es
          (codegen_target_dim (prepare_codegen (pis, ctxt, vars0)))
          prep_pis) loop) in Hgen.
  pose proof Hctxt' as Hctxt_gen.
  unfold n in Hctxt_gen.
  rewrite <- Hprepdim in Hctxt_gen.
  pose proof Hdim' as Hdim_gen.
  unfold n in Hdim_gen.
  rewrite <- Hprepdim in Hdim_gen.
  pose proof Hsched' as Hsched_gen.
  unfold n in Hsched_gen.
  rewrite <- Hprepdim in Hsched_gen.
  pose proof Henvdim' as Henvdim_gen.
  unfold n in Henvdim_gen.
  rewrite <- Hprepdim in Henvdim_gen.
  pose proof (CodeGen.complete_generate_many_preserve_sem
 	        es (codegen_target_dim (prepare_codegen (pis, ctxt, vars0)))
                prep_pis envv st st' Hctxt_gen loop Hgen H3) as Hpoly.
  eapply prepare_codegen_semantics_correct.
  - exact Hwf.
  - econstructor.
    + reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + rewrite Hprepcurdim.
      unfold prepare_codegen, prep_pis, es, n.
      simpl.
      change
        (CodeGen.PolyLang.env_poly_semantics
           (rev envv)
           (codegen_target_dim (prepare_codegen (pis, ctxt, vars0)))
           (map
              (prepare_pi (length ctxt)
                 (codegen_target_dim (pis, ctxt, vars0))) pis) st st').
      eapply Hpoly.
      * symmetry.
        eapply Instr.init_env_samelen with (envv := rev envv) in H2.
        rewrite rev_length in H2. exact H2.
      * exact Hdim_gen.
      * exact Henvdim_gen.
      * exact Hsched_gen.
Qed.

Theorem prepared_codegen_correct_general:
  forall pol st st',
    WHEN loop <- prepared_codegen (PolyLang.current_view_pprog pol) THEN
    PolyLang.wf_pprog_general pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros pol st st' loop Hcodegen Hwf Hloop.
  pose proof
    (PolyLang.wf_pprog_general_current_view_affine pol Hwf)
    as Hwf_cur.
  pose proof
    (prepared_codegen_correct
       (PolyLang.current_view_pprog pol) st st' loop
       Hcodegen Hwf_cur Hloop)
    as Hsem_cur.
  pose proof
    (PolyLang.instance_list_semantics_current_view_iff pol st st' Hwf)
    as Hview.
  apply (proj1 Hview).
  exact Hsem_cur.
Qed.

End PrepareCodegen.
