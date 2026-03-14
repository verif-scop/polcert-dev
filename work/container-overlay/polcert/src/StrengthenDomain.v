Require Import Bool.
Require Import List.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Require Import Base.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import Linalg.
Require Import PolIRs.
Require Import LibTactics.
Require Import sflib.

Module StrengthenDomain (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.

Definition env_dim_of (pp: PolyLang.t) : nat :=
  let '(_, varctxt, _) := pp in
  length varctxt.

Definition is_prefix_only_constraint (prefix_len: nat) (c: constraint) : bool :=
  is_null (skipn prefix_len (fst c)).

Definition strengthen_prefix_len (env_dim depth: nat) : nat :=
  env_dim + Nat.pred depth.

Definition nth_or_zero (n: nat) (xs: list Z) : Z :=
  nth n xs 0%Z.

Definition cancels_current_iter (iter_idx: nat) (c1 c2: constraint) : bool :=
  let z1 := nth_or_zero iter_idx (fst c1) in
  let z2 := nth_or_zero iter_idx (fst c2) in
  negb (Z.eqb z1 0) &&
  negb (Z.eqb z2 0) &&
  Z.eqb (z1 + z2) 0.

Fixpoint guards_from_constraint
    (iter_idx prefix_len: nat) (c: constraint) (pol: Domain) : Domain :=
  match pol with
  | [] => []
  | c' :: pol' =>
      let guard := add_constraint c c' in
      let guards := guards_from_constraint iter_idx prefix_len c pol' in
      if cancels_current_iter iter_idx c c' &&
         is_prefix_only_constraint prefix_len guard
      then guard :: guards
      else guards
  end.

Fixpoint inferred_prefix_guards (iter_idx prefix_len: nat) (pol: Domain) : Domain :=
  match pol with
  | [] => []
  | c :: pol' =>
      guards_from_constraint iter_idx prefix_len c pol' ++
      inferred_prefix_guards iter_idx prefix_len pol'
  end.

Definition strengthen_domain (depth env_dim: nat) (pol: Domain) : Domain :=
  match depth with
  | O => pol
  | S depth' =>
      let prefix_len := env_dim + depth' in
      let iter_idx := prefix_len in
      pol ++ inferred_prefix_guards iter_idx prefix_len pol
  end.

Definition strengthen_pi (env_dim: nat) (pi: PolyLang.PolyInstr)
  : PolyLang.PolyInstr :=
  {|
    PolyLang.pi_depth := pi.(PolyLang.pi_depth);
    PolyLang.pi_instr := pi.(PolyLang.pi_instr);
    PolyLang.pi_poly := strengthen_domain pi.(PolyLang.pi_depth) env_dim pi.(PolyLang.pi_poly);
    PolyLang.pi_schedule := pi.(PolyLang.pi_schedule);
    PolyLang.pi_point_witness := pi.(PolyLang.pi_point_witness);
    PolyLang.pi_transformation := pi.(PolyLang.pi_transformation);
    PolyLang.pi_access_transformation := pi.(PolyLang.pi_access_transformation);
    PolyLang.pi_waccess := pi.(PolyLang.pi_waccess);
    PolyLang.pi_raccess := pi.(PolyLang.pi_raccess);
  |}.

Definition strengthen_pprog (pp: PolyLang.t) : PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  (map (strengthen_pi (length varctxt)) pis, varctxt, vars).

Lemma guards_from_constraint_satisfied:
  forall iter_idx prefix_len p c pol,
    satisfies_constraint p c = true ->
    in_poly p pol = true ->
    in_poly p (guards_from_constraint iter_idx prefix_len c pol) = true.
Proof.
  intros iter_idx prefix_len p c pol Hc.
  induction pol as [|c' pol IH]; intros Hpol; simpl.
  - reflexivity.
  - unfold in_poly in Hpol. simpl in Hpol.
    apply andb_true_iff in Hpol.
    destruct Hpol as [Hc' Hpol].
    specialize (IH Hpol).
    destruct (cancels_current_iter iter_idx c c' &&
              is_prefix_only_constraint prefix_len (add_constraint c c')) eqn:Hkeep;
      simpl; auto.
    rewrite IH.
    apply andb_true_iff.
    split; auto.
    eapply add_constraint_satisfy; eauto.
Qed.

Lemma inferred_prefix_guards_satisfied:
  forall iter_idx prefix_len p pol,
    in_poly p pol = true ->
    in_poly p (inferred_prefix_guards iter_idx prefix_len pol) = true.
Proof.
  intros iter_idx prefix_len p pol.
  induction pol as [|c pol IH]; intros Hpol; simpl.
  - reflexivity.
  - unfold in_poly in Hpol. simpl in Hpol.
    apply andb_true_iff in Hpol.
    destruct Hpol as [Hc Hpol].
    rewrite in_poly_app.
    rewrite guards_from_constraint_satisfied with (iter_idx := iter_idx) (c := c); auto.
Qed.

Lemma strengthen_domain_in_poly:
  forall depth env_dim p pol,
    in_poly p (strengthen_domain depth env_dim pol) = in_poly p pol.
Proof.
  intros depth env_dim p pol.
  unfold strengthen_domain.
  destruct depth as [|depth']; simpl.
  - reflexivity.
  - rewrite in_poly_app.
    destruct (in_poly p pol) eqn:Hpol; simpl; auto.
    rewrite inferred_prefix_guards_satisfied
      with (iter_idx := env_dim + depth') (prefix_len := env_dim + depth') by exact Hpol.
    reflexivity.
Qed.

Lemma strengthen_pi_in_poly:
  forall env_dim pi p,
    in_poly p (strengthen_pi env_dim pi).(PolyLang.pi_poly) =
    in_poly p pi.(PolyLang.pi_poly).
Proof.
  intros. unfold strengthen_pi. simpl.
  apply strengthen_domain_in_poly.
Qed.

Lemma strengthen_pi_belongs_to_iff:
  forall env_dim ip pi,
    PolyLang.belongs_to ip (strengthen_pi env_dim pi) <->
    PolyLang.belongs_to ip pi.
Proof.
  intros env_dim ip pi.
  unfold PolyLang.belongs_to.
  rewrite strengthen_pi_in_poly.
  tauto.
Qed.

Lemma add_vector_length_same:
  forall v1 v2 n,
    length v1 = n ->
    length v2 = n ->
    length (add_vector v1 v2) = n.
Proof.
  induction v1 as [|x v1 IH]; intros v2 n H1 H2.
  - destruct v2; simpl in *; lia.
  - destruct v2 as [|y v2]; simpl in *; [lia|].
    inversion H1; inversion H2; subst.
    simpl. f_equal. eapply IH; eauto.
Qed.

Lemma add_constraint_exact_cols:
  forall cols c1 c2,
    length (fst c1) = cols ->
    length (fst c2) = cols ->
    length (fst (add_constraint c1 c2)) = cols.
Proof.
  intros cols [v1 z1] [v2 z2] H1 H2. simpl.
  eapply add_vector_length_same; eauto.
Qed.

Lemma guards_from_constraint_exact_cols:
  forall iter_idx prefix_len cols c pol,
    length (fst c) = cols ->
    exact_listzzs_cols cols pol ->
    exact_listzzs_cols cols (guards_from_constraint iter_idx prefix_len c pol).
Proof.
  intros iter_idx prefix_len cols c pol Hc Hexact listz z listzz Hin Heq.
  induction pol as [|[v' z'] pol IH]; simpl in Hin.
  - contradiction.
  - destruct (cancels_current_iter iter_idx c (v', z') &&
              is_prefix_only_constraint prefix_len (add_constraint c (v', z'))) eqn:Hkeep.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst listzz.
        assert (Hc' : length v' = length (fst c)).
        {
          pose proof (Hexact v' z' (v', z') (or_introl eq_refl) eq_refl) as Hc''.
          lia.
        }
        inversion Heq; subst.
        eapply add_vector_length_same; eauto.
      * eapply IH; eauto.
        intros listz0 z0 listzz0 Hin0 Heq0.
          eapply Hexact; eauto. right; exact Hin0.
    + eapply IH; eauto.
      intros listz0 z0 listzz0 Hin0 Heq0.
      eapply Hexact; eauto. right; exact Hin0.
Qed.

Lemma inferred_prefix_guards_exact_cols:
  forall iter_idx prefix_len cols pol,
    exact_listzzs_cols cols pol ->
    exact_listzzs_cols cols (inferred_prefix_guards iter_idx prefix_len pol).
Proof.
  intros iter_idx prefix_len cols pol Hexact listz z listzz Hin Heq.
  induction pol as [|[v z0] pol IH]; simpl in Hin.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + assert (Hc : length v = cols).
      {
        pose proof (Hexact v z0 (v, z0) (or_introl eq_refl) eq_refl) as Hv.
        exact Hv.
      }
      eapply (guards_from_constraint_exact_cols iter_idx prefix_len cols (v, z0) pol).
      * exact Hc.
      * intros listz0 z1 listzz0 Hin0 Heq0.
        eapply Hexact; eauto. right; exact Hin0.
      * exact Hin.
      * exact Heq.
    + eapply IH.
      * intros listz0 z1 listzz0 Hin0 Heq0.
        eapply Hexact; eauto. right; exact Hin0.
      * exact Hin.
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
  rewrite <- Hcols.
  apply le_n.
Qed.

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

Lemma strengthen_pi_wf_pinstr:
  forall env vars pi,
    PolyLang.wf_pinstr env vars pi ->
    PolyLang.wf_pinstr env vars (strengthen_pi (length env) pi).
Proof.
  intros env vars pi Hwf.
  unfold PolyLang.wf_pinstr in *.
  unfold strengthen_pi. simpl.
  destruct Hwf as
      [Hwitdim
       [Hcols_le
        [Hpoly_nrl
         [Hsched_nrl
          [Hpoly_exact
           [Htf_exact
            [Hacc_tf_exact
             [Hsched_exact [Hw Hr]]]]]]]]].
  assert (Hpoly_exact' :
    exact_listzzs_cols (length env + PolyLang.pi_depth pi)
      (strengthen_domain (PolyLang.pi_depth pi) (length env) (PolyLang.pi_poly pi))).
  {
    unfold strengthen_domain.
    destruct (PolyLang.pi_depth pi) as [|depth'] eqn:Hdepth.
    - exact Hpoly_exact.
    - simpl.
      eapply exact_listzzs_cols_app.
      * exact Hpoly_exact.
      * eapply inferred_prefix_guards_exact_cols; eauto.
  }
  repeat split.
  - exact Hwitdim.
  - unfold PolyLang.pinstr_current_dim.
    apply Nat.le_max_l.
  - unfold PolyLang.pinstr_current_dim.
    eapply Nat.le_trans.
    + eapply exact_listzzs_cols_implies_poly_nrl_le; exact Hpoly_exact'.
    + apply Nat.le_max_l.
  - unfold PolyLang.pinstr_current_dim.
    eapply Nat.le_trans.
    + eapply exact_listzzs_cols_implies_poly_nrl_le; exact Hsched_exact.
    + apply Nat.le_max_l.
  - exact Hpoly_exact'.
  - exact Htf_exact.
  - exact Hacc_tf_exact.
  - exact Hsched_exact.
  - exact Hw.
  - exact Hr.
Qed.

Lemma strengthen_pi_wf_pinstr_affine:
  forall env vars pi,
    PolyLang.wf_pinstr_affine env vars pi ->
    PolyLang.wf_pinstr_affine env vars (strengthen_pi (length env) pi).
Proof.
  intros env vars pi Hwf.
  unfold PolyLang.wf_pinstr_affine in *.
  destruct Hwf as [Hwf [Hw Heq]].
  split.
  - eapply strengthen_pi_wf_pinstr; eauto.
  - unfold strengthen_pi. simpl. repeat split; assumption.
Qed.

Theorem strengthen_pprog_wf:
  forall pp,
    PolyLang.wf_pprog pp ->
    PolyLang.wf_pprog (strengthen_pprog pp).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold PolyLang.wf_pprog in *.
  simpl in *.
  destruct Hwf as [Hlen Hpis].
  split; [exact Hlen|].
  intros pi' Hin.
  apply in_map_iff in Hin.
  destruct Hin as [pi [Heq Hin]].
  subst pi'.
  eapply strengthen_pi_wf_pinstr.
  eapply Hpis; eauto.
Qed.

Theorem strengthen_pprog_wf_affine:
  forall pp,
    PolyLang.wf_pprog_affine pp ->
    PolyLang.wf_pprog_affine (strengthen_pprog pp).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold PolyLang.wf_pprog_affine in *.
  simpl in *.
  destruct Hwf as [Hlen Hpis].
  split; [exact Hlen|].
  intros pi' Hin.
  apply in_map_iff in Hin.
  destruct Hin as [pi [Heq Hin]].
  subst pi'.
  eapply strengthen_pi_wf_pinstr_affine.
  eapply Hpis; eauto.
Qed.

Lemma nth_error_strengthen_pprog:
  forall env_dim pis n pi,
    nth_error pis n = Some pi ->
    nth_error (map (strengthen_pi env_dim) pis) n =
    Some (strengthen_pi env_dim pi).
Proof.
  intros. rewrite map_nth_error with (d := pi); auto.
Qed.

Lemma nth_error_strengthen_pprog_inv:
  forall env_dim pis n pi',
    nth_error (map (strengthen_pi env_dim) pis) n = Some pi' ->
    exists pi,
      nth_error pis n = Some pi /\
      pi' = strengthen_pi env_dim pi.
Proof.
  intros env_dim pis n pi' Hnth.
  rewrite nth_error_map_iff in Hnth.
  destruct Hnth as [pi [Hnth Heq]].
  exists pi. split; auto.
Qed.

Lemma flatten_instrs_strengthen_iff:
  forall env_dim envv pis ipl,
    length envv = env_dim ->
    PolyLang.flatten_instrs envv (map (strengthen_pi env_dim) pis) ipl <->
    PolyLang.flatten_instrs envv pis ipl.
Proof.
  intros env_dim envv pis ipl Henv.
  unfold PolyLang.flatten_instrs.
  split; intros [Hpref [Hmem [Hnodup Hsorted]]].
  - split; [exact Hpref|].
    split.
    + intros ip0.
      specialize (Hmem ip0).
      split.
      * intro Hin.
        rewrite Hmem in Hin.
        destruct Hin as [pi' [Hnth [Hpref' [Hbel Hlen]]]].
        eapply nth_error_strengthen_pprog_inv in Hnth.
        destruct Hnth as [pi [Hnth Heq]].
        exists pi. subst pi'.
        split; [exact Hnth|].
        split; [exact Hpref'|].
        split; [exact (proj1 (strengthen_pi_belongs_to_iff env_dim ip0 pi) Hbel)|].
        exact Hlen.
      * intro Hin.
        rewrite Hmem.
        destruct Hin as [pi [Hnth [Hpref' [Hbel Hlen]]]].
        exists (strengthen_pi env_dim pi).
        split.
        -- eapply nth_error_strengthen_pprog; eauto.
        -- split; [exact Hpref'|].
           split; [exact (proj2 (strengthen_pi_belongs_to_iff env_dim ip0 pi) Hbel)|].
           exact Hlen.
    + split; [exact Hnodup|exact Hsorted].
  - split; [exact Hpref|].
    split.
    + intros ip0.
      specialize (Hmem ip0).
      split.
      * intro Hin.
        rewrite Hmem in Hin.
        destruct Hin as [pi [Hnth [Hpref' [Hbel Hlen]]]].
        exists (strengthen_pi env_dim pi).
        split.
        -- eapply nth_error_strengthen_pprog; eauto.
        -- split; [exact Hpref'|].
           split; [exact (proj2 (strengthen_pi_belongs_to_iff env_dim ip0 pi) Hbel)|].
           exact Hlen.
      * intro Hin.
        rewrite Hmem.
        destruct Hin as [pi [Hnth [Hpref' [Hbel Hlen]]]].
        eapply nth_error_strengthen_pprog_inv in Hnth.
        destruct Hnth as [pi0 [Hnth Heq]].
        subst pi.
        exists pi0.
        split; [exact Hnth|].
        split; [exact Hpref'|].
        split; [exact (proj1 (strengthen_pi_belongs_to_iff env_dim ip0 pi0) Hbel)|].
        exact Hlen.
    + split; [exact Hnodup|exact Hsorted].
Qed.

Theorem poly_instance_list_semantics_unstrengthen:
  forall env_dim envv pp st1 st2,
    length envv = env_dim ->
    PolyLang.poly_instance_list_semantics envv
      (let '(pis, varctxt, vars) := pp in (map (strengthen_pi env_dim) pis, varctxt, vars)) st1 st2 ->
    PolyLang.poly_instance_list_semantics envv pp st1 st2.
Proof.
  intros env_dim envv [[pis varctxt] vars] st1 st2 Henv Hsem.
  inversion Hsem as
      [envv' pprog pis' varctxt' vars' st1' st2' ipl sorted_ipl
       Hpprog Hflatten Hperm Hsorted Hipl];
    subst.
  simpl in Hpprog.
  inversion Hpprog; subst; clear Hpprog.
  econstructor.
  - reflexivity.
  - apply (proj1 (flatten_instrs_strengthen_iff (length envv) envv pis ipl eq_refl)).
    exact Hflatten.
  - exact Hperm.
  - exact Hsorted.
  - exact Hipl.
Qed.

Theorem instance_list_semantics_unstrengthen:
  forall pp st1 st2,
    PolyLang.instance_list_semantics (strengthen_pprog pp) st1 st2 ->
    PolyLang.instance_list_semantics pp st1 st2.
Proof.
  intros [[pis varctxt] vars] st1 st2 Hsem.
  inversion Hsem as
      [pprog pis' varctxt' vars' envv st1' st2'
       Hpprog Hcompat Hna Hinit Hpoly];
    subst.
  unfold strengthen_pprog in Hpprog. simpl in Hpprog.
  inversion Hpprog; subst; clear Hpprog.
  econstructor; eauto.
  eapply poly_instance_list_semantics_unstrengthen with (env_dim := length varctxt').
  - symmetry. eapply Instr.init_env_samelen; eauto.
  - exact Hpoly.
Qed.

End StrengthenDomain.
