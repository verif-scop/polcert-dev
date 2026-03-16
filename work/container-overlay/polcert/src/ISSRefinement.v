Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Base.
Require Import Linalg.
Require Import PolyBase.
Require Import PolyLang.
Require Import PointWitness.
Require Import ISSWitness.
Require Import PolIRs.
Import ListNotations.

Module ISSRefinement (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module Ty := PolIRs.Ty.
Module PolyLang := PolIRs.PolyLang.

Definition ident := Instr.ident.

Definition payload_eq_except_domain
    (pi1 pi2: PolyLang.PolyInstr) : Prop :=
  pi1.(PolyLang.pi_depth) = pi2.(PolyLang.pi_depth) /\
  pi1.(PolyLang.pi_instr) = pi2.(PolyLang.pi_instr) /\
  pi1.(PolyLang.pi_schedule) = pi2.(PolyLang.pi_schedule) /\
  pi1.(PolyLang.pi_point_witness) = pi2.(PolyLang.pi_point_witness) /\
  pi1.(PolyLang.pi_transformation) = pi2.(PolyLang.pi_transformation) /\
  pi1.(PolyLang.pi_access_transformation) =
    pi2.(PolyLang.pi_access_transformation) /\
  pi1.(PolyLang.pi_waccess) = pi2.(PolyLang.pi_waccess) /\
  pi1.(PolyLang.pi_raccess) = pi2.(PolyLang.pi_raccess).

Definition payload_eq_except_domainb
    (pi1 pi2: PolyLang.PolyInstr) : bool :=
  Nat.eqb pi1.(PolyLang.pi_depth) pi2.(PolyLang.pi_depth) &&
  Instr.eqb pi1.(PolyLang.pi_instr) pi2.(PolyLang.pi_instr) &&
  listzzs_strict_eqb pi1.(PolyLang.pi_schedule) pi2.(PolyLang.pi_schedule) &&
  PointWitness.point_space_witness_eqb
    pi1.(PolyLang.pi_point_witness)
    pi2.(PolyLang.pi_point_witness) &&
  listzzs_strict_eqb
    pi1.(PolyLang.pi_transformation)
    pi2.(PolyLang.pi_transformation) &&
  listzzs_strict_eqb
    pi1.(PolyLang.pi_access_transformation)
    pi2.(PolyLang.pi_access_transformation) &&
  access_list_strict_eqb
    pi1.(PolyLang.pi_waccess)
    pi2.(PolyLang.pi_waccess) &&
  access_list_strict_eqb
    pi1.(PolyLang.pi_raccess)
    pi2.(PolyLang.pi_raccess).

Lemma payload_eq_except_domainb_correct :
  forall pi1 pi2,
    payload_eq_except_domainb pi1 pi2 = true ->
    payload_eq_except_domain pi1 pi2.
Proof.
  intros pi1 pi2 H.
  unfold payload_eq_except_domainb in H.
  repeat match goal with
  | Hconj : _ && _ = true |- _ => apply andb_true_iff in Hconj
  | Hconj : _ /\ _ |- _ => destruct Hconj
  end.
  repeat match goal with
  | Heq : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Heq
  | Heq : Instr.eqb _ _ = true |- _ => apply Instr.eqb_eq in Heq
  | Heq : listzzs_strict_eqb _ _ = true |- _ => apply listzzs_strict_eqb_eq in Heq
  | Heq : PointWitness.point_space_witness_eqb _ _ = true |- _ =>
      apply PointWitness.point_space_witness_eqb_eq in Heq
  | Heq : access_list_strict_eqb _ _ = true |- _ =>
      apply access_list_strict_eqb_eq in Heq
  end.
  unfold payload_eq_except_domain.
  repeat split.
  all: assumption.
Qed.

Lemma payload_eq_except_domain_refl :
  forall pi,
    payload_eq_except_domain pi pi.
Proof.
  intros pi.
  unfold payload_eq_except_domain.
  repeat split; reflexivity.
Qed.

Definition iss_pairs
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    : list (PolyLang.PolyInstr * iss_stmt_witness) :=
  combine after_pis stmt_ws.

Definition child_pairs_for_parent
    (parent: nat)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    : list (PolyLang.PolyInstr * iss_stmt_witness) :=
  filter
    (fun pair =>
       Nat.eqb (isw_parent_stmt (snd pair)) parent)
    (iss_pairs after_pis stmt_ws).

Definition children_for_parent
    (parent: nat)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    : list PolyLang.PolyInstr :=
  map fst (child_pairs_for_parent parent after_pis stmt_ws).

Definition point_in_pinstr_domain
    (point: DomIndex)
    (pi: PolyLang.PolyInstr) : Prop :=
  in_poly point pi.(PolyLang.pi_poly) = true.

Definition point_satisfies_iss_cut
    (point: DomIndex)
    (cut: iss_cut)
    (sign: iss_halfspace_sign) : Prop :=
  let '(v, c) := cut in
  match sign with
  | ISSCutLtZero => (dot_product v point + c < 0)%Z
  | ISSCutGeZero => (0 <= dot_product v point + c)%Z
  end.

Definition iss_signed_cut_constraint
    (cut: iss_cut)
    (sign: iss_halfspace_sign) : constraint :=
  let '(v, c) := cut in
  match sign with
  | ISSCutLtZero => (v, (-c - 1)%Z)
  | ISSCutGeZero => (-- v, c)
  end.

Fixpoint iss_piece_constraints
    (cuts: list iss_cut)
    (signs: list iss_halfspace_sign) : option Domain :=
  match cuts, signs with
  | [], [] => Some []
  | cut :: cuts', sign :: signs' =>
      match iss_piece_constraints cuts' signs' with
      | Some constrs => Some (iss_signed_cut_constraint cut sign :: constrs)
      | None => None
      end
  | _, _ => None
  end.

Lemma iss_cut_lt0_constraint_arith :
  forall d c,
    (d + c < 0)%Z <->
    (d <=? (-c - 1))%Z = true.
Proof.
  intros d c.
  split; intro H.
  - apply Z.leb_le. lia.
  - apply Z.leb_le in H. lia.
Qed.

Lemma iss_cut_ge0_constraint_arith :
  forall d c,
    (0 <= d + c)%Z <->
    ((- d) <=? c)%Z = true.
Proof.
  intros d c.
  split; intro H.
  - apply Z.leb_le. lia.
  - apply Z.leb_le in H. lia.
Qed.

Lemma dot_product_opp_right_local :
  forall p v,
    dot_product p (map Z.opp v) = Z.opp (dot_product p v).
Proof.
  induction p as [|x p IH]; intros v.
  - destruct v; reflexivity.
  - destruct v as [|y v']; simpl; try lia.
    rewrite IH. lia.
Qed.

Lemma iss_signed_cut_constraint_correct :
  forall point cut sign,
    point_satisfies_iss_cut point cut sign <->
    satisfies_constraint point (iss_signed_cut_constraint cut sign) = true.
Proof.
  intros point [v c] sign.
  destruct sign; simpl.
  - unfold satisfies_constraint.
    rewrite dot_product_commutative.
    apply iss_cut_lt0_constraint_arith.
  - unfold satisfies_constraint.
    unfold Vopp.
    simpl.
    rewrite dot_product_opp_right_local.
    rewrite dot_product_commutative.
    apply iss_cut_ge0_constraint_arith.
Qed.

Lemma iss_piece_constraints_correct :
  forall point cuts signs constrs,
    iss_piece_constraints cuts signs = Some constrs ->
    Forall2 (point_satisfies_iss_cut point) cuts signs <->
    in_poly point constrs = true.
Proof.
  intros point cuts.
  induction cuts as [|cut cuts IH]; intros signs constrs Hconstrs.
  - destruct signs; simpl in Hconstrs; try discriminate.
    inversion Hconstrs; subst.
    split; intro H.
    + reflexivity.
    + constructor.
  - destruct signs as [|sign signs]; simpl in Hconstrs; try discriminate.
    destruct (iss_piece_constraints cuts signs) as [tail_constrs|] eqn:Htail;
      inversion Hconstrs; subst; clear Hconstrs.
    simpl.
    specialize (IH signs tail_constrs Htail).
    split; intro H.
    + inversion H as [|? ? ? ? Hhead_prop Htail_prop]; subst; clear H.
      simpl.
      apply (proj1 (iss_signed_cut_constraint_correct point cut sign)) in Hhead_prop.
      apply (proj1 IH) in Htail_prop.
      rewrite Hhead_prop.
      rewrite Htail_prop.
      reflexivity.
    + rewrite andb_true_iff in H.
      destruct H as [Hhead Htail_ok].
      constructor.
      * apply (proj2 (iss_signed_cut_constraint_correct point cut sign)).
        exact Hhead.
      * apply (proj2 IH).
        exact Htail_ok.
Qed.

Definition domains_all_subset
    (source: PolyLang.PolyInstr)
    (pieces: list PolyLang.PolyInstr) : Prop :=
  forall point piece,
    In piece pieces ->
    point_in_pinstr_domain point piece ->
    point_in_pinstr_domain point source.

Definition domains_cover
    (source: PolyLang.PolyInstr)
    (pieces: list PolyLang.PolyInstr) : Prop :=
  forall point,
    point_in_pinstr_domain point source ->
    exists piece,
      In piece pieces /\
      point_in_pinstr_domain point piece.

Definition domains_pairwise_disjoint
    (pieces: list PolyLang.PolyInstr) : Prop :=
  forall point i j pi1 pi2,
    nth_error pieces i = Some pi1 ->
    nth_error pieces j = Some pi2 ->
    i <> j ->
    point_in_pinstr_domain point pi1 ->
    point_in_pinstr_domain point pi2 ->
    False.

Definition stmt_partition_refinement
    (source: PolyLang.PolyInstr)
    (pieces: list PolyLang.PolyInstr) : Prop :=
  Forall (payload_eq_except_domain source) pieces /\
  domains_all_subset source pieces /\
  domains_cover source pieces /\
  domains_pairwise_disjoint pieces.

Definition parent_witnesses_in_range
    (before_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  Forall (fun w => (isw_parent_stmt w < length before_pis)%nat) stmt_ws.

Definition stmt_payload_matches_witness
    (before_pis: list PolyLang.PolyInstr)
    (after_pi: PolyLang.PolyInstr)
    (w: iss_stmt_witness) : Prop :=
  exists source,
    nth_error before_pis (isw_parent_stmt w) = Some source /\
    payload_eq_except_domain source after_pi.

Definition stmt_parent_payload_relation
    (before_pis: list PolyLang.PolyInstr)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  Forall2 (stmt_payload_matches_witness before_pis) after_pis stmt_ws.

Definition domain_partition_shape
    (before after: PolyLang.t)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  let '(before_pis, before_varctxt, before_vars) := before in
  let '(after_pis, after_varctxt, after_vars) := after in
  before_varctxt = after_varctxt /\
  before_vars = after_vars /\
  parent_witnesses_in_range before_pis stmt_ws /\
  stmt_parent_payload_relation before_pis after_pis stmt_ws.

Definition stmt_piece_signs_wf
    (cuts: list iss_cut)
    (w: iss_stmt_witness) : Prop :=
  length w.(isw_piece_signs) = length cuts.

Definition stmt_domain_matches_cuts
    (before_pis: list PolyLang.PolyInstr)
    (cuts: list iss_cut)
    (after_pi: PolyLang.PolyInstr)
    (w: iss_stmt_witness) : Prop :=
  exists source piece_constrs,
    nth_error before_pis (isw_parent_stmt w) = Some source /\
    iss_piece_constraints cuts w.(isw_piece_signs) = Some piece_constrs /\
    after_pi.(PolyLang.pi_poly) = source.(PolyLang.pi_poly) ++ piece_constrs.

Definition stmt_piece_signs_relation
    (cuts: list iss_cut)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  Forall (stmt_piece_signs_wf cuts) stmt_ws.

Definition stmt_domain_cut_relation
    (before_pis: list PolyLang.PolyInstr)
    (after_pis: list PolyLang.PolyInstr)
    (cuts: list iss_cut)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  Forall2 (stmt_domain_matches_cuts before_pis cuts) after_pis stmt_ws.

Definition domain_partition_cut_shape
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  let '(before_pis, _, _) := before in
  let '(after_pis, _, _) := after in
  domain_partition_shape before after w.(iw_stmt_witnesses) /\
  stmt_piece_signs_relation w.(iw_cuts) w.(iw_stmt_witnesses) /\
  stmt_domain_cut_relation
    before_pis after_pis w.(iw_cuts) w.(iw_stmt_witnesses).

Definition domain_partition_refinement
    (before after: PolyLang.t)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  let '(before_pis, before_varctxt, before_vars) := before in
  let '(after_pis, after_varctxt, after_vars) := after in
  before_varctxt = after_varctxt /\
  before_vars = after_vars /\
  length after_pis = length stmt_ws /\
  parent_witnesses_in_range before_pis stmt_ws /\
  forall parent source,
    nth_error before_pis parent = Some source ->
    stmt_partition_refinement
      source
      (children_for_parent parent after_pis stmt_ws).

Definition domain_partition_shape_with_witness
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  domain_partition_shape before after w.(iw_stmt_witnesses).

Definition domain_partition_refinement_with_witness
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  domain_partition_refinement before after w.(iw_stmt_witnesses).

Fixpoint all_iss_sign_vectors
    (n: nat) : list (list iss_halfspace_sign) :=
  match n with
  | O => [[]]
  | S n' =>
      let tail := all_iss_sign_vectors n' in
      map (cons ISSCutLtZero) tail ++
      map (cons ISSCutGeZero) tail
  end.

Definition child_signs_for_parent
    (parent: nat)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness)
    : list (list iss_halfspace_sign) :=
  map (fun pair => isw_piece_signs (snd pair))
      (child_pairs_for_parent parent after_pis stmt_ws).

Definition parent_sign_partition_complete
    (cuts: list iss_cut)
    (parent: nat)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  NoDup (child_signs_for_parent parent after_pis stmt_ws) /\
  forall signs,
    In signs (all_iss_sign_vectors (length cuts)) ->
    In signs (child_signs_for_parent parent after_pis stmt_ws).

Definition cut_partition_complete
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  let '(before_pis, _, _) := before in
  let '(after_pis, _, _) := after in
  forall parent source,
    nth_error before_pis parent = Some source ->
    parent_sign_partition_complete
      w.(iw_cuts) parent after_pis w.(iw_stmt_witnesses).

Definition domain_partition_complete_cut_shape
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  domain_partition_cut_shape before after w /\
  cut_partition_complete before after w.

Definition iss_sign_for_point
    (point: DomIndex)
    (cut: iss_cut) : iss_halfspace_sign :=
  let '(v, c) := cut in
  if Z_lt_ge_dec (dot_product v point + c) 0
  then ISSCutLtZero
  else ISSCutGeZero.

Fixpoint iss_signs_for_point
    (point: DomIndex)
    (cuts: list iss_cut) : list iss_halfspace_sign :=
  match cuts with
  | [] => []
  | cut :: cuts' =>
      iss_sign_for_point point cut ::
      iss_signs_for_point point cuts'
  end.

Definition parent_partition_properties
    (before_pis: list PolyLang.PolyInstr)
    (after_pis: list PolyLang.PolyInstr)
    (stmt_ws: list iss_stmt_witness) : Prop :=
  forall parent source,
    nth_error before_pis parent = Some source ->
    domains_all_subset
      source (children_for_parent parent after_pis stmt_ws) /\
    domains_cover
      source (children_for_parent parent after_pis stmt_ws) /\
    domains_pairwise_disjoint
      (children_for_parent parent after_pis stmt_ws).

Definition domain_partition_refinement_obligations
    (before after: PolyLang.t)
    (w: iss_witness) : Prop :=
  let '(before_pis, _, _) := before in
  let '(after_pis, _, _) := after in
  domain_partition_shape_with_witness before after w /\
  length after_pis = length w.(iw_stmt_witnesses) /\
  parent_partition_properties before_pis after_pis w.(iw_stmt_witnesses).

Lemma domain_partition_cut_shape_implies_shape :
  forall before after w,
    domain_partition_cut_shape before after w ->
    domain_partition_shape_with_witness before after w.
Proof.
  intros before after w Hcut.
  unfold domain_partition_shape_with_witness.
  unfold domain_partition_cut_shape in Hcut.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  simpl in Hcut.
  exact (proj1 Hcut).
Qed.

Lemma all_iss_sign_vectors_length :
  forall n signs,
    In signs (all_iss_sign_vectors n) ->
    length signs = n.
Proof.
  induction n as [|n IH]; intros signs Hin.
  - simpl in Hin.
    destruct Hin as [Hin | []].
    subst. reflexivity.
  - simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [tail [Hsigns Htail]].
      subst signs.
      simpl.
      f_equal.
      eapply IH; eauto.
    + apply in_map_iff in Hin.
      destruct Hin as [tail [Hsigns Htail]].
      subst signs.
      simpl.
      f_equal.
      eapply IH; eauto.
Qed.

Lemma iss_sign_for_point_satisfies :
  forall point cut,
    point_satisfies_iss_cut point cut (iss_sign_for_point point cut).
Proof.
  intros point [v c].
  unfold iss_sign_for_point, point_satisfies_iss_cut.
  destruct (Z_lt_ge_dec (dot_product v point + c) 0); lia.
Qed.

Lemma iss_signs_for_point_satisfy :
  forall point cuts,
    Forall2 (point_satisfies_iss_cut point)
      cuts (iss_signs_for_point point cuts).
Proof.
  intros point cuts.
  induction cuts as [|cut cuts IH]; simpl.
  - constructor.
  - constructor.
    + apply iss_sign_for_point_satisfies.
    + exact IH.
Qed.

Lemma iss_signs_for_point_in_all :
  forall point cuts,
    In (iss_signs_for_point point cuts)
       (all_iss_sign_vectors (length cuts)).
Proof.
  intros point cuts.
  induction cuts as [|cut cuts IH]; simpl.
  - left. reflexivity.
  - destruct cut as [v c].
    unfold iss_sign_for_point in *.
    simpl.
    destruct (Z_lt_ge_dec (dot_product v point + c) 0).
    + apply in_or_app. left.
      apply in_map_iff.
      exists (iss_signs_for_point point cuts).
      split; [reflexivity | exact IH].
    + apply in_or_app. right.
      apply in_map_iff.
      exists (iss_signs_for_point point cuts).
      split; [reflexivity | exact IH].
Qed.

Lemma point_satisfies_iss_cut_functional :
  forall point cut sign1 sign2,
    point_satisfies_iss_cut point cut sign1 ->
    point_satisfies_iss_cut point cut sign2 ->
    sign1 = sign2.
Proof.
  intros point cut sign1 sign2 H1 H2.
  destruct cut as [v c].
  destruct sign1, sign2; simpl in *; try reflexivity; lia.
Qed.

Lemma point_satisfies_iss_cuts_functional :
  forall point cuts signs1 signs2,
    Forall2 (point_satisfies_iss_cut point) cuts signs1 ->
    Forall2 (point_satisfies_iss_cut point) cuts signs2 ->
    signs1 = signs2.
Proof.
  intros point cuts signs1 signs2 Hsat1.
  revert signs2.
  induction Hsat1; intros signs2 Hsat2.
  - inversion Hsat2. reflexivity.
  - inversion Hsat2; subst.
    f_equal.
    + eapply point_satisfies_iss_cut_functional; eauto.
    + eapply IHHsat1; eauto.
Qed.

Lemma nth_error_map_some :
  forall (A B: Type) (f: A -> B) xs n x,
    nth_error xs n = Some x ->
    nth_error (map f xs) n = Some (f x).
Proof.
  intros A B f xs.
  induction xs as [|xhd xtl IH]; intros n x Hnth.
  - destruct n; inversion Hnth.
  - destruct n.
    + simpl in *. inversion Hnth. reflexivity.
    + simpl in *. eapply IH; eauto.
Qed.

Lemma nth_error_map_inv :
  forall (A B: Type) (f: A -> B) xs n y,
    nth_error (map f xs) n = Some y ->
    exists x,
      nth_error xs n = Some x /\
      y = f x.
Proof.
  induction xs as [|x xs IH]; intros n y Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n; simpl in Hnth.
    + inversion Hnth. subst. exists x. split; reflexivity.
    + eapply IH in Hnth.
      destruct Hnth as [x' [Hxs Hy]].
      exists x'. split; exact Hxs || exact Hy.
Qed.

Lemma NoDup_nth_error_injective :
  forall A (xs: list A) i j x,
    NoDup xs ->
    nth_error xs i = Some x ->
    nth_error xs j = Some x ->
    i = j.
Proof.
  intros A xs i j x Hnd Hi Hj.
  rewrite NoDup_nth_error in Hnd.
  apply Hnd.
  - rewrite <- nth_error_Some.
    rewrite Hi.
    discriminate.
  - rewrite Hi, Hj.
    reflexivity.
Qed.

Lemma Forall2_combine_inv :
  forall A B (P: A -> B -> Prop) xs ys x y,
    Forall2 P xs ys ->
    In (x, y) (combine xs ys) ->
    P x y.
Proof.
  intros A B P xs.
  induction xs as [|x0 xs IH]; intros ys x y Hrel Hin.
  - inversion Hin.
  - destruct ys as [|y0 ys]; simpl in *.
    + inversion Hin.
    + inversion Hrel; subst.
      destruct Hin as [Heq | Hin].
      * inversion Heq; subst. assumption.
      * eapply IH; eauto.
Qed.

Lemma Forall2_length_eq :
  forall A B (P: A -> B -> Prop) xs ys,
    Forall2 P xs ys ->
    length xs = length ys.
Proof.
  intros A B P xs ys Hrel.
  induction Hrel; simpl; congruence.
Qed.

Lemma in_poly_app_inv_local :
  forall p pol1 pol2,
    in_poly p (pol1 ++ pol2) = true ->
    in_poly p pol1 = true /\ in_poly p pol2 = true.
Proof.
  intros p pol1 pol2 Hin.
  rewrite in_poly_app in Hin.
  apply andb_true_iff in Hin.
  exact Hin.
Qed.

Lemma stmt_payload_matches_witness_parent :
  forall before_pis after_pi w parent source,
    stmt_payload_matches_witness before_pis after_pi w ->
    isw_parent_stmt w = parent ->
    nth_error before_pis parent = Some source ->
    payload_eq_except_domain source after_pi.
Proof.
  intros before_pis after_pi w parent source Hmatch Hparent Hsource.
  unfold stmt_payload_matches_witness in Hmatch.
  destruct Hmatch as (source' & Hnth & Hpayload).
  rewrite Hparent in Hnth.
  rewrite Hsource in Hnth.
  inversion Hnth; subst.
  exact Hpayload.
Qed.

Lemma stmt_parent_payload_relation_children_payload :
  forall before_pis after_pis stmt_ws parent source,
    stmt_parent_payload_relation before_pis after_pis stmt_ws ->
    nth_error before_pis parent = Some source ->
    Forall
      (payload_eq_except_domain source)
      (children_for_parent parent after_pis stmt_ws).
Proof.
  intros before_pis after_pis stmt_ws parent source Hrel Hsource.
  unfold children_for_parent, child_pairs_for_parent, iss_pairs.
  apply Forall_forall.
  intros child Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[after_pi w] [Hchild Hin_pair]].
  subst child.
  apply filter_In in Hin_pair.
  destruct Hin_pair as [Hin_pair Hpred].
  apply Nat.eqb_eq in Hpred.
  pose proof (Forall2_combine_inv _ _ _ _ _ _ _ Hrel Hin_pair) as Hmatch.
  eapply stmt_payload_matches_witness_parent; eauto.
Qed.

Lemma stmt_domain_matches_cuts_in_domain_iff :
  forall before_pis cuts after_pi w point source piece_constrs,
    stmt_domain_matches_cuts before_pis cuts after_pi w ->
    nth_error before_pis (isw_parent_stmt w) = Some source ->
    iss_piece_constraints cuts (isw_piece_signs w) = Some piece_constrs ->
    point_in_pinstr_domain point after_pi <->
    point_in_pinstr_domain point source /\
    Forall2 (point_satisfies_iss_cut point) cuts (isw_piece_signs w).
Proof.
  intros before_pis cuts after_pi w point source piece_constrs
         Hmatch Hsource Hpiece.
  unfold stmt_domain_matches_cuts in Hmatch.
  destruct Hmatch as (source' & piece_constrs' & Hsource' & Hpiece' & Hafter_eq).
  rewrite Hsource in Hsource'.
  inversion Hsource'; subst source'; clear Hsource'.
  rewrite Hpiece in Hpiece'.
  inversion Hpiece'; subst piece_constrs'; clear Hpiece'.
  unfold point_in_pinstr_domain.
  rewrite Hafter_eq.
  rewrite in_poly_app.
  rewrite (iss_piece_constraints_correct point cuts (isw_piece_signs w) piece_constrs Hpiece).
  rewrite andb_true_iff.
  tauto.
Qed.

Lemma stmt_domain_cut_relation_all_subset :
  forall before_pis after_pis stmt_ws cuts parent source,
    stmt_domain_cut_relation before_pis after_pis cuts stmt_ws ->
    nth_error before_pis parent = Some source ->
    domains_all_subset
      source (children_for_parent parent after_pis stmt_ws).
Proof.
  intros before_pis after_pis stmt_ws cuts parent source Hrel Hsource.
  unfold domains_all_subset.
  intros point piece Hin Hpiece.
  unfold children_for_parent, child_pairs_for_parent, iss_pairs in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[after_pi w] [Hpiece_eq Hin_pair]].
  subst piece.
  apply filter_In in Hin_pair.
  destruct Hin_pair as [Hin_pair Hparent].
  simpl in Hparent.
  apply Nat.eqb_eq in Hparent.
  pose proof (Forall2_combine_inv _ _ _ _ _ _ _ Hrel Hin_pair) as Hmatch.
  unfold stmt_domain_matches_cuts in Hmatch.
  destruct Hmatch as (source' & piece_constrs & Hnth & Hpiece_constrs & Hpoly_eq).
  rewrite Hparent in Hnth.
  rewrite Hsource in Hnth.
  inversion Hnth; subst source'; clear Hnth.
  unfold point_in_pinstr_domain in *.
  simpl in Hpiece.
  rewrite Hpoly_eq in Hpiece.
  apply in_poly_app_inv_local in Hpiece.
  exact (proj1 Hpiece).
Qed.

Lemma parent_sign_partition_complete_has_child :
  forall cuts parent after_pis stmt_ws signs,
    parent_sign_partition_complete cuts parent after_pis stmt_ws ->
    In signs (all_iss_sign_vectors (length cuts)) ->
    exists pair,
      In pair (child_pairs_for_parent parent after_pis stmt_ws) /\
      isw_piece_signs (snd pair) = signs.
Proof.
  intros cuts parent after_pis stmt_ws signs [Hnodup Hcomplete] Hin.
  unfold child_signs_for_parent in Hcomplete.
  specialize (Hcomplete signs Hin).
  rename Hcomplete into Hsign_in.
  apply in_map_iff in Hsign_in.
  destruct Hsign_in as [pair [Hsigns Hin_pair]].
  exists pair.
  split; assumption.
Qed.

Lemma stmt_domain_cut_relation_cover :
  forall before_pis after_pis stmt_ws cuts parent source,
    stmt_domain_cut_relation before_pis after_pis cuts stmt_ws ->
    parent_sign_partition_complete cuts parent after_pis stmt_ws ->
    nth_error before_pis parent = Some source ->
    domains_cover
      source (children_for_parent parent after_pis stmt_ws).
Proof.
  intros before_pis after_pis stmt_ws cuts parent source
         Hrel Hcomplete Hsource.
  unfold domains_cover.
  intros point Hsource_in.
  set (signs := iss_signs_for_point point cuts).
  assert (Hsigns_in : In signs (all_iss_sign_vectors (length cuts))).
  {
    unfold signs.
    apply iss_signs_for_point_in_all.
  }
  destruct (parent_sign_partition_complete_has_child
              cuts parent after_pis stmt_ws signs Hcomplete Hsigns_in)
    as [pair [Hin_pair Hpair_signs]].
  destruct pair as [piece w].
  simpl in Hpair_signs.
  exists piece.
  split.
  - unfold children_for_parent.
    apply in_map_iff.
    exists (piece, w).
    split; [reflexivity | exact Hin_pair].
  - apply filter_In in Hin_pair.
    simpl in Hin_pair.
    destruct Hin_pair as [Hin_pair Hparent].
    simpl in Hparent.
    apply Nat.eqb_eq in Hparent.
    pose proof (Forall2_combine_inv _ _ _ _ _ _ _ Hrel Hin_pair) as Hmatch.
    unfold stmt_domain_matches_cuts in Hmatch.
    destruct Hmatch as (source' & piece_constrs & Hnth & Hpiece_constrs & Hpoly_eq).
    rewrite Hparent in Hnth.
    rewrite Hsource in Hnth.
    inversion Hnth; subst source'; clear Hnth.
    rewrite Hpair_signs in Hpiece_constrs.
    unfold point_in_pinstr_domain.
    rewrite Hpoly_eq.
    rewrite in_poly_app.
    rewrite Hsource_in.
    assert (Hsat : Forall2 (point_satisfies_iss_cut point) cuts signs).
    {
      unfold signs.
      apply iss_signs_for_point_satisfy.
    }
    apply (proj1 (iss_piece_constraints_correct point cuts signs piece_constrs Hpiece_constrs)) in Hsat.
    simpl.
    rewrite Hsat.
    reflexivity.
Qed.

Lemma stmt_domain_cut_relation_disjoint :
  forall before_pis after_pis stmt_ws cuts parent source,
    stmt_domain_cut_relation before_pis after_pis cuts stmt_ws ->
    parent_sign_partition_complete cuts parent after_pis stmt_ws ->
    nth_error before_pis parent = Some source ->
    domains_pairwise_disjoint
      (children_for_parent parent after_pis stmt_ws).
Proof.
  intros before_pis after_pis stmt_ws cuts parent source
         Hrel [Hnodup Hcomplete] Hsource.
  unfold domains_pairwise_disjoint.
  intros point i j pi1 pi2 Hi Hj Hneq Hdom1 Hdom2.
  set (pairs := child_pairs_for_parent parent after_pis stmt_ws).
  set (sign_rows := child_signs_for_parent parent after_pis stmt_ws).
  assert (Hpair1 :
            exists w1,
              nth_error pairs i = Some (pi1, w1)).
  {
    unfold pairs, children_for_parent, child_pairs_for_parent in Hi.
    eapply nth_error_map_inv in Hi.
    destruct Hi as [[pi w] [Hnth Heq]].
    simpl in Heq. inversion Heq; subst.
    exists w. exact Hnth.
  }
  assert (Hpair2 :
            exists w2,
              nth_error pairs j = Some (pi2, w2)).
  {
    unfold pairs, children_for_parent, child_pairs_for_parent in Hj.
    eapply nth_error_map_inv in Hj.
    destruct Hj as [[pi w] [Hnth Heq]].
    simpl in Heq. inversion Heq; subst.
    exists w. exact Hnth.
  }
  destruct Hpair1 as [w1 Hpair1].
  destruct Hpair2 as [w2 Hpair2].
  assert (Hin_pair1 : In (pi1, w1) pairs).
  { apply nth_error_In with (n := i). exact Hpair1. }
  assert (Hin_pair2 : In (pi2, w2) pairs).
  { apply nth_error_In with (n := j). exact Hpair2. }
  unfold pairs, child_pairs_for_parent in Hin_pair1, Hin_pair2.
  apply filter_In in Hin_pair1.
  apply filter_In in Hin_pair2.
  destruct Hin_pair1 as [Hin_pair1 Hparent1].
  destruct Hin_pair2 as [Hin_pair2 Hparent2].
  simpl in Hparent1, Hparent2.
  apply Nat.eqb_eq in Hparent1.
  apply Nat.eqb_eq in Hparent2.
  pose proof (Forall2_combine_inv _ _ _ _ _ _ _ Hrel Hin_pair1) as Hmatch1.
  pose proof (Forall2_combine_inv _ _ _ _ _ _ _ Hrel Hin_pair2) as Hmatch2.
  unfold stmt_domain_matches_cuts in Hmatch1.
  unfold stmt_domain_matches_cuts in Hmatch2.
  destruct Hmatch1 as (source1 & constrs1 & Hnth1 & Hconstrs1 & Hpoly1).
  destruct Hmatch2 as (source2 & constrs2 & Hnth2 & Hconstrs2 & Hpoly2).
  rewrite Hparent1 in Hnth1.
  rewrite Hparent2 in Hnth2.
  rewrite Hsource in Hnth1. inversion Hnth1; subst source1; clear Hnth1.
  rewrite Hsource in Hnth2. inversion Hnth2; subst source2; clear Hnth2.
  assert (Hmatch1_rel : stmt_domain_matches_cuts before_pis cuts pi1 w1).
  {
    exists source, constrs1.
    split.
    - rewrite Hparent1. exact Hsource.
    - split; assumption.
  }
  assert (Hmatch2_rel : stmt_domain_matches_cuts before_pis cuts pi2 w2).
  {
    exists source, constrs2.
    split.
    - rewrite Hparent2. exact Hsource.
    - split; assumption.
  }
  assert (Hsource1 :
            nth_error before_pis (isw_parent_stmt w1) = Some source).
  {
    rewrite Hparent1. exact Hsource.
  }
  assert (Hsource2 :
            nth_error before_pis (isw_parent_stmt w2) = Some source).
  {
    rewrite Hparent2. exact Hsource.
  }
  assert (Hsat1 :
            Forall2 (point_satisfies_iss_cut point) cuts (isw_piece_signs w1)).
  {
    pose proof
      ((proj1 (stmt_domain_matches_cuts_in_domain_iff
                 before_pis cuts pi1 w1 point source constrs1
                 Hmatch1_rel Hsource1 Hconstrs1)) Hdom1)
      as Hpair_sat1.
    exact (proj2 Hpair_sat1).
  }
  assert (Hsat2 :
            Forall2 (point_satisfies_iss_cut point) cuts (isw_piece_signs w2)).
  {
    pose proof
      ((proj1 (stmt_domain_matches_cuts_in_domain_iff
                 before_pis cuts pi2 w2 point source constrs2
                 Hmatch2_rel Hsource2 Hconstrs2)) Hdom2)
      as Hpair_sat2.
    exact (proj2 Hpair_sat2).
  }
  assert (Hsigns_eq :
            isw_piece_signs w1 = isw_piece_signs w2).
  {
    eapply point_satisfies_iss_cuts_functional; eauto.
  }
  assert (Hsign_nth1 :
            nth_error sign_rows i = Some (isw_piece_signs w1)).
  {
    unfold sign_rows, child_signs_for_parent, pairs.
    exact
      (nth_error_map_some
         (PolyLang.PolyInstr * iss_stmt_witness)
         (list iss_halfspace_sign)
         (fun pair => isw_piece_signs (snd pair))
         (child_pairs_for_parent parent after_pis stmt_ws)
         i
         (pi1, w1)
         Hpair1).
  }
  assert (Hsign_nth2 :
            nth_error sign_rows j = Some (isw_piece_signs w2)).
  {
    unfold sign_rows, child_signs_for_parent, pairs.
    exact
      (nth_error_map_some
         (PolyLang.PolyInstr * iss_stmt_witness)
         (list iss_halfspace_sign)
         (fun pair => isw_piece_signs (snd pair))
         (child_pairs_for_parent parent after_pis stmt_ws)
         j
         (pi2, w2)
         Hpair2).
  }
  rewrite <- Hsigns_eq in Hsign_nth2.
  assert (i = j).
  {
    eapply NoDup_nth_error_injective; eauto.
  }
  contradiction.
Qed.

Lemma domain_partition_shape_stmt_witnesses_length :
  forall before after w,
    domain_partition_shape_with_witness before after w ->
    let '(after_pis, _, _) := after in
    length after_pis = length w.(iw_stmt_witnesses).
Proof.
  intros before after w Hshape.
  unfold domain_partition_shape_with_witness in Hshape.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold domain_partition_shape in Hshape.
  simpl in *.
  destruct Hshape as (_ & _ & _ & Hpayload).
  eapply Forall2_length_eq in Hpayload.
  exact Hpayload.
Qed.

Lemma domain_partition_complete_cut_shape_obligations :
  forall before after w,
    domain_partition_complete_cut_shape before after w ->
    domain_partition_refinement_obligations before after w.
Proof.
  intros before after w [Hcut Hcomplete].
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  assert (Hshape :
            domain_partition_shape_with_witness
              (before_pis, before_varctxt, before_vars)
              (after_pis, after_varctxt, after_vars) w).
  {
    eapply domain_partition_cut_shape_implies_shape.
    exact Hcut.
  }
  assert (Hlen :
            length after_pis = length (iw_stmt_witnesses w)).
  {
    unfold domain_partition_shape_with_witness, domain_partition_shape in Hshape.
    simpl in Hshape.
    destruct Hshape as (_ & _ & _ & Hpayload).
    eapply Forall2_length_eq in Hpayload.
    exact Hpayload.
  }
  unfold domain_partition_refinement_obligations.
  simpl.
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + unfold parent_partition_properties.
      intros parent source Hsource.
      split.
      * eapply stmt_domain_cut_relation_all_subset.
        -- exact (proj2 (proj2 Hcut)).
        -- exact Hsource.
      * split.
        -- eapply stmt_domain_cut_relation_cover.
           ++ exact (proj2 (proj2 Hcut)).
           ++ eapply Hcomplete; eauto.
           ++ exact Hsource.
        -- eapply stmt_domain_cut_relation_disjoint.
           ++ exact (proj2 (proj2 Hcut)).
           ++ eapply Hcomplete; eauto.
           ++ exact Hsource.
Qed.

Lemma domain_partition_refinement_intro :
  forall before after stmt_ws,
    domain_partition_shape before after stmt_ws ->
    length (let '(after_pis, _, _) := after in after_pis) = length stmt_ws ->
    (forall parent source,
        let '(before_pis, _, _) := before in
        let '(after_pis, _, _) := after in
        nth_error before_pis parent = Some source ->
        stmt_partition_refinement
          source
          (children_for_parent parent after_pis stmt_ws)) ->
    domain_partition_refinement before after stmt_ws.
Proof.
  intros before after stmt_ws Hshape Hlen Hparts.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold domain_partition_shape in Hshape.
  unfold domain_partition_refinement.
  simpl in *.
  destruct Hshape as (Hctxt & Hvars & Hparents & Hpayload).
  exact
    (conj Hctxt
      (conj Hvars
        (conj Hlen
          (conj Hparents
            (fun parent0 source0 Hsource =>
               Hparts parent0 source0 Hsource))))).
Qed.

Lemma domain_partition_refinement_from_obligations :
  forall before after w,
    domain_partition_refinement_obligations before after w ->
    domain_partition_refinement_with_witness before after w.
Proof.
  intros before after w Hobl.
  destruct before as [[before_pis before_varctxt] before_vars].
  destruct after as [[after_pis after_varctxt] after_vars].
  unfold domain_partition_refinement_obligations in Hobl.
  unfold domain_partition_refinement_with_witness.
  simpl in *.
  destruct Hobl as [Hshape [Hlen Hparts]].
  eapply (domain_partition_refinement_intro
            (before_pis, before_varctxt, before_vars)
            (after_pis, after_varctxt, after_vars)
            (iw_stmt_witnesses w)).
  - exact Hshape.
  - exact Hlen.
  - intros parent source Hsource.
    unfold parent_partition_properties in Hparts.
    specialize (Hparts parent source Hsource).
    destruct Hparts as [Hall [Hcover Hdisj]].
    unfold domain_partition_shape_with_witness in Hshape.
    unfold domain_partition_shape in Hshape.
    simpl in Hshape.
    destruct Hshape as (_ & _ & _ & Hpayload).
    unfold stmt_partition_refinement.
    repeat split.
    + eapply stmt_parent_payload_relation_children_payload; eauto.
    + exact Hall.
    + exact Hcover.
    + exact Hdisj.
Qed.

Lemma domain_partition_refinement_from_complete_cut_shape :
  forall before after w,
    domain_partition_complete_cut_shape before after w ->
    domain_partition_refinement_with_witness before after w.
Proof.
  intros before after w Hcomplete.
  eapply domain_partition_refinement_from_obligations.
  eapply domain_partition_complete_cut_shape_obligations.
  exact Hcomplete.
Qed.

Lemma domains_pairwise_disjoint_singleton :
  forall pi,
    domains_pairwise_disjoint [pi].
Proof.
  intros pi point i j pi1 pi2 Hi Hj Hneq _ _.
  assert (Hi_lt: (i < length [pi])%nat).
  {
    apply nth_error_Some.
    rewrite Hi.
    discriminate.
  }
  assert (Hj_lt: (j < length [pi])%nat).
  {
    apply nth_error_Some.
    rewrite Hj.
    discriminate.
  }
  simpl in Hi_lt, Hj_lt.
  lia.
Qed.

Lemma stmt_partition_refinement_singleton :
  forall pi,
    stmt_partition_refinement pi [pi].
Proof.
  intros pi.
  unfold stmt_partition_refinement.
  repeat split.
  - constructor.
    + apply payload_eq_except_domain_refl.
    + constructor.
  - intros point piece Hin Hpiece.
    simpl in Hin.
    destruct Hin as [Hin | []].
    subst. exact Hpiece.
  - intros point Hsource.
    exists pi.
    split; [left; reflexivity | exact Hsource].
  - apply domains_pairwise_disjoint_singleton.
Qed.

End ISSRefinement.
