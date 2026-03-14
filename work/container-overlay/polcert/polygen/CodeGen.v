(* *****************************************************************)
(*                                                                 *)
(*               Verified polyhedral AST generation                *)
(*                                                                 *)
(*                 Nathanaël Courant, Inria Paris                  *)
(*                                                                 *)
(*  Copyright Inria. All rights reserved. This file is distributed *)
(*  under the terms of the GNU Lesser General Public License as    *)
(*  published by the Free Software Foundation, either version 2.1  *)
(*  of the License, or (at your option) any later version.         *)
(*                                                                 *)
(* *****************************************************************)

Require Import ZArith.
Require Import List.
Require Import Psatz.


Require Import Linalg.
Require Import ImpureAlarmConfig.

Require Import PolyLang.
Require Import ASTGen.
(* Require Import PolyLoop. *)
Require Import PolyLoopSimpl.
Require Import LoopGen.
(* Require Import Loop. *)
Require Import Misc.

Open Scope Z_scope.

Require Import InstrTy.
Require Import PolIRs.

Require Import LibTactics.

Module CodeGen (PolIRs: POLIRS).

(* Module Instr := PolIRs.BaseInstr. *)
Module PolyLang := PolIRs.PolyLang.
Module PolyLoop := PolIRs.PolyLoop.
Module Loop := PolIRs.Loop.

Module ASTGen := ASTGen(PolIRs).
Module PolyLoopSimplifier := PolyLoopSimplify(PolIRs).
Module LoopGen := LoopGen(PolIRs).

Definition codegen_target_dim (pol: PolIRs.PolyLang.t) : nat :=
  let '(_, _, vars) := pol in
  Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim pol).

Definition complete_generate d n pi :=
  BIND polyloop <- ASTGen.generate d n pi -;
  LoopGen.polyloop_to_loop (n - d)%nat polyloop.

Theorem complete_generate_preserve_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate d n pi THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(PolyLang.pi_poly) -> fst c =v= resize n (fst c)) ->
    PolyLang.env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hdn st Hst Hloop Henv Hsize.
  unfold complete_generate in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop.
  eapply ASTGen.generate_preserves_sem; eauto.
  eapply LoopGen.polyloop_to_loop_correct; eauto.
Qed.


(** after elimination, each instance prefixs its timestamp, which should be less than `k`. here d = n + k - es,  *)
(** meaning: timestamp length + domain index length - one shared env size *)
Definition complete_generate_lex_many d n pis :=
  BIND polyloop <- ASTGen.generate_loop_many d n pis -;
  BIND simp <- PolyLoopSimplifier.polyloop_simplify polyloop (n - d)%nat nil -;
  LoopGen.polyloop_to_loop (n - d)%nat simp.

Theorem complete_generate_lex_many_preserve_sem :
  forall d n pis env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate_lex_many d n pis THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    ASTGen.pis_have_dimension pis n ->
    PolyLang.env_poly_lex_semantics (rev env) n pis mem1 mem2.
Proof.
  intros d n pis env mem1 mem2 Hdn st Hst Hloop Henv Hpis.
  unfold complete_generate_lex_many in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop; bind_imp_destruct Hst simp Hsimp.
  eapply ASTGen.generate_loop_many_preserves_sem; eauto; [|unfold ASTGen.generate_invariant; auto].
  eapply PolyLoopSimplifier.polyloop_simplify_correct; [|exact Hsimp| | |]; auto; [unfold poly_nrl; simpl; lia|].
  eapply LoopGen.polyloop_to_loop_correct; eauto.
Qed.

Definition complete_generate_many es n pis :=
  let k := list_max (map (fun pi => length pi.(PolyLang.pi_schedule)) pis) in
  let epis := PolyLang.elim_schedule k es pis in
  complete_generate_lex_many (n + k - es)%nat (n + k)%nat epis.

Theorem complete_generate_many_preserve_sem :
  forall es n pis env mem1 mem2,
    (es <= n)%nat ->
    WHEN st <- complete_generate_many es n pis THEN
    Loop.loop_semantics st env mem1 mem2 ->
    length env = es ->
    ASTGen.pis_have_dimension pis n ->
    (forall pi, In pi pis ->
        PolyLang.current_env_dim_in_dim n pi.(PolyLang.pi_point_witness) = es) ->
    (forall pi, In pi pis -> (poly_nrl pi.(PolyLang.pi_schedule) <= n)%nat) ->
    PolyLang.env_poly_semantics (rev env) n pis mem1 mem2.
Proof.
  intros es n pis env mem1 mem2 Hes st Hst Hloop Henv Hpis Hpis_envdim Hpis2.
  unfold complete_generate_many in Hst.
  eapply complete_generate_lex_many_preserve_sem in Hst; [|lia].
  set (k := list_max (map (fun pi => length pi.(PolyLang.pi_schedule)) pis)) in *.
  assert (Hlex :
    PolyLang.env_poly_lex_semantics (rev env) (n + k)
      (PolyLang.elim_schedule k es pis) mem1 mem2).
  {
    eapply Hst; [exact Hloop| |].
    - subst k. lia.
    - unfold ASTGen.pis_have_dimension, PolyLang.elim_schedule in *. rewrite forallb_map, forallb_forall in *.
      intros pi Hpi; specialize (Hpis pi Hpi). reflect.
      rewrite PolyLang.pi_elim_schedule_nrl by (apply list_max_ge; rewrite in_map_iff; exists pi; auto).
      specialize (Hpis2 pi Hpi); lia.
  }
  eapply (PolyLang.poly_elim_schedule_semantics_env_preserve
            k es (rev env) n pis mem1 mem2).
  - rewrite rev_length. symmetry. exact Henv.
  - lia.
  - exact Hlex.
  - intros k' pi Hpi. apply nth_error_In in Hpi. apply list_max_ge. rewrite in_map_iff; exists pi; auto.
  - intros k' pi Hpi.
    apply nth_error_In in Hpi.
    specialize (Hpis_envdim pi Hpi).
    exact Hpis_envdim.
Qed.

Definition codegen (pol: PolIRs.PolyLang.t): imp Loop.t :=
  let '(pis, varctxt, vars) := pol in 
  let n := Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim pol) in
  BIND loop <- complete_generate_many (length varctxt) n pis -; 
  pure (loop, varctxt, vars).

Lemma wf_pprog_implies_pis_have_dimension: 
  forall pis ctxt vars n,
    PolIRs.PolyLang.wf_pprog (pis, ctxt, vars) ->
    (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars) <= n)%nat ->
    ASTGen.pis_have_dimension pis n.
Proof.
  intros pis ctxt vars n Hwf Hdim.
  unfold PolIRs.PolyLang.wf_pprog in Hwf.
  unfold ASTGen.pis_have_dimension.
  destruct Hwf as (_ & Hwf3).
  eapply forallb_forall. intros pi Hin. 
  pose proof (Hwf3 pi Hin) as Hwfpi.
  unfold PolIRs.PolyLang.wf_pinstr in Hwfpi. 
  destruct Hwfpi as (_ & _ & Hpoly_nrl & _).
  eapply Nat.leb_le.
  eapply Nat.le_trans.
  - exact Hpoly_nrl.
  - eapply Nat.le_trans.
    + eapply PolIRs.PolyLang.pprog_current_dim_ge_pinstr; exact Hin.
    + exact Hdim.
Qed.

Lemma wf_pprog_implies_pis_sched_valid_dimension: 
  forall pis ctxt vars n,
    PolIRs.PolyLang.wf_pprog (pis, ctxt, vars) ->
    (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars) <= n)%nat ->
    (forall pi, In pi pis ->
        poly_nrl (PolyLang.pi_schedule pi) <= n).
Proof. 
  intros pis ctxt vars n Hwf Hdim.
  unfold PolIRs.PolyLang.wf_pprog in Hwf.
  destruct Hwf as (_ & Hwf3).
  intros pi Hin. 
  pose proof (Hwf3 pi Hin) as Hwfpi.
  unfold PolIRs.PolyLang.wf_pinstr in Hwfpi. 
  destruct Hwfpi as (_ & _ & _ & Hsched_nrl & _).
  eapply Nat.le_trans.
  - exact Hsched_nrl.
  - eapply Nat.le_trans.
    + eapply PolIRs.PolyLang.pprog_current_dim_ge_pinstr; exact Hin.
    + exact Hdim.
Qed.

Lemma wf_pprog_implies_pis_witness_valid_dimension :
  forall pis ctxt vars n,
    PolIRs.PolyLang.wf_pprog (pis, ctxt, vars) ->
    (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars) <= n)%nat ->
    (forall pi, In pi pis ->
        (PointWitness.witness_current_point_dim (PolyLang.pi_point_witness pi)
         <= n)%nat).
Proof.
  intros pis ctxt vars n Hwf Hdim pi Hin.
  unfold PolIRs.PolyLang.wf_pprog in Hwf.
  destruct Hwf as (_ & Hwfpis).
  pose proof (Hwfpis pi Hin) as Hwfpi.
  unfold PolIRs.PolyLang.wf_pinstr in Hwfpi.
  destruct Hwfpi as (Hcur & Hcur_le & _).
  assert (Hdepth_le :
    PolIRs.PolyLang.pi_depth pi <= PolIRs.PolyLang.pinstr_current_dim ctxt pi).
  { lia. }
  eapply Nat.le_trans.
  - rewrite Hcur. exact Hdepth_le.
  - eapply Nat.le_trans.
    + eapply PolIRs.PolyLang.pprog_current_dim_ge_pinstr; exact Hin.
    + exact Hdim.
Qed.

(* currently, Loop.wf is a trivial placeholder *)
Lemma codegen_preserve_wf: 
  forall pol,
    WHEN loop <- codegen pol THEN 
    PolIRs.PolyLang.wf_pprog pol ->
    PolIRs.Loop.wf loop.
Proof.
  intros pol loop Hcodegen Hwf1.
  unfold PolIRs.Loop.wf. intros; trivial.
Qed.


Theorem codegen_correct: 
  forall pol st st', 
    WHEN loop <- codegen pol THEN
    PolIRs.PolyLang.wf_pprog pol ->
    PolIRs.PolyLang.pprog_current_dim pol = codegen_target_dim pol ->
    (forall pi,
        In pi (fst (fst pol)) ->
        PolIRs.PolyLang.current_env_dim_in_dim
          (codegen_target_dim pol)
          pi.(PolIRs.PolyLang.pi_point_witness) =
        length (snd (fst pol))) ->
    PolIRs.Loop.semantics loop st st' -> 
    PolIRs.PolyLang.semantics pol st st'.
Proof.
  intros. intros loop Hcodegen Hwf Htarget Henvdim Hsemt.
  unfold codegen in Hcodegen.
  destruct pol as ((pis & varctxt0) & vars0).
  bind_imp_destruct Hcodegen loop' Hgen.
  eapply mayReturn_pure in Hcodegen.
  rewrite <- Hcodegen in Hsemt.
  inversion Hsemt. rename env into envv.
  inversion H; subst.
  pose proof (PolIRs.Instr.init_env_samelen _ _ _ H2) as Henvlen.
  rewrite rev_length in Henvlen.
  assert (Hctxt_le_vars : (length ctxt <= length vars)%nat).
  {
    unfold PolIRs.PolyLang.wf_pprog in Hwf.
    tauto.
  }
  assert (Hctxt_le :
    (length ctxt
     <= Nat.max (length vars)
          (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))%nat).
  {
    eapply Nat.le_trans.
    - exact Hctxt_le_vars.
    - apply Nat.le_max_l.
  }
  assert (Hpoly :
    PolIRs.PolyLang.env_poly_semantics
      (rev envv)
      (Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))
      pis st st').
  {
    pose proof
      (complete_generate_many_preserve_sem
         (length ctxt)
         (Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))
         pis envv st st'
         Hctxt_le loop0 Hgen H3 (eq_sym Henvlen))
      as Hpoly_gen.
    assert (Hpis_dim :
      ASTGen.pis_have_dimension
        pis
        (Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))).
    {
      eapply wf_pprog_implies_pis_have_dimension; eauto.
      apply Nat.le_max_r.
    }
    assert (Hpis_envdim :
      forall pi, In pi pis ->
        PolIRs.PolyLang.current_env_dim_in_dim
          (Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))
          pi.(PolIRs.PolyLang.pi_point_witness) =
        length ctxt).
    {
      intros pi Hin.
      eapply Henvdim.
      exact Hin.
    }
    assert (Hpis_sched :
      forall pi, In pi pis ->
        (poly_nrl pi.(PolIRs.PolyLang.pi_schedule) <=
         Nat.max (length vars) (PolIRs.PolyLang.pprog_current_dim (pis, ctxt, vars)))%nat).
    {
      eapply wf_pprog_implies_pis_sched_valid_dimension; eauto.
      apply Nat.le_max_r.
    }
    specialize (Hpoly_gen Hpis_dim Hpis_envdim Hpis_sched).
    exact Hpoly_gen.
  }
  eapply PolIRs.PolyLang.PSemaIntro with (envv:=rev envv).
  - reflexivity.
  - exact H0.
  - exact H1.
  - exact H2.
  - rewrite Htarget. exact Hpoly.
Qed.

End CodeGen.
