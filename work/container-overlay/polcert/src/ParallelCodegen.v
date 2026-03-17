Require Import List.
Require Import Result.
Require Import String.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.
Require Import PolIRs.
Require Import PrepareCodegen.
Require Import ParallelLoop.
Require Import ParallelValidator.

Module ParallelCodegen (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module Loop := PolIRs.Loop.
Module PrepareCore := PrepareCodegen PolIRs.
Module ParallelLoop := ParallelLoop Instr.
Module ParallelValidator := ParallelValidator PolIRs.

Fixpoint tag_expr (e : Loop.expr) : ParallelLoop.expr :=
  match e with
  | Loop.Constant z => ParallelLoop.BaseLoop.Constant z
  | Loop.Sum e1 e2 => ParallelLoop.BaseLoop.Sum (tag_expr e1) (tag_expr e2)
  | Loop.Mult z e1 => ParallelLoop.BaseLoop.Mult z (tag_expr e1)
  | Loop.Div e1 z => ParallelLoop.BaseLoop.Div (tag_expr e1) z
  | Loop.Mod e1 z => ParallelLoop.BaseLoop.Mod (tag_expr e1) z
  | Loop.Var n => ParallelLoop.BaseLoop.Var n
  | Loop.Max e1 e2 => ParallelLoop.BaseLoop.Max (tag_expr e1) (tag_expr e2)
  | Loop.Min e1 e2 => ParallelLoop.BaseLoop.Min (tag_expr e1) (tag_expr e2)
  end.

Fixpoint tag_test (t : Loop.test) : ParallelLoop.test :=
  match t with
  | Loop.LE e1 e2 => ParallelLoop.BaseLoop.LE (tag_expr e1) (tag_expr e2)
  | Loop.EQ e1 e2 => ParallelLoop.BaseLoop.EQ (tag_expr e1) (tag_expr e2)
  | Loop.And t1 t2 => ParallelLoop.BaseLoop.And (tag_test t1) (tag_test t2)
  | Loop.Or t1 t2 => ParallelLoop.BaseLoop.Or (tag_test t1) (tag_test t2)
  | Loop.Not t1 => ParallelLoop.BaseLoop.Not (tag_test t1)
  | Loop.TConstantTest b => ParallelLoop.BaseLoop.TConstantTest b
  end.

Fixpoint erase_expr (e : ParallelLoop.expr) : Loop.expr :=
  match e with
  | ParallelLoop.BaseLoop.Constant z => Loop.Constant z
  | ParallelLoop.BaseLoop.Sum e1 e2 => Loop.Sum (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.Mult z e1 => Loop.Mult z (erase_expr e1)
  | ParallelLoop.BaseLoop.Div e1 z => Loop.Div (erase_expr e1) z
  | ParallelLoop.BaseLoop.Mod e1 z => Loop.Mod (erase_expr e1) z
  | ParallelLoop.BaseLoop.Var n => Loop.Var n
  | ParallelLoop.BaseLoop.Max e1 e2 => Loop.Max (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.Min e1 e2 => Loop.Min (erase_expr e1) (erase_expr e2)
  end.

Fixpoint erase_test (t : ParallelLoop.test) : Loop.test :=
  match t with
  | ParallelLoop.BaseLoop.LE e1 e2 => Loop.LE (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.EQ e1 e2 => Loop.EQ (erase_expr e1) (erase_expr e2)
  | ParallelLoop.BaseLoop.And t1 t2 => Loop.And (erase_test t1) (erase_test t2)
  | ParallelLoop.BaseLoop.Or t1 t2 => Loop.Or (erase_test t1) (erase_test t2)
  | ParallelLoop.BaseLoop.Not t1 => Loop.Not (erase_test t1)
  | ParallelLoop.BaseLoop.TConstantTest b => Loop.TConstantTest b
  end.

Lemma erase_tag_expr_eq :
  forall e,
    erase_expr (tag_expr e) = e.
Proof.
  induction e; simpl; try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Lemma erase_tag_test_eq :
  forall t,
    erase_test (tag_test t) = t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try rewrite ?erase_tag_expr_eq; reflexivity.
Qed.

Lemma map_erase_tag_expr_eq :
  forall es,
    List.map erase_expr (List.map tag_expr es) = es.
Proof.
  induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite erase_tag_expr_eq, IH. reflexivity.
Qed.

Fixpoint tag_loop_stmt_at (d : nat) (s : Loop.stmt) {struct s} : ParallelLoop.stmt
with tag_loop_stmts_at (d : nat) (ss : Loop.stmt_list) {struct ss} : ParallelLoop.stmt_list.
Proof.
  - destruct s; simpl.
    + exact (ParallelLoop.Loop ParallelLoop.SeqMode (Some d) (tag_expr e) (tag_expr e0) (tag_loop_stmt_at (S d) s)).
    + exact (ParallelLoop.Instr i (List.map tag_expr l)).
    + exact (ParallelLoop.Seq (tag_loop_stmts_at d s)).
    + exact (ParallelLoop.Guard (tag_test t) (tag_loop_stmt_at d s)).
  - destruct ss; simpl.
    + exact ParallelLoop.SNil.
    + exact (ParallelLoop.SCons (tag_loop_stmt_at d s) (tag_loop_stmts_at d ss)).
Defined.

Definition tag_loop (p : Loop.t) : ParallelLoop.t :=
  match p with
  | ((s, ctxt), vars) => (tag_loop_stmt_at 0 s, ctxt, vars)
  end.

Fixpoint erase_to_loop_stmt (s : ParallelLoop.stmt) {struct s} : Loop.stmt
with erase_to_loop_stmts (ss : ParallelLoop.stmt_list) {struct ss} : Loop.stmt_list.
Proof.
  - destruct s; simpl.
    + exact (Loop.Loop (erase_expr e) (erase_expr e0) (erase_to_loop_stmt s)).
    + exact (Loop.Instr i (List.map erase_expr l)).
    + exact (Loop.Seq (erase_to_loop_stmts s)).
    + exact (Loop.Guard (erase_test t) (erase_to_loop_stmt s)).
  - destruct ss; simpl.
    + exact Loop.SNil.
    + exact (Loop.SCons (erase_to_loop_stmt s) (erase_to_loop_stmts ss)).
Defined.

Definition erase_to_loop (p : ParallelLoop.t) : Loop.t :=
  match p with
  | ((s, ctxt), vars) => (erase_to_loop_stmt s, ctxt, vars)
  end.

Fixpoint tagged_from_depth_stmt (d : nat) (s : ParallelLoop.stmt) : Prop
with tagged_from_depth_stmts (d : nat) (ss : ParallelLoop.stmt_list) : Prop.
Proof.
  - destruct s; simpl.
    + exact (o = Some d /\ tagged_from_depth_stmt (S d) s).
    + exact True.
    + exact (tagged_from_depth_stmts d s).
    + exact (tagged_from_depth_stmt d s).
  - destruct ss; simpl.
    + exact True.
    + exact (tagged_from_depth_stmt d s /\ tagged_from_depth_stmts d ss).
Defined.

Definition tagged_from_top (p : ParallelLoop.t) : Prop :=
  match p with
  | ((s, _), _) => tagged_from_depth_stmt 0 s
  end.

Fixpoint tag_loop_stmt_tagged_from_depth
  (d : nat) (s : Loop.stmt) {struct s}
  : tagged_from_depth_stmt d (tag_loop_stmt_at d s)
with tag_loop_stmts_tagged_from_depth
  (d : nat) (ss : Loop.stmt_list) {struct ss}
  : tagged_from_depth_stmts d (tag_loop_stmts_at d ss).
Proof.
  - destruct s; simpl.
    + split; auto.
    + auto.
    + apply tag_loop_stmts_tagged_from_depth.
    + apply tag_loop_stmt_tagged_from_depth.
  - destruct ss; simpl.
    + auto.
    + split.
      * apply tag_loop_stmt_tagged_from_depth.
      * apply tag_loop_stmts_tagged_from_depth.
Qed.

Fixpoint erase_parallelize_dim_stmt_to_loop_eq
  (d : nat) (s : ParallelLoop.stmt) {struct s}
  : erase_to_loop_stmt (ParallelLoop.parallelize_dim_stmt d s) = erase_to_loop_stmt s
with erase_parallelize_dim_stmts_to_loop_eq
  (d : nat) (ss : ParallelLoop.stmt_list) {struct ss}
  : erase_to_loop_stmts (ParallelLoop.parallelize_dim_stmts d ss) = erase_to_loop_stmts ss.
Proof.
  - destruct s; simpl.
    + destruct l.
      * destruct o as [n|]; simpl; rewrite erase_parallelize_dim_stmt_to_loop_eq; reflexivity.
      * destruct o as [n|]; simpl; rewrite erase_parallelize_dim_stmt_to_loop_eq; reflexivity.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmts_to_loop_eq. reflexivity.
    + rewrite erase_parallelize_dim_stmt_to_loop_eq. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmt_to_loop_eq, erase_parallelize_dim_stmts_to_loop_eq.
      reflexivity.
Qed.

Lemma erase_parallelize_dim_to_loop_eq :
  forall d p,
    erase_to_loop (ParallelLoop.parallelize_dim d p) = erase_to_loop p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_parallelize_dim_stmt_to_loop_eq.
  reflexivity.
Qed.

Lemma erase_tag_loop_stmt_at_eq :
  forall d s,
    erase_to_loop_stmt (tag_loop_stmt_at d s) = s
with erase_tag_loop_stmts_at_eq :
  forall d ss,
    erase_to_loop_stmts (tag_loop_stmts_at d ss) = ss.
Proof.
  - intros d s. destruct s; simpl.
    + rewrite !erase_tag_expr_eq, erase_tag_loop_stmt_at_eq. reflexivity.
    + rewrite map_erase_tag_expr_eq. reflexivity.
    + rewrite erase_tag_loop_stmts_at_eq. reflexivity.
    + rewrite erase_tag_test_eq, erase_tag_loop_stmt_at_eq. reflexivity.
  - intros d ss. destruct ss; simpl.
    + reflexivity.
    + rewrite erase_tag_loop_stmt_at_eq, erase_tag_loop_stmts_at_eq. reflexivity.
Qed.

Lemma erase_tag_loop_eq :
  forall p,
    erase_to_loop (tag_loop p) = p.
Proof.
  intros [[s ctxt] vars]; simpl.
  rewrite erase_tag_loop_stmt_at_eq.
  reflexivity.
Qed.

Lemma erase_expr_eval_eq :
  forall env e,
    Loop.eval_expr env (erase_expr e) =
    ParallelLoop.BaseLoop.eval_expr env e.
Proof.
  induction e; simpl; try rewrite ?IHe, ?IHe1, ?IHe2; reflexivity.
Qed.

Lemma erase_expr_list_map_eval_eq :
  forall env es,
    List.map (Loop.eval_expr env) (List.map erase_expr es) =
    List.map (ParallelLoop.BaseLoop.eval_expr env) es.
Proof.
  induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite erase_expr_eval_eq, IH. reflexivity.
Qed.

Lemma erase_test_eval_eq :
  forall env t,
    Loop.eval_test env (erase_test t) =
    ParallelLoop.BaseLoop.eval_test env t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try rewrite ?erase_expr_eval_eq; reflexivity.
Qed.

Lemma iter_semantics_refine_exact :
  forall A (P Q : A -> Instr.State.t -> Instr.State.t -> Prop),
    forall xs st1 st2,
      Instr.IterSem.iter_semantics P xs st1 st2 ->
      (forall x stA stB, In x xs -> P x stA stB -> Q x stA stB) ->
      Instr.IterSem.iter_semantics Q xs st1 st2.
Proof.
  intros A P Q xs st1 st2 Hiter.
  induction Hiter; intros Hstep.
  - constructor.
  - econstructor.
    + eapply Hstep; eauto.
      left; reflexivity.
    + eapply IHHiter.
      intros y stA stB Hin HP.
      eapply Hstep; eauto.
      right; exact Hin.
Qed.

Scheme pl_stmt_mutind := Induction for ParallelLoop.stmt Sort Prop
with pl_stmts_mutind := Induction for ParallelLoop.stmt_list Sort Prop.
Combined Scheme pl_stmt_stmts_mutind from pl_stmt_mutind, pl_stmts_mutind.

Definition erase_stmt_sem_goal (s : ParallelLoop.stmt) : Prop :=
  forall env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics (ParallelLoop.erase_stmt s) env st1 st2 ->
    Loop.loop_semantics (erase_to_loop_stmt s) env st1 st2.

Definition erase_stmts_sem_goal (ss : ParallelLoop.stmt_list) : Prop :=
  forall env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics
      (ParallelLoop.BaseLoop.Seq (ParallelLoop.erase_stmt_list ss)) env st1 st2 ->
    Loop.loop_semantics (Loop.Seq (erase_to_loop_stmts ss)) env st1 st2.

Lemma erase_to_loop_stmt_semantics_mutual :
  (forall s, erase_stmt_sem_goal s) /\
  (forall ss, erase_stmts_sem_goal ss).
Proof.
  apply (pl_stmt_stmts_mutind erase_stmt_sem_goal erase_stmts_sem_goal).
  - intros mode od lb ub body IHbody env st1 st2 Hsem.
    inversion Hsem; subst.
    eapply Loop.LLoop.
    rewrite !erase_expr_eval_eq.
    lazymatch goal with
    | Hiter :
        Instr.IterSem.iter_semantics
          (fun x =>
             ParallelLoop.BaseLoop.loop_semantics
               (ParallelLoop.erase_stmt body) (x :: env)) _ _ _ |- _ =>
        pose proof Hiter as Hiter';
        eapply iter_semantics_refine_exact with
          (Q := fun x => Loop.loop_semantics (erase_to_loop_stmt body) (x :: env))
          in Hiter'
    end.
    + exact Hiter'.
    + intros x stA stB _ Hbody_sem.
      eapply IHbody; eauto.
  - intros i es env st1 st2 Hsem.
    inversion Hsem; subst.
    eapply Loop.LInstr.
    rewrite erase_expr_list_map_eval_eq.
    eauto.
  - intros ss IHss env st1 st2 Hsem.
    eapply IHss; eauto.
  - intros test body IHbody env st1 st2 Hsem.
    inversion Hsem; subst.
    + eapply Loop.LGuardTrue.
      * eapply IHbody; eauto.
      * rewrite erase_test_eval_eq. eauto.
    + eapply Loop.LGuardFalse.
      rewrite erase_test_eval_eq. eauto.
  - intros env st1 st2 Hsem.
    inversion Hsem; subst.
    constructor.
  - intros s IHs ss IHss env st1 st2 Hsem.
    inversion Hsem; subst.
    eapply Loop.LSeq.
    + eapply IHs; eauto.
    + eapply IHss; eauto.
Qed.

Lemma erase_to_loop_stmt_semantics :
  forall s env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics (ParallelLoop.erase_stmt s) env st1 st2 ->
    Loop.loop_semantics (erase_to_loop_stmt s) env st1 st2.
Proof.
  exact (proj1 erase_to_loop_stmt_semantics_mutual).
Qed.

Lemma erase_to_loop_stmts_semantics :
  forall ss env st1 st2,
    ParallelLoop.BaseLoop.loop_semantics
      (ParallelLoop.BaseLoop.Seq (ParallelLoop.erase_stmt_list ss)) env st1 st2 ->
    Loop.loop_semantics (Loop.Seq (erase_to_loop_stmts ss)) env st1 st2.
Proof.
  exact (proj2 erase_to_loop_stmt_semantics_mutual).
Qed.

Lemma erase_to_loop_semantics :
  forall p st1 st2,
    ParallelLoop.BaseLoop.semantics (ParallelLoop.erase_parallel p) st1 st2 ->
    Loop.semantics (erase_to_loop p) st1 st2.
Proof.
  intros [[s ctxt] vars] st1 st2 Hsem.
  inversion Hsem as [loop_ext loop ctxt' vars' env st1' st2' Heq Hcompat Hna Hinit Hloop];
    subst.
  inversion Heq; subst.
  econstructor; eauto.
  reflexivity.
  eapply erase_to_loop_stmt_semantics; eauto.
Qed.

Definition tagged_prepared_codegen
  (pp : PolyLang.t) : imp ParallelLoop.t :=
  BIND loop <- PrepareCore.prepared_codegen pp -;
  pure (tag_loop loop).

Record codegen_matches_current_dims
  (_pp : PolyLang.t) (pl : ParallelLoop.t) : Prop := {
  cmd_origin_tagged :
    tagged_from_top pl
}.

Definition annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (ParallelLoop.parallelize_dim cert.(ParallelValidator.certified_dim) pl).

Definition result_is_ok {A} (r : result A) : bool :=
  match r with
  | Okk _ => true
  | Err _ => false
  end.

Fixpoint all_es_safeb_stmt (s : ParallelLoop.stmt) : bool
with all_es_safeb_stmts (ss : ParallelLoop.stmt_list) : bool.
Proof.
  - destruct s; simpl.
    + exact (all_es_safeb_stmt s).
    + exact (result_is_ok (ParallelLoop.BaseLoop.exprlist_to_aff l)).
    + exact (all_es_safeb_stmts s).
    + exact (all_es_safeb_stmt s).
  - destruct ss; simpl.
    + exact true.
    + exact (all_es_safeb_stmt s && all_es_safeb_stmts ss).
Defined.

Definition all_es_safeb (p : ParallelLoop.t) : bool :=
  match p with
  | ((s, _), _) => all_es_safeb_stmt s
  end.

Lemma all_es_safeb_stmt_sound :
  forall s,
    all_es_safeb_stmt s = true ->
    ParallelLoop.trace_safe_stmt s
with all_es_safeb_stmts_sound :
  forall ss,
    all_es_safeb_stmts ss = true ->
    ParallelLoop.trace_safe_stmts ss.
Proof.
  - intros s Hsafe.
    destruct s; simpl in *.
    + eapply all_es_safeb_stmt_sound; eauto.
    + destruct (ParallelLoop.BaseLoop.exprlist_to_aff l) eqn:Haff;
        inversion Hsafe; subst; eauto.
    + eapply all_es_safeb_stmts_sound; eauto.
    + eapply all_es_safeb_stmt_sound; eauto.
  - intros ss Hsafe.
    destruct ss; simpl in *.
    + constructor.
    + rewrite andb_true_iff in Hsafe.
      destruct Hsafe as [Hs Hss].
      split.
      * eapply all_es_safeb_stmt_sound; eauto.
      * eapply all_es_safeb_stmts_sound; eauto.
Qed.

Lemma all_es_safeb_sound :
  forall p,
    all_es_safeb p = true ->
    ParallelLoop.trace_safe p.
Proof.
  intros [[s ctxt] vars] Hsafe; simpl in *.
  eapply all_es_safeb_stmt_sound; eauto.
Qed.

Definition checked_annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp (result ParallelLoop.t) :=
  BIND pl <- annotated_codegen pp cert -;
  if all_es_safeb pl then pure (Okk pl)
  else pure (Err "Annotated parallel codegen produced non-affine instruction trace loop"%string).

Lemma tagged_prepared_codegen_matches :
  forall pp pl,
    mayReturn (tagged_prepared_codegen pp) pl ->
    codegen_matches_current_dims pp pl.
Proof.
  intros pp pl Hgen.
  unfold tagged_prepared_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [loop [Hprep Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  constructor.
  destruct loop as [[s ctxt] vars]; simpl.
  apply tag_loop_stmt_tagged_from_depth.
Qed.

Lemma tagged_prepared_codegen_erase_eq :
  forall pp pl,
    mayReturn (tagged_prepared_codegen pp) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp pl Hgen.
  unfold tagged_prepared_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [loop [Hprep Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  exists loop.
  split; auto.
  simpl.
  apply erase_tag_loop_eq.
Qed.

Lemma annotated_codegen_erase_eq :
  forall pp cert pl,
    mayReturn (annotated_codegen pp cert) pl ->
    exists loop,
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      erase_to_loop pl = loop.
Proof.
  intros pp cert pl Hgen.
  unfold annotated_codegen in Hgen.
  apply mayReturn_bind in Hgen.
  destruct Hgen as [tagged [Htag Hpure]].
  apply mayReturn_pure in Hpure.
  subst pl.
  pose proof (tagged_prepared_codegen_erase_eq pp tagged Htag) as Herase.
  destruct Herase as [loop [Hprep Herase]].
  exists loop.
  split; auto.
  rewrite erase_parallelize_dim_to_loop_eq.
  exact Herase.
Qed.

Lemma annotated_codegen_refines_prepared_codegen :
  forall pp cert pl st st',
    mayReturn (annotated_codegen pp cert) pl ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists loop st'',
      mayReturn (PrepareCore.prepared_codegen pp) loop /\
      Loop.semantics loop st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pp cert [[s ctxt] vars] st st' Hgen Hsafe Hsem.
  pose proof (annotated_codegen_erase_eq pp cert ((s, ctxt), vars) Hgen)
    as [loop [Hprep Herase]].
  pose proof (ParallelLoop.semantics_refines_erased ((s, ctxt), vars) st st' Hsafe Hsem)
    as [st'' [Herased Heq]].
  exists loop, st''.
  split; [exact Hprep|].
  split.
  - rewrite <- Herase.
    eapply erase_to_loop_semantics.
    exact Herased.
  - exact Heq.
Qed.

Theorem annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn (annotated_codegen (PolyLang.current_view_pprog pol) cert) pl ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.trace_safe pl ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsafe Hsem.
  destruct
    (annotated_codegen_refines_prepared_codegen
       (PolyLang.current_view_pprog pol) cert pl st st'
       Hcodegen Hsafe Hsem)
    as [loop [st'' [Hprep [Hloop Heq]]]].
  exists st''.
  split.
  - eapply PrepareCore.prepared_codegen_correct_general; eauto.
  - exact Heq.
Qed.

Lemma checked_annotated_codegen_ok_inv :
  forall pp cert pl,
    mayReturn (checked_annotated_codegen pp cert) (Okk pl) ->
    mayReturn (annotated_codegen pp cert) pl /\
    ParallelLoop.trace_safe pl.
Proof.
  intros pp cert pl Hcodegen.
  unfold checked_annotated_codegen in Hcodegen.
  apply mayReturn_bind in Hcodegen.
  destruct Hcodegen as [pl' [Hann Hret]].
  destruct (all_es_safeb pl') eqn:Hsafe.
  - apply mayReturn_pure in Hret.
    inversion Hret; subst pl'.
    split.
    + exact Hann.
    + eapply all_es_safeb_sound; eauto.
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

Theorem checked_annotated_codegen_correct_general :
  forall pol cert pl st st',
    mayReturn (checked_annotated_codegen (PolyLang.current_view_pprog pol) cert) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\
      Instr.State.eq st' st''.
Proof.
  intros pol cert pl st st' Hcodegen Hwf Hsem.
  destruct (checked_annotated_codegen_ok_inv
              (PolyLang.current_view_pprog pol) cert pl Hcodegen)
    as [Hann Hsafe].
  eapply annotated_codegen_correct_general; eauto.
Qed.

End ParallelCodegen.
