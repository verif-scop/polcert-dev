Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Result.
Import ListNotations.

Require Import InstrTy.
Require Import Loop.
Require Import Misc.
Require Import LibTactics.

Open Scope Z_scope.
Open Scope list_scope.

Module ParallelLoop (IInstr : INSTR).

Module Instr := IInstr.
Module BaseLoop := Loop IInstr.
Module ILSema := BaseLoop.ILSema.
Module Ty := IInstr.Ty.

Definition ident := IInstr.ident.
Definition instr := IInstr.t.
Definition mem := IInstr.State.t.
Definition expr := BaseLoop.expr.
Definition test := BaseLoop.test.
Definition InstrPoint := ILSema.InstrPoint.

Inductive loop_mode :=
| SeqMode
| ParMode.

Inductive stmt :=
| Loop : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt
| Seq : stmt_list -> stmt
| Guard : test -> stmt -> stmt
with stmt_list :=
| SNil : stmt_list
| SCons : stmt -> stmt_list -> stmt_list.

Definition t := (stmt * list ident * list (ident * Ty.t))%type.

Fixpoint erase_stmt (s : stmt) : BaseLoop.stmt :=
  match s with
  | Loop _ _ lb ub body => BaseLoop.Loop lb ub (erase_stmt body)
  | Instr i es => BaseLoop.Instr i es
  | Seq ss => BaseLoop.Seq (erase_stmt_list ss)
  | Guard tst body => BaseLoop.Guard tst (erase_stmt body)
  end
with erase_stmt_list (ss : stmt_list) : BaseLoop.stmt_list :=
  match ss with
  | SNil => BaseLoop.SNil
  | SCons s ss' => BaseLoop.SCons (erase_stmt s) (erase_stmt_list ss')
  end.

Definition erase_parallel (p : t) : BaseLoop.t :=
  let '(s, ctxt, vars) := p in
  (erase_stmt s, ctxt, vars).

Fixpoint parallelize_dim_stmt (d : nat) (s : stmt) : stmt :=
  match s with
  | Loop SeqMode (Some d') lb ub body =>
      Loop (if Nat.eqb d d' then ParMode else SeqMode)
           (Some d')
           lb
           ub
           (parallelize_dim_stmt d body)
  | Loop mode od lb ub body =>
      Loop mode od lb ub (parallelize_dim_stmt d body)
  | Instr i es => Instr i es
  | Seq ss => Seq (parallelize_dim_stmts d ss)
  | Guard tst body => Guard tst (parallelize_dim_stmt d body)
  end
with parallelize_dim_stmts (d : nat) (ss : stmt_list) : stmt_list :=
  match ss with
  | SNil => SNil
  | SCons s ss' => SCons (parallelize_dim_stmt d s) (parallelize_dim_stmts d ss')
  end.

Definition parallelize_dim (d : nat) (p : t) : t :=
  let '(s, ctxt, vars) := p in
  (parallelize_dim_stmt d s, ctxt, vars).

Fixpoint of_loop_stmt (s : BaseLoop.stmt) : stmt :=
  match s with
  | BaseLoop.Loop lb ub body => Loop SeqMode None lb ub (of_loop_stmt body)
  | BaseLoop.Instr i es => Instr i es
  | BaseLoop.Seq ss => Seq (of_loop_stmt_list ss)
  | BaseLoop.Guard tst body => Guard tst (of_loop_stmt body)
  end
with of_loop_stmt_list (ss : BaseLoop.stmt_list) : stmt_list :=
  match ss with
  | BaseLoop.SNil => SNil
  | BaseLoop.SCons s ss' => SCons (of_loop_stmt s) (of_loop_stmt_list ss')
  end.

Definition of_loop (p : BaseLoop.t) : t :=
  let '(s, ctxt, vars) := p in
  (of_loop_stmt s, ctxt, vars).

Fixpoint all_origin_none_stmt (s : stmt) : Prop :=
  match s with
  | Loop _ od _ _ body => od = None /\ all_origin_none_stmt body
  | Instr _ _ => True
  | Seq ss => all_origin_none_stmts ss
  | Guard _ body => all_origin_none_stmt body
  end
with all_origin_none_stmts (ss : stmt_list) : Prop :=
  match ss with
  | SNil => True
  | SCons s ss' => all_origin_none_stmt s /\ all_origin_none_stmts ss'
  end.

Definition all_origin_none (p : t) : Prop :=
  let '(s, _, _) := p in all_origin_none_stmt s.

Inductive seq_trace : stmt -> list Z -> list InstrPoint -> Prop :=
| STInstr : forall i es env,
    seq_trace (Instr i es) env [BaseLoop.mk_instr_point i es env]
| STSeqStmt : forall env sts tr,
    seq_traces sts env tr ->
    seq_trace (Seq sts) env tr
| STGuardTrue : forall env tst st tr,
    BaseLoop.eval_test env tst = true ->
    seq_trace st env tr ->
    seq_trace (Guard tst st) env tr
| STGuardFalse : forall env tst st,
    BaseLoop.eval_test env tst = false ->
    seq_trace (Guard tst st) env []
| STLoop : forall mode od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    seq_trace (Loop mode od lb ub body) env tr
with seq_traces : stmt_list -> list Z -> list InstrPoint -> Prop :=
| STTracesNil : forall env,
    seq_traces SNil env []
| STTracesCons : forall env st sts tr1 tr2,
    seq_trace st env tr1 ->
    seq_traces sts env tr2 ->
    seq_traces (SCons st sts) env (tr1 ++ tr2).

Inductive interleave_family : list (list InstrPoint) -> list InstrPoint -> Prop :=
| IF_nil :
    interleave_family [] []
| IF_skip_nil : forall trs out,
    interleave_family trs out ->
    interleave_family ([] :: trs) out
| IF_take : forall pre x xs post out,
    interleave_family (pre ++ xs :: post) out ->
    interleave_family (pre ++ (x :: xs) :: post) (x :: out).

Definition family_ordered_permutable (trs : list (list InstrPoint)) : Prop :=
  forall pre1 tr1 pre2 tr2 post ip1 ip2,
    trs = pre1 ++ tr1 :: pre2 ++ tr2 :: post ->
    In ip1 tr1 ->
    In ip2 tr2 ->
    ILSema.Permutable ip1 ip2.

Inductive interleave_safe : list (list InstrPoint) -> list InstrPoint -> Prop :=
| IS_nil :
    interleave_safe [] []
| IS_skip_nil : forall trs out,
    interleave_safe trs out ->
    interleave_safe ([] :: trs) out
| IS_take : forall pre x xs post out,
    (forall y, In y (concat pre) -> ILSema.Permutable y x) ->
    interleave_safe (pre ++ xs :: post) out ->
    interleave_safe (pre ++ (x :: xs) :: post) (x :: out).

Inductive par_trace : stmt -> list Z -> list InstrPoint -> Prop :=
| PTInstr : forall i es env,
    par_trace (Instr i es) env [BaseLoop.mk_instr_point i es env]
| PTSeqStmt : forall env sts tr,
    par_traces sts env tr ->
    par_trace (Seq sts) env tr
| PTGuardTrue : forall env tst st tr,
    BaseLoop.eval_test env tst = true ->
    par_trace st env tr ->
    par_trace (Guard tst st) env tr
| PTGuardFalse : forall env tst st,
    BaseLoop.eval_test env tst = false ->
    par_trace (Guard tst st) env []
| PTLoopSeq : forall od lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
    tr = concat trs ->
    par_trace (Loop SeqMode od lb ub body) env tr
| PTLoopPar : forall d lb ub body env zs trs tr,
    zs = Zrange (BaseLoop.eval_expr env lb) (BaseLoop.eval_expr env ub) ->
    Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
    interleave_safe trs tr ->
    par_trace (Loop ParMode (Some d) lb ub body) env tr
with par_traces : stmt_list -> list Z -> list InstrPoint -> Prop :=
| PTTracesNil : forall env,
    par_traces SNil env []
| PTTracesCons : forall env st sts tr1 tr2,
    par_trace st env tr1 ->
    par_traces sts env tr2 ->
    par_traces (SCons st sts) env (tr1 ++ tr2).

Definition loop_semantics (s : stmt) (env : list Z) (mem1 mem2 : mem) : Prop :=
  exists tr,
    par_trace s env tr /\
    ILSema.instr_point_list_semantics tr mem1 mem2.

Inductive semantics : t -> mem -> mem -> Prop :=
| PLSemaIntro : forall loop_ext loop ctxt vars env mem1 mem2,
    loop_ext = (loop, ctxt, vars) ->
    IInstr.Compat vars mem1 ->
    IInstr.NonAlias mem1 ->
    IInstr.InitEnv ctxt (rev env) mem1 ->
    loop_semantics loop env mem1 mem2 ->
    semantics loop_ext mem1 mem2.

Fixpoint trace_safe_stmt (s : stmt) : Prop :=
  match s with
  | Loop _ _ _ _ body => trace_safe_stmt body
  | Instr _ es => exists affs, BaseLoop.exprlist_to_aff es = Okk affs
  | Seq ss => trace_safe_stmts ss
  | Guard _ body => trace_safe_stmt body
  end
with trace_safe_stmts (ss : stmt_list) : Prop :=
  match ss with
  | SNil => True
  | SCons s ss' => trace_safe_stmt s /\ trace_safe_stmts ss'
  end.

Definition trace_safe (p : t) : Prop :=
  let '(s, _, _) := p in trace_safe_stmt s.

Fixpoint erase_parallelize_dim_stmt_eq_rec
  (d : nat) (s : stmt) {struct s}
  : erase_stmt (parallelize_dim_stmt d s) = erase_stmt s
with erase_parallelize_dim_stmts_eq_rec
  (d : nat) (ss : stmt_list) {struct ss}
  : erase_stmt_list (parallelize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - destruct s; simpl.
    + destruct l.
      * destruct o as [n|].
        -- destruct (Nat.eqb d n); simpl; rewrite erase_parallelize_dim_stmt_eq_rec; reflexivity.
        -- simpl. rewrite erase_parallelize_dim_stmt_eq_rec. reflexivity.
      * destruct o as [n|]; simpl; rewrite erase_parallelize_dim_stmt_eq_rec; reflexivity.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmts_eq_rec. reflexivity.
    + rewrite erase_parallelize_dim_stmt_eq_rec. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_parallelize_dim_stmt_eq_rec, erase_parallelize_dim_stmts_eq_rec.
      reflexivity.
Qed.

Lemma erase_parallelize_dim_stmt_eq :
  forall d s,
    erase_stmt (parallelize_dim_stmt d s) = erase_stmt s
with erase_parallelize_dim_stmts_eq :
  forall d ss,
    erase_stmt_list (parallelize_dim_stmts d ss) = erase_stmt_list ss.
Proof.
  - intros d s.
    apply erase_parallelize_dim_stmt_eq_rec.
  - intros d ss.
    apply erase_parallelize_dim_stmts_eq_rec.
Qed.

Lemma erase_parallelize_dim_eq :
  forall d p,
    erase_parallel (parallelize_dim d p) = erase_parallel p.
Proof.
  intros d [[s ctxt] vars]; simpl.
  rewrite erase_parallelize_dim_stmt_eq.
  reflexivity.
Qed.

Fixpoint erase_of_loop_stmt_eq_rec
  (s : BaseLoop.stmt) {struct s}
  : erase_stmt (of_loop_stmt s) = s
with erase_of_loop_stmt_list_eq_rec
  (ss : BaseLoop.stmt_list) {struct ss}
  : erase_stmt_list (of_loop_stmt_list ss) = ss.
Proof.
  - destruct s; simpl.
    + rewrite erase_of_loop_stmt_eq_rec. reflexivity.
    + reflexivity.
    + rewrite erase_of_loop_stmt_list_eq_rec. reflexivity.
    + rewrite erase_of_loop_stmt_eq_rec. reflexivity.
  - destruct ss; simpl.
    + reflexivity.
    + rewrite erase_of_loop_stmt_eq_rec, erase_of_loop_stmt_list_eq_rec. reflexivity.
Qed.

Lemma erase_of_loop_stmt_eq :
  forall s,
    erase_stmt (of_loop_stmt s) = s
with erase_of_loop_stmt_list_eq :
  forall ss,
    erase_stmt_list (of_loop_stmt_list ss) = ss.
Proof.
  - intros s.
    apply erase_of_loop_stmt_eq_rec.
  - intros ss.
    apply erase_of_loop_stmt_list_eq_rec.
Qed.

Lemma erase_of_loop_eq :
  forall p,
    erase_parallel (of_loop p) = p.
Proof.
  intros [[s ctxt] vars]; simpl.
  rewrite erase_of_loop_stmt_eq.
  reflexivity.
Qed.

Fixpoint of_loop_stmt_all_origin_none_rec
  (s : BaseLoop.stmt) {struct s}
  : all_origin_none_stmt (of_loop_stmt s)
with of_loop_stmt_list_all_origin_none_rec
  (ss : BaseLoop.stmt_list) {struct ss}
  : all_origin_none_stmts (of_loop_stmt_list ss).
Proof.
  - destruct s; simpl.
    + split; auto.
    + auto.
    + apply of_loop_stmt_list_all_origin_none_rec.
    + apply of_loop_stmt_all_origin_none_rec.
  - destruct ss; simpl.
    + auto.
    + split.
      * apply of_loop_stmt_all_origin_none_rec.
      * apply of_loop_stmt_list_all_origin_none_rec.
Qed.

Lemma of_loop_stmt_all_origin_none :
  forall s,
    all_origin_none_stmt (of_loop_stmt s)
with of_loop_stmt_list_all_origin_none :
  forall ss,
    all_origin_none_stmts (of_loop_stmt_list ss).
Proof.
  - intros s.
    apply of_loop_stmt_all_origin_none_rec.
  - intros ss.
    apply of_loop_stmt_list_all_origin_none_rec.
Qed.

Lemma of_loop_all_origin_none :
  forall p,
    all_origin_none (of_loop p).
Proof.
  intros [[s ctxt] vars]; simpl.
  apply of_loop_stmt_all_origin_none.
Qed.

Lemma instr_point_sema_stable_under_state_eq :
  forall ip st1 st2 st1' st2',
    Instr.State.eq st1 st1' ->
    Instr.State.eq st2 st2' ->
    ILSema.instr_point_sema ip st1 st2 ->
    ILSema.instr_point_sema ip st1' st2'.
Proof.
  intros ip st1 st2 st1' st2' Heq1 Heq2 Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  econstructor.
  eapply Instr.instr_semantics_stable_under_state_eq; eauto.
Qed.

Lemma instr_point_sema_preserve_nonalias :
  forall ip st1 st2,
    Instr.NonAlias st1 ->
    ILSema.instr_point_sema ip st1 st2 ->
    Instr.NonAlias st2.
Proof.
  intros ip st1 st2 Hna Hsem.
  inversion Hsem as [wcs rcs Hinstr]; subst.
  eapply Instr.sema_prsv_nonalias; eauto.
Qed.

Lemma instr_point_list_semantics_nil_inv :
  forall st1 st2,
    ILSema.instr_point_list_semantics [] st1 st2 ->
    Instr.State.eq st1 st2.
Proof.
  intros st1 st2 Hsem.
  inversion Hsem; subst; assumption.
Qed.

Lemma instr_point_list_semantics_singleton_inv :
  forall ip st1 st2,
    ILSema.instr_point_list_semantics [ip] st1 st2 ->
    ILSema.instr_point_sema ip st1 st2.
Proof.
  intros ip st1 st2 Hsem.
  inversion Hsem as [|st1' stmid st2' ip' il Hip Hnil]; subst.
  simpl in *.
  inversion Hnil; subst.
  eapply instr_point_sema_stable_under_state_eq; eauto using Instr.State.eq_refl.
Qed.

Lemma instr_point_list_semantics_app_inv :
  forall l1 l2 st1 st3,
    ILSema.instr_point_list_semantics (l1 ++ l2) st1 st3 ->
    exists st2,
      ILSema.instr_point_list_semantics l1 st1 st2 /\
      ILSema.instr_point_list_semantics l2 st2 st3.
Proof.
  induction l1 as [|ip l1 IH]; intros l2 st1 st3 Hsem.
  - exists st1.
    split.
    + constructor. apply Instr.State.eq_refl.
    + simpl in Hsem. exact Hsem.
  - simpl in Hsem.
    inversion Hsem as [|st1' stmid st3' ip' il Hip Htail]; subst.
    specialize (IH l2 stmid st3 Htail) as [st2 [Hleft Hright]].
    exists st2.
    split.
    + econstructor; eauto.
    + exact Hright.
Qed.

Lemma base_loop_semantics_aux_implies_loop_semantics :
  forall s env mem1 mem2,
    BaseLoop.loop_semantics_aux s env mem1 mem2 ->
    BaseLoop.loop_semantics s env mem1 mem2.
Proof.
  refine
    (BaseLoop.loop_semantics_aux_mutual_ind
       (fun s env mem1 mem2 _ => BaseLoop.loop_semantics s env mem1 mem2)
       (fun zs s env mem1 mem2 _ =>
          Instr.IterSem.iter_semantics
            (fun x => BaseLoop.loop_semantics s (x :: env))
            zs mem1 mem2)
       _ _ _ _ _ _ _ _).
  - intros i es env mem1 mem2 wcs rcs Hinstr.
    eapply BaseLoop.LInstr; eauto.
  - intros env mem.
    apply BaseLoop.LSeqEmpty.
  - intros env st sts mem1 mem2 mem3 l Hst l0 Hsts.
    eapply BaseLoop.LSeq; eauto.
  - intros env t st mem1 mem2 Heval l Hst.
    eapply BaseLoop.LGuardTrue; eauto.
  - intros env t st mem Heval.
    eapply BaseLoop.LGuardFalse; eauto.
  - intros env lb ub st mem1 mem2 l Hiter.
    eapply BaseLoop.LLoop; eauto.
  - intros st env mem.
    apply Instr.IterSem.IDone.
  - intros x xs st env mem1 mem2 mem3 l Hhead l0 Htail.
    econstructor; eauto.
Qed.

Lemma base_loop_semantics_aux_list_implies_iter :
  forall zs s env mem1 mem2,
    BaseLoop.loop_semantics_aux_list zs s env mem1 mem2 ->
    Instr.IterSem.iter_semantics
      (fun x => BaseLoop.loop_semantics s (x :: env))
      zs mem1 mem2.
Proof.
  refine
    (BaseLoop.loop_semantics_aux_list_mutual_ind
       (fun s env mem1 mem2 _ => BaseLoop.loop_semantics s env mem1 mem2)
       (fun zs s env mem1 mem2 _ =>
          Instr.IterSem.iter_semantics
            (fun x => BaseLoop.loop_semantics s (x :: env))
            zs mem1 mem2)
       _ _ _ _ _ _ _ _).
  - intros i es env mem1 mem2 wcs rcs Hinstr.
    eapply BaseLoop.LInstr; eauto.
  - intros env mem.
    apply BaseLoop.LSeqEmpty.
  - intros env st sts mem1 mem2 mem3 l Hst l0 Hsts.
    eapply BaseLoop.LSeq; eauto.
  - intros env t st mem1 mem2 Heval l Hst.
    eapply BaseLoop.LGuardTrue; eauto.
  - intros env t st mem Heval.
    eapply BaseLoop.LGuardFalse; eauto.
  - intros env lb ub st mem1 mem2 l Hiter.
    eapply BaseLoop.LLoop; eauto.
  - intros st env mem.
    apply Instr.IterSem.IDone.
  - intros x xs st env mem1 mem2 mem3 l Hhead l0 Htail.
    econstructor; eauto.
Qed.

Lemma base_loop_instance_list_implies_loop_semantics :
  forall s env il mem1 mem2,
    BaseLoop.loop_instance_list_semantics s env il mem1 mem2 ->
    BaseLoop.loop_semantics s env mem1 mem2.
Proof.
  intros s env il mem1 mem2 Hinst.
  eapply base_loop_semantics_aux_implies_loop_semantics.
  eapply BaseLoop.instance_list_implies_loop_semantics_aux; eauto.
Qed.

Lemma seq_trace_forall2_refines_erased :
  forall body env,
    (forall env' tr mem1 mem2,
       trace_safe_stmt body ->
       seq_trace body env' tr ->
       ILSema.instr_point_list_semantics tr mem1 mem2 ->
       exists mem2',
         BaseLoop.loop_semantics (erase_stmt body) env' mem1 mem2' /\
         Instr.State.eq mem2 mem2') ->
    forall zs trs mem1 mem2,
      trace_safe_stmt body ->
      Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
      ILSema.instr_point_list_semantics (concat trs) mem1 mem2 ->
      exists mem2',
        Instr.IterSem.iter_semantics
          (fun z => BaseLoop.loop_semantics (erase_stmt body) (z :: env))
          zs mem1 mem2' /\
        Instr.State.eq mem2 mem2'.
Proof.
  intros body env Hbody zs trs mem1 mem2 Hsafe_body Hfor.
  revert mem1 mem2 Hsafe_body.
  induction Hfor as [|z tr zs' trs' Htri Hfor' IHfor'];
    intros mem1 mem2 Hsafe_body Hsem_concat.
  - simpl in Hsem_concat.
    exists mem1.
    split.
    + constructor.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem_concat.
    eapply instr_point_list_semantics_app_inv in Hsem_concat.
    destruct Hsem_concat as [mem_mid [Hsem_head Hsem_tail]].
    pose proof
      (Hbody (z :: env) tr mem1 mem_mid Hsafe_body Htri Hsem_head)
      as [mem_mid' [Hbody_sem Heq_mid]].
    pose proof
      (ILSema.instr_point_list_sema_stable_under_state_eq
         (concat trs') mem_mid mem2 mem_mid' mem2
         Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
      as Hsem_tail'.
    pose proof (IHfor' mem_mid' mem2 Hsafe_body Hsem_tail')
      as [mem2' [Hrest_sem Heq_tail]].
    exists mem2'.
    split.
    + eapply Instr.IterSem.IProgress.
      * exact Hbody_sem.
      * exact Hrest_sem.
    + exact Heq_tail.
Qed.

Lemma seq_trace_refines_erased_stmt :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'
with seq_trace_refines_erased_stmts :
  forall ss env tr mem1 mem2,
    trace_safe_stmts ss ->
    seq_traces ss env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (BaseLoop.Seq (erase_stmt_list ss)) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  - intros s.
    induction s as [mode od lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace as
          [| | | | mode' od' lb' ub' body' env' zs trs tr' Hzs Hfor Hconcat];
        subst.
      match goal with
      | Hfor0 :
          Forall2 (fun z tri => seq_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
          pose proof
            (seq_trace_forall2_refines_erased
               body env IHbody zs0 trs0 mem1 mem2 Hsafe Hfor0 Hsem)
            as [mem2' [Hloop_sem Heq]]
      end.
      exists mem2'. split.
      * econstructor. exact Hloop_sem.
      * exact Heq.
    + inversion Htrace; subst.
      simpl in Hsafe.
      pose proof (instr_point_list_semantics_singleton_inv _ _ _ Hsem) as Hip.
      inversion Hip as [wcs rcs Hinstr]; subst.
      unfold BaseLoop.mk_instr_point in Hinstr.
      destruct Hsafe as [affs Haff].
      rewrite Haff in Hinstr.
      simpl in Hinstr.
      pose proof (BaseLoop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      exists mem2.
      split.
      * eapply BaseLoop.LInstr with (wcs := wcs) (rcs := rcs).
        rewrite <- Haff_ok in Hinstr.
        exact Hinstr.
      * apply Instr.State.eq_refl.
    + inversion Htrace; subst.
      eapply seq_trace_refines_erased_stmts; eauto.
    + inversion Htrace as
          [| | env' tst st tr' Heval Hbodytrace | env' tst st Heval |];
        subst; simpl in Hsafe.
      * pose proof (IHbody env tr mem1 mem2 Hsafe Hbodytrace Hsem)
          as [mem2' [Hbody_sem Heq]].
        exists mem2'.
        split; [eapply BaseLoop.LGuardTrue; eauto | exact Heq].
      * exists mem1.
        split;
          [eapply BaseLoop.LGuardFalse; eauto
          | eapply Instr.State.eq_sym;
            eapply instr_point_list_semantics_nil_inv; eauto].
  - intros ss.
    induction ss as [|s ss IHss']; intros env tr mem1 mem2 Hsafe Htrace Hsem.
    + inversion Htrace; subst.
      exists mem1.
      split;
        [constructor
        | eapply Instr.State.eq_sym;
          eapply instr_point_list_semantics_nil_inv; eauto].
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hsafe.
      destruct Hsafe as [Hsafe_s Hsafe_ss].
      eapply instr_point_list_semantics_app_inv in Hsem.
      destruct Hsem as [mem_mid [Hsem_head Hsem_tail]].
      pose proof
        (seq_trace_refines_erased_stmt
           s env tr1 mem1 mem_mid Hsafe_s Hst Hsem_head)
        as [mem_mid' [Hs_sem Heq_mid]].
      pose proof
        (ILSema.instr_point_list_sema_stable_under_state_eq
           tr2 mem_mid mem2 mem_mid' mem2
           Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
        as Hsem_tail'.
      pose proof
        (IHss' env tr2 mem_mid' mem2 Hsafe_ss Hsts Hsem_tail')
        as [mem2' [Hss_sem Heq_tail]].
      exists mem2'.
      split.
      * econstructor; eauto.
      * eapply Instr.State.eq_trans.
        -- exact Heq_tail.
        -- apply Instr.State.eq_refl.
Qed.

Lemma seq_trace_refines_erased :
  forall s env tr mem1 mem2,
    trace_safe_stmt s ->
    seq_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros. eapply seq_trace_refines_erased_stmt; eauto.
Qed.

Lemma instr_point_list_semantics_swap_adj :
  forall ip1 ip2 rest st1 st4,
    Instr.NonAlias st1 ->
    ILSema.Permutable ip1 ip2 ->
    ILSema.instr_point_list_semantics (ip1 :: ip2 :: rest) st1 st4 ->
    exists st4',
      ILSema.instr_point_list_semantics (ip2 :: ip1 :: rest) st1 st4' /\
      Instr.State.eq st4 st4'.
Proof.
  intros ip1 ip2 rest st1 st4 Hna Hperm Hsem.
  inversion Hsem as [|st1' st2 st4' ip1' l1 Hip1 Htail]; subst.
  inversion Htail as [|st2' st3 st4'' ip2' l2 Hip2 Hrest]; subst.
  unfold ILSema.Permutable in Hperm.
  specialize (Hperm st1 Hna).
  destruct Hperm as [Hfwd _].
  destruct (Hfwd _ _ Hip1 Hip2) as (st2'' & st3' & Hip2' & Hip1' & Heq3).
  pose proof
    (ILSema.instr_point_list_sema_stable_under_state_eq
       rest st3 st4 st3' st4
       Hrest Heq3 (Instr.State.eq_refl st4))
    as Hrest'.
  exists st4.
  split.
  - econstructor.
    + exact Hip2'.
    + econstructor.
      * exact Hip1'.
      * exact Hrest'.
  - apply Instr.State.eq_refl.
Qed.

Lemma move_front_permutable :
  forall prefix x rest st1 st2,
    Instr.NonAlias st1 ->
    (forall y, In y prefix -> ILSema.Permutable y x) ->
    ILSema.instr_point_list_semantics (prefix ++ x :: rest) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (x :: prefix ++ rest) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  induction prefix as [|y prefix IH]; intros x rest st1 st2 Hna Hperm Hsem.
  - simpl in *.
    exists st2.
    split; [exact Hsem | apply Instr.State.eq_refl].
  - simpl in Hsem.
    inversion Hsem as [|st1' stmid st2' ip' il Hip Htail]; subst.
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    assert (Hperm_tail : forall y0, In y0 prefix -> ILSema.Permutable y0 x).
    {
      intros y0 Hin.
      apply Hperm.
      right; exact Hin.
    }
    pose proof (IH x rest stmid st2 Hna_mid Hperm_tail Htail)
      as (st2' & Htail_moved & Heq_tail).
    assert
      (Hyx :
         ILSema.instr_point_list_semantics (y :: x :: prefix ++ rest) st1 st2').
    {
      econstructor.
      - exact Hip.
      - exact Htail_moved.
    }
    pose proof
      (instr_point_list_semantics_swap_adj
         y x (prefix ++ rest) st1 st2'
         Hna (Hperm y (or_introl eq_refl)) Hyx)
      as (st2'' & Hswapped & Heq_swap).
    exists st2''.
    split.
    + exact Hswapped.
    + eapply Instr.State.eq_trans; eauto.
Qed.

Lemma move_back_permutable :
  forall x prefix rest st1 st2,
    Instr.NonAlias st1 ->
    (forall y, In y prefix -> ILSema.Permutable y x) ->
    ILSema.instr_point_list_semantics (x :: prefix ++ rest) st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (prefix ++ x :: rest) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  induction prefix as [|y prefix IH]; intros rest st1 st2 Hna Hperm Hsem.
  - simpl in *.
    exists st2.
    split; [exact Hsem | apply Instr.State.eq_refl].
  - simpl in Hsem.
    assert (Hyx : ILSema.Permutable x y).
    {
      eapply ILSema.Permutable_symm.
      apply Hperm.
      left; reflexivity.
    }
    pose proof
      (instr_point_list_semantics_swap_adj
         x y (prefix ++ rest) st1 st2 Hna Hyx Hsem)
      as [st2' [Hswapped Heq_swap]].
    inversion Hswapped as [|st1' stmid st2'' ip' il Hy Htail]; subst.
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    assert (Hperm_tail : forall y0, In y0 prefix -> ILSema.Permutable y0 x).
    {
      intros y0 Hin.
      apply Hperm.
      right; exact Hin.
    }
    destruct (IH rest stmid st2' Hna_mid Hperm_tail Htail)
      as [st2'' [Hmoved Heq_tail]].
    exists st2''.
    split.
    + econstructor; eauto.
    + eapply Instr.State.eq_trans; eauto.
Qed.

Lemma instr_point_list_semantics_cons_inv :
  forall ip rest st1 st2,
    ILSema.instr_point_list_semantics (ip :: rest) st1 st2 ->
    exists stmid,
      ILSema.instr_point_sema ip st1 stmid /\
      ILSema.instr_point_list_semantics rest stmid st2.
Proof.
  intros ip rest st1 st2 Hsem.
  inversion Hsem as [|st1' stmid st2' ip' il Hip Htail]; subst.
  exists stmid.
  split; assumption.
Qed.

Lemma iter_semantics_preserve_nonalias :
  forall A (P : A -> mem -> mem -> Prop),
    (forall x mem1 mem2,
        P x mem1 mem2 ->
        Instr.NonAlias mem1 ->
        Instr.NonAlias mem2) ->
    forall xs mem1 mem2,
      Instr.IterSem.iter_semantics P xs mem1 mem2 ->
      Instr.NonAlias mem1 ->
      Instr.NonAlias mem2.
Proof.
  intros A P Hstep xs mem1 mem2 Hiter.
  induction Hiter; intros Hna.
  - exact Hna.
  - apply IHHiter.
    eapply Hstep; eauto.
Qed.

Scheme base_stmt_mutind := Induction for BaseLoop.stmt Sort Prop
with base_stmts_mutind := Induction for BaseLoop.stmt_list Sort Prop.
Combined Scheme base_stmt_stmts_mutind from base_stmt_mutind, base_stmts_mutind.

Definition base_stmt_preserve_nonalias_goal (s : BaseLoop.stmt) : Prop :=
  forall env mem1 mem2,
    BaseLoop.loop_semantics s env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.

Definition base_stmts_preserve_nonalias_goal (ss : BaseLoop.stmt_list) : Prop :=
  forall env mem1 mem2,
    BaseLoop.loop_semantics (BaseLoop.Seq ss) env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.

Lemma base_loop_semantics_preserve_nonalias_mutual :
  (forall s,
      base_stmt_preserve_nonalias_goal s) /\
  (forall ss,
      base_stmts_preserve_nonalias_goal ss).
Proof.
  apply
    (base_stmt_stmts_mutind
       base_stmt_preserve_nonalias_goal
       base_stmts_preserve_nonalias_goal).
  - intros lb ub body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    lazymatch goal with
    | Hiter : Instr.IterSem.iter_semantics _ _ _ _ |- _ =>
        eapply
          (iter_semantics_preserve_nonalias
             Z
             (fun x mem1 mem2 => BaseLoop.loop_semantics body (x :: env) mem1 mem2));
          [intros x mem1' mem2' Hbody_sem Hna'; eapply IHbody; eauto
          | exact Hiter
          | exact Hna]
    end.
  - intros i es env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    eauto using Instr.sema_prsv_nonalias.
  - intros ss IHss env mem1 mem2 Hsem Hna.
    eapply IHss; eauto.
  - intros test body IHbody env mem1 mem2 Hsem Hna.
    inversion Hsem; subst; eauto.
  - intros env mem1 mem2 Hsem Hna.
    inversion Hsem; subst; eauto.
  - intros s IHs ss IHss env mem1 mem2 Hsem Hna.
    inversion Hsem; subst.
    eapply IHss.
    + eauto.
    + eapply IHs; eauto.
Qed.

Lemma base_loop_semantics_preserve_nonalias_stmt :
  forall s,
    base_stmt_preserve_nonalias_goal s.
Proof.
  exact (proj1 base_loop_semantics_preserve_nonalias_mutual).
Qed.

Lemma base_loop_semantics_preserve_nonalias_stmts :
  forall ss,
    base_stmts_preserve_nonalias_goal ss.
Proof.
  exact (proj2 base_loop_semantics_preserve_nonalias_mutual).
Qed.

Lemma base_loop_semantics_preserve_nonalias :
  forall s env mem1 mem2,
    BaseLoop.loop_semantics s env mem1 mem2 ->
    Instr.NonAlias mem1 ->
    Instr.NonAlias mem2.
Proof.
  intros s.
  apply base_loop_semantics_preserve_nonalias_stmt.
Qed.

Lemma interleave_safe_refines_concat :
  forall trs out st1 st2,
    Instr.NonAlias st1 ->
    interleave_safe trs out ->
    ILSema.instr_point_list_semantics out st1 st2 ->
    exists st2',
      ILSema.instr_point_list_semantics (concat trs) st1 st2' /\
      Instr.State.eq st2 st2'.
Proof.
  intros trs out st1 st2 Hna Hsafe.
  revert st1 st2 Hna.
  induction Hsafe; intros st1 st2 Hna Hsem.
  - simpl in Hsem.
    exists st1.
    split.
    + constructor. apply Instr.State.eq_refl.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem.
    eapply IHHsafe; eauto.
  - destruct (instr_point_list_semantics_cons_inv _ _ _ _ Hsem)
      as [stmid [Hx Htail]].
    assert (Hna_mid : Instr.NonAlias stmid).
    {
      eapply instr_point_sema_preserve_nonalias; eauto.
    }
    destruct (IHHsafe stmid st2 Hna_mid Htail)
      as [st2' [Hconcat_tail Heq_tail]].
    assert
      (Hshape_rest :
         concat (pre ++ xs :: post) =
         concat pre ++ concat (xs :: post)).
    {
      rewrite concat_app.
      reflexivity.
    }
    assert
      (Hcons :
         ILSema.instr_point_list_semantics
           (x :: concat pre ++ concat (xs :: post)) st1 st2').
    {
      econstructor.
      - exact Hx.
      - rewrite <- Hshape_rest.
        exact Hconcat_tail.
    }
    assert
      (Hshape :
         concat (pre ++ (x :: xs) :: post) =
         concat pre ++ x :: concat (xs :: post)).
    {
      rewrite concat_app.
      simpl.
      reflexivity.
    }
    destruct
      (move_back_permutable
         x (concat pre) (concat (xs :: post)) st1 st2'
         Hna H Hcons)
      as [st2'' [Hconcat_full Heq_move]].
    assert
      (Hconcat_full' :
         ILSema.instr_point_list_semantics
           (concat (pre ++ (x :: xs) :: post)) st1 st2'').
    {
      rewrite Hshape.
      exact Hconcat_full.
    }
    exists st2''.
    split.
    + exact Hconcat_full'.
    + eapply Instr.State.eq_trans.
      * exact Heq_tail.
      * exact Heq_move.
Qed.

Lemma par_trace_forall2_refines_erased :
  forall body env,
    (forall env' tr mem1 mem2,
        Instr.NonAlias mem1 ->
        trace_safe_stmt body ->
        par_trace body env' tr ->
        ILSema.instr_point_list_semantics tr mem1 mem2 ->
        exists mem2',
          BaseLoop.loop_semantics (erase_stmt body) env' mem1 mem2' /\
          Instr.State.eq mem2 mem2') ->
    forall zs trs mem1 mem2,
      Instr.NonAlias mem1 ->
      trace_safe_stmt body ->
      Forall2 (fun z tri => par_trace body (z :: env) tri) zs trs ->
      ILSema.instr_point_list_semantics (concat trs) mem1 mem2 ->
      exists mem2',
        Instr.IterSem.iter_semantics
          (fun z => BaseLoop.loop_semantics (erase_stmt body) (z :: env))
          zs mem1 mem2' /\
        Instr.State.eq mem2 mem2'.
Proof.
  intros body env Hbody zs trs mem1 mem2 Hna Hsafe_body Hfor.
  revert mem1 mem2 Hna Hsafe_body.
  induction Hfor as [|z tr zs' trs' Htri Hfor' IHfor'];
    intros mem1 mem2 Hna Hsafe_body Hsem_concat.
  - simpl in Hsem_concat.
    exists mem1.
    split.
    + constructor.
    + eapply Instr.State.eq_sym.
      eapply instr_point_list_semantics_nil_inv; eauto.
  - simpl in Hsem_concat.
    eapply instr_point_list_semantics_app_inv in Hsem_concat.
    destruct Hsem_concat as [mem_mid [Hsem_head Hsem_tail]].
    pose proof
      (Hbody (z :: env) tr mem1 mem_mid Hna Hsafe_body Htri Hsem_head)
      as [mem_mid' [Hbody_sem Heq_mid]].
    assert (Hna_mid' : Instr.NonAlias mem_mid').
    {
      eapply base_loop_semantics_preserve_nonalias; eauto.
    }
    pose proof
      (ILSema.instr_point_list_sema_stable_under_state_eq
         (concat trs') mem_mid mem2 mem_mid' mem2
         Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
      as Hsem_tail'.
    pose proof (IHfor' mem_mid' mem2 Hna_mid' Hsafe_body Hsem_tail')
      as [mem2' [Hrest_sem Heq_tail]].
    exists mem2'.
    split.
    + eapply Instr.IterSem.IProgress.
      * exact Hbody_sem.
      * exact Hrest_sem.
    + exact Heq_tail.
Qed.

Lemma par_trace_refines_erased_stmt :
  forall s env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    par_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'
with par_trace_refines_erased_stmts :
  forall ss env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmts ss ->
    par_traces ss env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (BaseLoop.Seq (erase_stmt_list ss)) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  - intros s.
    induction s as [mode od lb ub body IHbody|i es|ss _|t body IHbody];
      intros env tr mem1 mem2 Hna Hsafe Htrace Hsem.
    + inversion Htrace as
          [| | | |od' lb' ub' body' env' zs trs tr' Hzs Hfor Hconcat
           |d lb' ub' body' env' zs trs tr' Hzs Hfor Hinter];
        subst.
      * simpl in Hsafe.
        match goal with
        | Hfor0 :
            Forall2 (fun z tri => par_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
            pose proof
              (par_trace_forall2_refines_erased
                 body env IHbody zs0 trs0 mem1 mem2 Hna Hsafe Hfor0 Hsem)
              as [mem2' [Hloop_sem Heq]]
        end.
        exists mem2'. split.
        -- econstructor. exact Hloop_sem.
        -- exact Heq.
      * simpl in Hsafe.
        lazymatch goal with
        | Hfor0 :
            Forall2 (fun z tri => seq_trace body (z :: env) tri) ?zs0 ?trs0 |- _ =>
            lazymatch goal with
            | Hinter0 : interleave_safe trs0 ?tr0 |- _ =>
                pose proof
                  (interleave_safe_refines_concat
                     trs0 tr0 mem1 mem2 Hna Hinter0 Hsem)
                  as [mem2a [Hconcat_sem Heq_concat]];
                pose proof
                  (seq_trace_forall2_refines_erased
                     body env
                     (fun env' tr mem1 mem2 =>
                        seq_trace_refines_erased_stmt body env' tr mem1 mem2)
                     zs0 trs0 mem1 mem2a Hsafe Hfor0 Hconcat_sem)
                  as [mem2' [Hloop_sem Heq_seq]]
            end
        end.
        exists mem2'. split.
        -- econstructor. exact Hloop_sem.
        -- eapply Instr.State.eq_trans; eauto.
    + inversion Htrace; subst.
      simpl in Hsafe.
      pose proof (instr_point_list_semantics_singleton_inv _ _ _ Hsem) as Hip.
      inversion Hip as [wcs rcs Hinstr]; subst.
      unfold BaseLoop.mk_instr_point in Hinstr.
      destruct Hsafe as [affs Haff].
      rewrite Haff in Hinstr.
      simpl in Hinstr.
      pose proof (BaseLoop.exprlist_to_aff_correct es env affs Haff) as Haff_ok.
      exists mem2.
      split.
      * eapply BaseLoop.LInstr with (wcs := wcs) (rcs := rcs).
        rewrite <- Haff_ok in Hinstr.
        exact Hinstr.
      * apply Instr.State.eq_refl.
    + inversion Htrace; subst.
      eapply par_trace_refines_erased_stmts; eauto.
    + inversion Htrace as
          [| | env' tst st tr' Heval Hbodytrace | env' tst st Heval | |];
        subst; simpl in Hsafe.
      * pose proof (IHbody env tr mem1 mem2 Hna Hsafe Hbodytrace Hsem)
          as [mem2' [Hbody_sem Heq]].
        exists mem2'.
        split; [eapply BaseLoop.LGuardTrue; eauto | exact Heq].
      * exists mem1.
        split;
          [eapply BaseLoop.LGuardFalse; eauto
          | eapply Instr.State.eq_sym;
            eapply instr_point_list_semantics_nil_inv; eauto].
  - intros ss.
    induction ss as [|s ss IHss']; intros env tr mem1 mem2 Hna Hsafe Htrace Hsem.
    + inversion Htrace; subst.
      exists mem1.
      split;
        [constructor
        | eapply Instr.State.eq_sym;
          eapply instr_point_list_semantics_nil_inv; eauto].
    + inversion Htrace as [|env' st sts tr1 tr2 Hst Hsts]; subst.
      simpl in Hsafe.
      destruct Hsafe as [Hsafe_s Hsafe_ss].
      eapply instr_point_list_semantics_app_inv in Hsem.
      destruct Hsem as [mem_mid [Hsem_head Hsem_tail]].
      pose proof
        (par_trace_refines_erased_stmt
           s env tr1 mem1 mem_mid Hna Hsafe_s Hst Hsem_head)
        as [mem_mid' [Hs_sem Heq_mid]].
      assert (Hna_mid' : Instr.NonAlias mem_mid').
      {
        eapply base_loop_semantics_preserve_nonalias; eauto.
      }
      pose proof
        (ILSema.instr_point_list_sema_stable_under_state_eq
           tr2 mem_mid mem2 mem_mid' mem2
           Hsem_tail Heq_mid (Instr.State.eq_refl mem2))
        as Hsem_tail'.
      pose proof
        (IHss' env tr2 mem_mid' mem2 Hna_mid' Hsafe_ss Hsts Hsem_tail')
        as [mem2' [Hss_sem Heq_tail]].
      exists mem2'.
      split.
      * econstructor; eauto.
      * exact Heq_tail.
Qed.

Lemma par_trace_refines_erased :
  forall s env tr mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    par_trace s env tr ->
    ILSema.instr_point_list_semantics tr mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros. eapply par_trace_refines_erased_stmt; eauto.
Qed.

Lemma loop_semantics_refines_erased :
  forall s env mem1 mem2,
    Instr.NonAlias mem1 ->
    trace_safe_stmt s ->
    loop_semantics s env mem1 mem2 ->
    exists mem2',
      BaseLoop.loop_semantics (erase_stmt s) env mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros s env mem1 mem2 Hna Hsafe [tr [Htrace Hsem]].
  eapply par_trace_refines_erased; eauto.
Qed.

Lemma semantics_refines_erased :
  forall p mem1 mem2,
    trace_safe p ->
    semantics p mem1 mem2 ->
    exists mem2',
      BaseLoop.semantics (erase_parallel p) mem1 mem2' /\
      Instr.State.eq mem2 mem2'.
Proof.
  intros [[s ctxt] vars] mem1 mem2 Hsafe Hsem.
  inversion Hsem as [loop_ext loop ctxt' vars' env mem1' mem2' Heq Hcompat Hna Hinit Hloop];
    subst.
  inversion Heq; subst.
  simpl in Hsafe.
  destruct (loop_semantics_refines_erased loop env mem1 mem2 Hna Hsafe Hloop)
    as [mem2'' [Hloop' Heq_loop]].
  exists mem2''.
  split.
  - econstructor; eauto.
    reflexivity.
  - exact Heq_loop.
Qed.

End ParallelLoop.
