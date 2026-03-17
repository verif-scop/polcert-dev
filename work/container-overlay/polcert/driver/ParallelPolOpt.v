Require Import Result.
Require Import PolyLang.
Require Import PolIRs.
Require Import Loop.
Require Import ParallelCodegen.
Require Import Validator.
Require Import PolOpt.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module ParallelPolOpt (PolIRs : POLIRS).

Module CoreOpt := PolOpt PolIRs.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.
Module ValidatorCore := Validator PolIRs.
Module ParallelCodegenCore := ParallelCodegen PolIRs.

Definition checked_parallel_current_annotated_codegen
    (pol : PolyLang.t)
    (plan : ValidatorCore.parallel_plan)
  : imp (result ParallelCodegenCore.ParallelLoop.t) :=
  BIND cert_res <- ValidatorCore.checked_parallelize_current
                     (PolyLang.current_view_pprog pol) plan -;
  match cert_res with
  | Okk cert =>
      let cert' :=
        {| ParallelCodegenCore.ParallelValidator.certified_dim :=
             cert.(ValidatorCore.ParallelCore.certified_dim) |} in
      ParallelCodegenCore.checked_annotated_codegen
        (PolyLang.current_view_pprog pol) cert'
  | Err msg => pure (Err msg)
  end.

Lemma checked_parallel_current_annotated_codegen_correct :
  forall pol plan pl st st',
    mayReturn (checked_parallel_current_annotated_codegen pol plan) (Okk pl) ->
    PolyLang.wf_pprog_general pol ->
    ParallelCodegenCore.ParallelLoop.semantics pl st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol plan pl st st' Hopt Hwf Hsem.
  unfold checked_parallel_current_annotated_codegen in Hopt.
  apply mayReturn_bind in Hopt.
  destruct Hopt as [cert_res [Hcert Hret]].
  destruct cert_res as [cert|msg].
  - eapply ParallelCodegenCore.checked_annotated_codegen_correct_general; eauto.
  - apply mayReturn_pure in Hret.
    discriminate.
Qed.

End ParallelPolOpt.
