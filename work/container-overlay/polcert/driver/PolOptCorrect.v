Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Require Import ISSValidatorCorrect.
Require Import PolIRs.
Require Import PolOpt.

Local Open Scope impure_scope.

Module PolOptCorrect (PolIRs: POLIRS).

Module Core := PolOpt PolIRs.
Module ISSValidatorCorrectCore := ISSValidatorCorrect PolIRs.
Module LoopIR := PolIRs.Loop.
Module PolyLang := PolIRs.PolyLang.
Module State := PolIRs.State.

Lemma try_checked_iss_phase_pipeline_from_poly_correct:
  forall pol before_scop st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.try_checked_iss_phase_pipeline_from_poly pol before_scop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol before_scop st st' Hwf loop' Hopt Hloop.
  unfold Core.try_checked_iss_phase_pipeline_from_poly in Hopt.
  destruct (Core.infer_iss_from_source_scop pol before_scop) as [iss_opt|msg]
    eqn:Hiss_infer.
  - destruct iss_opt as [[pol_iss w]|].
    + destruct (Core.ValidatorCore.checked_iss_complete_cut_shape_validate pol pol_iss w)
        eqn:Hiss_check.
      * bind_imp_destruct Hopt iss_wf Hiss_wf.
        destruct iss_wf.
        -- pose proof
             (Core.check_wf_polyprog_affine_correct pol_iss _ Hiss_wf eq_refl)
             as Hwf_iss.
           pose proof
             (Core.try_phase_pipeline_from_source_pol_correct
                pol_iss
                Core.run_pluto_phase_pipeline_with_iss
                before_scop
                st st'
                Hwf_iss
                loop'
                Hopt
                Hloop)
             as Hiss_corr.
           destruct Hiss_corr as [st_iss [Hiss_sem Heq_iss]].
           pose proof
             (ISSValidatorCorrectCore
                .checked_iss_complete_cut_shape_validate_semantics_correct
                pol pol_iss w st st_iss Hiss_check Hiss_sem)
             as Hback.
           destruct Hback as [st_src [Hsrc_sem Heq_src]].
           exists st_src.
           split; auto.
           eapply State.eq_trans; eauto.
        -- eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
      * eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
    + eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
  - eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
Qed.

Lemma phase_opt_prepared_from_poly_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.phase_opt_prepared_from_poly pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold Core.phase_opt_prepared_from_poly,
    Core.phase_pipeline_opt_prepared_from_poly,
    Core.phase_pipeline_opt_prepared_from_poly_no_iss in Hopt.
  destruct (Core.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (Core.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    + eapply Core.try_phase_pipeline_from_source_pol_correct; eauto.
    + eapply Core.affine_opt_prepared_from_poly_correct; eauto.
  - eapply Core.PrepareCore.prepared_codegen_correct in Hopt; eauto.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Lemma phase_opt_prepared_from_poly_with_iss_correct:
  forall pol st st',
    PolyLang.wf_pprog_affine pol ->
    WHEN loop' <- Core.phase_opt_prepared_from_poly_with_iss pol THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      PolyLang.instance_list_semantics pol st st'' /\ State.eq st' st''.
Proof.
  intros pol st st' Hwf loop' Hopt Hloop.
  unfold Core.phase_opt_prepared_from_poly_with_iss,
    Core.phase_pipeline_opt_prepared_from_poly_with_iss in Hopt.
  destruct (Core.has_nonscalar_stmt pol) eqn:Hnonscalar.
  - destruct (Core.export_for_phase_scheduler pol) as [before_scop|] eqn:Hbefore.
    + eapply try_checked_iss_phase_pipeline_from_poly_correct; eauto.
    + eapply Core.affine_opt_prepared_from_poly_correct; eauto.
  - eapply Core.PrepareCore.prepared_codegen_correct in Hopt; eauto.
    exists st'. split; auto. eapply State.eq_refl.
Qed.

Theorem Opt_prepared_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_prepared loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.Opt_prepared, Core.phase_opt_prepared in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := Core.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (Core.Strengthen.strengthen_pprog_wf_affine pol0
       (Core.extractor_success_wf_pprog_affine loop pol0
          Hextok))
    as Hwf_pol.
  pose proof
    (phase_opt_prepared_from_poly_correct pol st st' Hwf_pol loop' Hopt Hloop)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply Core.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (Core.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_prepared_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_prepared_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  intros loop st st' loop' Hopt Hloop.
  unfold Core.Opt_prepared_with_iss, Core.phase_opt_prepared_with_iss in Hopt.
  bind_imp_destruct Hopt pol0 Hextimp.
  set (pol := Core.Strengthen.strengthen_pprog pol0) in *.
  pose proof Hextimp as Hextok.
  apply res_to_alarm_correct in Hextok.
  pose proof
    (Core.Strengthen.strengthen_pprog_wf_affine pol0
       (Core.extractor_success_wf_pprog_affine loop pol0
          Hextok))
    as Hwf_pol.
  pose proof
    (phase_opt_prepared_from_poly_with_iss_correct pol st st' Hwf_pol loop' Hopt Hloop)
    as Hphase_corr.
  destruct Hphase_corr as [st_str [Hstr_sem Heq_str]].
  eapply Core.Strengthen.instance_list_semantics_unstrengthen in Hstr_sem.
  pose proof (Core.Extractor.extractor_correct loop pol0 st st_str Hextok Hstr_sem)
    as Hext_corr.
  destruct Hext_corr as [st_src [Hloop_src Heq_src]].
  exists st_src.
  split; auto.
  eapply State.eq_trans.
  - exact Heq_str.
  - exact Heq_src.
Qed.

Theorem Opt_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  exact Opt_prepared_correct.
Qed.

Theorem Opt_with_iss_correct:
  forall loop st st',
    WHEN loop' <- Core.Opt_with_iss loop THEN
    LoopIR.semantics loop' st st' ->
    exists st'',
      LoopIR.semantics loop st st'' /\ State.eq st' st''.
Proof.
  exact Opt_prepared_with_iss_correct.
Qed.

End PolOptCorrect.
