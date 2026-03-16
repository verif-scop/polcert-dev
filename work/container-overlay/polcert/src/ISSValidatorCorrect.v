Require Import ISSBoolChecker.
Require Import ISSCutSemantics.
Require Import ISSValidator.
Require Import PolIRs.

Module ISSValidatorCorrect (PolIRs: POLIRS).

Module ISSVal := ISSValidator PolIRs.
Module ISSCheck := ISSBoolChecker PolIRs.
Module ISSSem := ISSCutSemantics PolIRs.
Module State := PolIRs.Instr.State.
Module PolyLang := PolIRs.PolyLang.

Lemma checked_iss_complete_cut_shape_validate_semantics_correct :
  forall before after w st1 st2,
    ISSVal.checked_iss_complete_cut_shape_validate before after w = true ->
    PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after w st1 st2 Hcheck Hsem_after.
  eapply ISSSem.iss_complete_cut_shape_to_before_correct; eauto.
  eapply ISSCheck.check_domain_partition_complete_cut_shapeb_sound; eauto.
Qed.

End ISSValidatorCorrect.
