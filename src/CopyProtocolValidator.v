Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import CopyProtocolWitness.
Require Import CopyCommitWitness.
Require Import CopyMappingWitness.
Require Import CopyProtocolValueWitness.

Import ListNotations.

(** View-level wrapper for copy-mediated local storage.

    [CopyProtocolWitness] checks the finite copy/local/commit bookkeeping.  It
    does not prove that target instructions simulate source instructions.  This
    module gives that witness a composable theorem shape:

      1. [before -> source_view] is checked by the existing scheduler route;
      2. [source_view -> after] supplies a feature-specific semantic refinement
         under explicit input/output views;
      3. the copy witness is returned as a local obligation and the whole pass
         composes into one [view_refinement].

    This keeps the protocol checker useful without weakening the existing
    [State.eq] pipeline or pretending that copy bookkeeping is full semantic
    correctness. *)

Module CopyProtocolValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_copy_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_copy_source_view_correct :
  forall before source_view ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition copy_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record copy_protocol_view_contract
    (input_view output_view: View.view)
    (trace: list copy_event)
    (source_view after: PolyLang.t) : Prop := {
  cpvc_protocol :
    copy_protocol_wf trace;
  cpvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpvvc_protocol :
    copy_protocol_wf trace;
  cpvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_mapping_view_contract
    (input_view output_view: View.view)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (source_view after: PolyLang.t) : Prop := {
  cpmvc_protocol :
    copy_protocol_wf trace;
  cpmvc_mapping :
    copy_mapping_obligations mapping trace;
  cpmvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_mapping_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpmvvc_protocol :
    copy_protocol_wf trace;
  cpmvvc_mapping :
    copy_mapping_obligations mapping trace;
  cpmvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpmvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Record copy_protocol_commit_mapping_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (trace: list copy_event)
    (value_trace: copy_value_trace value)
    (source_view after: PolyLang.t) : Prop := {
  cpcmvvc_protocol :
    copy_protocol_wf trace;
  cpcmvvc_commit_cover :
    copy_commit_obligations expected_commit_targets trace;
  cpcmvvc_mapping :
    copy_mapping_obligations mapping trace;
  cpcmvvc_value_simulation :
    copy_value_simulation_obligations value value_trace;
  cpcmvvc_semantic_refinement :
    copy_source_view_refines_view
      input_view output_view source_view after;
}.

Definition copy_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_copy_protocol_view_correct :
  forall input_view output_view trace before source_view after ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_view_contract
      input_view output_view trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view trace before source_view after ok
         Hret Hok Hprotocol Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_mapping_view_correct :
  forall input_view output_view mapping trace before source_view after ok,
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_mappingb mapping trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_mapping_view_contract
      input_view output_view mapping trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping trace before source_view after ok
         Hret Hok Hprotocol Hmapping Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view trace value_trace
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_value_view_contract
      value input_view output_view trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view trace value_trace
         before source_view after ok Hvalue_eqb Hret Hok
         Hprotocol Hvalue Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_mapping_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping trace value_trace
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_mapping_value_view_contract
      value input_view output_view mapping trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping trace value_trace
         before source_view after ok Hvalue_eqb Hret Hok
         Hprotocol Hmapping Hvalue Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_commit_mapping_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view expected_commit_targets
         mapping trace value_trace before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_copy_source_view before source_view) ok ->
    ok = true ->
    check_copy_protocol_wfb trace = true ->
    check_copy_commit_coverb expected_commit_targets trace = true ->
    check_copy_mappingb mapping trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    copy_source_view_refines_view
      input_view output_view source_view after ->
    copy_protocol_commit_mapping_value_view_contract
      value input_view output_view expected_commit_targets
      mapping trace value_trace source_view after /\
    View.view_refinement
      input_view
      (copy_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view expected_commit_targets
         mapping trace value_trace before source_view after ok
         Hvalue_eqb Hret Hok Hprotocol Hcommit Hmapping Hvalue
         Hcopy_semantics.
  pose proof
    (check_copy_protocol_wfb_sound trace Hprotocol)
    as Hcopy_protocol.
  pose proof
    (check_copy_commit_coverb_obligations_sound
       expected_commit_targets trace Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_copy_mappingb_sound mapping trace Hmapping)
    as Hcopy_mapping.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_protocol.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_copy_protocol_commits_nodup :
  forall trace,
    check_copy_protocol_wfb trace = true ->
    NoDup (copy_protocol_committed_targets trace).
Proof.
  apply check_copy_protocol_wfb_commits_nodup.
Qed.

End CopyProtocolValidator.
