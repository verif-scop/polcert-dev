Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import PhaseSeparationWitness.
Require Import PhaseValueWitness.
Require Import PhaseProjectionWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for phase-separated storage protocols.

    The finite witness checks visibility and no-overwrite obligations for a
    sequence of phase boundaries.  The semantic meaning of the phase change
    (for example, that a ping-pong swap advances logical time) remains an
    explicit refinement obligation. *)

Module PhaseSeparationValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_phase_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_phase_source_view_correct :
  forall before source_view ok,
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition phase_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record phase_separation_view_contract
    (input_view output_view: View.view)
    (entry_live: list MemCell)
    (steps: list phase_step)
    (source_view after: PolyLang.t) : Prop := {
  psvc_phase_protocol :
    phase_protocol_safe entry_live steps;
  psvc_semantic_refinement :
    phase_source_view_refines_view
      input_view output_view source_view after;
}.

Record phase_separation_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (entry_live: list MemCell)
    (entry_values: list (phase_cell_value value))
    (steps: list phase_step)
    (value_steps: list (phase_value_step value))
    (source_view after: PolyLang.t) : Prop := {
  psvvc_phase_protocol :
    phase_protocol_safe entry_live steps;
  psvvc_value_protocol :
    phase_value_protocol value entry_live entry_values steps value_steps;
  psvvc_semantic_refinement :
    phase_source_view_refines_view
      input_view output_view source_view after;
}.

Record phase_projection_view_contract
    (input_view output_view: View.view)
    (entry_live source_liveouts: list MemCell)
    (steps: list phase_step)
    (mapping: phase_projection_mapping)
    (source_view after: PolyLang.t) : Prop := {
  ppvc_phase_protocol :
    phase_protocol_safe entry_live steps;
  ppvc_projection :
    phase_projection_obligations
      source_liveouts (phase_protocol_final_live entry_live steps) mapping;
  ppvc_semantic_refinement :
    phase_source_view_refines_view
      input_view output_view source_view after;
}.

Record phase_projection_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (entry_live source_liveouts: list MemCell)
    (entry_values: list (phase_cell_value value))
    (steps: list phase_step)
    (value_steps: list (phase_value_step value))
    (mapping: phase_projection_mapping)
    (projection_values: list (phase_projection_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  ppvvc_phase_protocol :
    phase_protocol_safe entry_live steps;
  ppvvc_value_protocol :
    phase_value_protocol value entry_live entry_values steps value_steps;
  ppvvc_projection :
    phase_projection_obligations
      source_liveouts (phase_protocol_final_live entry_live steps) mapping;
  ppvvc_projection_values :
    phase_projection_value_obligations value mapping projection_values;
  ppvvc_semantic_refinement :
    phase_source_view_refines_view
      input_view output_view source_view after;
}.

Record phase_projection_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (entry_live source_liveouts: list MemCell)
    (entry_values: list (phase_cell_value value))
    (steps: list phase_step)
    (value_steps: list (phase_value_step value))
    (mapping: phase_projection_mapping)
    (projection_values: list (phase_projection_value_entry value))
    (source_specs final_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  ppcvvc_value_base :
    phase_projection_value_view_contract
      value input_view output_view entry_live source_liveouts
      entry_values steps value_steps mapping projection_values
      source_view after;
  ppcvvc_storage_compatible :
    storage_compatibility_obligations mapping source_specs final_specs;
}.

Definition phase_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_phase_separation_view_correct :
  forall input_view output_view entry_live steps
         before source_view after ok,
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    check_phase_protocolb entry_live steps = true ->
    phase_source_view_refines_view
      input_view output_view source_view after ->
    phase_separation_view_contract
      input_view output_view entry_live steps source_view after /\
    View.view_refinement
      input_view
      (phase_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view entry_live steps
         before source_view after ok Hret Hok Hphase Hsemantics.
  pose proof
    (check_phase_protocolb_sound entry_live steps Hphase)
    as Hphase_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_phase_projection_view_correct :
  forall input_view output_view entry_live source_liveouts steps mapping
         before source_view after ok,
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    check_phase_protocolb entry_live steps = true ->
    check_phase_projectionb
      source_liveouts
      (phase_protocol_final_live entry_live steps)
      mapping = true ->
    phase_source_view_refines_view
      input_view output_view source_view after ->
    phase_projection_view_contract
      input_view output_view entry_live source_liveouts steps mapping
      source_view after /\
    View.view_refinement
      input_view
      (phase_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view entry_live source_liveouts steps mapping
         before source_view after ok Hret Hok Hphase Hprojection Hsemantics.
  pose proof
    (check_phase_protocolb_sound entry_live steps Hphase)
    as Hphase_obligations.
  pose proof
    (check_phase_projection_obligationsb_sound
       source_liveouts
       (phase_protocol_final_live entry_live steps)
       mapping Hprojection)
    as Hprojection_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_phase_separation_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view entry_live entry_values steps value_steps
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    check_phase_protocolb entry_live steps = true ->
    check_phase_value_protocolb
      value value_eqb entry_live entry_values steps value_steps = true ->
    phase_source_view_refines_view
      input_view output_view source_view after ->
    phase_separation_value_view_contract
      value input_view output_view entry_live entry_values steps value_steps
      source_view after /\
    View.view_refinement
      input_view
      (phase_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         entry_live entry_values steps value_steps
         before source_view after ok
         Hvalue_eqb Hret Hok Hphase Hvalue Hsemantics.
  pose proof
    (check_phase_protocolb_sound entry_live steps Hphase)
    as Hphase_obligations.
  pose proof
    (check_phase_value_protocolb_sound
       value value_eqb Hvalue_eqb
       entry_live entry_values steps value_steps Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_phase_separation_view_correct
       input_view output_view entry_live steps
       before source_view after ok Hret Hok Hphase Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_phase_projection_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view entry_live source_liveouts entry_values
         steps value_steps mapping projection_values
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    check_phase_protocolb entry_live steps = true ->
    check_phase_value_protocolb
      value value_eqb entry_live entry_values steps value_steps = true ->
    check_phase_projectionb
      source_liveouts
      (phase_protocol_final_live entry_live steps)
      mapping = true ->
    check_phase_projection_valueb
      value value_eqb mapping projection_values = true ->
    phase_source_view_refines_view
      input_view output_view source_view after ->
    phase_projection_value_view_contract
      value input_view output_view entry_live source_liveouts entry_values
      steps value_steps mapping projection_values source_view after /\
    View.view_refinement
      input_view
      (phase_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         entry_live source_liveouts entry_values
         steps value_steps mapping projection_values
         before source_view after ok Hvalue_eqb Hret Hok
         Hphase Hvalue Hprojection Hprojection_values Hsemantics.
  pose proof
    (check_phase_protocolb_sound entry_live steps Hphase)
    as Hphase_obligations.
  pose proof
    (check_phase_value_protocolb_sound
       value value_eqb Hvalue_eqb
       entry_live entry_values steps value_steps Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_phase_projection_obligationsb_sound
       source_liveouts
       (phase_protocol_final_live entry_live steps)
       mapping Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_phase_projection_valueb_sound
       value value_eqb Hvalue_eqb
       mapping projection_values Hprojection_values)
    as Hprojection_value_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_phase_projection_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view entry_live source_liveouts entry_values
         steps value_steps mapping projection_values
         source_specs final_specs
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_phase_source_view before source_view) ok ->
    ok = true ->
    check_phase_protocolb entry_live steps = true ->
    check_phase_value_protocolb
      value value_eqb entry_live entry_values steps value_steps = true ->
    check_phase_projectionb
      source_liveouts
      (phase_protocol_final_live entry_live steps)
      mapping = true ->
    check_phase_projection_valueb
      value value_eqb mapping projection_values = true ->
    check_storage_compatibilityb mapping source_specs final_specs = true ->
    phase_source_view_refines_view
      input_view output_view source_view after ->
    phase_projection_compatible_value_view_contract
      value input_view output_view entry_live source_liveouts entry_values
      steps value_steps mapping projection_values
      source_specs final_specs source_view after /\
    View.view_refinement
      input_view
      (phase_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         entry_live source_liveouts entry_values
         steps value_steps mapping projection_values
         source_specs final_specs
         before source_view after ok Hvalue_eqb Hret Hok
         Hphase Hvalue Hprojection Hprojection_values
         Hstorage Hsemantics.
  pose proof
    (check_storage_compatibilityb_sound
       mapping source_specs final_specs Hstorage)
    as Hstorage_obligations.
  pose proof
    (checked_phase_projection_value_view_correct
       value value_eqb input_view output_view
       entry_live source_liveouts entry_values steps value_steps
       mapping projection_values before source_view after ok
       Hvalue_eqb Hret Hok Hphase Hvalue Hprojection
       Hprojection_values Hsemantics)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End PhaseSeparationValidator.
