Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.
Require Import CopyCommitWitness.
Require Import CopyInstanceWitness.
Require Import CopyMappingWitness.
Require Import CopyProtocolValueWitness.
Require Import InstanceProjectionWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** Combined wrapper for scratchpad / packing / copy-mediated local buffers.

    A real copy-mediated transformation is not just one primitive.  It usually
    combines:

      - inserted/helper target instances, checked by an instance projection
        witness;
      - local-buffer fill/use/commit ordering, checked by a copy protocol
        witness;
      - local/private storage separation from public and framed cells.

    This module packages those three finite witnesses under one composable
    [view_refinement] theorem.  The value-simulation proof that copy-in/local
    compute/copy-out implements the source computation is still an explicit
    semantic refinement obligation. *)

Module ScratchpadCopyValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_scratchpad_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_scratchpad_source_view_correct :
  forall before source_view ok,
    mayReturn (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition scratchpad_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record scratchpad_copy_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  scc_projection :
    instance_projection_obligations
      source_domain source_liveouts targets;
  scc_copy_protocol :
    copy_protocol_wf copy_trace;
  scc_local_separation :
    private_separation_obligations
      local_cells public_cells frame_cells;
  scc_semantic_refinement :
    scratchpad_source_view_refines_view
      input_view output_view source_view after;
}.

Record scratchpad_copy_commit_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  scccc_base :
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after;
  scccc_commit_cover :
    copy_commit_obligations expected_commit_targets copy_trace;
}.

Record scratchpad_copy_instance_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccic_base :
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after;
  sccic_instance_trace :
    copy_instance_trace_obligations targets copy_trace;
}.

Record scratchpad_copy_instance_commit_view_contract
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (copy_trace: list copy_event)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccicc_base :
    scratchpad_copy_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after;
  sccicc_instance_trace :
    copy_instance_trace_obligations targets copy_trace;
}.

Record scratchpad_copy_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  sccf_base :
    scratchpad_copy_instance_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after;
  sccf_mapping :
    copy_mapping_obligations mapping copy_trace;
  sccf_value_simulation :
    copy_value_simulation_obligations value value_trace;
}.

Record scratchpad_copy_compatible_full_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_domain source_liveouts: list logical_instance)
    (targets: list projected_instance)
    (expected_commit_targets: list MemCell)
    (mapping: copy_cell_mapping)
    (copy_trace: list copy_event)
    (value_trace: copy_value_trace value)
    (local_cells public_cells frame_cells: list MemCell)
    (public_specs local_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  scccf_base :
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after;
  scccf_storage_compatible :
    storage_compatibility_obligations mapping public_specs local_specs;
}.

Definition scratchpad_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_scratchpad_copy_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hseparation Hsemantics.
  pose proof
    (check_instance_projectionb_sound
       source_domain source_liveouts targets Hprojection)
    as Hprojection_obligations.
  pose proof
    (check_copy_protocol_wfb_sound copy_trace Hcopy)
    as Hcopy_obligations.
  pose proof
    (check_private_separationb_sound
       local_cells public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scratchpad_copy_commit_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hcommit Hseparation Hsemantics.
  pose proof
    (check_copy_commit_coverb_obligations_sound
       expected_commit_targets copy_trace Hcommit)
    as Hcommit_obligations.
  pose proof
    (checked_scratchpad_copy_view_correct
       input_view output_view
       source_domain source_liveouts targets copy_trace
       local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_instance_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_instance_view_contract
      input_view output_view
      source_domain source_liveouts targets copy_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets copy_trace
         local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hinstance Hseparation Hsemantics.
  pose proof
    (check_copy_instance_traceb_obligations_sound
       targets copy_trace Hinstance)
    as Hinstance_obligations.
  pose proof
    (checked_scratchpad_copy_view_correct
       input_view output_view
       source_domain source_liveouts targets copy_trace
       local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_instance_commit_view_correct :
  forall input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_instance_commit_view_contract
      input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      copy_trace local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         copy_trace local_cells public_cells frame_cells
         before source_view after ok
         Hret Hok Hprojection Hcopy Hcommit Hinstance Hseparation Hsemantics.
  pose proof
    (check_copy_instance_traceb_obligations_sound
       targets copy_trace Hinstance)
    as Hinstance_obligations.
  pose proof
    (checked_scratchpad_copy_commit_view_correct
       input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       copy_trace local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hcommit Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
         Hseparation Hsemantics.
  pose proof
    (check_copy_mappingb_sound mapping copy_trace Hmapping)
    as Hmapping_obligations.
  pose proof
    (check_copy_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_scratchpad_copy_instance_commit_view_correct
       input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       copy_trace local_cells public_cells frame_cells
       before source_view after ok
       Hret Hok Hprojection Hcopy Hcommit Hinstance
       Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scratchpad_copy_compatible_full_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_scratchpad_source_view before source_view) ok ->
    ok = true ->
    check_instance_projectionb
      source_domain source_liveouts targets = true ->
    check_copy_protocol_wfb copy_trace = true ->
    check_copy_commit_coverb expected_commit_targets copy_trace = true ->
    check_copy_instance_traceb targets copy_trace = true ->
    check_copy_mappingb mapping copy_trace = true ->
    check_copy_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      local_cells public_cells frame_cells = true ->
    check_storage_compatibilityb mapping public_specs local_specs = true ->
    scratchpad_source_view_refines_view
      input_view output_view source_view after ->
    scratchpad_copy_compatible_full_view_contract
      value input_view output_view
      source_domain source_liveouts targets expected_commit_targets
      mapping copy_trace value_trace
      local_cells public_cells frame_cells
      public_specs local_specs source_view after /\
    View.view_refinement
      input_view
      (scratchpad_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_domain source_liveouts targets expected_commit_targets
         mapping copy_trace value_trace
         local_cells public_cells frame_cells
         public_specs local_specs
         before source_view after ok Hvalue_eqb Hret Hok
         Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
         Hseparation Hstorage Hsemantics.
  pose proof
    (check_storage_compatibilityb_sound
       mapping public_specs local_specs Hstorage)
    as Hstorage_obligations.
  pose proof
    (checked_scratchpad_copy_full_view_correct
       value value_eqb input_view output_view
       source_domain source_liveouts targets expected_commit_targets
       mapping copy_trace value_trace
       local_cells public_cells frame_cells
       before source_view after ok Hvalue_eqb Hret Hok
       Hprojection Hcopy Hcommit Hinstance Hmapping Hvalue
       Hseparation Hsemantics)
    as [Hbase Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End ScratchpadCopyValidator.
