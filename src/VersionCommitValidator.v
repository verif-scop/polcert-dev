Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolyBase.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import InstanceProjectionWitness.
Require Import VersionCommitWitness.
Require Import VersionCommitValueWitness.
Require Import VersionReadWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for version selection and commit.

    The finite witness checks exact source-liveout coverage and unique selected
    target versions.  Read-selection witnesses additionally record that
    internal target reads use versions produced by the intended dynamic source
    writes.  Deriving those finite entries from concrete instructions remains
    part of the feature-specific semantic refinement. *)

Module VersionCommitValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_version_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_version_source_view_correct :
  forall before source_view ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition version_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record version_commit_view_contract
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (source_view after: PolyLang.t) : Prop := {
  vcvc_commit :
    version_commit_obligations source_liveouts mapping;
  vcvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (entries: list (version_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcovc_commit :
    version_commit_obligations source_liveouts mapping;
  vcovc_value :
    version_value_obligations value mapping entries;
  vcovc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_compatible_view_contract
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (source_view after: PolyLang.t) : Prop := {
  vccvc_commit :
    version_commit_obligations source_liveouts mapping;
  vccvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  vccvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (entries: list (version_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vccvvc_commit :
    version_commit_obligations source_liveouts mapping;
  vccvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  vccvvc_value :
    version_value_obligations value mapping entries;
  vccvvc_semantic_refinement :
    version_source_view_refines_view
      input_view output_view source_view after;
}.

Record version_commit_read_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_liveouts: list MemCell)
    (mapping: version_commit_mapping)
    (logical_specs physical_specs: list storage_spec)
    (commit_entries: list (version_value_entry value))
    (expected_reads: list logical_instance)
    (produced_versions: produced_version_mapping)
    (read_entries: list version_read_entry)
    (read_value_entries: list (version_read_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  vcrcvc_commit_base :
    version_commit_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_entries source_view after;
  vcrcvc_read_selection :
    version_read_selection_obligations
      expected_reads produced_versions read_entries;
  vcrcvc_read_values :
    version_read_value_obligations
      value read_entries read_value_entries;
}.

Definition version_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_version_commit_view_correct :
  forall input_view output_view source_liveouts mapping
         before source_view after ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_view_contract
      input_view output_view source_liveouts mapping source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view source_liveouts mapping
         before source_view after ok Hret Hok Hcommit Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_version_commit_compatible_view_correct :
  forall input_view output_view source_liveouts mapping
         logical_specs physical_specs before source_view after ok,
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_compatible_view_contract
      input_view output_view source_liveouts mapping
      logical_specs physical_specs source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view source_liveouts mapping
         logical_specs physical_specs before source_view after ok
         Hret Hok Hcommit Hcompat Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_version_commit_view_correct
       input_view output_view source_liveouts mapping
       before source_view after ok Hret Hok Hcommit Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_version_valueb value value_eqb mapping entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_value_view_contract
      value input_view output_view source_liveouts mapping entries
      source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping entries before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hvalue Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_version_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_version_commit_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_version_valueb value value_eqb mapping entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs entries source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hvalue Hsemantics.
  pose proof
    (check_version_commitb_sound source_liveouts mapping Hcommit)
    as Hcommit_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_version_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (checked_version_commit_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping entries
       before source_view after ok Hvalue_eqb Hret Hok
       Hcommit Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_version_commit_read_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view source_liveouts mapping
         logical_specs physical_specs commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_version_source_view before source_view) ok ->
    ok = true ->
    check_version_commitb source_liveouts mapping = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    check_version_valueb value value_eqb mapping commit_entries = true ->
    check_version_read_selectionb
      expected_reads produced_versions read_entries = true ->
    check_version_read_valueb
      value_eqb read_entries read_value_entries = true ->
    version_source_view_refines_view
      input_view output_view source_view after ->
    version_commit_read_compatible_value_view_contract
      value input_view output_view source_liveouts mapping
      logical_specs physical_specs commit_entries
      expected_reads produced_versions read_entries read_value_entries
      source_view after /\
    View.view_refinement
      input_view
      (version_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view source_liveouts
         mapping logical_specs physical_specs commit_entries
         expected_reads produced_versions read_entries read_value_entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_value
         Hread_selection Hread_values Hsemantics.
  pose proof
    (check_version_read_selectionb_sound
       expected_reads produced_versions read_entries Hread_selection)
    as Hread_selection_obligations.
  pose proof
    (check_version_read_valueb_sound
       value value_eqb Hvalue_eqb
       read_entries read_value_entries Hread_values)
    as Hread_value_obligations.
  pose proof
    (checked_version_commit_compatible_value_view_correct
       value value_eqb input_view output_view source_liveouts mapping
       logical_specs physical_specs commit_entries
       before source_view after ok
       Hvalue_eqb Hret Hok Hcommit Hcompat Hcommit_value Hsemantics)
    as [Hcommit_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End VersionCommitValidator.
