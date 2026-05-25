Require Import Bool.
Require Import List.

Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import AffineValidator.
Require Import TransformContract.
Require Import StateView.
Require Import ViewPipeline.
Require Import ReuseConflictWitness.
Require Import LifetimeConflictWitness.
Require Import ReuseValueWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for conflict-safe non-injective reuse.

    The finite witness proves that the supplied reuse map separates all listed
    conflicts.  A full contraction validator still needs two larger semantic
    facts:

      - the conflict relation over-approximates live-range overlap under the
        schedule;
      - the output view projects logical cells through the reused physical
        storage at the boundary.

    This module deliberately leaves those as the explicit
    [reuse_source_view_refines_view] obligation while making the finite checker
    composable with the existing source-view schedule route. *)

Module ReuseConflictValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_reuse_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_reuse_source_view_correct :
  forall before source_view ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition reuse_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  crvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  crvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  crvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  crvvc_value :
    reuse_value_obligations value mapping entries;
  crvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record live_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  lcrvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  lcrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  lcrvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  lcrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record live_conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  lcrvvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  lcrvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  lcrvvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  lcrvvc_value :
    reuse_value_obligations value mapping entries;
  lcrvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  ccrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  ccrvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  ccrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_live_conflict_reuse_view_contract
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (source_view after: PolyLang.t) : Prop := {
  clcrvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  clcrvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  clcrvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  clcrvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  clcrvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Record compatible_live_conflict_reuse_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (mapping: reuse_mapping)
    (logical_specs physical_specs: list storage_spec)
    (intervals: list live_interval)
    (conflicts: conflict_pairs)
    (entries: list (reuse_value_entry value))
    (source_view after: PolyLang.t) : Prop := {
  clcrvvc_live_conflicts :
    live_conflict_obligations intervals conflicts;
  clcrvvc_reuse :
    conflict_safe_reuse_obligations mapping conflicts;
  clcrvvc_live_reuse_safe :
    live_overlaps_reuse_separated mapping intervals;
  clcrvvc_value :
    reuse_value_obligations value mapping entries;
  clcrvvc_storage_compatible :
    storage_compatibility_obligations
      mapping logical_specs physical_specs;
  clcrvvc_semantic_refinement :
    reuse_source_view_refines_view
      input_view output_view source_view after;
}.

Definition reuse_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_conflict_reuse_view_correct :
  forall input_view output_view mapping conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    conflict_reuse_view_contract
      input_view output_view mapping conflicts source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping conflicts
         before source_view after ok Hret Hok Hreuse Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping conflicts entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    conflict_reuse_value_view_contract
      value input_view output_view mapping conflicts entries
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hreuse Hvalue Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_live_conflict_reuse_view_correct :
  forall input_view output_view mapping intervals conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    live_conflict_reuse_view_contract
      input_view output_view mapping intervals conflicts
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping intervals conflicts
         before source_view after ok Hret Hok Hlive Hreuse Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (checked_conflict_reuse_view_correct
       input_view output_view mapping conflicts
       before source_view after ok Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_conflict_reuse_view_correct :
  forall input_view output_view mapping logical_specs physical_specs conflicts
         before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_conflict_reuse_view_contract
      input_view output_view mapping logical_specs physical_specs conflicts
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping logical_specs physical_specs conflicts
         before source_view after ok Hret Hok Hreuse Hcompat Hsemantics.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_conflict_reuse_view_correct
       input_view output_view mapping conflicts
       before source_view after ok Hret Hok Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_live_conflict_reuse_view_correct :
  forall input_view output_view mapping logical_specs physical_specs
         intervals conflicts before source_view after ok,
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_live_conflict_reuse_view_contract
      input_view output_view mapping logical_specs physical_specs
      intervals conflicts source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view mapping logical_specs physical_specs
         intervals conflicts before source_view after ok
         Hret Hok Hlive Hreuse Hcompat Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_live_conflict_reuse_view_correct
       input_view output_view mapping intervals conflicts
       before source_view after ok Hret Hok Hlive Hreuse Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_live_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping intervals conflicts entries
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    live_conflict_reuse_value_view_contract
      value input_view output_view mapping intervals conflicts entries
      source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping intervals conflicts
         entries before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (checked_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping conflicts entries
       before source_view after ok Hvalue_eqb Hret Hok
       Hreuse Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_compatible_live_conflict_reuse_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view mapping logical_specs physical_specs
         intervals conflicts entries before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reuse_source_view before source_view) ok ->
    ok = true ->
    check_live_conflictb intervals conflicts = true ->
    check_conflict_safe_reuseb mapping conflicts = true ->
    check_reuse_valueb value value_eqb mapping entries = true ->
    check_storage_compatibilityb
      mapping logical_specs physical_specs = true ->
    reuse_source_view_refines_view
      input_view output_view source_view after ->
    compatible_live_conflict_reuse_value_view_contract
      value input_view output_view mapping logical_specs physical_specs
      intervals conflicts entries source_view after /\
    View.view_refinement
      input_view
      (reuse_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view mapping
         logical_specs physical_specs intervals conflicts entries
         before source_view after ok
         Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hcompat Hsemantics.
  pose proof
    (check_live_conflictb_sound intervals conflicts Hlive)
    as Hlive_obligations.
  pose proof
    (check_conflict_safe_reuseb_sound mapping conflicts Hreuse)
    as Hreuse_obligations.
  pose proof
    (live_conflict_and_conflict_safe_reuse_sound
       mapping conflicts intervals Hlive_obligations Hreuse_obligations)
    as Hlive_reuse_safe.
  pose proof
    (check_reuse_valueb_sound
       value value_eqb Hvalue_eqb mapping entries Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       mapping logical_specs physical_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (checked_live_conflict_reuse_value_view_correct
       value value_eqb input_view output_view mapping
       intervals conflicts entries before source_view after ok
       Hvalue_eqb Hret Hok Hlive Hreuse Hvalue Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End ReuseConflictValidator.
