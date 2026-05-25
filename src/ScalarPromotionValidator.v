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
Require Import ScalarPromotionWitness.
Require Import ScalarPromotionValueWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for scalar promotion / register replacement.

    The finite witness checks the local protocol around a promoted source cell:
    load before scalar use, no interfering source write, and store-back when
    the source cell is live out.  The promoted scalar is also checked as
    private target storage.  The actual value simulation between the source
    memory events and the scalar events remains an explicit semantic
    refinement obligation. *)

Module ScalarPromotionValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_promotion_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_promotion_source_view_correct :
  forall before source_view ok,
    mayReturn (check_promotion_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition promotion_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Record scalar_promotion_view_contract
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (value_trace: scalar_promotion_value_trace value)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spvvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spvvc_value_simulation :
    scalar_value_simulation_obligations value value_trace;
  spvvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spvvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_compatible_view_contract
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (logical_specs scalar_specs: list storage_spec)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spcvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spcvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spcvc_storage_compatible :
    storage_compatibility_obligations
      [(source_cell, scalar_cell)] logical_specs scalar_specs;
  spcvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Record scalar_promotion_compatible_value_view_contract
    (value: Type)
    (input_view output_view: View.view)
    (source_cell scalar_cell: MemCell)
    (source_liveout: bool)
    (trace: list scalar_promotion_event)
    (value_trace: scalar_promotion_value_trace value)
    (logical_specs scalar_specs: list storage_spec)
    (public_cells frame_cells: list MemCell)
    (source_view after: PolyLang.t) : Prop := {
  spcvvc_protocol :
    scalar_promotion_obligations
      source_cell scalar_cell source_liveout trace;
  spcvvc_value_simulation :
    scalar_value_simulation_obligations value value_trace;
  spcvvc_scalar_separation :
    private_separation_obligations
      [scalar_cell] public_cells frame_cells;
  spcvvc_storage_compatible :
    storage_compatibility_obligations
      [(source_cell, scalar_cell)] logical_specs scalar_specs;
  spcvvc_semantic_refinement :
    promotion_source_view_refines_view
      input_view output_view source_view after;
}.

Definition promotion_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_scalar_promotion_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout trace
         public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_view_contract
      input_view output_view source_cell scalar_cell source_liveout trace
      public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout trace
         public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scalar_promotion_compatible_view_correct :
  forall input_view output_view
         source_cell scalar_cell source_liveout trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_compatible_view_contract
      input_view output_view source_cell scalar_cell source_liveout trace
      logical_specs scalar_specs public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_cell scalar_cell source_liveout trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hret Hok Hpromotion Hcompat Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  pose proof
    (checked_scalar_promotion_view_correct
       input_view output_view source_cell scalar_cell source_liveout trace
       public_cells frame_cells before source_view after ok
       Hret Hok Hpromotion Hseparation Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

Theorem checked_scalar_promotion_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace public_cells frame_cells
      source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_scalar_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_scalar_promotion_compatible_value_view_correct :
  forall (value: Type) (value_eqb: value -> value -> bool)
         input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn
      (check_promotion_source_view before source_view) ok ->
    ok = true ->
    check_scalar_promotionb
      source_cell scalar_cell source_liveout trace = true ->
    check_scalar_value_traceb value_eqb value_trace = true ->
    check_storage_compatibilityb
      [(source_cell, scalar_cell)] logical_specs scalar_specs = true ->
    check_private_separationb
      [scalar_cell] public_cells frame_cells = true ->
    promotion_source_view_refines_view
      input_view output_view source_view after ->
    scalar_promotion_compatible_value_view_contract
      value input_view output_view source_cell scalar_cell
      source_liveout trace value_trace logical_specs scalar_specs
      public_cells frame_cells source_view after /\
    View.view_refinement
      input_view
      (promotion_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb input_view output_view
         source_cell scalar_cell source_liveout trace value_trace
         logical_specs scalar_specs public_cells frame_cells
         before source_view after ok
         Hvalue_eqb Hret Hok Hpromotion Hvalue Hcompat
         Hseparation Hsemantics.
  pose proof
    (check_scalar_promotionb_sound
       source_cell scalar_cell source_liveout trace Hpromotion)
    as Hpromotion_obligations.
  pose proof
    (check_scalar_value_traceb_sound
       value value_eqb Hvalue_eqb value_trace Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_storage_compatibilityb_sound
       [(source_cell, scalar_cell)] logical_specs scalar_specs Hcompat)
    as Hcompat_obligations.
  pose proof
    (check_private_separationb_sound
       [scalar_cell] public_cells frame_cells Hseparation)
    as Hseparation_obligations.
  pose proof
    (checked_scalar_promotion_value_view_correct
       value value_eqb input_view output_view
       source_cell scalar_cell source_liveout trace value_trace
       public_cells frame_cells before source_view after ok
       Hvalue_eqb Hret Hok Hpromotion Hvalue Hseparation Hsemantics)
    as [_ Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End ScalarPromotionValidator.
