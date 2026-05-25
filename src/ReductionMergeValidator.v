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
Require Import ReductionMergeWitness.
Require Import ReductionMergeValueWitness.
Require Import ReductionAlgebraWitness.
Require Import StorageCompatibilityWitness.

Import ListNotations.

(** View-level wrapper for reduction privatization and merge.

    The finite witness checks reduction-domain partitioning and private
    accumulator/merge coverage.  The algebraic law required to replace the
    source reduction order by private partials plus a merge is not a boolean
    syntactic fact; it remains an explicit proposition in the contract. *)

Module ReductionMergeValidator (PolIRs: POLIRS).

Module PolyLang := PolIRs.PolyLang.
Module Pipeline := ViewPipeline PolIRs.
Module AffineCore := Pipeline.AffineCore.
Module Transform := Pipeline.Transform.
Module View := Pipeline.View.

Definition check_reduction_source_view
    (before source_view: PolyLang.t) : imp bool :=
  Pipeline.check_source_view before source_view.

Theorem check_reduction_source_view_correct :
  forall before source_view ok,
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    Transform.refinement_under
      Transform.identity_observation before source_view.
Proof.
  exact Pipeline.check_source_view_correct.
Qed.

Definition reduction_source_view_refines_view
    (input_view output_view: View.view)
    (source_view after: PolyLang.t) : Prop :=
  Pipeline.source_view_refines_view
    input_view output_view source_view after.

Fixpoint reduction_accumulator_storage_mapping
    (public_accumulator: MemCell)
    (partial_accumulators: list MemCell) : list (MemCell * MemCell) :=
  match partial_accumulators with
  | [] => []
  | partial_accumulator :: tail =>
      (public_accumulator, partial_accumulator) ::
      reduction_accumulator_storage_mapping public_accumulator tail
  end.

Record reduction_merge_view_contract
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (merge_law: Prop)
    (source_view after: PolyLang.t) : Prop := {
  rmvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmvc_merge_law :
    merge_law;
  rmvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (merge_law: Prop)
    (source_view after: PolyLang.t) : Prop := {
  rmvvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmvvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmvvc_merge_law :
    merge_law;
  rmvvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_associative_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmavc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmavc_algebra :
    reduction_associative_obligations
      value merge_op identity carrier;
  rmavc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmcvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmcvc_algebra :
    reduction_commutative_obligations
      value merge_op identity carrier;
  rmcvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_associative_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmavvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmavvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmavvc_algebra :
    reduction_associative_obligations
      value merge_op identity carrier;
  rmavvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmcsvc_merge_witness :
    reduction_merge_obligations
      source_domain chunks partial_accumulators merge_order;
  rmcsvc_value_merge :
    reduction_value_merge_obligations
      value merge_op initial_value final_value
      merge_order accumulator_values;
  rmcsvc_algebra :
    reduction_commutative_obligations
      value merge_op identity carrier;
  rmcsvc_semantic_refinement :
    reduction_source_view_refines_view
      input_view output_view source_view after;
}.

Record reduction_merge_commutative_compatible_value_view_contract
    (value: Type)
    (merge_op: value -> value -> value)
    (identity: value)
    (input_view output_view: View.view)
    (source_domain: list logical_instance)
    (chunks: reduction_chunks)
    (partial_accumulators merge_order: list MemCell)
    (public_accumulator: MemCell)
    (public_specs accumulator_specs: list storage_spec)
    (initial_value final_value: value)
    (accumulator_values: list (reduction_accumulator_value value))
    (carrier: list value)
    (source_view after: PolyLang.t) : Prop := {
  rmccsvc_value_base :
    reduction_merge_commutative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after;
  rmccsvc_storage_compatible :
    storage_compatibility_obligations
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs;
}.

Definition reduction_pipeline_final_view
    (output_view: View.view) : View.view :=
  Pipeline.pipeline_final_view output_view.

Theorem checked_reduction_merge_view_correct :
  forall input_view output_view
         source_domain chunks partial_accumulators merge_order
         (merge_law: Prop)
         before source_view after ok,
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    merge_law ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_view_contract
      input_view output_view source_domain chunks
      partial_accumulators merge_order merge_law source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros input_view output_view
         source_domain chunks partial_accumulators merge_order merge_law
         before source_view after ok Hret Hok Hmerge Hlaw Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_associative_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_associative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_associative_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_associative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order carrier
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_commutative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values
         (merge_law: Prop)
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    merge_law ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_value_view_contract
      value merge_op input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values merge_law source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values merge_law
         before source_view after ok Hvalue_eqb Hret Hok Hmerge
         Hvalue Hlaw Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_associative_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_associative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_associative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_reduction_associative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order initial_value final_value
      accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics.
  pose proof
    (check_reduction_mergeb_sound
       source_domain chunks partial_accumulators merge_order Hmerge)
    as Hmerge_obligations.
  pose proof
    (check_reduction_value_mergeb_sound
       value value_eqb merge_op Hvalue_eqb
       initial_value final_value merge_order accumulator_values Hvalue)
    as Hvalue_obligations.
  pose proof
    (check_reduction_commutative_lawb_sound
       value value_eqb merge_op identity Hvalue_eqb carrier Halgebra)
    as Halgebra_obligations.
  split.
  - constructor; assumption.
  - apply
      (Pipeline.compose_checked_source_view
         input_view output_view before source_view after ok);
      assumption.
Qed.

Theorem checked_reduction_merge_commutative_compatible_value_view_correct :
  forall (value: Type)
         (value_eqb: value -> value -> bool)
         (merge_op: value -> value -> value)
         identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         before source_view after ok,
    (forall left right,
       value_eqb left right = true ->
       left = right) ->
    mayReturn (check_reduction_source_view before source_view) ok ->
    ok = true ->
    check_reduction_mergeb
      source_domain chunks partial_accumulators merge_order = true ->
    @check_reduction_value_mergeb
      value value_eqb merge_op initial_value final_value
      merge_order accumulator_values = true ->
    @check_reduction_commutative_lawb
      value value_eqb merge_op identity carrier = true ->
    check_storage_compatibilityb
      (reduction_accumulator_storage_mapping
         public_accumulator partial_accumulators)
      public_specs accumulator_specs = true ->
    reduction_source_view_refines_view
      input_view output_view source_view after ->
    reduction_merge_commutative_compatible_value_view_contract
      value merge_op identity input_view output_view source_domain chunks
      partial_accumulators merge_order public_accumulator
      public_specs accumulator_specs
      initial_value final_value accumulator_values carrier source_view after /\
    View.view_refinement
      input_view
      (reduction_pipeline_final_view output_view)
      before after.
Proof.
  intros value value_eqb merge_op identity
         input_view output_view
         source_domain chunks partial_accumulators merge_order
         public_accumulator public_specs accumulator_specs
         initial_value final_value accumulator_values carrier
         before source_view after ok
         Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hstorage Hsemantics.
  pose proof
    (check_storage_compatibilityb_sound
       (reduction_accumulator_storage_mapping
          public_accumulator partial_accumulators)
       public_specs accumulator_specs Hstorage)
    as Hstorage_obligations.
  pose proof
    (checked_reduction_merge_commutative_value_view_correct
       value value_eqb merge_op identity input_view output_view
       source_domain chunks partial_accumulators merge_order
       initial_value final_value accumulator_values carrier
       before source_view after ok
       Hvalue_eqb Hret Hok Hmerge Hvalue Halgebra Hsemantics)
    as [Hvalue_contract Hview].
  split.
  - constructor; assumption.
  - exact Hview.
Qed.

End ReductionMergeValidator.
