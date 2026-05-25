Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Value witness for reduction privatization and merge.

    [ReductionMergeWitness] checks chunk coverage, private accumulator
    uniqueness, and merge-order coverage.  This module checks a narrower value
    layer: the merge order is paired with values for the corresponding private
    accumulators, and folding those values with a supplied merge operator
    yields the claimed final value.

    This does not prove that the transformation is allowed to reassociate or
    reorder the source reduction.  The algebraic law remains an explicit
    semantic assumption in [ReductionMergeValidator]. *)

Definition reduction_accumulator_value (value: Type) :=
  (MemCell * value)%type.

Fixpoint reduction_value_lookup {value: Type}
    (cell: MemCell)
    (values: list (reduction_accumulator_value value)) : option value :=
  match values with
  | [] => None
  | (value_cell, value') :: tail =>
      if mem_cell_strict_eqb cell value_cell
      then Some value'
      else reduction_value_lookup cell tail
  end.

Fixpoint reduction_merge_values_for_order {value: Type}
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : option (list value) :=
  match merge_order with
  | [] => Some []
  | cell :: tail =>
      match reduction_value_lookup cell values,
            reduction_merge_values_for_order tail values with
      | Some value', Some tail_values =>
          Some (value' :: tail_values)
      | _, _ => None
      end
  end.

Fixpoint fold_reduction_values {value: Type}
    (merge_op: value -> value -> value)
    (acc: value)
    (values: list value) : value :=
  match values with
  | [] => acc
  | value' :: tail =>
      fold_reduction_values merge_op (merge_op acc value') tail
  end.

Definition reduction_value_merge_result {value: Type}
    (merge_op: value -> value -> value)
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : Prop :=
  exists ordered_values,
    reduction_merge_values_for_order merge_order values =
      Some ordered_values /\
    fold_reduction_values merge_op initial_value ordered_values =
      final_value.

Definition check_reduction_value_mergeb {value: Type}
    (value_eqb: value -> value -> bool)
    (merge_op: value -> value -> value)
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : bool :=
  match reduction_merge_values_for_order merge_order values with
  | Some ordered_values =>
      value_eqb
        (fold_reduction_values merge_op initial_value ordered_values)
        final_value
  | None => false
  end.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Variable merge_op: value -> value -> value.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_reduction_value_mergeb_result_sound :
  forall initial_value final_value merge_order values,
    check_reduction_value_mergeb
      value_eqb merge_op initial_value final_value
      merge_order values = true ->
    reduction_value_merge_result
      merge_op initial_value final_value merge_order values.
Proof.
  intros initial_value final_value merge_order values Hcheck.
  unfold check_reduction_value_mergeb in Hcheck.
  destruct (reduction_merge_values_for_order merge_order values)
    as [ordered_values |] eqn:Hordered; try discriminate.
  apply value_eqb_sound in Hcheck.
  exists ordered_values.
  split.
  - exact Hordered.
  - exact Hcheck.
Qed.

Record reduction_value_merge_obligations
    (initial_value final_value: value)
    (merge_order: list MemCell)
    (values: list (reduction_accumulator_value value)) : Prop := {
  rvmo_merge_result :
    reduction_value_merge_result
      merge_op initial_value final_value merge_order values;
}.

Lemma check_reduction_value_mergeb_sound :
  forall initial_value final_value merge_order values,
    check_reduction_value_mergeb
      value_eqb merge_op initial_value final_value
      merge_order values = true ->
    reduction_value_merge_obligations
      initial_value final_value merge_order values.
Proof.
  intros initial_value final_value merge_order values Hcheck.
  constructor.
  apply check_reduction_value_mergeb_result_sound.
  exact Hcheck.
Qed.

End Soundness.
