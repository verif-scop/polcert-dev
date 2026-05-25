Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.
Require Import CopyProtocolWitness.

Import ListNotations.

(** Value-flow witness for copy-mediated local storage.

    [CopyProtocolWitness] proves that local reads and copy-outs are defined and
    commits are unique.  This module adds a value-flow layer: copy-in transfers
    the source value to the local cell, local writes update the local value,
    local reads observe the current local value, and copy-out commits the
    current local value to the target. *)

Inductive copy_value_event (value: Type) :=
| CopyValueIn (source_value local_value: value)
| CopyValueRead (read_value: value)
| CopyValueWrite (new_local_value: value)
| CopyValueOut (local_value target_value: value).

Arguments CopyValueIn {value} _ _.
Arguments CopyValueRead {value} _.
Arguments CopyValueWrite {value} _.
Arguments CopyValueOut {value} _ _.

Definition copy_value_trace (value: Type) :=
  list (copy_event * copy_value_event value).

Fixpoint lookup_local_value {value: Type}
    (local_cell: MemCell)
    (locals: list (MemCell * value)) : option value :=
  match locals with
  | [] => None
  | (cell, local_value) :: tail =>
      if mem_cell_strict_eqb local_cell cell
      then Some local_value
      else lookup_local_value local_cell tail
  end.

Fixpoint update_local_value {value: Type}
    (local_cell: MemCell)
    (local_value: value)
    (locals: list (MemCell * value)) : list (MemCell * value) :=
  match locals with
  | [] => [(local_cell, local_value)]
  | (cell, old_value) :: tail =>
      if mem_cell_strict_eqb local_cell cell
      then (cell, local_value) :: tail
      else (cell, old_value) ::
           update_local_value local_cell local_value tail
  end.

Fixpoint copy_value_trace_simulates_from {value: Type}
    (locals: list (MemCell * value))
    (trace: copy_value_trace value) : Prop :=
  match trace with
  | [] => True
  | (CopyIn _ local_cell, CopyValueIn source_value local_value)
      :: tail =>
      source_value = local_value /\
      copy_value_trace_simulates_from
        (update_local_value local_cell local_value locals) tail
  | (LocalRead local_cell, CopyValueRead read_value) :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          read_value = current_value /\
          copy_value_trace_simulates_from locals tail
      | None => False
      end
  | (LocalWrite local_cell, CopyValueWrite new_local_value) :: tail =>
      copy_value_trace_simulates_from
        (update_local_value local_cell new_local_value locals) tail
  | (CopyOut local_cell _, CopyValueOut local_value target_value)
      :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          local_value = current_value /\
          target_value = current_value /\
          copy_value_trace_simulates_from locals tail
      | None => False
      end
  | _ :: _ => False
  end.

Definition copy_value_trace_simulates {value: Type}
    (trace: copy_value_trace value) : Prop :=
  copy_value_trace_simulates_from [] trace.

Fixpoint check_copy_value_trace_fromb {value: Type}
    (value_eqb: value -> value -> bool)
    (locals: list (MemCell * value))
    (trace: copy_value_trace value) : bool :=
  match trace with
  | [] => true
  | (CopyIn _ local_cell, CopyValueIn source_value local_value)
      :: tail =>
      value_eqb source_value local_value &&
      check_copy_value_trace_fromb
        value_eqb
        (update_local_value local_cell local_value locals)
        tail
  | (LocalRead local_cell, CopyValueRead read_value) :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          value_eqb read_value current_value &&
          check_copy_value_trace_fromb value_eqb locals tail
      | None => false
      end
  | (LocalWrite local_cell, CopyValueWrite new_local_value) :: tail =>
      check_copy_value_trace_fromb
        value_eqb
        (update_local_value local_cell new_local_value locals)
        tail
  | (CopyOut local_cell _, CopyValueOut local_value target_value)
      :: tail =>
      match lookup_local_value local_cell locals with
      | Some current_value =>
          value_eqb local_value current_value &&
          value_eqb target_value current_value &&
          check_copy_value_trace_fromb value_eqb locals tail
      | None => false
      end
  | _ :: _ => false
  end.

Definition check_copy_value_traceb {value: Type}
    (value_eqb: value -> value -> bool)
    (trace: copy_value_trace value) : bool :=
  check_copy_value_trace_fromb value_eqb [] trace.

Section Soundness.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Lemma check_copy_value_trace_fromb_sound :
  forall trace locals,
    check_copy_value_trace_fromb
      value_eqb locals trace = true ->
    copy_value_trace_simulates_from locals trace.
Proof.
  induction trace as [|[copy_event' value_event] tail IH];
    intros locals Hcheck; simpl in Hcheck.
  - exact I.
  - destruct copy_event' as [source_cell local_cell
                            | local_cell
                            | local_cell
                            | local_cell target_cell];
      destruct value_event as [source_value local_value
                              | read_value
                              | new_local_value
                              | out_local_value out_target_value];
      simpl in Hcheck; try discriminate.
    + apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + cbn.
      destruct (lookup_local_value local_cell locals) as
        [current_value |] eqn:Hlookup; cbn in Hcheck; try discriminate.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hvalue Htail].
      apply value_eqb_sound in Hvalue.
      split.
      * exact Hvalue.
      * apply IH.
        exact Htail.
    + apply IH.
      exact Hcheck.
    + cbn.
      destruct (lookup_local_value local_cell locals) as
        [current_value |] eqn:Hlookup; cbn in Hcheck; try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as ((Hlocal & Htarget) & Htail).
      apply value_eqb_sound in Hlocal.
      apply value_eqb_sound in Htarget.
      split.
      * exact Hlocal.
      * split.
        -- exact Htarget.
        -- apply IH.
           exact Htail.
Qed.

Record copy_value_simulation_obligations
    (trace: copy_value_trace value) : Prop := {
  cvso_trace_simulates :
    copy_value_trace_simulates trace;
}.

Lemma check_copy_value_traceb_sound :
  forall trace,
    check_copy_value_traceb value_eqb trace = true ->
    copy_value_simulation_obligations trace.
Proof.
  unfold check_copy_value_traceb.
  intros trace Hcheck.
  constructor.
  apply check_copy_value_trace_fromb_sound.
  exact Hcheck.
Qed.

End Soundness.
