Require Import Bool.
Require Import List.

Require Import CopyProtocolWitness.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Instance-role alignment for copy-mediated helper events.

    [CopyProtocolWitness] checks an ordered copy/local/commit trace.
    [InstanceProjectionWitness] checks that projected target instances are
    internal or commit-role instances and that commits exact-cover source
    live-outs.  This file connects the two finite witnesses: a copy-out helper
    event must be a commit-role projected instance, while copy-in/local helper
    events must be internal. *)

Definition instance_role_eqb (left right: instance_role) : bool :=
  match left, right with
  | Internal, Internal => true
  | Commit, Commit => true
  | _, _ => false
  end.

Lemma instance_role_eqb_eq :
  forall left right,
    instance_role_eqb left right = true ->
    left = right.
Proof.
  intros [] []; simpl; auto; discriminate.
Qed.

Definition copy_event_projected_role (event: copy_event) : instance_role :=
  match event with
  | CopyIn _ _ => Internal
  | LocalRead _ => Internal
  | LocalWrite _ => Internal
  | CopyOut _ _ => Commit
  end.

Fixpoint copy_instance_trace_matches
    (targets: list projected_instance)
    (trace: list copy_event) : Prop :=
  match targets, trace with
  | [], [] => True
  | target :: targets_tail, event :: trace_tail =>
      projected_role target = copy_event_projected_role event /\
      copy_instance_trace_matches targets_tail trace_tail
  | _, _ => False
  end.

Fixpoint check_copy_instance_traceb
    (targets: list projected_instance)
    (trace: list copy_event) : bool :=
  match targets, trace with
  | [], [] => true
  | target :: targets_tail, event :: trace_tail =>
      instance_role_eqb
        (projected_role target)
        (copy_event_projected_role event) &&
      check_copy_instance_traceb targets_tail trace_tail
  | _, _ => false
  end.

Lemma check_copy_instance_traceb_sound :
  forall targets trace,
    check_copy_instance_traceb targets trace = true ->
    copy_instance_trace_matches targets trace.
Proof.
  induction targets as [|target targets_tail IH];
    intros trace Hcheck; destruct trace as [|event trace_tail];
    simpl in Hcheck; try discriminate.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hrole Htail].
    apply instance_role_eqb_eq in Hrole.
    split.
    + exact Hrole.
    + apply IH.
      exact Htail.
Qed.

Record copy_instance_trace_obligations
    (targets: list projected_instance)
    (trace: list copy_event) : Prop := {
  cito_trace_matches :
    copy_instance_trace_matches targets trace;
}.

Lemma check_copy_instance_traceb_obligations_sound :
  forall targets trace,
    check_copy_instance_traceb targets trace = true ->
    copy_instance_trace_obligations targets trace.
Proof.
  intros targets trace Hcheck.
  constructor.
  apply check_copy_instance_traceb_sound.
  exact Hcheck.
Qed.
