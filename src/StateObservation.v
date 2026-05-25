Require Import PolyBase.
Require Import PolIRs.
Require Import StorageWitness.
Require Import CellView.
Require Import TransformContract.
Require Import StateView.

(** A minimal observation interface for storage-changing transformations.

    [StateTy.STATE] intentionally exposes only [State.eq].  That is enough for
    schedule validation, but not enough to state layout projection, private
    storage erasure, or commit-only observation.  This module keeps the extra
    observation power separate from [StateTy] so existing proofs and state
    implementations are not forced to change. *)

Module Type CELL_OBSERVER (PolIRs: POLIRS).

Module State := PolIRs.State.

Parameter cell_value : Type.
Parameter cell_value_eq : cell_value -> cell_value -> Prop.

Parameter cell_value_eq_refl :
  forall v, cell_value_eq v v.

Parameter cell_value_eq_sym :
  forall v1 v2, cell_value_eq v1 v2 -> cell_value_eq v2 v1.

Parameter cell_value_eq_trans :
  forall v1 v2 v3,
    cell_value_eq v1 v2 ->
    cell_value_eq v2 v3 ->
    cell_value_eq v1 v3.

Parameter observed_cell_eq : MemCell -> MemCell -> Prop.

Parameter observed_cell_eq_refl :
  forall c, observed_cell_eq c c.

Parameter observe_cell : State.t -> MemCell -> cell_value -> Prop.

(** Observing equal states at the same cell yields equal observed values. *)
Parameter observe_cell_state_eq :
  forall st1 st2 c v1,
    State.eq st1 st2 ->
    observe_cell st1 c v1 ->
    exists v2,
      observe_cell st2 c v2 /\
      cell_value_eq v1 v2.

(** Observing equivalent cell names in the same state yields equal values. *)
Parameter observe_cell_cell_eq :
  forall st c1 c2 v1,
    observed_cell_eq c1 c2 ->
    observe_cell st c1 v1 ->
    exists v2,
      observe_cell st c2 v2 /\
      cell_value_eq v1 v2.

End CELL_OBSERVER.

Module StateObservation
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module State := PolIRs.State.
Module Transform := TransformContract PolIRs.
Module View := StateView PolIRs.
Module Storage := StorageWitness PolIRs.
Module O := Observer.

Definition observer_identity_cell_relation : cell_relation :=
  O.observed_cell_eq.

Lemma observer_identity_cell_relation_reflexive :
  cell_relation_reflexive observer_identity_cell_relation.
Proof.
  unfold cell_relation_reflexive, observer_identity_cell_relation.
  apply O.observed_cell_eq_refl.
Qed.

(** A target cell is related to the source cell whose value it represents. *)
Definition related_cells_observation
    (rel: cell_relation) : Transform.observation :=
  fun st_target st_source =>
    forall target_cell source_cell target_value,
      rel target_cell source_cell ->
      O.observe_cell st_target target_cell target_value ->
      exists source_value,
        O.observe_cell st_source source_cell source_value /\
        O.cell_value_eq target_value source_value.

Definition related_cells_view (rel: cell_relation) : View.view :=
  View.mk_view (related_cells_observation rel).

Theorem related_cells_observation_compose :
  forall target_mid mid_source,
    Transform.relation_included
      (Transform.compose_state_relation
         (related_cells_observation target_mid)
         (related_cells_observation mid_source))
      (related_cells_observation
         (compose_cell_relation target_mid mid_source)).
Proof.
  unfold Transform.relation_included.
  unfold Transform.compose_state_relation.
  unfold related_cells_observation.
  unfold compose_cell_relation.
  intros target_mid mid_source st_target st_source
         (st_mid & Htarget_mid & Hmid_source)
         target_cell source_cell target_value
         (mid_cell & Hcell_target_mid & Hcell_mid_source)
         Htarget.
  destruct
    (Htarget_mid
       target_cell mid_cell target_value Hcell_target_mid Htarget)
    as (mid_value & Hmid & Hvalue_target_mid).
  destruct
    (Hmid_source
       mid_cell source_cell mid_value Hcell_mid_source Hmid)
    as (source_value & Hsource & Hvalue_mid_source).
  exists source_value.
  split.
  - exact Hsource.
  - eapply O.cell_value_eq_trans; eauto.
Qed.

Theorem related_cells_view_compose_included :
  forall target_mid mid_source,
    View.view_included
      (View.compose_view
         (related_cells_view target_mid)
         (related_cells_view mid_source))
      (related_cells_view
         (compose_cell_relation target_mid mid_source)).
Proof.
  unfold View.view_included.
  simpl.
  intros target_mid mid_source.
  apply related_cells_observation_compose.
Qed.

Record cell_view := {
  cv_cell_relation : cell_relation;
  cv_source_observable : MemCell -> Prop;
  cv_target_observable : MemCell -> Prop;
  cv_related_source_observable :
    forall target_cell source_cell,
      cv_cell_relation target_cell source_cell ->
      cv_source_observable source_cell;
  cv_related_target_observable :
    forall target_cell source_cell,
      cv_cell_relation target_cell source_cell ->
      cv_target_observable target_cell;
  cv_source_observable_covered :
    forall source_cell,
      cv_source_observable source_cell ->
      exists target_cell,
        cv_target_observable target_cell /\
        cv_cell_relation target_cell source_cell;
  cv_target_observable_covered :
    forall target_cell,
      cv_target_observable target_cell ->
      exists source_cell,
        cv_source_observable source_cell /\
        cv_cell_relation target_cell source_cell;
}.

Definition cell_view_to_generic (cv: cell_view) : generic_cell_view := {|
  gcv_cell_relation := cv_cell_relation cv;
  gcv_source_observable := cv_source_observable cv;
  gcv_target_observable := cv_target_observable cv;
  gcv_related_source_observable :=
    cv_related_source_observable cv;
  gcv_related_target_observable :=
    cv_related_target_observable cv;
  gcv_source_observable_covered :=
    cv_source_observable_covered cv;
  gcv_target_observable_covered :=
    cv_target_observable_covered cv;
|}.

Definition generic_cell_view_to_cell_view
    (gcv: generic_cell_view) : cell_view := {|
  cv_cell_relation := gcv_cell_relation gcv;
  cv_source_observable := gcv_source_observable gcv;
  cv_target_observable := gcv_target_observable gcv;
  cv_related_source_observable :=
    gcv_related_source_observable gcv;
  cv_related_target_observable :=
    gcv_related_target_observable gcv;
  cv_source_observable_covered :=
    gcv_source_observable_covered gcv;
  cv_target_observable_covered :=
    gcv_target_observable_covered gcv;
|}.

Definition cell_view_observation (cv: cell_view) : Transform.observation :=
  related_cells_observation (cv_cell_relation cv).

Definition cell_view_state_view (cv: cell_view) : View.view :=
  related_cells_view (cv_cell_relation cv).

Definition generic_cell_view_observation
    (gcv: generic_cell_view) : Transform.observation :=
  related_cells_observation (gcv_cell_relation gcv).

Definition generic_cell_view_state_view
    (gcv: generic_cell_view) : View.view :=
  related_cells_view (gcv_cell_relation gcv).

Theorem generic_cell_view_state_view_compose_included :
  forall target_mid mid_source
         (Hcompatible:
            generic_cell_view_mid_observables_compatible
              target_mid mid_source),
    View.view_included
      (View.compose_view
         (generic_cell_view_state_view target_mid)
         (generic_cell_view_state_view mid_source))
      (generic_cell_view_state_view
         (compose_generic_cell_view
            target_mid mid_source Hcompatible)).
Proof.
  intros target_mid mid_source Hcompatible.
  apply related_cells_view_compose_included.
Qed.

Theorem generic_cell_view_to_cell_view_state_view :
  forall gcv,
    cell_view_state_view (generic_cell_view_to_cell_view gcv) =
    generic_cell_view_state_view gcv.
Proof.
  reflexivity.
Qed.

Theorem cell_view_to_generic_state_view :
  forall cv,
    generic_cell_view_state_view (cell_view_to_generic cv) =
    cell_view_state_view cv.
Proof.
  reflexivity.
Qed.

(** [target_mid] observes target cells against the intermediate source side,
    while [mid_source] observes intermediate target cells against source cells.
    To compose their public-cell coverage, the two views must agree on which
    intermediate cells are observable. *)
Definition cell_view_mid_observables_compatible
    (target_mid mid_source: cell_view) : Prop :=
  (forall mid_cell,
      cv_source_observable target_mid mid_cell ->
      cv_target_observable mid_source mid_cell) /\
  (forall mid_cell,
      cv_target_observable mid_source mid_cell ->
      cv_source_observable target_mid mid_cell).

Definition cell_view_mid_observables_compatible_to_generic
    (target_mid mid_source: cell_view)
    (Hcompatible:
       cell_view_mid_observables_compatible target_mid mid_source)
    : generic_cell_view_mid_observables_compatible
        (cell_view_to_generic target_mid)
        (cell_view_to_generic mid_source) :=
  Hcompatible.

Definition generic_cell_view_mid_observables_compatible_to_cell_view
    (target_mid mid_source: generic_cell_view)
    (Hcompatible:
       generic_cell_view_mid_observables_compatible target_mid mid_source)
    : cell_view_mid_observables_compatible
        (generic_cell_view_to_cell_view target_mid)
        (generic_cell_view_to_cell_view mid_source) :=
  Hcompatible.

Definition compose_cell_view
    (target_mid mid_source: cell_view)
    (Hcompatible:
       cell_view_mid_observables_compatible target_mid mid_source)
    : cell_view := {|
  cv_cell_relation :=
    compose_cell_relation
      (cv_cell_relation target_mid)
      (cv_cell_relation mid_source);
  cv_source_observable :=
    cv_source_observable mid_source;
  cv_target_observable :=
    cv_target_observable target_mid;
  cv_related_source_observable :=
    fun target_cell source_cell Hrel =>
      let '(ex_intro _ mid_cell Hmid) := Hrel in
      let '(conj _ Hcell_mid_source) := Hmid in
      cv_related_source_observable
        mid_source mid_cell source_cell Hcell_mid_source;
  cv_related_target_observable :=
    fun target_cell source_cell Hrel =>
      let '(ex_intro _ mid_cell Hmid) := Hrel in
      let '(conj Hcell_target_mid _) := Hmid in
      cv_related_target_observable
        target_mid target_cell mid_cell Hcell_target_mid;
  cv_source_observable_covered :=
    fun source_cell Hsource =>
      match
        cv_source_observable_covered mid_source source_cell Hsource
      with
      | ex_intro _ mid_cell (conj Hmid_target Hcell_mid_source) =>
          match
            cv_source_observable_covered
              target_mid mid_cell
              (proj2 Hcompatible mid_cell Hmid_target)
          with
          | ex_intro _ target_cell (conj Htarget Hcell_target_mid) =>
              ex_intro _
                target_cell
                (conj Htarget
                   (ex_intro _
                      mid_cell
                      (conj Hcell_target_mid Hcell_mid_source)))
          end
      end;
  cv_target_observable_covered :=
    fun target_cell Htarget =>
      match
        cv_target_observable_covered target_mid target_cell Htarget
      with
      | ex_intro _ mid_cell (conj Hmid_source Hcell_target_mid) =>
          match
            cv_target_observable_covered
              mid_source mid_cell
              (proj1 Hcompatible mid_cell Hmid_source)
          with
          | ex_intro _ source_cell (conj Hsource Hcell_mid_source) =>
              ex_intro _
                source_cell
                (conj Hsource
                   (ex_intro _
                      mid_cell
                      (conj Hcell_target_mid Hcell_mid_source)))
          end
      end;
|}.

Theorem cell_view_state_view_compose_included :
  forall target_mid mid_source
         (Hcompatible:
            cell_view_mid_observables_compatible target_mid mid_source),
    View.view_included
      (View.compose_view
         (cell_view_state_view target_mid)
         (cell_view_state_view mid_source))
      (cell_view_state_view
         (compose_cell_view target_mid mid_source Hcompatible)).
Proof.
  intros target_mid mid_source Hcompatible.
  apply related_cells_view_compose_included.
Qed.

Theorem cell_view_to_generic_compose_state_view :
  forall target_mid mid_source
         (Hcompatible:
            cell_view_mid_observables_compatible target_mid mid_source),
    generic_cell_view_state_view
      (cell_view_to_generic
         (compose_cell_view target_mid mid_source Hcompatible)) =
    generic_cell_view_state_view
      (compose_generic_cell_view
         (cell_view_to_generic target_mid)
         (cell_view_to_generic mid_source)
         (cell_view_mid_observables_compatible_to_generic
            target_mid mid_source Hcompatible)).
Proof.
  reflexivity.
Qed.

Theorem generic_cell_view_to_cell_view_compose_state_view :
  forall target_mid mid_source
         (Hcompatible:
            generic_cell_view_mid_observables_compatible
              target_mid mid_source),
    cell_view_state_view
      (generic_cell_view_to_cell_view
         (compose_generic_cell_view
            target_mid mid_source Hcompatible)) =
    cell_view_state_view
      (compose_cell_view
         (generic_cell_view_to_cell_view target_mid)
         (generic_cell_view_to_cell_view mid_source)
         (generic_cell_view_mid_observables_compatible_to_cell_view
            target_mid mid_source Hcompatible)).
Proof.
  reflexivity.
Qed.

(** The same pass contract as [cell_view_transform_contract], but stated over
    the observer-independent public-cell view carrier.  The local
    [cell_view_transform_contract] below remains for existing validators while
    feature-specific code migrates to [generic_cell_view]. *)
Record generic_cell_view_transform_contract
    (public_view: generic_cell_view)
    (before after: PolIRs.PolyLang.t) : Prop := {
  gcvtc_access_remap :
    Storage.pprog_same_instance_access_remap
      (gcv_cell_relation public_view) before after;
  gcvtc_view_refinement :
    View.view_refinement
      (generic_cell_view_state_view public_view)
      (generic_cell_view_state_view public_view)
      before after;
}.

Record composed_generic_cell_view_transform_contract
    (target_mid mid_source: generic_cell_view)
    (Hcompatible:
       generic_cell_view_mid_observables_compatible target_mid mid_source)
    (before after: PolIRs.PolyLang.t) : Prop := {
  cgcvtc_access_remap :
    Storage.pprog_same_instance_access_remap
      (gcv_cell_relation
         (compose_generic_cell_view
            target_mid mid_source Hcompatible))
      before after;
  cgcvtc_view_refinement :
    View.view_refinement
      (View.compose_view
         (generic_cell_view_state_view target_mid)
         (generic_cell_view_state_view mid_source))
      (generic_cell_view_state_view
         (compose_generic_cell_view
            target_mid mid_source Hcompatible))
      before after;
}.

Theorem generic_cell_view_transform_contract_compose :
  forall target_mid mid_source
         (Hcompatible:
            generic_cell_view_mid_observables_compatible
              target_mid mid_source)
         before mid after,
    generic_cell_view_transform_contract target_mid mid after ->
    generic_cell_view_transform_contract mid_source before mid ->
    composed_generic_cell_view_transform_contract
      target_mid mid_source Hcompatible before after.
Proof.
  intros target_mid mid_source Hcompatible before mid after
         Htarget_mid Hmid_source.
  destruct Htarget_mid as [Haccess_target_mid Hview_target_mid].
  destruct Hmid_source as [Haccess_mid_source Hview_mid_source].
  constructor.
  - simpl.
    eapply Storage.pprog_same_instance_access_remap_compose; eauto.
  - pose proof
      (View.view_refinement_compose
         (generic_cell_view_state_view target_mid)
         (generic_cell_view_state_view target_mid)
         (generic_cell_view_state_view mid_source)
         (generic_cell_view_state_view mid_source)
         before mid after
         Hview_target_mid Hview_mid_source)
      as Hcomposed.
    eapply
      (View.view_refinement_monotone
         (View.compose_view
            (generic_cell_view_state_view target_mid)
            (generic_cell_view_state_view mid_source))
         (View.compose_view
            (generic_cell_view_state_view target_mid)
            (generic_cell_view_state_view mid_source))
         (View.compose_view
            (generic_cell_view_state_view target_mid)
            (generic_cell_view_state_view mid_source))
         (generic_cell_view_state_view
            (compose_generic_cell_view
               target_mid mid_source Hcompatible))
         before after).
    + apply View.view_included_refl.
    + apply generic_cell_view_state_view_compose_included.
    + exact Hcomposed.
Qed.

(** A reusable contract for a same-instance storage pass whose access remap and
    endpoint relation are governed by the same public cell view.  The semantic
    refinement remains explicit: the syntactic access witness is only the
    storage-name side condition, not a full instruction simulation proof. *)
Record cell_view_transform_contract
    (public_view: cell_view)
    (before after: PolIRs.PolyLang.t) : Prop := {
  cvtc_access_remap :
    Storage.pprog_same_instance_access_remap
      (cv_cell_relation public_view) before after;
  cvtc_view_refinement :
    View.view_refinement
      (cell_view_state_view public_view)
      (cell_view_state_view public_view)
      before after;
}.

Record composed_cell_view_transform_contract
    (target_mid mid_source: cell_view)
    (Hcompatible:
       cell_view_mid_observables_compatible target_mid mid_source)
    (before after: PolIRs.PolyLang.t) : Prop := {
  ccvtc_access_remap :
    Storage.pprog_same_instance_access_remap
      (cv_cell_relation
         (compose_cell_view target_mid mid_source Hcompatible))
      before after;
  ccvtc_view_refinement :
    View.view_refinement
      (View.compose_view
         (cell_view_state_view target_mid)
         (cell_view_state_view mid_source))
      (cell_view_state_view
         (compose_cell_view target_mid mid_source Hcompatible))
      before after;
}.

Theorem cell_view_transform_contract_compose :
  forall target_mid mid_source
         (Hcompatible:
            cell_view_mid_observables_compatible target_mid mid_source)
         before mid after,
    cell_view_transform_contract target_mid mid after ->
    cell_view_transform_contract mid_source before mid ->
    composed_cell_view_transform_contract
      target_mid mid_source Hcompatible before after.
Proof.
  intros target_mid mid_source Hcompatible before mid after
         Htarget_mid Hmid_source.
  destruct Htarget_mid as [Haccess_target_mid Hview_target_mid].
  destruct Hmid_source as [Haccess_mid_source Hview_mid_source].
  constructor.
  - simpl.
    eapply Storage.pprog_same_instance_access_remap_compose; eauto.
  - pose proof
      (View.view_refinement_compose
         (cell_view_state_view target_mid)
         (cell_view_state_view target_mid)
         (cell_view_state_view mid_source)
         (cell_view_state_view mid_source)
         before mid after
         Hview_target_mid Hview_mid_source)
      as Hcomposed.
    eapply
      (View.view_refinement_monotone
         (View.compose_view
            (cell_view_state_view target_mid)
            (cell_view_state_view mid_source))
         (View.compose_view
            (cell_view_state_view target_mid)
            (cell_view_state_view mid_source))
         (View.compose_view
            (cell_view_state_view target_mid)
            (cell_view_state_view mid_source))
         (cell_view_state_view
            (compose_cell_view target_mid mid_source Hcompatible))
         before after).
    + apply View.view_included_refl.
    + apply cell_view_state_view_compose_included.
    + exact Hcomposed.
Qed.

Theorem cell_view_transform_contract_to_generic :
  forall public_view before after,
    cell_view_transform_contract public_view before after ->
    generic_cell_view_transform_contract
      (cell_view_to_generic public_view) before after.
Proof.
  intros public_view before after Hcontract.
  destruct Hcontract as [Haccess Hview].
  constructor; assumption.
Qed.

Theorem generic_cell_view_transform_contract_to_cell_view :
  forall public_view before after,
    generic_cell_view_transform_contract public_view before after ->
    cell_view_transform_contract
      (generic_cell_view_to_cell_view public_view) before after.
Proof.
  intros public_view before after Hcontract.
  destruct Hcontract as [Haccess Hview].
  constructor; assumption.
Qed.

Definition all_cells_observable (_: MemCell) : Prop := True.

Definition observer_identity_cell_view : cell_view := {|
  cv_cell_relation := observer_identity_cell_relation;
  cv_source_observable := all_cells_observable;
  cv_target_observable := all_cells_observable;
  cv_related_source_observable := fun _ _ _ => I;
  cv_related_target_observable := fun _ _ _ => I;
  cv_source_observable_covered :=
    fun source_cell _ =>
      ex_intro _
        source_cell
        (conj I (O.observed_cell_eq_refl source_cell));
  cv_target_observable_covered :=
    fun target_cell _ =>
      ex_intro _
        target_cell
        (conj I (O.observed_cell_eq_refl target_cell));
|}.

Definition observer_identity_view : View.view :=
  related_cells_view observer_identity_cell_relation.

Definition observer_identity_cell_view_state_view : View.view :=
  cell_view_state_view observer_identity_cell_view.

Lemma identity_related_cells_observation_contains_state_eq :
  Transform.observation_contains_state_eq
    (related_cells_observation observer_identity_cell_relation).
Proof.
  unfold Transform.observation_contains_state_eq.
  unfold related_cells_observation.
  unfold observer_identity_cell_relation.
  intros st_target st_source Hstate target_cell source_cell target_value
         Hcell Htarget.
  pose proof
    (O.observe_cell_state_eq st_target st_source target_cell target_value
       Hstate Htarget)
    as Hstate_obs.
  destruct Hstate_obs as
    (source_value_at_target & Hsource_target & Hvalue_target).
  pose proof
    (O.observe_cell_cell_eq st_source target_cell source_cell
       source_value_at_target Hcell Hsource_target)
    as Hcell_obs.
  destruct Hcell_obs as (source_value & Hsource & Hvalue_source).
  exists source_value.
  split.
  - exact Hsource.
  - eapply O.cell_value_eq_trans; eauto.
Qed.

Definition identity_related_cells_observation_contract
    : Transform.observation_contract := {|
  Transform.oc_observation :=
    related_cells_observation observer_identity_cell_relation;
  Transform.oc_contains_state_eq :=
    identity_related_cells_observation_contains_state_eq;
|}.

Lemma identity_view_included_observer_identity_view :
  View.view_included View.identity_view observer_identity_view.
Proof.
  unfold View.view_included.
  simpl.
  exact identity_related_cells_observation_contains_state_eq.
Qed.

End StateObservation.
