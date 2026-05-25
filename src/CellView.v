Require Import List.

Require Import PolyBase.
Require Import StorageWitness.

Import ListNotations.

(** Observer-independent public-cell views.

    [StateView.v] already gives all validators a shared state-view carrier.
    The next layer down is a public-cell view: a target-to-source cell relation
    plus finite/public observability coverage facts.  This structure does not
    depend on a concrete state observer, so it should not be trapped inside a
    [StateObservation] functor instance.

    Existing validators still use their historical functor-local
    [StateObservation.cell_view] records.  This file is the shared carrier they
    can gradually migrate to through adapters, without weakening the existing
    [State.eq] route or rewriting feature proofs in one large step. *)

Record generic_cell_view := {
  gcv_cell_relation : cell_relation;
  gcv_source_observable : MemCell -> Prop;
  gcv_target_observable : MemCell -> Prop;
  gcv_related_source_observable :
    forall target_cell source_cell,
      gcv_cell_relation target_cell source_cell ->
      gcv_source_observable source_cell;
  gcv_related_target_observable :
    forall target_cell source_cell,
      gcv_cell_relation target_cell source_cell ->
      gcv_target_observable target_cell;
  gcv_source_observable_covered :
    forall source_cell,
      gcv_source_observable source_cell ->
      exists target_cell,
        gcv_target_observable target_cell /\
        gcv_cell_relation target_cell source_cell;
  gcv_target_observable_covered :
    forall target_cell,
      gcv_target_observable target_cell ->
      exists source_cell,
        gcv_source_observable source_cell /\
        gcv_cell_relation target_cell source_cell;
}.

(** [target_mid] observes target cells against the intermediate source side,
    while [mid_source] observes intermediate target cells against source cells.
    Composition is meaningful only when the two views agree on the observable
    intermediate cells. *)
Definition generic_cell_view_mid_observables_compatible
    (target_mid mid_source: generic_cell_view) : Prop :=
  (forall mid_cell,
      gcv_source_observable target_mid mid_cell ->
      gcv_target_observable mid_source mid_cell) /\
  (forall mid_cell,
      gcv_target_observable mid_source mid_cell ->
      gcv_source_observable target_mid mid_cell).

Definition compose_generic_cell_view
    (target_mid mid_source: generic_cell_view)
    (Hcompatible:
       generic_cell_view_mid_observables_compatible
         target_mid mid_source)
    : generic_cell_view := {|
  gcv_cell_relation :=
    compose_cell_relation
      (gcv_cell_relation target_mid)
      (gcv_cell_relation mid_source);
  gcv_source_observable :=
    gcv_source_observable mid_source;
  gcv_target_observable :=
    gcv_target_observable target_mid;
  gcv_related_source_observable :=
    fun target_cell source_cell Hrel =>
      let '(ex_intro _ mid_cell Hmid) := Hrel in
      let '(conj _ Hcell_mid_source) := Hmid in
      gcv_related_source_observable
        mid_source mid_cell source_cell Hcell_mid_source;
  gcv_related_target_observable :=
    fun target_cell source_cell Hrel =>
      let '(ex_intro _ mid_cell Hmid) := Hrel in
      let '(conj Hcell_target_mid _) := Hmid in
      gcv_related_target_observable
        target_mid target_cell mid_cell Hcell_target_mid;
  gcv_source_observable_covered :=
    fun source_cell Hsource =>
      match
        gcv_source_observable_covered mid_source source_cell Hsource
      with
      | ex_intro _ mid_cell (conj Hmid_target Hcell_mid_source) =>
          match
            gcv_source_observable_covered
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
  gcv_target_observable_covered :=
    fun target_cell Htarget =>
      match
        gcv_target_observable_covered target_mid target_cell Htarget
      with
      | ex_intro _ mid_cell (conj Hmid_source Hcell_target_mid) =>
          match
            gcv_target_observable_covered
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
