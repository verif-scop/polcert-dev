Require Import List.

Require Import PolyBase.
Require Import PolIRs.
Require Import StorageWitness.
Require Import StateObservation.
Require Import ReuseConflictWitness.

Import ListNotations.

(** Observer-backed state views for boundary reuse maps.

    A conflict-safe reuse witness says which logical values may safely share
    physical storage.  The final observation still needs a boundary map telling
    which physical cell currently represents each source-observable logical
    cell.  This module turns that finite boundary map into the common
    [StateView.view] vocabulary through [StateObservation.related_cells_view].

    The map should be understood as a boundary selector, not as a complete
    lifetime proof.  Conflict/liveness obligations remain in
    [ReuseConflictWitness] and the semantic refinement supplied to the
    validator. *)

Module ReuseStateView
    (PolIRs: POLIRS)
    (Observer: CELL_OBSERVER PolIRs).

Module Observation := StateObservation PolIRs Observer.
Module View := Observation.View.
Module Transform := Observation.Transform.

Definition reuse_observation
    (boundary_mapping: reuse_mapping) : Transform.observation :=
  Observation.related_cells_observation
    (reuse_cell_relation boundary_mapping).

Definition reuse_view
    (boundary_mapping: reuse_mapping) : View.view :=
  Observation.related_cells_view
    (reuse_cell_relation boundary_mapping).

Definition reuse_boundary_cell_relation
    (boundary_mapping: reuse_mapping)
    (source_cells: list MemCell) : cell_relation :=
  fun target_cell source_cell =>
    In source_cell source_cells /\
    reuse_cell_relation boundary_mapping target_cell source_cell.

Definition reuse_boundary_target_observable
    (boundary_mapping: reuse_mapping)
    (source_cells: list MemCell)
    (target_cell: MemCell) : Prop :=
  exists source_cell,
    In source_cell source_cells /\
    reuse_cell_relation boundary_mapping target_cell source_cell.

Definition reuse_boundary_observation
    (boundary_mapping: reuse_mapping)
    (source_cells: list MemCell) : Transform.observation :=
  Observation.related_cells_observation
    (reuse_boundary_cell_relation boundary_mapping source_cells).

Definition reuse_boundary_view
    (boundary_mapping: reuse_mapping)
    (source_cells: list MemCell) : View.view :=
  Observation.related_cells_view
    (reuse_boundary_cell_relation boundary_mapping source_cells).

Definition reuse_boundary_cell_view
    (boundary_mapping: reuse_mapping)
    (source_cells: list MemCell)
    (Hboundary:
       reuse_boundary_obligations boundary_mapping source_cells)
    : Observation.cell_view := {|
  Observation.cv_cell_relation :=
    reuse_boundary_cell_relation boundary_mapping source_cells;
  Observation.cv_source_observable :=
    fun source_cell => In source_cell source_cells;
  Observation.cv_target_observable :=
    reuse_boundary_target_observable boundary_mapping source_cells;
  Observation.cv_related_source_observable :=
    fun _ _ Hrel => proj1 Hrel;
  Observation.cv_related_target_observable :=
    fun target_cell source_cell Hrel =>
      ex_intro _
        source_cell
        (conj (proj1 Hrel) (proj2 Hrel));
  Observation.cv_source_observable_covered :=
    fun source_cell Hsource =>
      match
        rbo_sources_covered
          boundary_mapping source_cells Hboundary
          source_cell Hsource
      with
      | ex_intro _ target_cell Hrel =>
          ex_intro _
            target_cell
            (conj
               (ex_intro _
                  source_cell
                  (conj Hsource Hrel))
               (conj Hsource Hrel))
      end;
  Observation.cv_target_observable_covered :=
    fun target_cell Htarget =>
      match Htarget with
      | ex_intro _ source_cell (conj Hsource Hrel) =>
          ex_intro _
            source_cell
            (conj Hsource (conj Hsource Hrel))
      end;
|}.

End ReuseStateView.
