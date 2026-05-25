Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for padded/injective layout maps.

    The witness treats a layout rewrite as a finite source-to-target cell map at
    the boundary.  It checks that the map is functional on source cells,
    injective on target cells, all represented target cells are allocated, and
    padding cells are allocated but outside the represented target image. *)

Definition padding_layout_mapping := list (MemCell * MemCell).

Fixpoint padding_layout_sources
    (mapping: padding_layout_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (source_cell, _) :: tail =>
      source_cell :: padding_layout_sources tail
  end.

Fixpoint padding_layout_targets
    (mapping: padding_layout_mapping) : list MemCell :=
  match mapping with
  | [] => []
  | (_, target_cell) :: tail =>
      target_cell :: padding_layout_targets tail
  end.

Record padding_layout_obligations
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell) : Prop := {
  plo_source_functional :
    NoDup (padding_layout_sources mapping);
  plo_target_injective :
    NoDup (padding_layout_targets mapping);
  plo_targets_allocated :
    forall cell,
      In cell (padding_layout_targets mapping) ->
      In cell allocated_cells;
  plo_padding_nodup :
    NoDup padding_cells;
  plo_padding_allocated :
    forall cell,
      In cell padding_cells ->
      In cell allocated_cells;
  plo_padding_outside_targets :
    mem_cells_disjoint
      padding_cells (padding_layout_targets mapping);
}.

Definition check_padding_layoutb
    (mapping: padding_layout_mapping)
    (padding_cells allocated_cells: list MemCell) : bool :=
  mem_cells_nodupb (padding_layout_sources mapping) &&
  mem_cells_nodupb (padding_layout_targets mapping) &&
  mem_cells_subsetb (padding_layout_targets mapping) allocated_cells &&
  mem_cells_nodupb padding_cells &&
  mem_cells_subsetb padding_cells allocated_cells &&
  mem_cells_disjointb padding_cells (padding_layout_targets mapping).

Lemma check_padding_layoutb_sound :
  forall mapping padding_cells allocated_cells,
    check_padding_layoutb
      mapping padding_cells allocated_cells = true ->
    padding_layout_obligations
      mapping padding_cells allocated_cells.
Proof.
  intros mapping padding_cells allocated_cells Hcheck.
  unfold check_padding_layoutb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((((Hsource & Htarget) & Htarget_alloc) &
                        Hpadding_nodup) & Hpadding_alloc) &
                       Hpadding_disjoint).
  constructor.
  - apply mem_cells_nodupb_sound.
    exact Hsource.
  - apply mem_cells_nodupb_sound.
    exact Htarget.
  - eapply mem_cells_subsetb_sound.
    exact Htarget_alloc.
  - apply mem_cells_nodupb_sound.
    exact Hpadding_nodup.
  - eapply mem_cells_subsetb_sound.
    exact Hpadding_alloc.
  - apply mem_cells_disjointb_sound.
    exact Hpadding_disjoint.
Qed.
