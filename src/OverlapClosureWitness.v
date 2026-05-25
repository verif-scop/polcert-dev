Require Import Bool.
Require Import List.

Require Import PolyBase.
Require Import InstanceProjectionWitness.

Import ListNotations.

(** Finite local-dependence closure witness for overlapped tiling.

    [InstanceProjectionWitness] proves that target computations project to
    valid source instances and that commit-role computations cover source
    live-outs exactly once.  That is not enough for overlapped tiling: a tile
    may commit an interior instance only if every source dependence used by the
    tile is either an allowed tile live-in or produced by another computation
    in the same tile.

    This file checks that finite side condition.  It deliberately does not
    prove that a concrete instruction trace computes the same value; it records
    the local closure obligation that such a trace/value proof should consume. *)

Record overlap_dependency := {
  overlap_dependency_consumer : logical_instance;
  overlap_dependency_producer : logical_instance;
}.

Record overlap_tile := {
  overlap_tile_liveins : list logical_instance;
  overlap_tile_targets : list projected_instance;
  overlap_tile_dependencies : list overlap_dependency;
}.

Fixpoint overlap_tiles_targets
    (tiles: list overlap_tile) : list projected_instance :=
  match tiles with
  | [] => []
  | tile :: tail =>
      overlap_tile_targets tile ++ overlap_tiles_targets tail
  end.

Definition overlap_dependency_consumer_in_targetsb
    (targets: list projected_instance)
    (dep: overlap_dependency) : bool :=
  logical_instance_inb
    (overlap_dependency_consumer dep)
    (projected_sources targets).

Definition overlap_dependency_producer_availableb
    (liveins: list logical_instance)
    (targets: list projected_instance)
    (dep: overlap_dependency) : bool :=
  logical_instance_inb
    (overlap_dependency_producer dep) liveins ||
  logical_instance_inb
    (overlap_dependency_producer dep)
    (projected_sources targets).

Fixpoint prefix_before_logical_instance
    (consumer: logical_instance)
    (sources: list logical_instance) : list logical_instance :=
  match sources with
  | [] => []
  | source :: tail =>
      if logical_instance_eqb consumer source
      then []
      else source :: prefix_before_logical_instance consumer tail
  end.

Definition source_precedes_in_sources
    (producer consumer: logical_instance)
    (sources: list logical_instance) : Prop :=
  exists before after,
    sources = before ++ consumer :: after /\
    In producer before.

Definition logical_instance_precedesb
    (producer consumer: logical_instance)
    (targets: list projected_instance) : bool :=
  let sources := projected_sources targets in
  logical_instance_inb consumer sources &&
  logical_instance_inb
    producer
    (prefix_before_logical_instance consumer sources).

Definition overlap_dependency_producer_orderedb
    (liveins: list logical_instance)
    (targets: list projected_instance)
    (dep: overlap_dependency) : bool :=
  logical_instance_inb
    (overlap_dependency_producer dep) liveins ||
  logical_instance_precedesb
    (overlap_dependency_producer dep)
    (overlap_dependency_consumer dep)
    targets.

Fixpoint overlap_dependency_consumers_in_targetsb
    (targets: list projected_instance)
    (deps: list overlap_dependency) : bool :=
  match deps with
  | [] => true
  | dep :: tail =>
      overlap_dependency_consumer_in_targetsb targets dep &&
      overlap_dependency_consumers_in_targetsb targets tail
  end.

Fixpoint overlap_dependency_producers_availableb
    (liveins: list logical_instance)
    (targets: list projected_instance)
    (deps: list overlap_dependency) : bool :=
  match deps with
  | [] => true
  | dep :: tail =>
      overlap_dependency_producer_availableb liveins targets dep &&
      overlap_dependency_producers_availableb liveins targets tail
  end.

Fixpoint overlap_dependency_producers_orderedb
    (liveins: list logical_instance)
    (targets: list projected_instance)
    (deps: list overlap_dependency) : bool :=
  match deps with
  | [] => true
  | dep :: tail =>
      overlap_dependency_producer_orderedb liveins targets dep &&
      overlap_dependency_producers_orderedb liveins targets tail
  end.

Definition overlap_tile_closure
    (tile: overlap_tile) : Prop :=
  (forall dep,
      In dep (overlap_tile_dependencies tile) ->
      In (overlap_dependency_consumer dep)
         (projected_sources (overlap_tile_targets tile))) /\
  (forall dep,
      In dep (overlap_tile_dependencies tile) ->
      In (overlap_dependency_producer dep)
         (overlap_tile_liveins tile) \/
      In (overlap_dependency_producer dep)
         (projected_sources (overlap_tile_targets tile))).

Definition overlap_tile_ordered_closure
    (tile: overlap_tile) : Prop :=
  overlap_tile_closure tile /\
  (forall dep,
      In dep (overlap_tile_dependencies tile) ->
      In (overlap_dependency_producer dep)
         (overlap_tile_liveins tile) \/
      source_precedes_in_sources
        (overlap_dependency_producer dep)
        (overlap_dependency_consumer dep)
        (projected_sources (overlap_tile_targets tile))).

Definition check_overlap_tile_closureb
    (tile: overlap_tile) : bool :=
  overlap_dependency_consumers_in_targetsb
    (overlap_tile_targets tile)
    (overlap_tile_dependencies tile) &&
  overlap_dependency_producers_availableb
    (overlap_tile_liveins tile)
    (overlap_tile_targets tile)
    (overlap_tile_dependencies tile).

Definition check_overlap_tile_ordered_closureb
    (tile: overlap_tile) : bool :=
  check_overlap_tile_closureb tile &&
  overlap_dependency_producers_orderedb
    (overlap_tile_liveins tile)
    (overlap_tile_targets tile)
    (overlap_tile_dependencies tile).

Lemma overlap_dependency_consumers_in_targetsb_sound :
  forall targets deps,
    overlap_dependency_consumers_in_targetsb targets deps = true ->
    forall dep,
      In dep deps ->
      In (overlap_dependency_consumer dep) (projected_sources targets).
Proof.
  intros targets deps.
  induction deps as [|dep deps IH]; intros Hcheck dep' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      apply logical_instance_inb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma overlap_dependency_producer_availableb_sound :
  forall liveins targets dep,
    overlap_dependency_producer_availableb liveins targets dep = true ->
    In (overlap_dependency_producer dep) liveins \/
    In (overlap_dependency_producer dep) (projected_sources targets).
Proof.
  intros liveins targets dep Hcheck.
  unfold overlap_dependency_producer_availableb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hlivein | Htarget].
  - left.
    apply logical_instance_inb_sound.
    exact Hlivein.
  - right.
    apply logical_instance_inb_sound.
    exact Htarget.
Qed.

Lemma prefix_before_logical_instance_sound :
  forall consumer sources producer,
    logical_instance_inb consumer sources = true ->
    In producer (prefix_before_logical_instance consumer sources) ->
    source_precedes_in_sources producer consumer sources.
Proof.
  intros consumer sources.
  induction sources as [|source sources IH]; intros producer Hconsumer Hin.
  - unfold logical_instance_inb in Hconsumer.
    simpl in Hconsumer.
    discriminate.
  - simpl in Hin.
    unfold logical_instance_inb in Hconsumer.
    simpl in Hconsumer.
    destruct (logical_instance_eqb consumer source) eqn:Hhead.
    + contradiction.
    + simpl in Hconsumer.
      change (logical_instance_inb consumer sources = true) in Hconsumer.
      destruct Hin as [Heq | Hin_tail].
      * subst producer.
        pose proof
          (logical_instance_inb_sound consumer sources Hconsumer)
          as Hconsumer_in_tail.
        apply in_split in Hconsumer_in_tail.
        destruct Hconsumer_in_tail as (before & after & Hsplit).
        subst sources.
        exists (source :: before), after.
        split.
        -- reflexivity.
        -- simpl. left. reflexivity.
      * destruct (IH producer Hconsumer Hin_tail)
          as (before & after & Hsplit & Hproducer_before).
        subst sources.
        exists (source :: before), after.
        split.
        -- reflexivity.
        -- simpl. right. exact Hproducer_before.
Qed.

Lemma logical_instance_precedesb_sound :
  forall producer consumer targets,
    logical_instance_precedesb producer consumer targets = true ->
    source_precedes_in_sources
      producer consumer (projected_sources targets).
Proof.
  intros producer consumer targets Hcheck.
  unfold logical_instance_precedesb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hconsumer Hproducer].
  apply
    (prefix_before_logical_instance_sound
       consumer (projected_sources targets) producer).
  - exact Hconsumer.
  - apply logical_instance_inb_sound.
    exact Hproducer.
Qed.

Lemma overlap_dependency_producer_orderedb_sound :
  forall liveins targets dep,
    overlap_dependency_producer_orderedb liveins targets dep = true ->
    In (overlap_dependency_producer dep) liveins \/
    source_precedes_in_sources
      (overlap_dependency_producer dep)
      (overlap_dependency_consumer dep)
      (projected_sources targets).
Proof.
  intros liveins targets dep Hcheck.
  unfold overlap_dependency_producer_orderedb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hlivein | Hordered].
  - left.
    apply logical_instance_inb_sound.
    exact Hlivein.
  - right.
    apply logical_instance_precedesb_sound.
    exact Hordered.
Qed.

Lemma overlap_dependency_producers_availableb_sound :
  forall liveins targets deps,
    overlap_dependency_producers_availableb
      liveins targets deps = true ->
    forall dep,
      In dep deps ->
      In (overlap_dependency_producer dep) liveins \/
      In (overlap_dependency_producer dep) (projected_sources targets).
Proof.
  intros liveins targets deps.
  induction deps as [|dep deps IH]; intros Hcheck dep' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply overlap_dependency_producer_availableb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma overlap_dependency_producers_orderedb_sound :
  forall liveins targets deps,
    overlap_dependency_producers_orderedb
      liveins targets deps = true ->
    forall dep,
      In dep deps ->
      In (overlap_dependency_producer dep) liveins \/
      source_precedes_in_sources
        (overlap_dependency_producer dep)
        (overlap_dependency_consumer dep)
        (projected_sources targets).
Proof.
  intros liveins targets deps.
  induction deps as [|dep deps IH]; intros Hcheck dep' Hin;
    simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + subst.
      eapply overlap_dependency_producer_orderedb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma check_overlap_tile_closureb_sound :
  forall tile,
    check_overlap_tile_closureb tile = true ->
    overlap_tile_closure tile.
Proof.
  intros tile Hcheck.
  unfold check_overlap_tile_closureb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hconsumers Hproducers].
  split.
  - eapply overlap_dependency_consumers_in_targetsb_sound.
    exact Hconsumers.
  - eapply overlap_dependency_producers_availableb_sound.
    exact Hproducers.
Qed.

Lemma check_overlap_tile_ordered_closureb_sound :
  forall tile,
    check_overlap_tile_ordered_closureb tile = true ->
    overlap_tile_ordered_closure tile.
Proof.
  intros tile Hcheck.
  unfold check_overlap_tile_ordered_closureb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hclosure Hordered].
  split.
  - apply check_overlap_tile_closureb_sound.
    exact Hclosure.
  - eapply overlap_dependency_producers_orderedb_sound.
    exact Hordered.
Qed.

Fixpoint check_overlap_closureb
    (tiles: list overlap_tile) : bool :=
  match tiles with
  | [] => true
  | tile :: tail =>
      check_overlap_tile_closureb tile &&
      check_overlap_closureb tail
  end.

Fixpoint check_overlap_ordered_closureb
    (tiles: list overlap_tile) : bool :=
  match tiles with
  | [] => true
  | tile :: tail =>
      check_overlap_tile_ordered_closureb tile &&
      check_overlap_ordered_closureb tail
  end.

Record overlap_closure_obligations
    (tiles: list overlap_tile) : Prop := {
  oco_tiles_closed :
    forall tile,
      In tile tiles ->
      overlap_tile_closure tile;
}.

Record overlap_ordered_closure_obligations
    (tiles: list overlap_tile) : Prop := {
  ooco_tiles_closed :
    forall tile,
      In tile tiles ->
      overlap_tile_ordered_closure tile;
}.

Lemma check_overlap_closureb_sound :
  forall tiles,
    check_overlap_closureb tiles = true ->
    overlap_closure_obligations tiles.
Proof.
  induction tiles as [|tile tiles IH]; intros Hcheck.
  - constructor.
    intros tile Hin.
    contradiction.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Htile Htail].
    pose proof (check_overlap_tile_closureb_sound tile Htile)
      as Htile_closed.
    pose proof (IH Htail) as Htail_closed.
    constructor.
    intros tile' Hin.
    destruct Hin as [Heq | Hin_tail].
    + subst. exact Htile_closed.
    + destruct Htail_closed as [Hclosed].
      apply Hclosed.
      exact Hin_tail.
Qed.

Lemma check_overlap_ordered_closureb_sound :
  forall tiles,
    check_overlap_ordered_closureb tiles = true ->
    overlap_ordered_closure_obligations tiles.
Proof.
  induction tiles as [|tile tiles IH]; intros Hcheck.
  - constructor.
    intros tile Hin.
    contradiction.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck.
    destruct Hcheck as [Htile Htail].
    pose proof (check_overlap_tile_ordered_closureb_sound tile Htile)
      as Htile_closed.
    pose proof (IH Htail) as Htail_closed.
    constructor.
    intros tile' Hin.
    destruct Hin as [Heq | Hin_tail].
    + subst. exact Htile_closed.
    + destruct Htail_closed as [Hclosed].
      apply Hclosed.
      exact Hin_tail.
Qed.

Theorem overlap_closure_dependency_available :
  forall tiles tile dep,
    overlap_closure_obligations tiles ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    In (overlap_dependency_producer dep)
       (projected_sources (overlap_tile_targets tile)).
Proof.
  intros tiles tile dep Hclosure Htile Hdep.
  destruct Hclosure as [Hclosed].
  pose proof (Hclosed tile Htile) as Htile_closed.
  destruct Htile_closed as [_ Havailable].
  apply Havailable.
  exact Hdep.
Qed.

Theorem overlap_ordered_closure_dependency_ordered :
  forall tiles tile dep,
    overlap_ordered_closure_obligations tiles ->
    In tile tiles ->
    In dep (overlap_tile_dependencies tile) ->
    In (overlap_dependency_producer dep)
       (overlap_tile_liveins tile) \/
    source_precedes_in_sources
      (overlap_dependency_producer dep)
      (overlap_dependency_consumer dep)
      (projected_sources (overlap_tile_targets tile)).
Proof.
  intros tiles tile dep Hclosure Htile Hdep.
  destruct Hclosure as [Hclosed].
  pose proof (Hclosed tile Htile) as Htile_closed.
  destruct Htile_closed as [_ Hordered].
  apply Hordered.
  exact Hdep.
Qed.
