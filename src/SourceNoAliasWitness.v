Require Import Bool.
Require Import List.

Require Import Coqlib.
Require Import PolyBase.
Require Import PrivateStorageWitness.

Import ListNotations.

(** Finite witness for source no-alias abstraction.

    This is a boundary precondition, not a transformation.  It records a finite
    footprint for each logical source object and checks that different logical
    objects have disjoint concrete cells. *)

Definition source_object := positive.
Definition source_footprint := (source_object * list MemCell)%type.

Definition source_object_eqb
    (left right: source_object) : bool :=
  Pos.eqb left right.

Lemma source_object_eqb_eq :
  forall left right,
    source_object_eqb left right = true ->
    left = right.
Proof.
  unfold source_object_eqb.
  intros left right Hcheck.
  apply Pos.eqb_eq.
  exact Hcheck.
Qed.

Definition source_object_inb
    (object: source_object)
    (objects: list source_object) : bool :=
  existsb (source_object_eqb object) objects.

Lemma source_object_inb_sound :
  forall object objects,
    source_object_inb object objects = true ->
    In object objects.
Proof.
  unfold source_object_inb.
  intros object objects Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (object' & Hin & Heq).
  apply source_object_eqb_eq in Heq.
  subst. exact Hin.
Qed.

Lemma source_object_inb_complete :
  forall object objects,
    In object objects ->
    source_object_inb object objects = true.
Proof.
  unfold source_object_inb, source_object_eqb.
  intros object objects Hin.
  apply existsb_exists.
  exists object.
  split.
  - exact Hin.
  - apply Pos.eqb_refl.
Qed.

Fixpoint source_objects_nodupb
    (objects: list source_object) : bool :=
  match objects with
  | [] => true
  | object :: tail =>
      negb (source_object_inb object tail) &&
      source_objects_nodupb tail
  end.

Lemma source_objects_nodupb_sound :
  forall objects,
    source_objects_nodupb objects = true ->
    NoDup objects.
Proof.
  induction objects as [|object tail IH]; intros Hcheck;
    simpl in Hcheck.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hnotin Htail].
    apply negb_true_iff in Hnotin.
    constructor.
    + intro Hin.
      apply source_object_inb_complete in Hin.
      rewrite Hin in Hnotin.
      discriminate.
    + apply IH.
      exact Htail.
Qed.

Fixpoint source_footprint_objects
    (footprints: list source_footprint) : list source_object :=
  match footprints with
  | [] => []
  | (object, _) :: tail =>
      object :: source_footprint_objects tail
  end.

Fixpoint source_footprints_nodupb
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells) :: tail =>
      mem_cells_nodupb cells &&
      source_footprints_nodupb tail
  end.

Fixpoint source_footprints_nodup
    (footprints: list source_footprint) : Prop :=
  match footprints with
  | [] => True
  | (_, cells) :: tail =>
      NoDup cells /\ source_footprints_nodup tail
  end.

Lemma source_footprints_nodupb_sound :
  forall footprints,
    source_footprints_nodupb footprints = true ->
    source_footprints_nodup footprints.
Proof.
  induction footprints as [|[object cells] tail IH]; intros Hcheck;
    simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hcells Htail].
    split.
    + apply mem_cells_nodupb_sound.
      exact Hcells.
    + apply IH.
      exact Htail.
Qed.

Definition footprint_disjoint_from
    (cells: list MemCell)
    (footprints: list source_footprint) : Prop :=
  forall object cells',
    In (object, cells') footprints ->
    mem_cells_disjoint cells cells'.

Fixpoint check_footprint_disjoint_fromb
    (cells: list MemCell)
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells') :: tail =>
      mem_cells_disjointb cells cells' &&
      check_footprint_disjoint_fromb cells tail
  end.

Lemma check_footprint_disjoint_fromb_sound :
  forall cells footprints,
    check_footprint_disjoint_fromb cells footprints = true ->
    footprint_disjoint_from cells footprints.
Proof.
  induction footprints as [|[object cells'] tail IH];
    intros Hcheck object' cells'' Hin; simpl in Hcheck, Hin.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Heq | Hin_tail].
    + inversion Heq; subst.
      apply mem_cells_disjointb_sound.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Fixpoint source_footprints_pairwise_disjoint
    (footprints: list source_footprint) : Prop :=
  match footprints with
  | [] => True
  | (_, cells) :: tail =>
      footprint_disjoint_from cells tail /\
      source_footprints_pairwise_disjoint tail
  end.

Fixpoint check_source_footprints_pairwise_disjointb
    (footprints: list source_footprint) : bool :=
  match footprints with
  | [] => true
  | (_, cells) :: tail =>
      check_footprint_disjoint_fromb cells tail &&
      check_source_footprints_pairwise_disjointb tail
  end.

Lemma check_source_footprints_pairwise_disjointb_sound :
  forall footprints,
    check_source_footprints_pairwise_disjointb footprints = true ->
    source_footprints_pairwise_disjoint footprints.
Proof.
  induction footprints as [|[object cells] tail IH]; intros Hcheck;
    simpl in Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    split.
    + apply check_footprint_disjoint_fromb_sound.
      exact Hhead.
    + apply IH.
      exact Htail.
Qed.

Record source_no_alias_obligations
    (footprints: list source_footprint) : Prop := {
  sna_objects_nodup :
    NoDup (source_footprint_objects footprints);
  sna_footprints_nodup :
    source_footprints_nodup footprints;
  sna_pairwise_disjoint :
    source_footprints_pairwise_disjoint footprints;
}.

Definition check_source_no_aliasb
    (footprints: list source_footprint) : bool :=
  source_objects_nodupb (source_footprint_objects footprints) &&
  source_footprints_nodupb footprints &&
  check_source_footprints_pairwise_disjointb footprints.

Lemma check_source_no_aliasb_sound :
  forall footprints,
    check_source_no_aliasb footprints = true ->
    source_no_alias_obligations footprints.
Proof.
  intros footprints Hcheck.
  unfold check_source_no_aliasb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hobjects & Hfootprints) & Hdisjoint).
  constructor.
  - apply source_objects_nodupb_sound.
    exact Hobjects.
  - apply source_footprints_nodupb_sound.
    exact Hfootprints.
  - apply check_source_footprints_pairwise_disjointb_sound.
    exact Hdisjoint.
Qed.
