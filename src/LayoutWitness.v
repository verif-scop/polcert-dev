Require Import Bool.
Require Import List.
Require Import ZArith.

Require Import AST.
Require Import Linalg.
Require Import PolyBase.
Require Import PointWitness.
Require Import PolIRs.
Require Import StorageWitness.

Import ListNotations.

(** A first concrete layout-remapping witness.

    This covers padding/array-renaming layouts where the physical target array
    may have a different identifier but keeps the same logical subscripts:

      source: A[i][j]
      target: A_pad[i][j]

    Transpose-style and linearized layouts need an index map in addition to the
    array-id map.  The witnesses below cover two finite fragments: index
    permutation, such as [A[i][j] -> A_t[j][i]], and affine index composition,
    such as [A[i][j] -> A_lin[i * stride + j]]. *)

Record array_rename := {
  ar_target_array : ident;
  ar_source_array : ident;
}.

Record array_index_permutation := {
  aip_target_array : ident;
  aip_source_array : ident;
  aip_permutation : list nat;
}.

Record array_affine_layout := {
  aal_target_array : ident;
  aal_source_array : ident;
  aal_index_map : AffineFunction;
}.

Inductive declared_layout_index_map :=
| layout_same_index
| layout_index_permutation (indices: list nat)
| layout_affine_index_map (index_map: AffineFunction).

Record declared_array_layout := {
  dal_target_array : ident;
  dal_source_array : ident;
  dal_index_map : declared_layout_index_map;
}.

Fixpoint select_list_by_indices {A: Type}
    (indices: list nat) (xs: list A) : option (list A) :=
  match indices with
  | [] => Some []
  | index :: rest =>
      match nth_error xs index, select_list_by_indices rest xs with
      | Some x, Some selected => Some (x :: selected)
      | _, _ => None
      end
  end.

Lemma nth_error_map_some :
  forall (A B: Type) (f: A -> B) xs index x,
    nth_error xs index = Some x ->
    nth_error (map f xs) index = Some (f x).
Proof.
  intros A B f xs.
  induction xs as [|head tail IH]; intros index x Hnth;
    destruct index as [|index]; simpl in Hnth; try discriminate.
  - inversion Hnth. reflexivity.
  - simpl. apply IH. exact Hnth.
Qed.

Lemma select_list_by_indices_map :
  forall (A B: Type) (f: A -> B) indices xs selected,
    select_list_by_indices indices xs = Some selected ->
    select_list_by_indices indices (map f xs) =
    Some (map f selected).
Proof.
  intros A B f indices.
  induction indices as [|index rest IH];
    intros xs selected Hselect; simpl in Hselect.
  - inversion Hselect. reflexivity.
  - destruct (nth_error xs index) as [x|] eqn:Hnth; try discriminate.
    destruct (select_list_by_indices rest xs) as [rest_selected|] eqn:Hrest;
      try discriminate.
    inversion Hselect. subst selected.
    simpl.
    rewrite (nth_error_map_some A B f xs index x Hnth).
    rewrite (IH xs rest_selected Hrest).
    reflexivity.
Qed.

Definition array_id_renamed_by (renames: list array_rename)
    (target_id source_id: ident) : Prop :=
  target_id = source_id \/
  exists rename,
    In rename renames /\
    target_id = ar_target_array rename /\
    source_id = ar_source_array rename.

Definition array_rename_cell_relation
    (renames: list array_rename) : cell_relation :=
  fun target_cell source_cell =>
    array_id_renamed_by renames
      target_cell.(arr_id) source_cell.(arr_id) /\
    veq target_cell.(arr_index) source_cell.(arr_index).

Definition array_index_permutation_cell_relation
    (layouts: list array_index_permutation) : cell_relation :=
  fun target_cell source_cell =>
    (target_cell.(arr_id) = source_cell.(arr_id) /\
     veq target_cell.(arr_index) source_cell.(arr_index)) \/
    exists layout,
      In layout layouts /\
      target_cell.(arr_id) = aip_target_array layout /\
      source_cell.(arr_id) = aip_source_array layout /\
      select_list_by_indices
        (aip_permutation layout)
        source_cell.(arr_index) =
      Some target_cell.(arr_index).

Definition array_affine_layout_cell_relation
    (layouts: list array_affine_layout) : cell_relation :=
  fun target_cell source_cell =>
    (target_cell.(arr_id) = source_cell.(arr_id) /\
     veq target_cell.(arr_index) source_cell.(arr_index)) \/
    exists layout,
      In layout layouts /\
      target_cell.(arr_id) = aal_target_array layout /\
      source_cell.(arr_id) = aal_source_array layout /\
      veq
        target_cell.(arr_index)
        (affine_product (aal_index_map layout) source_cell.(arr_index)).

Definition declared_layout_index_relation
    (index_map: declared_layout_index_map)
    (target_index source_index: list Z) : Prop :=
  match index_map with
  | layout_same_index =>
      veq target_index source_index
  | layout_index_permutation indices =>
      select_list_by_indices indices source_index = Some target_index
  | layout_affine_index_map affine_map =>
      veq target_index (affine_product affine_map source_index)
  end.

Definition declared_layout_cell_relation
    (layouts: list declared_array_layout) : cell_relation :=
  fun target_cell source_cell =>
    (target_cell.(arr_id) = source_cell.(arr_id) /\
     veq target_cell.(arr_index) source_cell.(arr_index)) \/
    exists layout,
      In layout layouts /\
      target_cell.(arr_id) = dal_target_array layout /\
      source_cell.(arr_id) = dal_source_array layout /\
      declared_layout_index_relation
        (dal_index_map layout)
        target_cell.(arr_index)
        source_cell.(arr_index).

Lemma array_rename_cell_relation_reflexive :
  forall renames,
    cell_relation_reflexive (array_rename_cell_relation renames).
Proof.
  unfold cell_relation_reflexive, array_rename_cell_relation.
  intros renames cell.
  split.
  - left; reflexivity.
  - apply veq_refl.
Qed.

Lemma array_index_permutation_cell_relation_reflexive :
  forall layouts,
    cell_relation_reflexive
      (array_index_permutation_cell_relation layouts).
Proof.
  unfold cell_relation_reflexive, array_index_permutation_cell_relation.
  intros layouts cell.
  left.
  split.
  - reflexivity.
  - apply veq_refl.
Qed.

Lemma array_affine_layout_cell_relation_reflexive :
  forall layouts,
    cell_relation_reflexive
      (array_affine_layout_cell_relation layouts).
Proof.
  unfold cell_relation_reflexive, array_affine_layout_cell_relation.
  intros layouts cell.
  left.
  split.
  - reflexivity.
  - apply veq_refl.
Qed.

Lemma declared_layout_cell_relation_reflexive :
  forall layouts,
    cell_relation_reflexive
      (declared_layout_cell_relation layouts).
Proof.
  unfold cell_relation_reflexive, declared_layout_cell_relation.
  intros layouts cell.
  left.
  split.
  - reflexivity.
  - apply veq_refl.
Qed.

Definition array_id_renamed_byb (renames: list array_rename)
    (target_id source_id: ident) : bool :=
  Pos.eqb target_id source_id ||
  existsb
    (fun rename =>
       Pos.eqb target_id (ar_target_array rename) &&
       Pos.eqb source_id (ar_source_array rename))
    renames.

Lemma array_id_renamed_byb_sound :
  forall renames target_id source_id,
    array_id_renamed_byb renames target_id source_id = true ->
    array_id_renamed_by renames target_id source_id.
Proof.
  unfold array_id_renamed_byb, array_id_renamed_by.
  intros renames target_id source_id Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hsame | Hrename].
  - left. apply Pos.eqb_eq. exact Hsame.
  - right.
    apply existsb_exists in Hrename.
    destruct Hrename as (rename & Hin & Hids).
    apply andb_true_iff in Hids.
    destruct Hids as [Htarget Hsource].
    exists rename.
    split; [exact Hin|].
    split.
    + apply Pos.eqb_eq. exact Htarget.
    + apply Pos.eqb_eq. exact Hsource.
Qed.

Fixpoint listzzs_exact_colsb
    (cols: nat) (aff: AffineFunction) : bool :=
  match aff with
  | [] => true
  | (row, _) :: rest =>
      Nat.eqb (length row) cols && listzzs_exact_colsb cols rest
  end.

Lemma listzzs_exact_colsb_sound :
  forall cols aff,
    listzzs_exact_colsb cols aff = true ->
    exact_listzzs_cols cols aff.
Proof.
  intros cols aff.
  induction aff as [|[row constant] rest IH];
    intros Hcheck listz z listzz Hin Heq; simpl in Hcheck.
  - contradiction.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    destruct Hin as [Hin_head | Hin_tail].
    + subst listzz.
      inversion Heq. subst.
      apply Nat.eqb_eq. exact Hhead.
    + eapply IH; eauto.
Qed.

Definition listzzs_uniform_colsb (aff: AffineFunction) : bool :=
  match aff with
  | [] => true
  | (row, _) :: _ => listzzs_exact_colsb (length row) aff
  end.

Lemma listzzs_uniform_colsb_sound :
  forall aff,
    listzzs_uniform_colsb aff = true ->
    exists cols, exact_listzzs_cols cols aff.
Proof.
  intros aff Hcheck.
  destruct aff as [|[row constant] rest].
  - exists 0%nat.
    unfold exact_listzzs_cols.
    intros listz z listzz Hin _.
    contradiction.
  - exists (length row).
    unfold listzzs_uniform_colsb in Hcheck.
    eapply listzzs_exact_colsb_sound.
    exact Hcheck.
Qed.

Definition affine_function_index_permutationb
    (indices: list nat)
    (target_aff source_aff: AffineFunction) : bool :=
  match select_list_by_indices indices source_aff with
  | Some selected_aff => listzzs_strict_eqb target_aff selected_aff
  | None => false
  end.

Lemma affine_function_index_permutationb_sound :
  forall indices target_aff source_aff,
    affine_function_index_permutationb
      indices target_aff source_aff = true ->
    select_list_by_indices indices source_aff = Some target_aff.
Proof.
  intros indices target_aff source_aff Hcheck.
  unfold affine_function_index_permutationb in Hcheck.
  destruct (select_list_by_indices indices source_aff) as [selected_aff|]
    eqn:Hselected; try discriminate.
  apply listzzs_strict_eqb_eq in Hcheck.
  subst.
  reflexivity.
Qed.

Definition affine_function_layoutb
    (layout_aff: AffineFunction)
    (target_aff source_aff: AffineFunction) : bool :=
  listzzs_uniform_colsb source_aff &&
  listzzs_strict_eqb target_aff (matrix_product layout_aff source_aff).

Lemma affine_function_layoutb_sound :
  forall layout_aff target_aff source_aff,
    affine_function_layoutb layout_aff target_aff source_aff = true ->
    target_aff = matrix_product layout_aff source_aff /\
    exists cols, exact_listzzs_cols cols source_aff.
Proof.
  intros layout_aff target_aff source_aff Hcheck.
  unfold affine_function_layoutb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hcols Haff].
  apply listzzs_strict_eqb_eq in Haff.
  apply listzzs_uniform_colsb_sound in Hcols.
  split.
  - exact Haff.
  - exact Hcols.
Qed.

Definition declared_layout_index_accessb
    (index_map: declared_layout_index_map)
    (target_aff source_aff: AffineFunction) : bool :=
  match index_map with
  | layout_same_index =>
      listzzs_strict_eqb target_aff source_aff
  | layout_index_permutation indices =>
      affine_function_index_permutationb indices target_aff source_aff
  | layout_affine_index_map affine_map =>
      affine_function_layoutb affine_map target_aff source_aff
  end.

Lemma declared_layout_index_accessb_sound :
  forall index_map target_aff source_aff,
    declared_layout_index_accessb
      index_map target_aff source_aff = true ->
    forall p,
      declared_layout_index_relation
        index_map
        (affine_product target_aff p)
        (affine_product source_aff p).
Proof.
  intros index_map target_aff source_aff Hcheck p.
  destruct index_map as [|indices|affine_map]; simpl in Hcheck.
  - apply listzzs_strict_eqb_eq in Hcheck.
    subst. apply veq_refl.
  - apply affine_function_index_permutationb_sound in Hcheck.
    exact
      (select_list_by_indices_map
         _ _
         (fun t => dot_product (fst t) p + snd t)
         indices source_aff target_aff Hcheck).
  - apply affine_function_layoutb_sound in Hcheck.
    destruct Hcheck as [Haff Hcols].
    destruct Hcols as [cols Hcols].
    subst target_aff.
    rewrite (matrix_product_assoc affine_map source_aff p cols Hcols).
    apply veq_refl.
Qed.

Definition array_rename_access_pairb (renames: list array_rename)
    (target_access source_access: AccessFunction) : bool :=
  let '(target_id, target_aff) := target_access in
  let '(source_id, source_aff) := source_access in
  array_id_renamed_byb renames target_id source_id &&
  listzzs_strict_eqb target_aff source_aff.

Definition array_index_permutation_access_pairb
    (layouts: list array_index_permutation)
    (target_access source_access: AccessFunction) : bool :=
  let '(target_id, target_aff) := target_access in
  let '(source_id, source_aff) := source_access in
  (Pos.eqb target_id source_id &&
   listzzs_strict_eqb target_aff source_aff) ||
  existsb
    (fun layout =>
       Pos.eqb target_id (aip_target_array layout) &&
       Pos.eqb source_id (aip_source_array layout) &&
       affine_function_index_permutationb
         (aip_permutation layout) target_aff source_aff)
    layouts.

Definition array_affine_layout_access_pairb
    (layouts: list array_affine_layout)
    (target_access source_access: AccessFunction) : bool :=
  let '(target_id, target_aff) := target_access in
  let '(source_id, source_aff) := source_access in
  (Pos.eqb target_id source_id &&
   listzzs_strict_eqb target_aff source_aff) ||
  existsb
    (fun layout =>
       Pos.eqb target_id (aal_target_array layout) &&
       Pos.eqb source_id (aal_source_array layout) &&
       affine_function_layoutb
         (aal_index_map layout) target_aff source_aff)
    layouts.

Definition declared_layout_access_pairb
    (layouts: list declared_array_layout)
    (target_access source_access: AccessFunction) : bool :=
  let '(target_id, target_aff) := target_access in
  let '(source_id, source_aff) := source_access in
  (Pos.eqb target_id source_id &&
   listzzs_strict_eqb target_aff source_aff) ||
  existsb
    (fun layout =>
       Pos.eqb target_id (dal_target_array layout) &&
       Pos.eqb source_id (dal_source_array layout) &&
       declared_layout_index_accessb
         (dal_index_map layout) target_aff source_aff)
    layouts.

Lemma array_rename_access_pairb_sound :
  forall renames target_access source_access,
    array_rename_access_pairb renames target_access source_access = true ->
    same_point_access_relation
      (array_rename_cell_relation renames)
      target_access source_access.
Proof.
  intros renames [target_id target_aff] [source_id source_aff] Hcheck.
  unfold array_rename_access_pairb in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hids Haff].
  apply array_id_renamed_byb_sound in Hids.
  apply listzzs_strict_eqb_eq in Haff.
  unfold same_point_access_relation.
  intros p.
  unfold array_rename_cell_relation.
  simpl.
  split.
  - exact Hids.
  - subst. apply veq_refl.
Qed.

Lemma array_index_permutation_access_pairb_sound :
  forall layouts target_access source_access,
    array_index_permutation_access_pairb
      layouts target_access source_access = true ->
    same_point_access_relation
      (array_index_permutation_cell_relation layouts)
      target_access source_access.
Proof.
  intros layouts [target_id target_aff] [source_id source_aff] Hcheck.
  unfold array_index_permutation_access_pairb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hidentity | Hlayout].
  - apply andb_true_iff in Hidentity.
    destruct Hidentity as [Hid Haff].
    apply Pos.eqb_eq in Hid.
    apply listzzs_strict_eqb_eq in Haff.
    unfold same_point_access_relation.
    intros p.
    unfold array_index_permutation_cell_relation.
    simpl.
    left.
    split.
    + exact Hid.
    + subst. apply veq_refl.
  - apply existsb_exists in Hlayout.
    destruct Hlayout as (layout & Hin & Hlayout_check).
    repeat rewrite andb_true_iff in Hlayout_check.
    destruct Hlayout_check as ((Htarget_id & Hsource_id) & Haff).
    apply Pos.eqb_eq in Htarget_id.
    apply Pos.eqb_eq in Hsource_id.
    apply affine_function_index_permutationb_sound in Haff.
    unfold same_point_access_relation.
    intros p.
    unfold array_index_permutation_cell_relation.
    simpl.
    right.
    exists layout.
    split; [exact Hin|].
    split; [exact Htarget_id|].
    split; [exact Hsource_id|].
    exact
      (select_list_by_indices_map
         _ _
         (fun t => dot_product (fst t) p + snd t)
         (aip_permutation layout)
         source_aff target_aff Haff).
Qed.

Lemma array_affine_layout_access_pairb_sound :
  forall layouts target_access source_access,
    array_affine_layout_access_pairb
      layouts target_access source_access = true ->
    same_point_access_relation
      (array_affine_layout_cell_relation layouts)
      target_access source_access.
Proof.
  intros layouts [target_id target_aff] [source_id source_aff] Hcheck.
  unfold array_affine_layout_access_pairb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hidentity | Hlayout].
  - apply andb_true_iff in Hidentity.
    destruct Hidentity as [Hid Haff].
    apply Pos.eqb_eq in Hid.
    apply listzzs_strict_eqb_eq in Haff.
    unfold same_point_access_relation.
    intros p.
    unfold array_affine_layout_cell_relation.
    simpl.
    left.
    split.
    + exact Hid.
    + subst. apply veq_refl.
  - apply existsb_exists in Hlayout.
    destruct Hlayout as (layout & Hin & Hlayout_check).
    repeat rewrite andb_true_iff in Hlayout_check.
    destruct Hlayout_check as ((Htarget_id & Hsource_id) & Haff).
    apply Pos.eqb_eq in Htarget_id.
    apply Pos.eqb_eq in Hsource_id.
    apply affine_function_layoutb_sound in Haff.
    destruct Haff as [Haff Hcols].
    destruct Hcols as [cols Hcols].
    unfold same_point_access_relation.
    intros p.
    unfold array_affine_layout_cell_relation.
    simpl.
    right.
    exists layout.
    split; [exact Hin|].
    split; [exact Htarget_id|].
    split; [exact Hsource_id|].
    subst target_aff.
    rewrite (matrix_product_assoc (aal_index_map layout) source_aff p cols Hcols).
    apply veq_refl.
Qed.

Lemma declared_layout_access_pairb_sound :
  forall layouts target_access source_access,
    declared_layout_access_pairb
      layouts target_access source_access = true ->
    same_point_access_relation
      (declared_layout_cell_relation layouts)
      target_access source_access.
Proof.
  intros layouts [target_id target_aff] [source_id source_aff] Hcheck.
  unfold declared_layout_access_pairb in Hcheck.
  apply orb_true_iff in Hcheck.
  destruct Hcheck as [Hidentity | Hlayout].
  - apply andb_true_iff in Hidentity.
    destruct Hidentity as [Hid Haff].
    apply Pos.eqb_eq in Hid.
    apply listzzs_strict_eqb_eq in Haff.
    unfold same_point_access_relation.
    intros p.
    unfold declared_layout_cell_relation.
    simpl.
    left.
    split.
    + exact Hid.
    + subst. apply veq_refl.
  - apply existsb_exists in Hlayout.
    destruct Hlayout as (layout & Hin & Hlayout_check).
    repeat rewrite andb_true_iff in Hlayout_check.
    destruct Hlayout_check as ((Htarget_id & Hsource_id) & Hindex).
    apply Pos.eqb_eq in Htarget_id.
    apply Pos.eqb_eq in Hsource_id.
    unfold same_point_access_relation.
    intros p.
    unfold declared_layout_cell_relation.
    simpl.
    right.
    exists layout.
    split; [exact Hin|].
    split; [exact Htarget_id|].
    split; [exact Hsource_id|].
    eapply declared_layout_index_accessb_sound.
    exact Hindex.
Qed.

Fixpoint array_rename_access_listb (renames: list array_rename)
    (target_accesses source_accesses: list AccessFunction) : bool :=
  match target_accesses, source_accesses with
  | [], [] => true
  | target_access :: target_tail, source_access :: source_tail =>
      array_rename_access_pairb renames target_access source_access &&
      array_rename_access_listb renames target_tail source_tail
  | _, _ => false
  end.

Fixpoint array_index_permutation_access_listb
    (layouts: list array_index_permutation)
    (target_accesses source_accesses: list AccessFunction) : bool :=
  match target_accesses, source_accesses with
  | [], [] => true
  | target_access :: target_tail, source_access :: source_tail =>
      array_index_permutation_access_pairb layouts target_access source_access &&
      array_index_permutation_access_listb layouts target_tail source_tail
  | _, _ => false
  end.

Fixpoint array_affine_layout_access_listb
    (layouts: list array_affine_layout)
    (target_accesses source_accesses: list AccessFunction) : bool :=
  match target_accesses, source_accesses with
  | [], [] => true
  | target_access :: target_tail, source_access :: source_tail =>
      array_affine_layout_access_pairb layouts target_access source_access &&
      array_affine_layout_access_listb layouts target_tail source_tail
  | _, _ => false
  end.

Fixpoint declared_layout_access_listb
    (layouts: list declared_array_layout)
    (target_accesses source_accesses: list AccessFunction) : bool :=
  match target_accesses, source_accesses with
  | [], [] => true
  | target_access :: target_tail, source_access :: source_tail =>
      declared_layout_access_pairb layouts target_access source_access &&
      declared_layout_access_listb layouts target_tail source_tail
  | _, _ => false
  end.

Lemma array_rename_access_listb_sound :
  forall renames target_accesses source_accesses,
    array_rename_access_listb renames target_accesses source_accesses = true ->
    access_list_relation
      (array_rename_cell_relation renames)
      target_accesses source_accesses.
Proof.
  intros renames target_accesses.
  induction target_accesses as [|target_access target_tail IH];
    intros source_accesses Hcheck;
    destruct source_accesses as [|source_access source_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply array_rename_access_pairb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma array_index_permutation_access_listb_sound :
  forall layouts target_accesses source_accesses,
    array_index_permutation_access_listb
      layouts target_accesses source_accesses = true ->
    access_list_relation
      (array_index_permutation_cell_relation layouts)
      target_accesses source_accesses.
Proof.
  intros layouts target_accesses.
  induction target_accesses as [|target_access target_tail IH];
    intros source_accesses Hcheck;
    destruct source_accesses as [|source_access source_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply array_index_permutation_access_pairb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma array_affine_layout_access_listb_sound :
  forall layouts target_accesses source_accesses,
    array_affine_layout_access_listb
      layouts target_accesses source_accesses = true ->
    access_list_relation
      (array_affine_layout_cell_relation layouts)
      target_accesses source_accesses.
Proof.
  intros layouts target_accesses.
  induction target_accesses as [|target_access target_tail IH];
    intros source_accesses Hcheck;
    destruct source_accesses as [|source_access source_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply array_affine_layout_access_pairb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma declared_layout_access_listb_sound :
  forall layouts target_accesses source_accesses,
    declared_layout_access_listb
      layouts target_accesses source_accesses = true ->
    access_list_relation
      (declared_layout_cell_relation layouts)
      target_accesses source_accesses.
Proof.
  intros layouts target_accesses.
  induction target_accesses as [|target_access target_tail IH];
    intros source_accesses Hcheck;
    destruct source_accesses as [|source_access source_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply declared_layout_access_pairb_sound; eauto.
    + eapply IH; eauto.
Qed.

Module LayoutWitness (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module Ty := PolIRs.Ty.
Module PL := PolIRs.PolyLang.
Module Storage := StorageWitness PolIRs.

Fixpoint ident_list_eqb (xs ys: list Instr.ident) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      Instr.ident_eqb x y && ident_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma ident_list_eqb_eq :
  forall xs ys,
    ident_list_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hcheck;
    destruct ys as [|y ys]; simpl in Hcheck; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply Instr.ident_eqb_eq in Hhead.
    apply IH in Htail.
    subst. reflexivity.
Qed.

Definition var_decl_eqb
    (x y: Instr.ident * Ty.t) : bool :=
  Instr.ident_eqb (fst x) (fst y) && Ty.eqb (snd x) (snd y).

Lemma var_decl_eqb_eq :
  forall x y,
    var_decl_eqb x y = true ->
    x = y.
Proof.
  intros [xid xty] [yid yty] Hcheck.
  unfold var_decl_eqb in Hcheck.
  simpl in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hid Hty].
  apply Instr.ident_eqb_eq in Hid.
  apply Ty.eqb_eq in Hty.
  subst. reflexivity.
Qed.

Fixpoint var_decl_list_eqb
    (xs ys: list (Instr.ident * Ty.t)) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      var_decl_eqb x y && var_decl_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma var_decl_list_eqb_eq :
  forall xs ys,
    var_decl_list_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hcheck;
    destruct ys as [|y ys]; simpl in Hcheck; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    apply var_decl_eqb_eq in Hhead.
    apply IH in Htail.
    subst. reflexivity.
Qed.

Definition check_pinstr_array_rename_access_remapb
    (renames: list array_rename)
    (source_view after: PL.PolyInstr) : bool :=
  Nat.eqb (PL.pi_depth after) (PL.pi_depth source_view) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr source_view) &&
  listzzs_strict_eqb (PL.pi_poly after) (PL.pi_poly source_view) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PL.pi_point_witness source_view) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (PL.pi_transformation source_view) &&
  array_rename_access_listb
    renames
    (PL.pi_waccess after)
    (PL.pi_waccess source_view) &&
  array_rename_access_listb
    renames
    (PL.pi_raccess after)
    (PL.pi_raccess source_view).

Definition check_pinstr_array_index_permutation_access_remapb
    (layouts: list array_index_permutation)
    (source_view after: PL.PolyInstr) : bool :=
  Nat.eqb (PL.pi_depth after) (PL.pi_depth source_view) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr source_view) &&
  listzzs_strict_eqb (PL.pi_poly after) (PL.pi_poly source_view) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PL.pi_point_witness source_view) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (PL.pi_transformation source_view) &&
  array_index_permutation_access_listb
    layouts
    (PL.pi_waccess after)
    (PL.pi_waccess source_view) &&
  array_index_permutation_access_listb
    layouts
    (PL.pi_raccess after)
    (PL.pi_raccess source_view).

Definition check_pinstr_array_affine_layout_access_remapb
    (layouts: list array_affine_layout)
    (source_view after: PL.PolyInstr) : bool :=
  Nat.eqb (PL.pi_depth after) (PL.pi_depth source_view) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr source_view) &&
  listzzs_strict_eqb (PL.pi_poly after) (PL.pi_poly source_view) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PL.pi_point_witness source_view) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (PL.pi_transformation source_view) &&
  array_affine_layout_access_listb
    layouts
    (PL.pi_waccess after)
    (PL.pi_waccess source_view) &&
  array_affine_layout_access_listb
    layouts
    (PL.pi_raccess after)
    (PL.pi_raccess source_view).

Definition check_pinstr_declared_layout_access_remapb
    (layouts: list declared_array_layout)
    (source_view after: PL.PolyInstr) : bool :=
  Nat.eqb (PL.pi_depth after) (PL.pi_depth source_view) &&
  Instr.eqb (PL.pi_instr after) (PL.pi_instr source_view) &&
  listzzs_strict_eqb (PL.pi_poly after) (PL.pi_poly source_view) &&
  point_space_witness_eqb
    (PL.pi_point_witness after)
    (PL.pi_point_witness source_view) &&
  listzzs_strict_eqb
    (PL.pi_transformation after)
    (PL.pi_transformation source_view) &&
  declared_layout_access_listb
    layouts
    (PL.pi_waccess after)
    (PL.pi_waccess source_view) &&
  declared_layout_access_listb
    layouts
    (PL.pi_raccess after)
    (PL.pi_raccess source_view).

Lemma check_pinstr_array_rename_access_remapb_sound :
  forall renames source_view after,
    check_pinstr_array_rename_access_remapb renames source_view after = true ->
    Storage.same_instance_access_remap
      (array_rename_cell_relation renames)
      source_view after.
Proof.
  intros renames source_view after Hcheck.
  unfold check_pinstr_array_rename_access_remapb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((((Hdepth & Hinstr) & Hpoly) & Hwitness) & Htf) & Hwaccess) & Hraccess).
  constructor.
  - apply Nat.eqb_eq. exact Hdepth.
  - apply Instr.eqb_eq. exact Hinstr.
  - apply listzzs_strict_eqb_eq. exact Hpoly.
  - apply point_space_witness_eqb_eq. exact Hwitness.
  - apply listzzs_strict_eqb_eq. exact Htf.
  - apply array_rename_access_listb_sound. exact Hwaccess.
  - apply array_rename_access_listb_sound. exact Hraccess.
Qed.

Lemma check_pinstr_array_index_permutation_access_remapb_sound :
  forall layouts source_view after,
    check_pinstr_array_index_permutation_access_remapb
      layouts source_view after = true ->
    Storage.same_instance_access_remap
      (array_index_permutation_cell_relation layouts)
      source_view after.
Proof.
  intros layouts source_view after Hcheck.
  unfold check_pinstr_array_index_permutation_access_remapb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((((Hdepth & Hinstr) & Hpoly) & Hwitness) & Htf) & Hwaccess) & Hraccess).
  constructor.
  - apply Nat.eqb_eq. exact Hdepth.
  - apply Instr.eqb_eq. exact Hinstr.
  - apply listzzs_strict_eqb_eq. exact Hpoly.
  - apply point_space_witness_eqb_eq. exact Hwitness.
  - apply listzzs_strict_eqb_eq. exact Htf.
  - apply array_index_permutation_access_listb_sound. exact Hwaccess.
  - apply array_index_permutation_access_listb_sound. exact Hraccess.
Qed.

Lemma check_pinstr_array_affine_layout_access_remapb_sound :
  forall layouts source_view after,
    check_pinstr_array_affine_layout_access_remapb
      layouts source_view after = true ->
    Storage.same_instance_access_remap
      (array_affine_layout_cell_relation layouts)
      source_view after.
Proof.
  intros layouts source_view after Hcheck.
  unfold check_pinstr_array_affine_layout_access_remapb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((((Hdepth & Hinstr) & Hpoly) & Hwitness) & Htf) & Hwaccess) & Hraccess).
  constructor.
  - apply Nat.eqb_eq. exact Hdepth.
  - apply Instr.eqb_eq. exact Hinstr.
  - apply listzzs_strict_eqb_eq. exact Hpoly.
  - apply point_space_witness_eqb_eq. exact Hwitness.
  - apply listzzs_strict_eqb_eq. exact Htf.
  - apply array_affine_layout_access_listb_sound. exact Hwaccess.
  - apply array_affine_layout_access_listb_sound. exact Hraccess.
Qed.

Lemma check_pinstr_declared_layout_access_remapb_sound :
  forall layouts source_view after,
    check_pinstr_declared_layout_access_remapb
      layouts source_view after = true ->
    Storage.same_instance_access_remap
      (declared_layout_cell_relation layouts)
      source_view after.
Proof.
  intros layouts source_view after Hcheck.
  unfold check_pinstr_declared_layout_access_remapb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    ((((((Hdepth & Hinstr) & Hpoly) & Hwitness) & Htf) & Hwaccess) & Hraccess).
  constructor.
  - apply Nat.eqb_eq. exact Hdepth.
  - apply Instr.eqb_eq. exact Hinstr.
  - apply listzzs_strict_eqb_eq. exact Hpoly.
  - apply point_space_witness_eqb_eq. exact Hwitness.
  - apply listzzs_strict_eqb_eq. exact Htf.
  - apply declared_layout_access_listb_sound. exact Hwaccess.
  - apply declared_layout_access_listb_sound. exact Hraccess.
Qed.

Fixpoint check_pinstrs_array_rename_access_remapb
    (renames: list array_rename)
    (source_views afters: list PL.PolyInstr) : bool :=
  match source_views, afters with
  | [], [] => true
  | source_view :: source_tail, after :: after_tail =>
      check_pinstr_array_rename_access_remapb renames source_view after &&
      check_pinstrs_array_rename_access_remapb renames source_tail after_tail
  | _, _ => false
  end.

Fixpoint check_pinstrs_array_index_permutation_access_remapb
    (layouts: list array_index_permutation)
    (source_views afters: list PL.PolyInstr) : bool :=
  match source_views, afters with
  | [], [] => true
  | source_view :: source_tail, after :: after_tail =>
      check_pinstr_array_index_permutation_access_remapb
        layouts source_view after &&
      check_pinstrs_array_index_permutation_access_remapb
        layouts source_tail after_tail
  | _, _ => false
  end.

Fixpoint check_pinstrs_array_affine_layout_access_remapb
    (layouts: list array_affine_layout)
    (source_views afters: list PL.PolyInstr) : bool :=
  match source_views, afters with
  | [], [] => true
  | source_view :: source_tail, after :: after_tail =>
      check_pinstr_array_affine_layout_access_remapb
        layouts source_view after &&
      check_pinstrs_array_affine_layout_access_remapb
        layouts source_tail after_tail
  | _, _ => false
  end.

Fixpoint check_pinstrs_declared_layout_access_remapb
    (layouts: list declared_array_layout)
    (source_views afters: list PL.PolyInstr) : bool :=
  match source_views, afters with
  | [], [] => true
  | source_view :: source_tail, after :: after_tail =>
      check_pinstr_declared_layout_access_remapb
        layouts source_view after &&
      check_pinstrs_declared_layout_access_remapb
        layouts source_tail after_tail
  | _, _ => false
  end.

Lemma check_pinstrs_array_rename_access_remapb_sound :
  forall renames source_views afters,
    check_pinstrs_array_rename_access_remapb
      renames source_views afters = true ->
    Forall2
      (Storage.same_instance_access_remap
         (array_rename_cell_relation renames))
      source_views afters.
Proof.
  intros renames source_views.
  induction source_views as [|source_view source_tail IH];
    intros afters Hcheck;
    destruct afters as [|after after_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply check_pinstr_array_rename_access_remapb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma check_pinstrs_array_index_permutation_access_remapb_sound :
  forall layouts source_views afters,
    check_pinstrs_array_index_permutation_access_remapb
      layouts source_views afters = true ->
    Forall2
      (Storage.same_instance_access_remap
         (array_index_permutation_cell_relation layouts))
      source_views afters.
Proof.
  intros layouts source_views.
  induction source_views as [|source_view source_tail IH];
    intros afters Hcheck;
    destruct afters as [|after after_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply check_pinstr_array_index_permutation_access_remapb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma check_pinstrs_array_affine_layout_access_remapb_sound :
  forall layouts source_views afters,
    check_pinstrs_array_affine_layout_access_remapb
      layouts source_views afters = true ->
    Forall2
      (Storage.same_instance_access_remap
         (array_affine_layout_cell_relation layouts))
      source_views afters.
Proof.
  intros layouts source_views.
  induction source_views as [|source_view source_tail IH];
    intros afters Hcheck;
    destruct afters as [|after after_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply check_pinstr_array_affine_layout_access_remapb_sound; eauto.
    + eapply IH; eauto.
Qed.

Lemma check_pinstrs_declared_layout_access_remapb_sound :
  forall layouts source_views afters,
    check_pinstrs_declared_layout_access_remapb
      layouts source_views afters = true ->
    Forall2
      (Storage.same_instance_access_remap
         (declared_layout_cell_relation layouts))
      source_views afters.
Proof.
  intros layouts source_views.
  induction source_views as [|source_view source_tail IH];
    intros afters Hcheck;
    destruct afters as [|after after_tail];
    simpl in Hcheck; try discriminate.
  - constructor.
  - apply andb_true_iff in Hcheck.
    destruct Hcheck as [Hhead Htail].
    constructor.
    + eapply check_pinstr_declared_layout_access_remapb_sound; eauto.
    + eapply IH; eauto.
Qed.

Definition check_pprog_array_rename_access_remapb
    (renames: list array_rename)
    (source_view after: PL.t) : bool :=
  let '(source_pis, source_varctxt, source_vars) := source_view in
  let '(after_pis, after_varctxt, after_vars) := after in
  ident_list_eqb source_varctxt after_varctxt &&
  var_decl_list_eqb source_vars after_vars &&
  check_pinstrs_array_rename_access_remapb renames source_pis after_pis.

Definition check_pprog_array_index_permutation_access_remapb
    (layouts: list array_index_permutation)
    (source_view after: PL.t) : bool :=
  let '(source_pis, source_varctxt, source_vars) := source_view in
  let '(after_pis, after_varctxt, after_vars) := after in
  ident_list_eqb source_varctxt after_varctxt &&
  var_decl_list_eqb source_vars after_vars &&
  check_pinstrs_array_index_permutation_access_remapb
    layouts source_pis after_pis.

Definition check_pprog_array_affine_layout_access_remapb
    (layouts: list array_affine_layout)
    (source_view after: PL.t) : bool :=
  let '(source_pis, source_varctxt, source_vars) := source_view in
  let '(after_pis, after_varctxt, after_vars) := after in
  ident_list_eqb source_varctxt after_varctxt &&
  var_decl_list_eqb source_vars after_vars &&
  check_pinstrs_array_affine_layout_access_remapb
    layouts source_pis after_pis.

Definition check_pprog_declared_layout_access_remapb
    (layouts: list declared_array_layout)
    (source_view after: PL.t) : bool :=
  let '(source_pis, source_varctxt, source_vars) := source_view in
  let '(after_pis, after_varctxt, after_vars) := after in
  ident_list_eqb source_varctxt after_varctxt &&
  var_decl_list_eqb source_vars after_vars &&
  check_pinstrs_declared_layout_access_remapb
    layouts source_pis after_pis.

Lemma check_pprog_array_rename_access_remapb_sound :
  forall renames source_view after,
    check_pprog_array_rename_access_remapb
      renames source_view after = true ->
    Storage.pprog_same_instance_access_remap
      (array_rename_cell_relation renames)
      source_view after.
Proof.
  intros renames ((source_pis, source_varctxt), source_vars)
         ((after_pis, after_varctxt), after_vars) Hcheck.
  unfold check_pprog_array_rename_access_remapb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hvarctxt & Hvars) & Hpis).
  apply ident_list_eqb_eq in Hvarctxt.
  apply var_decl_list_eqb_eq in Hvars.
  apply check_pinstrs_array_rename_access_remapb_sound in Hpis.
  unfold Storage.pprog_same_instance_access_remap.
  simpl.
  split.
  - symmetry. exact Hvarctxt.
  - split.
    + symmetry. exact Hvars.
    + exact Hpis.
Qed.

Lemma check_pprog_array_affine_layout_access_remapb_sound :
  forall layouts source_view after,
    check_pprog_array_affine_layout_access_remapb
      layouts source_view after = true ->
    Storage.pprog_same_instance_access_remap
      (array_affine_layout_cell_relation layouts)
      source_view after.
Proof.
  intros layouts ((source_pis, source_varctxt), source_vars)
         ((after_pis, after_varctxt), after_vars) Hcheck.
  unfold check_pprog_array_affine_layout_access_remapb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hvarctxt & Hvars) & Hpis).
  apply ident_list_eqb_eq in Hvarctxt.
  apply var_decl_list_eqb_eq in Hvars.
  apply check_pinstrs_array_affine_layout_access_remapb_sound in Hpis.
  unfold Storage.pprog_same_instance_access_remap.
  simpl.
  split.
  - symmetry. exact Hvarctxt.
  - split.
    + symmetry. exact Hvars.
    + exact Hpis.
Qed.

Lemma check_pprog_declared_layout_access_remapb_sound :
  forall layouts source_view after,
    check_pprog_declared_layout_access_remapb
      layouts source_view after = true ->
    Storage.pprog_same_instance_access_remap
      (declared_layout_cell_relation layouts)
      source_view after.
Proof.
  intros layouts ((source_pis, source_varctxt), source_vars)
         ((after_pis, after_varctxt), after_vars) Hcheck.
  unfold check_pprog_declared_layout_access_remapb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hvarctxt & Hvars) & Hpis).
  apply ident_list_eqb_eq in Hvarctxt.
  apply var_decl_list_eqb_eq in Hvars.
  apply check_pinstrs_declared_layout_access_remapb_sound in Hpis.
  unfold Storage.pprog_same_instance_access_remap.
  simpl.
  split.
  - symmetry. exact Hvarctxt.
  - split.
    + symmetry. exact Hvars.
    + exact Hpis.
Qed.

Lemma check_pprog_array_index_permutation_access_remapb_sound :
  forall layouts source_view after,
    check_pprog_array_index_permutation_access_remapb
      layouts source_view after = true ->
    Storage.pprog_same_instance_access_remap
      (array_index_permutation_cell_relation layouts)
      source_view after.
Proof.
  intros layouts ((source_pis, source_varctxt), source_vars)
         ((after_pis, after_varctxt), after_vars) Hcheck.
  unfold check_pprog_array_index_permutation_access_remapb in Hcheck.
  simpl in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hvarctxt & Hvars) & Hpis).
  apply ident_list_eqb_eq in Hvarctxt.
  apply var_decl_list_eqb_eq in Hvars.
  apply check_pinstrs_array_index_permutation_access_remapb_sound in Hpis.
  unfold Storage.pprog_same_instance_access_remap.
  simpl.
  split.
  - symmetry. exact Hvarctxt.
  - split.
    + symmetry. exact Hvars.
    + exact Hpis.
Qed.

End LayoutWitness.
