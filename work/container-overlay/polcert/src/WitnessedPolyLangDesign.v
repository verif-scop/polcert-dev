Require Import List.
Require Import ZArith.

Require Import PolyBase.
Require Import TilingWitness.
Require Import InstrTy.
Require Import PointWitness.
Require Import Linalg.

Import ListNotations.

Module WitnessedPolyLangDesign (Instr: INSTR).

Record PolyInstr := {
  pi_depth : nat;
  pi_instr : Instr.t;
  pi_poly : Domain;
  pi_schedule : Schedule;
  pi_transformation : Transformation;
  pi_point_witness : point_space_witness;
  pi_waccess : list AccessFunction;
  pi_raccess : list AccessFunction;
}.

Definition current_point_dim (pi: PolyInstr) : nat :=
  pi_depth pi.

Definition base_point_dim (pi: PolyInstr) : nat :=
  witness_base_point_dim (pi_point_witness pi).

Definition witness_added_dim (pi: PolyInstr) : nat :=
  witness_added_dims (pi_point_witness pi).

Definition current_point_cols (env_dim: nat) (pi: PolyInstr) : nat :=
  env_dim + current_point_dim pi.

Definition base_point_cols (env_dim: nat) (pi: PolyInstr) : nat :=
  env_dim + base_point_dim pi.

Definition current_to_base_transformation
    (env_dim: nat) (pi: PolyInstr) : Transformation :=
  point_witness_projection env_dim (pi_point_witness pi).

Definition current_src_transformation
    (env_dim: nat) (pi: PolyInstr) : Transformation :=
  matrix_product (pi_transformation pi) (current_to_base_transformation env_dim pi).

Definition wf_pinstr (env_dim vars_dim: nat) (pi: PolyInstr) : Prop :=
  let current_cols := current_point_cols env_dim pi in
  let base_cols := base_point_cols env_dim pi in
  current_cols <= vars_dim /\
  base_cols <= vars_dim /\
  exact_listzzs_cols current_cols (pi_poly pi) /\
  exact_listzzs_cols current_cols (pi_schedule pi) /\
  exact_listzzs_cols base_cols (pi_transformation pi) /\
  Forall (fun w => exact_listzzs_cols base_cols (snd w)) (pi_waccess pi) /\
  Forall (fun r => exact_listzzs_cols base_cols (snd r)) (pi_raccess pi).

Definition wf_pinstr_affine (env_dim vars_dim: nat) (pi: PolyInstr) : Prop :=
  wf_pinstr env_dim vars_dim pi /\
  pi_point_witness pi = PSWIdentity (pi_depth pi).

Definition wf_pinstr_tiling (env_dim vars_dim: nat) (pi: PolyInstr) : Prop :=
  wf_pinstr env_dim vars_dim pi /\
  match pi_point_witness pi with
  | PSWIdentity _ => True
  | PSWTiling w => well_formed_statement_tiling_witness w
  end.

Definition project_base_point
    (env: list Z) (pi: PolyInstr) (base current: list Z) : Prop :=
  related_by_point_witness env (pi_point_witness pi) base current.

Definition src_args_of
    (env: list Z) (pi: PolyInstr) (current src_args: list Z) : Prop :=
  src_args = affine_product (current_src_transformation (length env) pi) current.

Definition acc_args_of
    (env: list Z) (pi: PolyInstr) (current acc_args: list Z) : Prop :=
  acc_args = affine_product (current_src_transformation (length env) pi) current.

Lemma wf_pinstr_affine_implies_wf_pinstr :
  forall env_dim vars_dim pi,
    wf_pinstr_affine env_dim vars_dim pi ->
    wf_pinstr env_dim vars_dim pi.
Proof.
  intros env_dim vars_dim pi Hwf.
  unfold wf_pinstr_affine in Hwf.
  tauto.
Qed.

Lemma wf_pinstr_affine_implies_wf_pinstr_tiling :
  forall env_dim vars_dim pi,
    wf_pinstr_affine env_dim vars_dim pi ->
    wf_pinstr_tiling env_dim vars_dim pi.
Proof.
  intros env_dim vars_dim pi Hwf.
  unfold wf_pinstr_affine, wf_pinstr_tiling in *.
  destruct Hwf as [Hwf Hw].
  subst.
  split; auto.
Qed.

Lemma acc_args_of_eq_src_args_of :
  forall env pi current args,
    src_args_of env pi current args ->
    acc_args_of env pi current args.
Proof.
  intros env pi current args Hsrc.
  unfold src_args_of in Hsrc.
  unfold acc_args_of.
  exact Hsrc.
Qed.

End WitnessedPolyLangDesign.
