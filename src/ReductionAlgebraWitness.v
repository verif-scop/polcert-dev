Require Import Bool.
Require Import List.

Import ListNotations.

(** Finite algebra-law witness for reduction privatization.

    Reduction privatization needs an algebraic justification for replacing the
    source reduction order with private partial reductions plus a merge.  For
    general C values this is a semantic assumption: integer addition and
    relaxed floating-point addition have different contracts.  This module
    provides a bounded, checkable witness over an explicit finite carrier.  The
    resulting theorem is intentionally scoped to values in that carrier. *)

Section ReductionAlgebra.

Variable value: Type.
Variable value_eqb: value -> value -> bool.
Variable merge_op: value -> value -> value.
Variable identity: value.

Hypothesis value_eqb_sound:
  forall left right,
    value_eqb left right = true ->
    left = right.

Definition value_inb (x: value) (carrier: list value) : bool :=
  existsb (value_eqb x) carrier.

Definition value_in_carrier (carrier: list value) (x: value) : Prop :=
  In x carrier.

Lemma value_inb_sound :
  forall x carrier,
    value_inb x carrier = true ->
    value_in_carrier carrier x.
Proof.
  unfold value_inb, value_in_carrier.
  intros x carrier Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as (y & Hin & Heq).
  apply value_eqb_sound in Heq.
  subst. exact Hin.
Qed.

Definition reduction_closed_on (carrier: list value) : Prop :=
  forall x y,
    In x carrier ->
    In y carrier ->
    In (merge_op x y) carrier.

Definition reduction_associative_on (carrier: list value) : Prop :=
  forall x y z,
    In x carrier ->
    In y carrier ->
    In z carrier ->
    merge_op (merge_op x y) z =
    merge_op x (merge_op y z).

Definition reduction_commutative_on (carrier: list value) : Prop :=
  forall x y,
    In x carrier ->
    In y carrier ->
    merge_op x y = merge_op y x.

Definition reduction_identity_on (carrier: list value) : Prop :=
  In identity carrier /\
  forall x,
    In x carrier ->
    merge_op identity x = x /\
    merge_op x identity = x.

Definition check_reduction_closed_pairb
    (carrier: list value) (x y: value) : bool :=
  value_inb (merge_op x y) carrier.

Definition check_reduction_assoc_tripleb
    (x y z: value) : bool :=
  value_eqb
    (merge_op (merge_op x y) z)
    (merge_op x (merge_op y z)).

Definition check_reduction_comm_pairb
    (x y: value) : bool :=
  value_eqb (merge_op x y) (merge_op y x).

Definition check_reduction_identity_valueb
    (x: value) : bool :=
  value_eqb (merge_op identity x) x &&
  value_eqb (merge_op x identity) x.

Definition check_reduction_closedb
    (carrier: list value) : bool :=
  forallb
    (fun x =>
       forallb
         (fun y => check_reduction_closed_pairb carrier x y)
         carrier)
    carrier.

Definition check_reduction_associativeb
    (carrier: list value) : bool :=
  forallb
    (fun x =>
       forallb
         (fun y =>
            forallb
              (fun z => check_reduction_assoc_tripleb x y z)
              carrier)
         carrier)
    carrier.

Definition check_reduction_commutativeb
    (carrier: list value) : bool :=
  forallb
    (fun x =>
       forallb
         (fun y => check_reduction_comm_pairb x y)
         carrier)
    carrier.

Definition check_reduction_identityb
    (carrier: list value) : bool :=
  value_inb identity carrier &&
  forallb check_reduction_identity_valueb carrier.

Lemma check_reduction_closedb_sound :
  forall carrier,
    check_reduction_closedb carrier = true ->
    reduction_closed_on carrier.
Proof.
  unfold check_reduction_closedb, reduction_closed_on.
  intros carrier Hcheck x y Hx Hy.
  apply forallb_forall with (x := x) in Hcheck; auto.
  apply forallb_forall with (x := y) in Hcheck; auto.
  unfold check_reduction_closed_pairb in Hcheck.
  apply value_inb_sound.
  exact Hcheck.
Qed.

Lemma check_reduction_associativeb_sound :
  forall carrier,
    check_reduction_associativeb carrier = true ->
    reduction_associative_on carrier.
Proof.
  unfold check_reduction_associativeb, reduction_associative_on.
  intros carrier Hcheck x y z Hx Hy Hz.
  apply forallb_forall with (x := x) in Hcheck.
  2: exact Hx.
  apply forallb_forall with (x := y) in Hcheck.
  2: exact Hy.
  apply forallb_forall with (x := z) in Hcheck.
  2: exact Hz.
  unfold check_reduction_assoc_tripleb in Hcheck.
  apply value_eqb_sound.
  exact Hcheck.
Qed.

Lemma check_reduction_commutativeb_sound :
  forall carrier,
    check_reduction_commutativeb carrier = true ->
    reduction_commutative_on carrier.
Proof.
  unfold check_reduction_commutativeb, reduction_commutative_on.
  intros carrier Hcheck x y Hx Hy.
  apply forallb_forall with (x := x) in Hcheck.
  2: exact Hx.
  apply forallb_forall with (x := y) in Hcheck.
  2: exact Hy.
  unfold check_reduction_comm_pairb in Hcheck.
  apply value_eqb_sound.
  exact Hcheck.
Qed.

Lemma check_reduction_identityb_sound :
  forall carrier,
    check_reduction_identityb carrier = true ->
    reduction_identity_on carrier.
Proof.
  unfold check_reduction_identityb, reduction_identity_on.
  intros carrier Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Hidentity_in Hidentity].
  split.
  - apply value_inb_sound.
    exact Hidentity_in.
  - intros x Hx.
    apply forallb_forall with (x := x) in Hidentity; auto.
    unfold check_reduction_identity_valueb in Hidentity.
    apply andb_true_iff in Hidentity.
    destruct Hidentity as [Hleft Hright].
    split.
    + apply value_eqb_sound.
      exact Hleft.
    + apply value_eqb_sound.
      exact Hright.
Qed.

Record reduction_associative_obligations
    (carrier: list value) : Prop := {
  rao_closed :
    reduction_closed_on carrier;
  rao_associative :
    reduction_associative_on carrier;
  rao_identity :
    reduction_identity_on carrier;
}.

Record reduction_commutative_obligations
    (carrier: list value) : Prop := {
  rco_closed :
    reduction_closed_on carrier;
  rco_associative :
    reduction_associative_on carrier;
  rco_commutative :
    reduction_commutative_on carrier;
  rco_identity :
    reduction_identity_on carrier;
}.

Definition check_reduction_associative_lawb
    (carrier: list value) : bool :=
  check_reduction_closedb carrier &&
  check_reduction_associativeb carrier &&
  check_reduction_identityb carrier.

Definition check_reduction_commutative_lawb
    (carrier: list value) : bool :=
  check_reduction_closedb carrier &&
  check_reduction_associativeb carrier &&
  check_reduction_commutativeb carrier &&
  check_reduction_identityb carrier.

Lemma check_reduction_associative_lawb_sound :
  forall carrier,
    check_reduction_associative_lawb carrier = true ->
    reduction_associative_obligations carrier.
Proof.
  intros carrier Hcheck.
  unfold check_reduction_associative_lawb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as ((Hclosed & Hassoc) & Hidentity).
  constructor.
  - apply check_reduction_closedb_sound.
    exact Hclosed.
  - apply check_reduction_associativeb_sound.
    exact Hassoc.
  - apply check_reduction_identityb_sound.
    exact Hidentity.
Qed.

Lemma check_reduction_commutative_lawb_sound :
  forall carrier,
    check_reduction_commutative_lawb carrier = true ->
    reduction_commutative_obligations carrier.
Proof.
  intros carrier Hcheck.
  unfold check_reduction_commutative_lawb in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as (((Hclosed & Hassoc) & Hcomm) & Hidentity).
  constructor.
  - apply check_reduction_closedb_sound.
    exact Hclosed.
  - apply check_reduction_associativeb_sound.
    exact Hassoc.
  - apply check_reduction_commutativeb_sound.
    exact Hcomm.
  - apply check_reduction_identityb_sound.
    exact Hidentity.
Qed.

End ReductionAlgebra.
