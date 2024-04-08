From mathcomp Require Import ssreflect ssrbool ssrnat.
From Coq Require Import FunctionalExtensionality.

Class Field (K : Set) := {
  addition : K -> K -> K;
  addition_commutativity : forall k l : K, addition k l = addition l k;
  addition_associativity : forall k l m : K, addition k (addition l m) = addition (addition k l) m;
  zero : K;
  addition_unitality : forall k : K, addition k zero = k;
  opposite : K -> K;
  addition_invertibility : forall k : K, addition k (opposite k) = zero;
  multiplication : K -> K -> K;
  multiplication_commutativity : forall k l : K, multiplication k l = multiplication l k;
  multiplication_associativity : forall k l m : K, multiplication k (multiplication l m) = multiplication (multiplication k l) m;
  one : K;
  multiplication_unitality : forall k : K, multiplication k one = k;
  reciprocal : K -> K;
  multiplication_invertibility : forall k : K, k <> zero -> multiplication k (reciprocal k) = one;
  multiplication_distributivity_over_addition : forall k l m : K, multiplication k (addition l m) = addition (multiplication k l) (multiplication k m);
  zero_and_one_inequality : zero <> one;
}.

Declare Scope field_scope.
Delimit Scope field_scope with field.
Local Open Scope field_scope.

Notation "- k" := (opposite k) : field_scope.
Notation "k + l" := (addition k l) : field_scope.
Notation "0" := zero : field_scope.
Notation "k * l" := (multiplication k l) : field_scope.
Notation "1" := one : field_scope.

Lemma Field_multiplication_absorbability (K : Set) {FK : Field K} :
  forall k : K, k * 0 = 0.
Proof.
  move=> k.
  rewrite -(addition_unitality (k * 0)).
  rewrite -{2}(addition_invertibility (k * 0)).
  rewrite addition_associativity.
  rewrite -multiplication_distributivity_over_addition.
  rewrite addition_unitality.
  by rewrite addition_invertibility.
Qed.

Lemma Field_multiplication_opposite_one (K : Set) {FK : Field K} :
  forall k : K, k * -1%field = - k.
Proof.
  move=> k.
  rewrite -(addition_unitality (k * -1%field)).
  rewrite -(addition_invertibility (k * 1)).
  rewrite addition_associativity.
  rewrite [k * -1%field + k * 1]addition_commutativity.
  rewrite -multiplication_distributivity_over_addition.
  rewrite addition_invertibility.
  rewrite Field_multiplication_absorbability.
  rewrite addition_commutativity.
  rewrite addition_unitality.
  by rewrite multiplication_unitality.
Qed.

Definition Matrix (K : Prop) {FK : Field K} (m n : nat) := forall i j : nat, i < m -> j < n -> K.

Declare Scope matrix_scope.
Delimit Scope matrix_scope with matrix.
Local Open Scope matrix_scope.

Definition Matrix_addition {K : Prop} {FK : Field K} {m n : nat} (A B : Matrix K m n) : Matrix K m n :=
  fun i j Hi Hj => A i j Hi Hj + B i j Hi Hj.

Notation "A + B" := (Matrix_addition A B) : matrix_scope.

Definition Matrix_zero (K : Prop) {FK : Field K} (m n : nat) : Matrix K m n :=
  fun _ _ _ _ => 0.

Notation "'O' K m n" := (Matrix_zero K m n) (at level 1, K at next level, m at next level, n at next level) : matrix_scope.

Definition Matrix_opposite {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) : Matrix K m n :=
  fun i j Hi Hj => - A i j Hi Hj.

Notation "- A" := (Matrix_opposite A) : matrix_scope.

Proposition Matrix_addition_commutativity {K : Prop} {FK : Field K} {m n : nat} (A B : Matrix K m n) :
  A + B = B + A.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite addition_commutativity.
Qed.

Proposition Matrix_addition_associativity {K : Prop} {FK : Field K} {m n : nat} (A B C : Matrix K m n) :
  A + (B + C) = (A + B) + C.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite addition_associativity.
Qed.

Proposition Matrix_addition_unitality {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  A + O K m n = A.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite addition_unitality.
Qed.

Proposition Matrix_addition_invertibility {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  A + (- A) = O K m n.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite addition_invertibility.
Qed.

Definition Matrix_scalar_multiplication {K : Prop} {FK : Field K} {m n : nat} (k : K) (A : Matrix K m n) : Matrix K m n :=
  fun i j Hi Hj => k * A i j Hi Hj.

Notation "k * A" := (Matrix_scalar_multiplication k A) : matrix_scope.

Proposition Matrix_scalar_multiplication_Field_multiplication {K : Prop} {FK : Field K} {m n : nat} (k l : K) (A : Matrix K m n) :
  (k * l)%field * A = k * (l * A).
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite -multiplication_associativity.
Qed.

Proposition Matrix_scalar_multiplication_Field_one {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  1 * A = A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  rewrite multiplication_commutativity.
  by rewrite multiplication_unitality.
Qed.

Proposition Matrix_scalar_multiplication_Field_addition {K : Prop} {FK : Field K} {m n : nat} (k l : K) (A : Matrix K m n) :
  (k + l)%field * A = k * A + l * A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  rewrite multiplication_commutativity.
  rewrite multiplication_distributivity_over_addition.
  rewrite [(A i j Hi Hj * k)%field]multiplication_commutativity.
  by rewrite [(A i j Hi Hj * l)%field]multiplication_commutativity.
Qed.

Proposition Matrix_scalar_multiplication_Field_zero {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  0 * A = O K m n.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  rewrite multiplication_commutativity.
  by rewrite Field_multiplication_absorbability.
Qed.

Proposition Matrix_scalar_multiplication_Field_opposite_one {K : Prop} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  (-1%field)%field * A = - A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  rewrite multiplication_commutativity.
  by rewrite Field_multiplication_opposite_one.
Qed.

Proposition Matrix_scalar_multiplication_Matrix_addition {K : Prop} {FK : Field K} {m n : nat} (k : K) (A B : Matrix K m n) :
  k * (A + B) = k * A + k * B.
Proof.
  rewrite /Matrix_scalar_multiplication.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  extensionality Hi.
  extensionality Hj.
  by rewrite multiplication_distributivity_over_addition.
Qed.
