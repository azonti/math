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

Definition Matrix (K : Set) {FK : Field K} (m n : nat) := forall (i : {sval_i : nat | sval_i < m}) (j : {sval_j : nat | sval_j < n}), K.

Declare Scope matrix_scope.
Delimit Scope matrix_scope with matrix.
Local Open Scope matrix_scope.

Definition Matrix_addition {K : Set} {FK : Field K} {m n : nat} (A B : Matrix K m n) : Matrix K m n :=
  fun i j => A i j + B i j.

Notation "A + B" := (Matrix_addition A B) : matrix_scope.

Definition Matrix_zero (K : Set) {FK : Field K} (m n : nat) : Matrix K m n :=
  fun _ _ => 0.

Notation "'O' K m n" := (Matrix_zero K m n) (at level 1, K at next level, m at next level, n at next level) : matrix_scope.

Definition Matrix_opposite {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) : Matrix K m n :=
  fun i j => - A i j.

Notation "- A" := (Matrix_opposite A) : matrix_scope.

Proposition Matrix_addition_commutativity {K : Set} {FK : Field K} {m n : nat} (A B : Matrix K m n) :
  A + B = B + A.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  by rewrite addition_commutativity.
Qed.

Proposition Matrix_addition_associativity {K : Set} {FK : Field K} {m n : nat} (A B C : Matrix K m n) :
  A + (B + C) = (A + B) + C.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  by rewrite addition_associativity.
Qed.

Proposition Matrix_addition_unitality {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  A + O K m n = A.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  by rewrite addition_unitality.
Qed.

Proposition Matrix_addition_invertibility {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  A + (- A) = O K m n.
Proof.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  by rewrite addition_invertibility.
Qed.

Definition Matrix_scalar_multiplication {K : Set} {FK : Field K} {m n : nat} (k : K) (A : Matrix K m n) : Matrix K m n :=
  fun i j => k * A i j.

Notation "k * A" := (Matrix_scalar_multiplication k A) : matrix_scope.

Proposition Matrix_scalar_multiplication_Field_multiplication {K : Set} {FK : Field K} {m n : nat} (k l : K) (A : Matrix K m n) :
  (k * l)%field * A = k * (l * A).
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  by rewrite -multiplication_associativity.
Qed.

Proposition Matrix_scalar_multiplication_Field_one {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  1 * A = A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  rewrite multiplication_commutativity.
  by rewrite multiplication_unitality.
Qed.

Proposition Matrix_scalar_multiplication_Field_addition {K : Set} {FK : Field K} {m n : nat} (k l : K) (A : Matrix K m n) :
  (k + l)%field * A = k * A + l * A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  rewrite multiplication_commutativity.
  rewrite multiplication_distributivity_over_addition.
  rewrite [(A i j * k)%field]multiplication_commutativity.
  by rewrite [(A i j * l)%field]multiplication_commutativity.
Qed.

Proposition Matrix_scalar_multiplication_Field_zero {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  0 * A = O K m n.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  rewrite multiplication_commutativity.
  by rewrite Field_multiplication_absorbability.
Qed.

Proposition Matrix_scalar_multiplication_Field_opposite_one {K : Set} {FK : Field K} {m n : nat} (A : Matrix K m n) :
  (-1%field)%field * A = - A.
Proof.
  rewrite /Matrix_scalar_multiplication.
  extensionality i.
  extensionality j.
  rewrite multiplication_commutativity.
  by rewrite Field_multiplication_opposite_one.
Qed.

Proposition Matrix_scalar_multiplication_Matrix_addition {K : Set} {FK : Field K} {m n : nat} (k : K) (A B : Matrix K m n) :
  k * (A + B) = k * A + k * B.
Proof.
  rewrite /Matrix_scalar_multiplication.
  rewrite /Matrix_addition.
  extensionality i.
  extensionality j.
  by rewrite multiplication_distributivity_over_addition.
Qed.

Lemma Matrix_multiplication_function_sproof_l {p : nat} {sval_k sval_l : nat} (proof : sval_k <= p) (equality : sval_k = sval_l.+1) :
  sval_l < p.
Proof.
  move: proof.
  rewrite equality.
  by auto.
Qed.

Lemma Matrix_multiplication_function_next_proof {p : nat} {sval_k sval_l : nat} (proof : sval_k <= p) (equality : sval_k = sval_l.+1) :
  sval_l <= p.
Proof.
  move: proof.
  rewrite equality.
  by auto.
Qed.

Fixpoint Matrix_multiplication_function {K : Set} {FK : Field K} {m p n : nat} (A : Matrix K m p) (B : Matrix K p n) (i : {sval_i : nat | sval_i < m}) (j : {sval_j : nat | sval_j < n}) (sval_k : nat) (proof : sval_k <= p) : K :=
  match sval_k as sval_k_alias return sval_k = sval_k_alias -> K with
  | 0 => fun (equality : sval_k = 0%nat) => 0
  | sval_l.+1 => fun (equality : sval_k = sval_l.+1) => (A i (exist _ sval_l (Matrix_multiplication_function_sproof_l proof equality)) * B (exist _ sval_l (Matrix_multiplication_function_sproof_l proof equality)) j + Matrix_multiplication_function A B i j sval_l (Matrix_multiplication_function_next_proof proof equality))%field
  end (eq_refl sval_k).

Lemma Matrix_multiplication_function_initial_proof (p : nat) :
  p <= p.
Proof.
  by auto.
Qed.

Definition Matrix_multiplication {K : Set} {FK : Field K} {m p n : nat} (A : Matrix K m p) (B : Matrix K p n) : Matrix K m n :=
  fun i j => Matrix_multiplication_function A B i j p (Matrix_multiplication_function_initial_proof p).

Notation "A ** B" := (Matrix_multiplication A B) (at level 2) : matrix_scope.

Lemma Matrix_multiplication_extension_A_condition {m : nat} (sval_i : nat) :
  {sval_i < m} + {sval_i >= m}.
Proof.
  case: (leqP m sval_i).
  - by auto.
  - by auto.
Qed.

Definition Matrix_multiplication_extension_A {K : Set} {FK : Field K} {m p : nat} (A : Matrix K m p) (sval_i : nat) : {sval_k : nat | sval_k < p} -> K :=
  match Matrix_multiplication_extension_A_condition sval_i with
  | left lcondition => fun k => A (exist _ sval_i lcondition) k
  | right rcondition => fun _ => 0
  end.

Lemma Matrix_multiplication_extension_B_condition {n : nat} (sval_j : nat) :
  {sval_j < n} + {sval_j >= n}.
Proof.
  case: (leqP n sval_j).
  - by auto.
  - by auto.
Qed.

Definition Matrix_multiplication_extension_B {K : Set} {FK : Field K} {p n : nat} (B : Matrix K p n) (sval_j : nat) : {sval_k : nat | sval_k < p} -> K :=
  match Matrix_multiplication_extension_B_condition sval_j with
  | left lcondition => fun k => B k (exist _ sval_j lcondition)
  | right rcondition => fun _ => 0
  end.

Fixpoint Matrix_multiplication_extension {K : Set} {FK : Field K} {m p n : nat} (A : Matrix K m p) (B : Matrix K p n) (sval_i : nat) (sval_j : nat) (sval_k : nat) {proof : sval_k <= p} : K :=
  match sval_k as sval_k_alias return sval_k = sval_k_alias -> K with
  | 0 => fun (equality : sval_k = 0%nat) => 0
  | sval_l.+1 => fun (equality : sval_k = sval_l.+1) => (Matrix_multiplication_extension_A A sval_i (Matrix_multiplication_function_sproof_l proof equality)) (exist _ sval_l (Matrix_multiplication_function_sproof_l proof equality)) * B (exist _ sval_l (Matrix_multiplication_function_sproof_l proof equality)) (exist _ sval_j (Matrix_multiplication_function_sproof_l proof equality)) + Matrix_multiplication_extension_function A B sval_i sval_j sval_l (Matrix_multiplication_function_next_proof proof equality))%field
  end (eq_refl sval_k).
