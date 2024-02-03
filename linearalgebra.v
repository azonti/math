From mathcomp Require Import ssreflect.

Class Field (K : Prop) := {
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
  zero_not_one : zero <> one;
}.

Declare Scope field_scope.
Delimit Scope field_scope with field.
Local Open Scope field_scope.

Notation "k + l" := (addition k l) : field_scope.
Notation "- k" := (opposite k) : field_scope.
Notation "k * l" := (multiplication k l) : field_scope.
Notation "k ^ (- 1)" := (reciprocal k) (at level 30, right associativity) : field_scope.
