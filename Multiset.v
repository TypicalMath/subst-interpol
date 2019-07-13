Require Export Coq.Sets.Multiset.
Require Import Lang.

Notation "∅" := (EmptyBag prop). (* 2205 *)
Notation "[ P ]" := (SingletonBag eq propeq_dec P).
Infix ";" := munion (left associativity, at level 61).
Coercion prop_to_singleton (P : prop) : (multiset prop) := 
  SingletonBag eq propeq_dec P.

Definition MIn {A : Type} (a : A) (M : multiset A) : Prop :=
  O < multiplicity M a.
Definition MSubset {A : Type} (M1 M2 : multiset A) : Prop :=
  forall a, MIn a M1 -> MIn a M2.