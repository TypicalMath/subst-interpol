Require Export Coq.Sets.Multiset.
Require Import Lang.

Notation "∅" := (EmptyBag prop). (* 2205 *)
Notation "[ P ]" := (SingletonBag eq propeq_dec P).
Infix ";" := munion (left associativity, at level 61).
Coercion prop_to_singleton (P : prop) : (multiset prop) := 
  SingletonBag eq propeq_dec P.

Definition In {A : Type} (a : A) (M : multiset A) : Prop :=
  O < multiplicity M a.
Infix "∈" := In (at level 60). (*2208*)
Definition Subset {A : Type} (M1 M2 : multiset A) : Prop :=
  forall a, a ∈ M1 -> a ∈ M2.
Infix "⊆" := Subset (at level 61). (* 2286 *)