Require Export Coq.Sets.Multiset.
Require Import Lang.

Notation "∅" := (EmptyBag prop). (* 2205 *)
Notation "[ P ]" := (SingletonBag eq propeq_dec P).
Infix ";" := munion (left associativity, at level 61).
Coercion prop_to_singleton (P : prop) : (multiset prop) := 
  SingletonBag eq propeq_dec P.
