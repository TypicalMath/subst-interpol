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

Definition set := multiset.

Definition EMP := (EmptyBag atom). (* 0398 *)
Notation "{{ P }}" := (SingletonBag eq atomeq_dec P).

Definition union {A : Type} (s1 s2 : set A) : set A :=
  Bag (fun x => 
        match (multiplicity s1 x, multiplicity s2 x) with
          | (O, O) => O
          | _ => S O
          end
  ).
Infix "∪" := union (left associativity, at level 61). (* 222a *)

Definition intersection {A : Type} (s1 s2 : set A) : set A :=
  Bag (fun x => 
        match (multiplicity s1 x, multiplicity s2 x) with
          | (S n, S m) => S O
          | _ => O
          end
  ).
Infix "∩" := intersection (left associativity, at level 61). (* 2229 *)

Definition compl {A : Type} (s : set A) : set A :=
  Bag (fun x =>
        match (multiplicity s x) with
        | O => S O
        | S n => O
        end
  ).


Definition diff {A : Type} (s1 s2 : set A) : set A :=
  s1 ∩ (compl s2).
Infix "\" := diff (at level 60).

Definition In {A : Type} (a : A) (M : set A) : Prop :=
  O < multiplicity M a.
Infix "∈" := In (at level 61). (*2208*)

Definition Subset {A : Type} (M1 M2 : set A) : Prop :=
  forall a, a ∈ M1 -> a ∈ M2.
Infix "⊆" := Subset (at level 62). (* 2286 *)