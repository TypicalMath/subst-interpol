Require Import ListSet.
Require Import Lang.

Definition A := atom.
Definition Aeq_dec := atomeq_dec.

Definition atom_set := set atom.

Definition EMP := (empty_set atom).
Notation "{{ P }}" := (set_add atomeq_dec P EMP).
Notation "# A " := (length A) (at level 60).
Infix "∪" := (set_union atomeq_dec) (left associativity, at level 61). (* 222a *)
Infix "∩" := (set_inter atomeq_dec) (left associativity, at level 61). (* 2229 *)
Notation "A -- x" := (set_remove atomeq_dec x A) (at level 60).
Infix "\" := (set_diff atomeq_dec) (at level 60).
Infix "∈" := set_In (at level 61). (*2208*)

Definition set_sub (M1 M2 : atom_set) : Prop :=
  forall a, a ∈ M1 -> a ∈ M2.
Infix "⊆" := set_sub (at level 62). (* 2286 *)