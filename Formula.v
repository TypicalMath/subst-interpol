Require Import Lang.
Require Import Nat.
Require Import AtomSet.

Fixpoint weight (p : prop) : nat :=
match p with
  | p1 ∧ p2 => S ((weight p1) + (weight p2))
  | p1 ∨ p2 => S ((weight p1) + (weight p2))
  | p1 ⊃ p2 => S ((weight p1) + (weight p2))
  | p1 ⊂ p2 => S ((weight p1) + (weight p2))
  | p1 ⊗ p2 => S ((weight p1) + (weight p2))
  | _ => S O
  end.

Fixpoint atoms (p : prop) : atom_set :=
match p with
  | Var a => {{a}}
  | p1 ∧ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ∨ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊃ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊂ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊗ p2 => (atoms p1) ∪ (atoms p2)
  | _ => EMP
  end.