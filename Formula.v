Require Import Lang.
Require Import Nat.
Require Import Multiset.

Fixpoint weight (p : prop) : nat :=
match p with
  | p1 ∧ p2 => S ((weight p1) + (weight p2))
  | p1 ∨ p2 => S ((weight p1) + (weight p2))
  | p1 ⊃ p2 => S ((weight p1) + (weight p2))
  | p1 ⊂ p2 => S ((weight p1) + (weight p2))
  | p1 ⊗ p2 => S ((weight p1) + (weight p2))
  | _ => S O
  end.

Fixpoint atoms (p : prop) : (set atom) :=
match p with
  | Var a => {{a}}
  | p1 ∧ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ∨ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊃ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊂ p2 => (atoms p1) ∪ (atoms p2)
  | p1 ⊗ p2 => (atoms p1) ∪ (atoms p2)
  | _ => EMP
  end.

(* XXX -- THIS SHIT IS TOTALLY WRONG -- XXX *)
(* Reserved Notation "p ⊰ q" (no associativity, at level 61). (* 22b0 *)
Inductive sub_atom : prop -> prop -> Prop :=
| SA_refl : forall p, p ⊰ p
| SA_bot : forall p, ⊥ ⊰ p
| SA_top : forall p, ⊤ ⊰ p
| SA_zero : forall p, 0 ⊰ p
| SA_one : forall p, 1 ⊰ p
| SA_and1 : forall p q, p ⊰ p ∧ q
| SA_and2 : forall p q, q ⊰ p ∧ q
| SA_or1 : forall p q, p ⊰ p ∨ q
| SA_or2 : forall p q, q ⊰ p ∨ q
| SA_if1 : forall p q, p ⊰ p ⊃ q
| SA_if2 : forall p q, q ⊰ p ⊃ q
| SA_fi1 : forall p q, p ⊰ p ⊂ q
| SA_fi2 : forall p q, q ⊰ p ⊂ q
| SA_mul1 : forall p q, p ⊰ p ⊗ q
| SA_mul2 : forall p q, q ⊰ p ⊗ q
where "p ⊰ q" := (sub_atom p q).

Theorem atoms_complete : forall p q : prop,
  (p ⊰ q) <-> (forall a : atom, a ∈ (atoms p) -> a ∈ (atoms q)).
Proof.
  intros p q. split; intros H.
  - inversion H;
        intros a H'; unfold In in H'; unfold In; simpl;
        unfold lt; unfold lt in H';
        try apply (Plus.le_plus_trans _ _ _ H');
        try rewrite PeanoNat.Nat.add_comm;
        try apply (Plus.le_plus_trans _ _ _ H').
      apply H'.
  - destruct q.
    + unfold In in H. simpl in H.
    Abort. *)
(* XXX -- END OF THIS SHIT IS TOTALLY WRONG -- XXX *)