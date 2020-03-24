Definition atom := nat.

Inductive prop : Type :=
| Var : atom  -> prop
| Bot : prop
| Top : prop
| Zero : prop
| One : prop
| Disj : prop -> prop -> prop
| Conj : prop -> prop -> prop
| LDiv : prop -> prop -> prop
| RDiv : prop -> prop -> prop
| MCon : prop -> prop -> prop.

Definition Neg (p : prop) : prop := LDiv p Bot.

Notation "^x_ x" := (Var x) (at level 30).
Coercion atom_as_prop (a : atom) : prop := Var a.


Notation "⊥" := Bot. (* 22a5 *)
Notation "⊤" := Top. (* 22a4 *)
Notation "0" := Zero.
Notation "1" := One.
Notation "¬ P" := (Neg P) (at level 31). (* 00ac *)
Infix "∧" := Conj (left associativity, at level 32). (* 2227 *)
Infix "∨" := Disj (left associativity, at level 33). (* 2228 *)
Infix "⊃" := LDiv (right associativity, at level 34). (* 2283 *)
Infix "⊂" := RDiv (right associativity, at level 35). (* 2282 *)
Infix "⊗" := MCon (right associativity, at level 36). (* 2297 *)
Require Import PeanoNat.
Theorem propeq_dec : forall p q : prop, {p = q} + {p <> q}.
Proof.
  induction p; induction q;
      try (left; reflexivity);
      try (right; intros H; inversion H; contradiction H);
      try (destruct (IHp1 q1); destruct (IHp2 q2); subst;
        try (right; intros H; inversion H; contradiction n);
        left; reflexivity).
    destruct (PeanoNat.Nat.eq_dec a a0).
      - left. subst. reflexivity.
      - right. intros H. inversion H. contradiction n.
Qed.

Fixpoint propeq (p q : prop) : bool :=
  match (p, q) with
  | (^x_n, ^x_m) => PeanoNat.Nat.eqb n m
  | (⊥, ⊥) => true
  | (⊤, ⊤) => true
  | (0, 0) => true
  | (1, 1) => true
  | (p1 ∧ p2, q1 ∧ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ∨ p2, q1 ∨ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ⊃ p2, q1 ⊃ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ⊂ p2, q1 ⊂ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ⊗ p2, q1 ⊗ q2) => (propeq p1 q1) && (propeq p2 q2)
  | _ => false
  end.