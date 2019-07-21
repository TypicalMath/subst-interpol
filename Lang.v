Require Import Coq.Arith.Arith.

Inductive prop : Type :=
| Var : nat  -> prop
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

Notation "⊥" := Bot. (* 22a5 *)
Notation "⊤" := Top. (* 22a4 *)
Notation "0" := Zero.
Notation "1" := One.
Notation "¬ P" := (Neg P) (at level 51). (* 00ac *)
Infix "∧" := Conj (left associativity, at level 52). (* 2227 *)
Infix "∨" := Disj (left associativity, at level 53). (* 2228 *)
Infix "⊃" := LDiv (right associativity, at level 54). (* 2283 *)
Infix "⊂" := RDiv (right associativity, at level 55). (* 2282 *)
Infix "⊗" := MCon (right associativity, at level 56). (* 2297 *)

Theorem propeq_dec : forall p q : prop, {p = q} + {p <> q}.
Proof.
	decide equality.
	apply eq_nat_dec.
Qed.