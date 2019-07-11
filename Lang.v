Parameter atom : Set.

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

Axiom atomeq_dec : forall a b : atom, {a = b} + {a <> b}.

Theorem propeq_dec : forall p q : prop, {p = q} + {p <> q}.
Proof.
  induction p; induction q;
      try (left; reflexivity);
      try (right; intros H; inversion H; contradiction H);
      try (destruct (IHp1 q1); destruct (IHp2 q2); subst;
        try (right; intros H; inversion H; contradiction n);
        left; reflexivity).
    destruct (atomeq_dec a a0).
      - left. subst. reflexivity.
      - right. intros H. inversion H. contradiction n.
Qed.