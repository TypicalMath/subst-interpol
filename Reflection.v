Require Import Setoid.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split; inversion H.
    - intros _. reflexivity.
    - intros pP. apply H0 in pP. inversion pP.
    - intros _. apply H0.
    - intros con. inversion con.
Qed.
