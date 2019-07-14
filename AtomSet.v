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
Notation "A << x" := (set_add atomeq_dec x A) (at level 60).
Notation "A -- x" := (set_remove atomeq_dec x A) (at level 60).
Infix "\" := (set_diff atomeq_dec) (at level 60).
Infix "∈" := set_In (at level 61). (*2208*)

Definition set_sub (M1 M2 : atom_set) : Prop :=
  forall a, a ∈ M1 -> a ∈ M2.
Infix "⊆" := set_sub (at level 62). (* 2286 *)

Axiom set_eq : forall a b : atom_set,
  a ⊆ b -> b ⊆ a -> a = b.

Theorem add_not_empty : forall (s : atom_set) (a : atom),
  exists (s' : atom_set) (a' : atom), s << a = cons a' s'.
Proof.
  destruct s as [| h t]; simpl; intros a.
    - exists nil, a. reflexivity.
    - destruct (atomeq_dec a h).
      + exists t, h. reflexivity.
      + exists (t << a), h. reflexivity.
Qed.


Theorem subset_diff_iff : forall s1 s2 : atom_set,
  s1 \ s2 = EMP <-> s1 ⊆ s2.
Proof.
  unfold set_sub.
  intros s1 s2. split.
    - generalize dependent s2.
      induction s1 as [| h t IHt]; intros s2 H a aIs1.
        + inversion aIs1.
        + simpl in H. simpl in aIs1. destruct aIs1 as [aEh | aIt].
          * rewrite aEh in H. remember (set_mem atomeq_dec a s2) as aIs2.
            destruct aIs2 as [aIs2 | _].
              { symmetry in HeqaIs2. apply set_mem_correct1 in HeqaIs2. apply HeqaIs2. }
              { destruct (add_not_empty (t \ s2) a) as [s' [a' H0]].
                rewrite H in H0. inversion H0.
              }
          * apply IHt. {
            remember (set_mem atomeq_dec h s2) as hIs2.
            destruct hIs2.
              - apply H.
              - destruct (add_not_empty (t \ s2) h) as [s' [a' H0]].
                rewrite H in H0. inversion H0.
            } {
            apply aIt.
            }
    - generalize dependent s2.
      induction s1 as [| h t IHt]; intros s2 H.
        + reflexivity.
        + simpl. remember (set_mem atomeq_dec h s2) as hIs2.
          destruct hIs2 as [_ | hNIs2].
            * apply IHt. intros a H'. apply H. simpl. right. apply H'.
            * symmetry in HeqhIs2. apply set_mem_complete1 in HeqhIs2.
              specialize (H h). simpl in H. apply HeqhIs2 in H.
                { inversion H. }
                { left. reflexivity. }
Qed.