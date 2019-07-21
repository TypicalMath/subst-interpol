Require Import ListSet.
Require Import Lang.
Require Import Reflection.

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
Infix "∈" := List.In (at level 61). (*2208*)

Theorem set_memP : forall a s, reflect (a ∈ s) (set_mem atomeq_dec a s).
Proof.
  intros a s. apply iff_reflect. split.
    - apply set_mem_correct2.
    - apply set_mem_correct1.
Qed.

Infix "⊆" := List.incl (at level 62). (* 2286 *)

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
  unfold List.incl.
  intros s1 s2. split.
    - generalize dependent s2.
      induction s1 as [| h t IHt]; intros s2 H a aIs1.
        + inversion aIs1.
        + simpl in H. simpl in aIs1. destruct aIs1 as [aEh | aIt].
          * rewrite aEh in H. destruct (set_memP a s2) as [aIs2 | _].
            { apply aIs2. }
            { destruct (add_not_empty (t \ s2) a) as [s' [a' H0]].
              rewrite H in H0. inversion H0.
            }
          * apply IHt. {
            destruct (set_memP h s2) as [hIs2 | _].
              - apply H.
              - destruct (add_not_empty (t \ s2) h) as [s' [a' H0]].
                rewrite H in H0. inversion H0.
            } {
            apply aIt.
            }
    - generalize dependent s2.
      induction s1 as [| h t IHt]; intros s2 H.
        + reflexivity.
        + simpl. destruct (set_memP h s2) as [_ | hNIs2].
            * apply IHt. intros a H'. apply H. simpl. right. apply H'.
            * contradiction hNIs2. specialize (H h).
              apply H. left. reflexivity.
Qed.

Lemma con_subset : forall h (t s : atom_set), (cons h t) ⊆ s -> t ⊆ s.
Proof.
  unfold List.incl. intros h t s htSs a aIt. simpl in htSs.
  apply htSs. right. apply aIt. Qed.

Theorem set_inter_comm : forall s1 s2, s1 ∩ s2 = s1 ∩ s2.
Proof.
  induction s1 as [| h1 t1 IHt1];
    destruct s2 as [| h2 t2]; reflexivity.
Qed.

Lemma nil_diff : forall s, EMP \ s = EMP.
Proof. destruct s; reflexivity. Qed.


Lemma destruct_eq : forall h t s, h ∈ (s ∩ (cons h t)) <-> h ∈ s.
Proof.
  split.
    - apply set_inter_elim1.
    - intros hIb. apply set_inter_intro.
      + apply hIb.
      + left. reflexivity.
Qed.

Lemma destruct_mem : forall h t s,
  set_mem atomeq_dec h (s ∩ (cons h t)) = set_mem atomeq_dec h s.
Proof.
  intros h t s. destruct (destruct_eq h t s) as [H1 H2].
  destruct (set_memP h s) as [H | H].
    - apply H2 in H. apply set_mem_correct2. apply H.
    - apply set_mem_complete2. intros con.
      apply H1 in con. apply H in con. inversion con.
Qed.

Lemma add_preserve : forall a s, a ∈ s -> s << a = s.
Proof.
  intros a s aIs. apply set_eq; unfold List.incl; intros a0 H.
    - apply set_add_elim in H.
      destruct H as [a0Ea | a0Is].
        + rewrite a0Ea. apply aIs.
        + apply a0Is.
    - apply set_add_intro. right. apply H.
Qed.

Lemma add_length1 : forall a s, a ∈ s -> #(s << a) = # s.
Proof. intros a s aIs. apply f_equal. apply add_preserve. apply aIs. Qed.

Lemma add_length2 : forall a s, ~ a ∈ s -> #(s << a) = S(# s).
Proof.
  intros a s aIs. assert (add_adds: s << a = cons a s). { (* Totally BS *)
    apply set_eq; unfold List.incl; intros a0 H;
      try apply set_add_elim in H;
      try apply set_add_intro;
        destruct H as [H | H];
          try (left; symmetry; apply H);
          try (right; apply H).
  }
  rewrite add_adds. reflexivity.
Qed.

Theorem diff_length : forall a b, #(a \ b) <= # a.
Proof.
  intros a b. induction a as [| h t IHt]; simpl.
    - apply le_n.
    - destruct (set_memP h b) as [hIb | hNb].
      + apply le_S. apply IHt.
      + destruct (set_memP h t).
        * rewrite (add_length1 h (t \ b) (set_diff_intro _ h t b H hNb)).
          apply le_S. apply IHt.
        * rewrite (add_length2 h (t \ b)).
          { apply le_n_S. apply IHt. }
          { intros con. contradiction H. apply set_diff_elim1 in con. apply con. }
Qed.

Theorem diff_inter_elim : forall a b : atom_set, a \ (b ∩ a) = a \ b.
Proof.
  intros a b. apply set_eq.
    - induction a as [| h t IHt].
      + repeat rewrite nil_diff. apply List.incl_refl.
      + unfold List.incl. simpl. rewrite destruct_mem.
        destruct (set_memP h b) as [hIb | hNb].
          * intros a H. apply IHt.
            apply set_diff_intro.
              { apply set_diff_elim1 in H. apply H. }
              { apply set_diff_elim2 in H.
                intros con. contradiction H. apply set_inter_intro.
                  - apply set_inter_elim1 in con. apply con.
                  - right.  apply set_inter_elim2 in con. apply con.
              }
          * intros a H. unfold List.incl in IHt.
            apply set_add_elim in H as [H | H];
              apply set_add_intro.
              { left. apply H. }
              { right. apply IHt. apply set_diff_intro.
                  - apply set_diff_elim1 in H. apply H.
                  - apply set_diff_elim2 in H. intros con.
                    contradiction H. apply set_inter_intro.
                      + apply set_inter_elim1 in con. apply con.
                      + apply set_inter_elim2 in con. right. apply con.
              }
    - induction a as [| h t IHt].
      + repeat rewrite nil_diff. apply List.incl_refl.
      + unfold List.incl. simpl. rewrite destruct_mem.
        destruct (set_memP h b) as [hIb | hNb].
          * intros a H. apply set_diff_intro.
              { apply set_diff_elim1 in H. apply H. }
              { apply set_diff_elim2 in H.
                intros con. apply set_inter_elim in con.
                destruct con as [con _]. apply H in con.
                apply con.
              }
          * intros a H. apply set_add_elim in H as [H | H];
              apply set_add_intro.
            { left. apply H. }
            { right. apply IHt in H.
              apply set_diff_intro.
                - apply set_diff_elim1 in H. apply H.
                - intros con. apply set_inter_elim in con.
                  destruct con as [aIb aIht].
                  destruct aIht as [aEh | aIt].
                    + rewrite aEh in hNb. apply hNb in aIb. apply aIb.
                    + apply set_diff_elim2 in H. contradiction H.
                      apply set_inter_intro.
                        * apply aIb.
                        * apply aIt.
            }
Qed.