Require Import List.
Require Import Formula.
Require Import Lang.
Require Import Finset.
Import List.ListNotations.
Coercion prop_to_some (P : prop) : (option prop) := Some P.
Coercion list_to_prop (P : prop) : (list prop) := [P].
Reserved Notation "G ⇒ p" (no associativity, at level 61). (* 21d2 *)

Inductive FLe : list prop -> option prop -> Prop :=
  | A1:     forall p : prop, p ⇒ p (* Fle [p] p *)
  | A2:     forall G, G ⇒ ⊤
  | A3:     forall G p, ⊥::G ⇒ p
  | A4:     [] ⇒ 1
  | A5:     0 ⇒ None
  | OneW:   forall G p, G ⇒ p -> 1::G ⇒ p
  | ZeroW:  forall G, G ⇒ None -> G ⇒ 0
  | ConjL1: forall G (a b p : prop), a::G ⇒ p -> (a ∧ b)::G ⇒ p
  | ConjL2: forall G (a b p : prop), b::G ⇒ p -> (a ∧ b)::G ⇒ p
  | ConjR:  forall G (a b : prop), G ⇒ a -> G ⇒ b -> G ⇒ (a ∧ b)
  | DisjL:  forall G (a b p : prop), a::G ⇒ p -> b::G ⇒ p ->
              (a ∨ b)::G ⇒ p
  | DisjR1: forall G (a b : prop), G ⇒ a -> G ⇒ (a ∨ b)
  | DisjR2: forall G (a b : prop), G ⇒ b -> G ⇒ (a ∨ b)
  | MConL:  forall G (a b p : prop), a::b::G ⇒ p -> (a ⊗ b)::G ⇒ p
  | MConR:  forall G D (a b : prop), G ⇒ a -> D ⇒ b -> G++D ⇒ (a ⊗ b)
  | ImplL:  forall G D (a b p : prop), G ⇒ a -> b::D ⇒ p ->
              (a ⊃ b)::G++D ⇒ p
  | ImplR:  forall G (a b : prop), a::G ⇒ b -> G ⇒ (a ⊃ b)
  | Exc:    forall G D a b p, G++a::b::D ⇒ p -> G++b::a::D ⇒ p
where "G ⇒ p" := (FLe G p).

Notation "⇒ p" := ([] ⇒ p) (no associativity, at level 62).

Lemma implR_transitive : forall p q r, ⇒ (p ⊃ q) -> ⇒ (q ⊃ r) -> ⇒ (p ⊃ r).
Proof. Admitted.

Definition post_interpolant_ex (p : prop) (v : finset) :=
  exists a : prop,
    (^V a) ⊆ v /\
    ⇒ (p ⊃ a) /\
    forall b : prop, (^V p) ∩ (^V b) ⊆ v -> ⇒ (p ⊃ b) ->
      ⇒ (a ⊃ b).

Definition post_interpolant_prop (p : prop) := forall (v : finset),
  v ⊆ (^V p) -> post_interpolant_ex p v.

Definition pre_interpolant_ex (p : prop) (v : finset) :=
  exists a : prop,
    (^V a) ⊆ v /\
    ⇒ (a ⊃ p) /\
    forall b : prop, (^V p) ∩ (^V b) ⊆ v -> ⇒ (b ⊃ p) ->
      ⇒ (b ⊃ a).

Definition pre_interpolant_prop (p : prop) := forall (v : finset),
  v ⊆ (^V p) -> pre_interpolant_ex p v.

Theorem strong_induction : forall P : nat -> Prop,
  (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
  forall n : nat, P n.
Proof. Admitted.



Lemma l34A :
  (forall (p : prop) (a : atom), a ∈ (^V p) -> post_interpolant_ex p ((^V p) \ {{a}})) ->
    forall p, post_interpolant_prop p.
Proof.
  unfold post_interpolant_prop. unfold post_interpolant_ex.
  intros loc p v.
  remember (#((^V p) \ v)) as n.
  generalize dependent p. generalize dependent v.
  induction n using strong_induction; intros v p card vSub.
  destruct n.
    - symmetry in card. apply card_empty in card.
        apply diff_emp_incl in card.
        destruct (extensionality (^V p) v card vSub).
        exists p. split; try split.
          + apply card.
          + apply ImplR. apply A1.
          + intros b Meet me. apply me.
    - assert (card' : Nat.leb 1 (S n)). { reflexivity. }
      rewrite card in card'.
      apply choice in card'.
      destruct card' as [a aI].
      pose proof (loc p a) as loc'.
      pose proof (diff_le (^V p) v) as V.
      pose proof (proj1 (mem_incl (^V p \ v) (^V p)) V a aI) as exI.
      apply loc' in exI. destruct exI as [d [vd [pAd dInt]]].
      remember (v ∩ ^V d) as v'.
      pose proof (H (#(^V d \ v'))) as H.
      assert (subst: ^V d \ v' ⊆ (^V p \ {{a}}) \ v). {
        rewrite Heqv'. rewrite intersection_comm. rewrite <- diff_intersection.
        apply incl_diff_inv1. apply vd.
      }
      assert (card1: # (^V p \ v) = S (# ((^V p \ {{a}}) \ v))). {
        rewrite diff_semi_comm. apply card_single_diff. apply aI.
      }
      rewrite card1 in card. apply eq_add_S in card.
      pose proof (card_incl _ _ subst) as card_less.
      rewrite <- card in card_less.
      apply PeanoNat.Nat.leb_le in card_less.
      apply Lt.le_lt_n_Sm in card_less.
      pose proof (H card_less v' d (eq_refl _)) as H.
      rewrite Heqv' in H at 1.
      pose proof (H (intersection_glb1 _ _)) as H.
      destruct H as [ds [vds [dAds dsInt]]].
      exists ds. split; try split.
        + rewrite Heqv' in vds. rewrite intersection_comm in vds.
          apply (incl_transitive _ _ _ vds (intersection_glb1 _ _)).
        + apply (implR_transitive _ _ _ pAd dAds).
        + intros b meet You.
          apply mem_diff in aI as [aIp aNIv].
          assert (incl_but: v ⊆ ^V p \ {{a}}). {
            apply (incl_transitive _ (v \ {{a}}) _).
              - apply mem_incl. intros m mIv.
                apply mem_diff. split.
                  + apply mIv.
                  + apply Bool.not_true_is_false. intros con.
                    apply mem_singleton2 in con.
                    rewrite <- con in mIv.
                    rewrite mIv in aNIv. inversion aNIv.
              - apply incl_diff_inv1. apply vSub.
          }
          pose proof (dInt b (incl_transitive _ _ _ meet incl_but) You) as dAb.
          pose proof (incl_transitive _ _ _ vd (diff_incl _ _)) as dIp.
          pose proof (incl_intersection_inv _ _ (^V b) dIp) as bdIbp.
          rewrite intersection_comm in meet.
          pose proof (incl_transitive _ _ _ bdIbp meet) as bdIv.
          pose proof (intersection_glb2 _ _ _ bdIv (intersection_glb1 _ _)) as bdIvd.
          rewrite <- Heqv' in bdIvd.
          rewrite intersection_comm in bdIvd.
          apply (dsInt b bdIvd dAb).
Qed.