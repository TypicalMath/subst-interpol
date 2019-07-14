Require Import Lang.
Require Import Multiset.
Require Import Maybe.
Require Import AtomSet.
Require Import Formula.

Reserved Notation "G ⇒ p" (no associativity, at level 61). (* 21d2 *)
Inductive FLe : multiset prop -> maybe_prop -> Prop :=
| A1:     forall p, [p] ⇒ p
| A2:     forall G, G ⇒ ⊤
| A3:     forall G p, G;⊥ ⇒ p
| A4:     ∅ ⇒ 1
| A5:     0 ⇒ []
| OneW:   forall G p, G ⇒ p -> G;1 ⇒ p
| ZeroW:  forall G, G ⇒ [] -> G ⇒ 0
| ConjL1: forall G (a b p : prop), G;a ⇒ p -> G;(a ∧ b) ⇒ p
| ConjL2: forall G (a b p : prop), G;b ⇒ p -> G;(a ∧ b) ⇒ p
| ConjR:  forall G (a b : prop), G ⇒ a -> G ⇒ b -> G ⇒ (a ∧ b)
| DisjL:  forall G (a b p : prop), G;a ⇒ p -> G;b ⇒ p ->
            G;(a ∨ b) ⇒ p
| DisjR1: forall G (a b : prop), G ⇒ a -> G ⇒ (a ∨ b)
| DisjR2: forall G (a b : prop), G ⇒ b -> G ⇒ (a ∨ b)
| MConL:  forall G (a b p : prop), G;a;b ⇒ p -> G;(a ⊗ b) ⇒ p
| MConR:  forall G D (a b : prop), G ⇒ a -> D ⇒ b -> G;D ⇒ (a ⊗ b)
| ImplL:  forall G D (a b p : prop), G ⇒ a -> D;b ⇒ p ->
            G;D;(a ⊃ b) ⇒ p
| ImplR:  forall G (a b : prop), G;a ⇒ b -> G ⇒ (a ⊃ b)
where "G ⇒ p" := (FLe G p).

Notation "⇒ p" := (∅ ⇒ p) (no associativity, at level 62).

Definition post_interpolant_ex (p : prop) (v : atom_set) :=
  exists a,
    (atoms a) ⊆ v /\
    ⇒ (p ⊃ a) /\
    forall b, (atoms p) ∩ (atoms b) ⊆ v -> ⇒ (p ⊃ b) ->
      ⇒ (a ⊃ b).

Definition post_interpolant_prop (p : prop) := forall (v : atom_set),
  v ⊆ (atoms p) -> post_interpolant_ex p v.

Definition pre_interpolant_ex (p : prop) (v : atom_set) :=
  exists a,
    (atoms a) ⊆ v /\
    ⇒ (a ⊃ p) /\
    forall b, (atoms p) ∩ (atoms b) ⊆ v -> ⇒ (b ⊃ p) ->
      ⇒ (b ⊃ a).

Definition pre_interpolant_prop (p : prop) := forall (v : atom_set),
  v ⊆ (atoms p) -> pre_interpolant_ex p v.


Lemma l34A : forall (p : prop) (a : atom),
  a ∈ (atoms p) -> post_interpolant_ex p ((atoms p) \ {{a}}) ->
    forall q, post_interpolant_prop q.
Proof.
  unfold post_interpolant_prop. unfold post_interpolant_ex.
  intros p a aInp loc q v.
  remember (#((atoms q) \ v)) as n.
  generalize dependent q. generalize dependent v.
  induction n as [| n' IHn']; intros v q card vSub.
    - symmetry in card. apply List.length_zero_iff_nil in card.
      apply subset_diff_iff in card.
      destruct (set_eq (atoms q) v card vSub).
      exists q. split; try split.
        + apply card.
        + apply ImplR. apply A1.
        + intros b Meet me. apply me.
    - 
