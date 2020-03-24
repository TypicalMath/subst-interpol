Require Import BinNat BinNatDef BinPos BinPosDef.
Include BinNatDef.N.

Local Open Scope positive_scope.

Coercion bool_to_Prop (b : bool) : Prop := b = true.

Coercion pos_to_N (p : positive) : N := pos p.

Definition finset := N.
Notation "∅" := N0.

Fixpoint pos_cardinality (p : positive) : nat :=
  match p with
  | 1 => 1
  | p~0 => pos_cardinality p
  | p~1 => S (pos_cardinality p)
  end.

Definition cardinality (s : finset) : nat :=
  match s with
  | ∅ => 0
  | pos p => pos_cardinality p
  end.
Notation "# s" := (cardinality s) (at level 50).

Definition union : finset -> finset -> finset := lor.
Infix "∪" := union (left associativity, at level 61).

Definition intersection : finset -> finset -> finset := land.
Infix "∩" := intersection (left associativity, at level 61).

Definition diff : finset -> finset -> finset := ldiff.
Infix "\" := diff (left associativity, at level 62).

Definition mem : nat -> finset -> bool := fun n s => testbit_nat s n.
Infix "∈" := mem (at level 60).

Fixpoint pos_incl (p1 p2 : positive) : bool :=
  match (p1, p2) with
  | (1, 1) => true
  | (_, 1) => false
  | (1, p~0) => false
  | (1, p~1) => true
  | (p1~0, p2~0) => pos_incl p1 p2
  | (p1~0, p2~1) => pos_incl p1 p2
  | (p1~1, p2~0) => false
  | (p1~1, p2~1) => pos_incl p1 p2
  end.

Fixpoint incl (s1 s2 : finset) : bool :=
  match (s1, s2) with
  | (∅, _) => true
  | (_, ∅) => false
  | (pos p1, pos p2) => pos_incl p1 p2
  end.
Infix "⊆" := incl (at level 70).

Fixpoint pos_singleton_of (n : nat) : positive :=
  match n with
  | O => 1
  | S n => (pos_singleton_of n)~0
  end.

Fixpoint singleton_of (n : nat) : finset := pos (pos_singleton_of n).
Notation "{{ n }}" := (singleton_of n).

Lemma emp_minimum : forall s, ∅ ⊆ s. Proof. reflexivity. Qed.

Lemma emp_min : forall s, s ⊆ ∅ -> ∅ = s.
Proof.
  destruct s; auto. destruct p; intros cont; inversion cont.
Qed.

Lemma zero_incl : forall p, 1 ⊆ p~1.
Proof. reflexivity. Qed.

Lemma zero_not_incl : forall p, 1 ⊆ p~0 = false.
Proof. reflexivity. Qed.

Lemma pos_incl_reflexive: forall p, pos_incl p p.
Proof. induction p; try (apply IHp). reflexivity. Qed.


Lemma incl_reflexive : forall s1, s1 ⊆ s1.
Proof.
  destruct s1; try reflexivity.
  induction p; try reflexivity; apply IHp.
Qed.

Lemma incl_transitive : forall s1 s2 s3, s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
Proof.
  destruct s1; destruct s2; destruct s3; try reflexivity;
    intros H1 H2; try (apply H1); try (apply H2).
    - apply emp_min in H1. rewrite <- H1. reflexivity.
    - generalize dependent p0. generalize dependent p1.
      induction p; destruct p0; destruct p1; intros H1 H2;
        inversion H1; inversion H2; try reflexivity; simpl in *;
        apply (IHp p1 p0); try (apply H1); try (apply H2).
Qed.


Lemma choice : forall s, (Nat.leb 1 (# s)) <-> exists n, n ∈ s.
Proof.
  destruct s.
    - split; simpl; intros H; inversion H; inversion H0.
    - induction p; split; intros H;
      try reflexivity;
      try (exists 0%nat; reflexivity).
      + apply IHp in H. destruct H as [n H].
        exists (S n). apply H.
      + apply IHp. destruct H as [n H].
        exists (Nat.pred n). destruct n.
        * inversion H.
        * apply H.
Qed.

Lemma pos_card_min : forall p, Nat.leb 1 (pos_cardinality p).
Proof. induction p; try reflexivity. apply IHp. Qed.

Definition pos_choice : forall p, exists n, n ∈ (pos p) :=
  fun p => proj1 (choice (pos p)) (pos_card_min p).


Lemma extensionality : forall s1 s2, s1 ⊆ s2 -> s2 ⊆ s1 -> s1 = s2.
Proof.
  destruct s1; destruct s2;
    try reflexivity.
    - intros T F. inversion F.
    - intros F T. inversion F.
    - generalize dependent p0.
      induction p; induction p0; simpl;
        intros sI Is; try (inversion Is);
        try (apply IHp in sI);
        try (inversion sI); try (reflexivity);
        apply Is.
Qed.

Lemma extensionality_iff : forall s1 s2, (s1 ⊆ s2 /\ s2 ⊆ s1) <-> s1 = s2.
Proof.
  split.
    - intros [sI Is]. apply extensionality. apply sI. apply Is.
    - intros E. rewrite E. split; apply incl_reflexive.
Qed.

Lemma mem_incl : forall s1 s2, s1 ⊆ s2 <-> forall n, n ∈ s1 -> n ∈ s2.
Proof.
  split.
    - intros H n Hn. destruct s1.
      + inversion Hn.
      + destruct s2.
        * inversion H.
        * generalize dependent p.
          generalize dependent n.
          induction p0; destruct n; destruct p;
            try reflexivity;
            intros H; intros Hn;
            inversion H;
            inversion Hn;
            try (apply (IHp0 n p H Hn)).
    - destruct s1; destruct s2; try reflexivity.
      + intros H.
        destruct (pos_choice p) as [n nIp].
        apply H in nIp. inversion nIp.
      + generalize dependent p0.
        induction p; destruct p0;
          try reflexivity;
          try (intros H; apply IHp; destruct n; try (apply (H 1%nat)); try (apply (H (S (S n)))));
          intros H;
          try (destruct (pos_choice p) as [n nIp]; apply (H (S n)) in nIp; inversion nIp).
        * assert (cont : 0%nat ∈ p~1). { reflexivity. }
          apply H in cont. inversion cont.
        * assert (cont : 0%nat ∈ 1). { reflexivity. }
          apply H in cont. inversion cont.
Qed.

Lemma mem_pos_singleton1 : forall n, n ∈ pos_singleton_of n.
Proof. induction n. reflexivity. simpl. apply IHn. Qed.

Lemma mem_singleton1 : forall n, n ∈ {{n}}.
Proof. destruct n. reflexivity. simpl. apply mem_pos_singleton1. Qed.

Lemma mem_pos_singleton2 : forall n m, m ∈ pos_singleton_of n -> n = m.
Proof. induction n; destruct m; auto; intros H; inversion H. Qed.

Lemma mem_singleton2 : forall n m, m ∈ {{n}} -> n = m.
Proof.
  destruct n; destruct m; intros H; inversion H; auto.
  simpl in H. apply eq_S. apply (mem_pos_singleton2 _ _ H).
Qed.

Lemma singleton_mem_incl : forall n s, n ∈ s -> {{n}} ⊆ s.
Proof. intros. apply mem_incl. intros. destruct (mem_singleton2 _ _ H0). apply H. Qed.

Lemma double_nonempty : forall p, double (pos p) <> ∅.
Proof. intros p cont. inversion cont. Qed.


Lemma double_empty : forall s, double s = ∅ -> s = ∅.
Proof.
  destruct s; auto.
    intros con; inversion con.
Qed.

Lemma empty_double : forall s, s = ∅ -> double s = ∅.
Proof. intros s H. rewrite H. reflexivity. Qed.

Lemma succ_double_nonempty : forall s, BinPos.Pos.Nsucc_double s <> ∅.
Proof. destruct s; intros cont; inversion cont. Qed.

Lemma double_incl : forall s1 s2, s1 ⊆ s2 -> double s1 ⊆ double s2.
Proof. destruct s1; destruct s2; auto. Qed.

Lemma succ_double_incl : forall s1 s2, s1 ⊆ s2 ->
  BinPos.Pos.Nsucc_double s1 ⊆ BinPos.Pos.Nsucc_double s2.
Proof. destruct s1; destruct s2; auto. Qed.

Lemma double_succ_double_incl : forall s1 s2,
  s1 ⊆ s2 -> double s1 ⊆ BinPos.Pos.Nsucc_double s2.
Proof. destruct s1; destruct s2; auto. Qed.

Lemma pos_incl0 : forall p1 p2 : positive, p1 ⊆ p2 -> p1~0 ⊆ p2~0.
Proof. destruct p1; destruct p2; auto. Qed.

Lemma pos_incl1 : forall p1 p2 : positive, p1 ⊆ p2 -> p1~0 ⊆ p2~1.
Proof. destruct p1; destruct p2; auto. Qed.

Lemma pos_incl3 : forall p1 p2 : positive, p1 ⊆ p2 -> p1~1 ⊆ p2~1.
Proof. destruct p1; destruct p2; auto. Qed.

Lemma double_0 : forall s, 0%nat ∈ double s = false.
Proof. destruct s; auto. Qed.

Lemma succ_double_0 : forall s, 0%nat ∈ BinPos.Pos.Nsucc_double s.
Proof. destruct s; reflexivity. Qed.

Lemma double_n : forall s n, n ∈ s -> S n ∈ double s.
Proof. destruct s; auto. Qed.

Lemma succ_double_n : forall s n, n ∈ s -> S n ∈ BinPos.Pos.Nsucc_double s.
Proof. destruct s; auto. Qed.

Lemma double_Sn : forall s n, S n ∈ double s -> n ∈ s.
Proof. destruct s; auto. Qed.

Lemma succ_double_Sn : forall s n, S n ∈ BinPos.Pos.Nsucc_double s -> n ∈ s.
Proof. destruct s; auto. Qed.

Lemma union_idl : forall s, ∅ ∪ s = s. Proof. auto. Qed.

Lemma union_idr : forall s, s ∪ ∅ = s. Proof. destruct s; auto. Qed.

Lemma intersection_empl : forall s, ∅ ∩ s = ∅. Proof. auto. Qed.

Lemma intersection_empr : forall s, s ∩ ∅ = ∅. Proof. destruct s; auto. Qed.

Hint Resolve union_idl union_idr incl_reflexive pos_incl_reflexive.

Lemma union_lub1 : forall s1 s2, s1 ⊆ s1 ∪ s2.
Proof.
  destruct s1; destruct s2; auto.
    - rewrite union_idl. reflexivity.
    - generalize dependent p0.
      induction p; destruct p0; try reflexivity; simpl; auto;
        try (apply IHp).
Qed.

Lemma union_lub2 : forall s1 s2 s3, s1 ⊆ s3 -> s2 ⊆ s3 -> s1 ∪ s2 ⊆ s3.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
  generalize dependent p0. generalize dependent p1.
  induction p; destruct p0; destruct p1; simpl; auto;
    try (apply IHp).
Qed.

Definition union_absorb : forall s1 s2, s1 ⊆ s2 -> s2 ∪ s1 = s2 :=
  fun s1 s2 (s1I2: s1 ⊆ s2) =>
    extensionality _ _
    (union_lub2 _ _ _ (incl_reflexive _) s1I2)
      (union_lub1 _ _).

Hint Resolve intersection_empl intersection_empr emp_minimum.

Lemma intersection_glb1 : forall s1 s2, s1 ∩ s2 ⊆ s2.
Proof.
  destruct s1; destruct s2; auto.
  generalize dependent p0.
  induction p; destruct p0; auto;
    try reflexivity; simpl in *;
    destruct (BinPos.Pos.land p p0) eqn:H; try reflexivity;
    pose proof (IHp p0) as H'; rewrite H in H'; apply H'.
Qed.

Lemma intersection_glb2 : forall s1 s2 s3, s1 ⊆ s2 -> s1 ⊆ s3 -> s1 ⊆ s2 ∩ s3.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
  generalize dependent p0. generalize dependent p1.
  induction p; destruct p0; destruct p1; auto; simpl in *;
      destruct (BinPos.Pos.land p0 p1) eqn:H;
      try reflexivity;
      try (pose proof (IHp p1 p0) as H'; rewrite H in H'; simpl; apply H');
      intros H1 H2; inversion H1; inversion H2.
Qed.

Definition intersection_absorb : forall s1 s2, s1 ⊆ s2 -> s2 ∩ s1 = s1 :=
  fun s1 s2 (s1I2: s1 ⊆ s2) =>
    extensionality _ _
    (intersection_glb1 _ _)
    (intersection_glb2 _ _ _ s1I2 (incl_reflexive _)).

Definition incl_union : forall s1 s2, s2 ⊆ s1 -> s1 ∪ s2 = s1 :=
  fun s1 s2 s2Is1 =>
    extensionality (s1 ∪ s2) s1
      (union_lub2 s1 s2 s1 (incl_reflexive s1) s2Is1) (union_lub1 s1 s2).

Definition intersection_incl : forall s1 s2, s2 ⊆ s1 -> s1 ∩ s2 = s2 :=
  fun s1 s2 s2Is1 =>
    extensionality (s1 ∩ s2) s2
      (intersection_glb1 s1 s2) (intersection_glb2 s2 s1 s2 s2Is1 (incl_reflexive s2)).


Definition zero_intersection p : p~1 ∩ 1 = 1 :=
  intersection_incl _ _ (zero_incl _).

Lemma union_comm : forall s1 s2, s1 ∪ s2 = s2 ∪ s1.
Proof.
  intros s1 s2. apply extensionality;
        destruct s1; destruct s2; auto;
        generalize dependent p0;
        induction p; destruct p0; auto;
        try (apply IHp).
Qed.

Hint Resolve double_incl succ_double_incl.

Lemma intersection_comm : forall s1 s2, s1 ∩ s2 = s2 ∩ s1.
Proof.
  intros s1 s2. apply extensionality;
        destruct s1; destruct s2; auto;
        generalize dependent p0;
        induction p; destruct p0; try reflexivity;
        try (apply succ_double_incl; apply IHp);
        apply double_incl; apply IHp.
Qed.

Lemma intersection_incl_union : forall s1 s2, s1 ∩ s2 ⊆ s1 ∪ s2.
Proof.
  intros. rewrite union_comm.
  apply (incl_transitive _ s2 _).
  apply intersection_glb1. apply union_lub1.
Qed.

Lemma union_assoc : forall s1 s2 s3, s1 ∪ (s2 ∪ s3) = (s1 ∪ s2) ∪ s3.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
  apply extensionality;
    generalize dependent p0; generalize dependent p1;
    induction p; destruct p0; destruct p1; auto;
    simpl; try (apply IHp); auto.
Qed.

Hint Resolve zero_intersection.


Lemma intersection_assoc : forall s1 s2 s3, s1 ∩ (s2 ∩ s3) = (s1 ∩ s2) ∩ s3.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
  apply extensionality.
    - generalize dependent p0. generalize dependent p1.
      induction p; destruct p0; destruct p1; auto; simpl in *;
        try (
          destruct (BinPos.Pos.land p0 p1) eqn:H0;
          auto
        );
        try (
          destruct (BinPos.Pos.land p p0) eqn:H1;
          auto
        );
        try reflexivity; simpl;
        try (
          pose proof (IHp p1 p0) as H'; rewrite H0 in H';
          rewrite H1 in H'; rewrite intersection_empl in H';
          apply emp_min in H'; rewrite <- H'; reflexivity
        );
        try (
          pose proof (IHp p1 p0) as H'; rewrite H0 in H';
          rewrite H1 in H'; simpl in H'; apply (double_incl _ _ H')
        ).
        + destruct (BinPos.Pos.land p2 p1) eqn: H'; reflexivity.
        + pose proof (IHp p1 p0) as H'. rewrite H0 in H'.
          rewrite H1 in H'. simpl in H'. apply (succ_double_incl _ _ H').
    - generalize dependent p0. generalize dependent p1.
      induction p; destruct p0; destruct p1; auto; simpl;
          try (
            destruct (BinPos.Pos.land p p0) eqn:H1; try reflexivity; simpl; 
            destruct (BinPos.Pos.land p0 p1) eqn:H1'; try reflexivity;
            pose proof (IHp p1 p0) as H; simpl in H; rewrite H1 in H; rewrite H1' in H;
            simpl in H;
            try (assert (Z: 0%N = BinPos.Pos.Ndouble 0%N); try reflexivity; rewrite Z);
            apply double_incl; apply H
          ).
        + destruct (BinPos.Pos.land p p0) eqn:H1;
            destruct (BinPos.Pos.land p0 p1) eqn:H1'; simpl; try reflexivity.
            * destruct (BinPos.Pos.land p p2) eqn:H1''; try reflexivity.
            * destruct (BinPos.Pos.land p2 p1) eqn:H2. reflexivity.
              (* assert (con: (BinPos.Pos.land (pos (BinPos.Pos.land p p0)) p1) = 0%N). *)
              simpl in IHp. pose proof (IHp p1 p0) as H. rewrite H1' in H.
              rewrite H1 in H. simpl in H. apply emp_min in H. rewrite H2 in H.
              inversion H.
            * simpl in IHp. pose proof (IHp p1 p0) as H.
              rewrite H1 in H. rewrite H1' in H. simpl in H.
              apply succ_double_incl. apply H.
        + destruct (BinPos.Pos.land p0 p1) eqn:H1; simpl; try reflexivity.
Qed.

Lemma incl_union_inv : forall s1 s2 s3, s1 ⊆ s2 -> s1 ∪ s3 ⊆ s2 ∪ s3.
Proof.
  intros s1 s2 s3 s1I2. apply union_lub2.
    - apply (incl_transitive _ s2).
      + apply s1I2.
      + apply union_lub1.
    - rewrite union_comm. apply union_lub1.
Qed.

Lemma incl_intersection_inv : forall s1 s2 s3, s1 ⊆ s2 -> s3 ∩ s1 ⊆ s3 ∩ s2.
Proof.
  intros s1 s2 s3 s1I2. apply intersection_glb2.
    - rewrite intersection_comm. apply intersection_glb1.
    - apply (incl_transitive _ s1).
      + apply intersection_glb1.
      + apply s1I2.
Qed.

Definition mem_union : forall n s1 s2, n ∈ s1 -> n ∈ (s1 ∪ s2) :=
  fun n s1 s2 (nIs1 : n ∈ s1) =>
    proj1 (mem_incl _ _) (union_lub1 _ _) _ nIs1.

Lemma unioun_mem : forall n s1 s2, n ∈ (s1 ∪ s2) -> n ∈ s1 \/ n ∈ s2.
Proof.
  destruct s1; destruct s2; auto.
  generalize dependent p0. generalize dependent n.
  induction p; destruct p0; destruct n; auto; simpl;
    pose proof (IHp n p0) as H; simpl in H; apply H.
Qed.

Lemma mem_intersection : forall n s1 s2, n ∈ s1 /\ n ∈ s2 -> n ∈ (s1 ∩ s2).
Proof.
  intros n s1 s2 [nIs1 nIs2].
  destruct s1; destruct s2; auto.
  generalize dependent p0. generalize dependent n.
  induction p; destruct p0; destruct n; auto; simpl;
    intros nIs2; inversion nIs1; inversion nIs2;
    try (
      pose proof (IHp n H0 p0 H1) as H; simpl in H;
      destruct (BinPos.Pos.land p p0);
      inversion H;
      simpl; apply H
    ).
    destruct (BinPos.Pos.land p p0); try reflexivity.
Qed.

Definition intersection_mem : forall n s1 s2, n ∈ (s1 ∩ s2) -> n ∈ s2 :=
  fun n s1 s2 (nIi : n ∈ (s1 ∩ s2)) =>
    proj1 (mem_incl _ _) (intersection_glb1 _ _) _ nIi.

Lemma pos_card_nonzero : forall p, pos_cardinality p <> 0%nat.
Proof.
  induction p; simpl.
    - intros cont. inversion cont.
    - exact IHp.
    - intros cont. inversion cont.
Qed.

Lemma empty_card : # ∅ = 0%nat. Proof. reflexivity. Qed.

Lemma card_empty : forall s, # s = 0%nat -> s = ∅.
Proof.
  destruct s.
    - reflexivity.
    - destruct p; simpl;
        intros cont;
        try (apply pos_card_nonzero in cont);
        inversion cont.
Qed.

Lemma singleton_nonemp : forall n, {{n}} <> ∅.
Proof. induction n; intros H; inversion H. Qed.

Lemma singleton_card : forall n, #{{ n }} = 1%nat.
Proof.
  induction n.
    - reflexivity.
    - destruct n.
      + reflexivity.
      + simpl in *. apply IHn.
Qed.

Lemma card_incl : forall s1 s2, s1 ⊆ s2 -> Nat.leb (# s1) (# s2).
Proof.

  destruct s1; destruct s2; auto.
    - intros con. inversion con.
    - generalize dependent p0.
      induction p; destruct p0; auto; intros H; inversion H;
        pose proof (IHp p0) as H'; simpl in H';
        try (apply (proj2 (Arith.PeanoNat.Nat.leb_le _ _) (le_S _ _ (proj1 (Arith.PeanoNat.Nat.leb_le _ _) (H' H)))));
        apply H'; apply H.
Qed.

Definition card_union_leb_intersection :
  forall s1 s2, Nat.leb (# (s1 ∩ s2)) (# (s1 ∪ s2)) :=
    fun s1 s2 => card_incl _ _ (intersection_incl_union _ _).


Lemma card_land_plus : forall p1 p2,
  Nat.leb (# (BinPos.Pos.land p1 p2)) (pos_cardinality p1 + pos_cardinality p2).
Proof.
  intros. apply PeanoNat.Nat.leb_le. apply Plus.le_plus_trans. apply PeanoNat.Nat.leb_le.
  assert (A: pos_cardinality p1 = # (pos p1)). { reflexivity. }
  rewrite A.
  apply card_incl.
  assert (B: BinPos.Pos.land p1 p2 = p1 ∩ p2). { reflexivity. }
  rewrite B.
  rewrite intersection_comm.
  apply intersection_glb1.
Qed.

Hint Resolve PeanoNat.Nat.sub_0_r.

Lemma card_union : forall s1 s2,
  # (s1 ∪ s2) = ((# s1) + (# s2) - # (s1 ∩ s2))%nat.
Proof.
  destruct s1; destruct s2; auto.
    - simpl. rewrite PeanoNat.Nat.add_0_r. auto.
    - generalize dependent p0.
      induction p; destruct p0; auto; simpl;
        try (
          destruct (BinPos.Pos.lor p p0) eqn:H1;
          destruct (BinPos.Pos.land p p0) eqn:H2; simpl;
          pose proof (IHp p0) as H; simpl in H;
          rewrite H1 in H; rewrite H2 in H; simpl in H;
          try (
            destruct (pos_cardinality p2) eqn:H';
            try (rewrite H' in H); simpl in H
          );
          try (
            pose proof (card_land_plus p p0) as less;
            rewrite H2 in less; simpl in less;
            rewrite H;
            try (
              rewrite <- plus_n_Sm;
              rewrite (PeanoNat.Nat.sub_succ_l _ _ (proj1 (PeanoNat.Nat.leb_le _ _) less))
            );
            try (
              rewrite H' in less;
              rewrite PeanoNat.Nat.sub_succ_r;
              rewrite (PeanoNat.Nat.succ_pred _
                        (PeanoNat.Nat.sub_gt _ _
                          (proj1 (PeanoNat.Nat.le_succ_l _ _) (
                            proj1 (PeanoNat.Nat.leb_le _ _) less
                          ))
                        )
              )
            );
            try reflexivity
          );
          try (rewrite <- PeanoNat.Nat.add_succ_comm; simpl);
          try (rewrite PeanoNat.Nat.sub_0_r in H; rewrite H; reflexivity);
          try reflexivity
        );
        try (rewrite PeanoNat.Nat.sub_0_r);
        try (rewrite PeanoNat.Nat.add_1_r); try reflexivity.
  
      destruct (pos_cardinality p1) eqn:Hh; auto.
      rewrite PeanoNat.Nat.sub_succ_r.
      rewrite PeanoNat.Nat.sub_succ_r in H.
      assert (what: (0 < (pos_cardinality p + pos_cardinality p0 - n))%nat). {
        unfold lt. rewrite H. apply PeanoNat.Nat.le_pred_l.
      }
      apply (PeanoNat.Nat.succ_pred_pos _ what).
Qed.

Lemma diff_emp_id : forall s, s \ ∅ = s.
Proof. destruct s; reflexivity. Qed.
 
Lemma diff_le : forall s1 s2, s1 \ s2 ⊆ s1.
Proof.
  destruct s1; destruct s2;
    try reflexivity.
      - rewrite diff_emp_id. apply incl_reflexive.
      - generalize dependent p0.
        induction p; destruct p0;
        try reflexivity; simpl in *;
        try (apply pos_incl_reflexive);
        try (pose proof (IHp p0) as IHp0;
          destruct (BinPos.Pos.ldiff p p0); try reflexivity; try (apply IHp0)).
Qed.

Hint Resolve diff_emp_id diff_le.

Lemma diff_incl : forall s1 s2, s1 \ s2 ⊆ s1.
Proof. destruct s1; destruct s2; auto. Qed.

Hint Resolve diff_incl.
Hint Resolve double_0 succ_double_0 double_n succ_double_n double_Sn succ_double_Sn.

Lemma mem_diff : forall n s1 s2, n ∈ s1 /\ (n ∈ s2 = false) <-> n ∈ (s1 \ s2).
Proof.
  destruct s1; destruct s2; split; simpl; auto;
    try (
      intros [H1 H2]; inversion H1; inversion H2;
      try (apply H1)
    );
    try (intros H; inversion H).
    - clear H1 H3.
      generalize dependent p0. generalize dependent n.
      induction p; destruct p0; destruct n; simpl; auto;
        intros H; inversion H.
      inversion H0.
    - clear H1. generalize dependent p0. generalize dependent n.
      induction p; destruct p0; destruct n; simpl; auto;
        intros H; try (rewrite double_0 in H); inversion H.
      split; auto.
Qed.

Lemma diff_cut : forall s1 s2, s2 ∩ (s1 \ s2) = ∅.
Proof.
  intros. apply extensionality.
    - apply mem_incl. intros n H.
      pose proof (intersection_mem _ _ _ H) as nId.
      rewrite intersection_comm in H.
      pose proof (intersection_mem _ _ _ H) as nI2.
      apply mem_diff in nId as [_ nNI2].
      rewrite nNI2 in nI2. inversion nI2.
    - apply emp_minimum.
Qed.

Lemma incl_diff_inv1 : forall s1 s2 s3, s1 ⊆ s2 -> s1 \ s3 ⊆ s2 \ s3.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
    - intros con. inversion con.
    - generalize dependent p0. generalize dependent p1.
      induction p; destruct p0; destruct p1; auto; try reflexivity;
        try (intros H; inversion H);
        try (apply double_incl);
        try (apply succ_double_incl);
        try (apply double_succ_double_incl);
        try (apply (IHp p1 p0 H)).
      + simpl. destruct (BinPos.Pos.ldiff p0 p1) eqn:H'; reflexivity.
Qed.

Lemma incl_diff_inv2 : forall s1 s2 s3, s1 ⊆ s2 -> s3 \ s2 ⊆ s3 \ s1.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
    - intros con. inversion con.
    - generalize dependent p0. generalize dependent p1.
      induction p; destruct p0; destruct p1;
        try (intros H; inversion H);
        try (apply double_incl);
        try (apply succ_double_incl);
        try (apply double_succ_double_incl);
        try (apply (IHp p1 p0 H));
        auto.
      + simpl. destruct (BinPos.Pos.ldiff p1 p0) eqn:H'.
        * reflexivity.
        * simpl. pose proof (diff_le p1 p0) as H1. simpl in H1.
          rewrite H' in H1. apply H1.
Qed.


Hint Resolve intersection_glb1 intersection_glb2.

Lemma diff_intersection : forall s1 s2, s1 \ s2 = s1 \ s1 ∩ s2.
Proof.
  destruct s1; destruct s2; auto.
  apply extensionality.
    - apply (incl_diff_inv2 (p ∩ p0) p0 p (intersection_glb1 p p0)).
    - generalize dependent p0. induction p; destruct p0; auto; simpl;
        destruct (BinPos.Pos.land p p0) eqn:H1; simpl;
        destruct (BinPos.Pos.ldiff p p0) eqn:H2; simpl; try reflexivity;
        try (destruct (BinPos.Pos.ldiff p p1) eqn:H3; simpl; try reflexivity); 
        try (
          try (apply emp_min; symmetry; apply double_empty);
          pose proof (IHp p0) as H; simpl in H;
          rewrite H1 in H; rewrite H2 in H;
          try (rewrite H3 in H);
          try (apply emp_min in H; rewrite <- H; reflexivity);
          apply H
        ).
Qed.

Lemma diff_emp_incl : forall s1 s2, s1 \ s2 = ∅ <-> s1 ⊆ s2.
Proof.
  destruct s1; destruct s2; split; try reflexivity;
    try (generalize dependent p0); induction p;
      try (intros H; rewrite diff_emp_id in H; rewrite H; reflexivity);
      try (intros H; apply emp_min in H; rewrite <- H; reflexivity);
      destruct p0;
        try reflexivity;
        try (intros H; inversion H; simpl in *; rewrite H; reflexivity);
        intros H;
        try (apply double_empty in H; apply IHp; apply H);
        try (apply double_empty; apply IHp in H; apply H);
        try (apply empty_double; apply IHp; apply H).
  simpl in *. apply succ_double_nonempty in H. inversion H.
Qed.

Lemma diff_semi_comm : forall s1 s2 s3, s1 \ s2 \ s3 = s1 \ s3 \ s2.
Proof.
  destruct s1; destruct s2; destruct s3; auto.
  apply extensionality;
  generalize dependent p0; generalize dependent p1;
  induction p; destruct p0; destruct p1; auto; simpl;
    try (destruct (BinPos.Pos.ldiff p p0) eqn:H1);
    try (destruct (BinPos.Pos.ldiff p p1) eqn:H2; auto);
    try (
      pose proof (IHp p1 p0) as H; simpl in H;
      rewrite H1 in H; rewrite H2 in H;
      simpl in H; simpl;
      try (destruct (BinPos.Pos.ldiff p2 p1); auto);
      apply H
    ); try reflexivity; simpl;
    destruct (BinPos.Pos.ldiff p2 p0) eqn:H3; simpl;
    try (
      pose proof (IHp p1 p0) as H; simpl in H;
      rewrite H1 in H; rewrite H2 in H; simpl in H; apply emp_min in H;
      rewrite H3 in H; inversion H
    );
    reflexivity.
Qed.

Hint Resolve mem_intersection mem_diff diff_cut.

Lemma diff_relcompl1 : forall s1 s2, (s1 ∩ s2) ∩ (s1 \ s2) = ∅.
Proof.
  intros. apply extensionality.
    - apply (incl_transitive _ (s2 ∩ (s1 \ s2)) _).
        + rewrite intersection_comm.
          rewrite (intersection_comm s1 s2).
          rewrite intersection_assoc.
          rewrite (intersection_comm _ s2).
          rewrite intersection_comm.
          apply intersection_glb1.
        + rewrite diff_cut. apply incl_reflexive.
    - apply emp_minimum.
Qed.

Lemma diff_relcompl2 : forall s1 s2, (s1 ∩ s2) ∪ (s1 \ s2) = s1.
Proof.
  intros. apply extensionality.
    - pose proof (intersection_glb1 s2 s1) as iI1.
      rewrite intersection_comm in iI1.
      pose proof (diff_incl s1 s2) as dI1.
      apply (union_lub2 _ _ _ iI1 dI1).
    - apply mem_incl. intros n nI1.
      destruct (n ∈ s2) eqn:nI2.
        + apply mem_union. apply mem_intersection. split.
          * apply nI1.
          * apply nI2.
        + rewrite union_comm. apply mem_union. apply mem_diff. split.
          * apply nI1.
          * apply nI2.
Qed.

Lemma card_cut : forall s1 s2, # s1 = ((# (s1 ∩ s2)) + (# (s1 \ s2)))%nat.
Proof.
  intros. rewrite <- (diff_relcompl2 s1 s2) at 1.
  rewrite <- PeanoNat.Nat.sub_0_r.
  rewrite <- empty_card.
  rewrite <- (diff_relcompl1 s1 s2).
  apply card_union.
Qed.

Lemma card_incl_diff : forall s1 s2, s2 ⊆ s1 -> # s1 = (# s2 + # (s1 \ s2))%nat.
Proof.
  intros s1 s2 s1I2. rewrite <- (intersection_absorb _ _ s1I2) at 1.
  apply card_cut.
Qed.

Lemma card_single_diff : forall s n, n ∈ s -> # s = S (# (s \ {{n}})).
Proof.
  intros s n nIs. pose proof (card_incl_diff s {{n}}) as H.
  rewrite singleton_card in H. simpl in H. apply H.
  apply (singleton_mem_incl _ _ nIs).
Qed.

(*        
Check 1~0~1~0~1.
Compute (∅ ⊆ ∅).
Compute (∅ ⊆ 1).
Compute (1 ⊆ 1).
Compute (1 ⊆ 1~1).
Compute (1 ⊆ 1~0).
Compute (1~1~0 ⊆ 1~0).
Compute (1~0~1~1~0~1 ⊆ 1~1~0~1~0~1~0~1~1~0~1).
Compute (1~0~1~1~0~1 ⊆ 1~1~0~1~0~1~0~1~1~0~0).
Compute (1~0~1~1~1~1 ⊆ 1~1~0~1~0~1~0~1~1~0~1).
Compute (1~1~0~1~0~1~0~1~1~0~1 ⊆ 1~0~1~1~0~1).



Compute (cardinality 1~0~1~0~1).


Compute (1 ∈ 1~0~1~0~1). (* false *)

Compute (1 ∈ (1~0 ∪ 1~0~1~0~1)). (* true *)


Compute (0 ∈ 1~0~1~0~0). (* false *)

Compute (0 ∈ (1 ∪ 1~0~1~0~0)). (* true *)


Compute (0 ∈ ∅). (* false *)

Compute (0 ∈ (1 ∪ ∅)). (* true *)

Compute (0 ∈ 1). (* true *)
*)