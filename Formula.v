Require Import Lang.
Require Import Finset.

Fixpoint weight (p : prop) : nat :=
match p with
  | p1 ∧ p2 => S ((weight p1) + (weight p2))
  | p1 ∨ p2 => S ((weight p1) + (weight p2))
  | p1 ⊃ p2 => S ((weight p1) + (weight p2))
  | p1 ⊂ p2 => S ((weight p1) + (weight p2))
  | p1 ⊗ p2 => S ((weight p1) + (weight p2))
  | _ => S O
  end.

Fixpoint atoms_of (p : prop) : finset :=
  match p with
  | ^x_a => {{a}}
  | p1 ∧ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ∨ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ⊃ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ⊂ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ⊗ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | _ => ∅
  end.
Notation "^V" := atoms_of.

Fixpoint atoms_num (p : prop) : nat :=
  match p with
    | ^x__ => 1
    | p1 ∧ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ∨ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ⊃ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ⊂ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ⊗ p2 => (atoms_num p1) + (atoms_num p2)
    | _ => 0
    end.
(* 
Require Import BinNat BinNatDef BinPos BinPosDef.
Fixpoint partition {T : Type} (l : list T) (mask : N) : list T :=
  match (l, mask) with
  | (_, 0%N) => []
  | ([], _) => []
  | (h :: t, pos p) => match p with
                      | xH => [h]
                      | xO p => partition t p
                      | xI p => h :: (partition t p)
                      end
  end.

Fixpoint partition_list {T : Type} (l : list T) (mask : N) : list (list T) :=
  match (l, mask) with
  ([], _) => [[]]
  (_, 0%N) => [[]]
  (h :: t, pos p) => match p with
                    | xH => [[h]]
                    | xO p => 
  end.

Compute (partition_list [2;3;4;5]).


Fixpoint E0 (a : atom) (G : list prop) (mask : nat) : prop :=
  match G with
  | [] => 1
  | [^x_b] => if PeanoNat.Nat.eqb a b then ⊤ else ^x_b
  | (p ∧ q) :: G => (E0 a (p :: G) mask) ∧ (E0 a (p :: G) mask)
  | (p ∨ q) :: G => (E0 a (p :: G) mask) ∨ (E0 a (p :: G) mask)
  | (p ⊗ q) :: G => E0 a (p :: q :: G) mask
  | _ => 0
  end.


Fixpoint E1 (a : atom) (G : list prop) (mask : nat) : prop :=
  match (BinNatDef.of_nat mask) with
  | 0%N =>  *)