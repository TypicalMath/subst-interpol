Require Import Lang.

Inductive maybe_prop : Type :=
| None : maybe_prop
| Some : prop -> maybe_prop.

Notation "[ ]" := None.
Coercion Some : prop >-> maybe_prop.