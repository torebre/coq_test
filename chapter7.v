Require Import Arith Omega.

Theorem le_plus_minus : forall n m:nat, m <= n -> n = m+(n-m).
Proof.
intros n m H.

induction n.

rewrite <- le_n_0_eq with (1 := H); simpl; trivial.