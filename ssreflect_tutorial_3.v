From mathcomp Require Import eqtype ssrnat.
Require Import ssreflect ssrbool.

Print ex.

Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).
Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.
Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof.
move=> x [y Rxy].
by apply: R_trans _ (R_sym _ y _).
Qed.
End R_sym_trans.

Section Smullyan_drinker.
Variables (D : Type)(P : D -> Prop).
Hypothesis (d : D) (EM : forall A, A \/ ~A).
Lemma drinker : exists x, P x -> forall y, P y.
Proof.
case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y.
exists d => _ y; case: (EM (P y)) => // notPy.
by case: nonotPy; exists y.
Qed.
End Smullyan_drinker.

Print False.