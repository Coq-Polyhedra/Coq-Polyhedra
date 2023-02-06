From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import inner_product poly_base polyhedron lrel affine.

Import Order.Theory.
Import RelOrder.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.

Section Polar.

Context (R : realFieldType) (n : nat).
Context (P : 'poly[R]_n).

Definition polar_lrel (x : 'cV[R]_n) := [<-x , -1>].
Definition polar_base := [fset (polar_lrel x) | x in vertex_set P]%fset.
Definition polar := 'P(polar_base).

Hypothesis P_full_dim : (\pdim P = n.+1).
Hypothesis P_compact: compact P.
Hypothesis P0 : 0 \in P.

Context (eps : R).

Hypothesis eps_gt0: eps > 0.
Hypothesis interior0: forall d, eps *: d \in P.

Lemma polar_0: 0 \in polar.
Proof.
apply/in_poly_of_baseP=> ? /imfsetP [/= x _ ->].
by rewrite inE /= vdot0r lerN10.
Qed.

Lemma polar_full_dim: \pdim polar = n.+1.
Proof.
apply/anti_leq; rewrite affine.adim_leSn /=.
move: (compact_pointed P_compact); apply/contraTT.
rewrite -leqNgt=> po_dimn; apply/pointedPn.
move: po_dimn; rewrite dimN0_eq /=; 
  last (apply/proper0P; exists 0; exact: polar_0).
Admitted.


End Polar.