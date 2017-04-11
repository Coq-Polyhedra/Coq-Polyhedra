(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp perm matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import polyhedron simplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.


Section Duality.

Variable R: realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Variable c : 'cV[R]_n.

Lemma strong_duality_primal_dual_feasible :
  feasible A b -> dual_feasible A c ->
  exists p, [/\ p.1 \in polyhedron A b, p.2 \in dual_polyhedron A c & '[c,p.1] = '[b, p.2]].
Proof.
move => Hfeas.
rewrite -(bounded_is_dual_feasible _ Hfeas) => /boundedP_cert [[x u] /= [Hx Hu Hcx Hbu]].
exists (x,u); split; try by done.
by rewrite /= Hcx Hbu. 
Qed.

Lemma strong_duality_primal_feasible_dual_infeasible :
  feasible A b -> ~~ (dual_feasible A c) -> (unbounded A b c).
Proof.
move/feasibleP => [x Hx].
move/dual_infeasibleP => [d [Hd Hd']].
by apply/unboundedP_cert; exists (x, d); split.
Qed.

Lemma strong_duality_primal_infeasible_dual_feasible :
  ~~ (feasible A b) -> dual_feasible A c -> unbounded (dualA A) (dualb _ c) (-b).
Proof.
move/infeasibleP => [d [Hd Hd']].
move/dual_feasibleP => [u Hu].  
apply/unboundedP_cert; exists (u,d); split.
- by rewrite -dual_polyhedronE.
- by rewrite -dual_feasible_directionE.
- by rewrite vdotNl oppr_lt0.
Qed.  
  
Lemma farkas_lemma_on_inequalities z :
  (feasible A b) ->
  (forall x, x \in polyhedron A b -> '[c,x] >= z) <->
  (exists u, [/\ u >=m 0, A^T *m u = c & '[b,u] >= z]).
Proof.
move => Hfeas; split; last first.
- move => [u [Hu <- Hu']] x Hx.
  rewrite -vdot_mulmx.
  suff: '[u, A *m x] >= '[u,b].
  + by rewrite vdotC; apply: ler_trans.
  + apply: vdot_lev; try by [done | rewrite inE in Hx'].
- move => H.
  case: (boolP (bounded A b c)).
  + move/boundedP_cert => [[x u] /= [Hx Hu Hcx Hbu]].
    move: (Hu); rewrite inE => /andP [/eqP Hu' Hu''].
    exists u; split; try by done.
    by move: (H _ Hx); rewrite Hcx Hbu.
  + move/feasibleP: (Hfeas) => [x Hx].
    rewrite bounded_is_not_unbounded // negbK.
    move/unboundedP/(_ z) => [y [Hy Hy']].
    move/(_ y Hy): H.
    by move/(ltr_le_trans Hy'); rewrite ltrr. 
Qed.

End Duality.