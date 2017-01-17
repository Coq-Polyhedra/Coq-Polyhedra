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

Lemma strong_duality :
  feasible A b -> dual_feasible A c ->
  exists x, exists u, [/\ x \in polyhedron A b, u \in dual_polyhedron A c & duality_gap b c x u = 0].
Proof.
case: (simplexP A b c) => [/negP | [_ d] /= [_ Hd Hd'] 
                          | [x u] /= [Hx Hu Hcsc] _ _]; try by done.
- suff /negP: ~~ dual_feasible A c by done.
  by apply/dual_infeasibleP; exists d; split. 
- exists x; exists u; split; try by done.
  by apply/eqP; rewrite (compl_slack_cond_duality_gap_equiv Hx Hu) //.
Qed.

Lemma unbounded_feasible_direction_equiv :
  feasible A b ->
  (unbounded A b c <-> exists d, (feasible_direction A d) /\ '[c,d] < 0).
Proof.
move => Hfeas.
split; last by move => [d [Hd Hd']]; apply: (unbounded_certificate Hfeas Hd Hd').
- case: (simplexP A b c) => [|[x d] /= [Hx Hd Hd'] _
                             |[x u] /= [Hx Hu Hcsc] Hunbounded];
    try by [done | exists d].
  + have: (dual_feasible A c) by exists u.
    by move/dual_feasible_bounded/(_ Hunbounded).
Qed.

Lemma not_unbounded_is_bounded :
  ~ (unbounded A b c) -> (exists K, forall x, x \in polyhedron A b -> '[c,x] >= K).
Proof.
move => H.
case: (simplexP A b c) => [ Hinfeas
                          | [x d] /= [Hx Hd Hd'] 
                          | [x u] /= [Hx Hu Hcsc]]. 
- exists 0; move => x Hx.
  by have: (feasible A b) by exists x.
- suff: (unbounded A b c) by done.
  apply: (unbounded_certificate (d:= d)); try by done.
  by exists x.
- exists '[c,x]; rewrite -(compl_slack_cond_duality_gap_equiv Hx Hu) // in Hcsc.
  suff: (optimal_solution A b c x) by apply: proj2.
  by apply: (duality_gap_eq0_optimality Hx Hu (eqP Hcsc)).
Qed.

Lemma bounded_dual_feasible :
  feasible A b -> ~ (unbounded A b c) -> dual_feasible A c.
Proof.
move => Hfeas Hbounded.
case: (simplexP A b c) => [| [? d] /= [_ Hd Hd'] | [? u] /= [_ Hu _]]; first by done.
- by move: (unbounded_certificate Hfeas Hd Hd').
- by exists u.
Qed.

Lemma farkas_lemma z :
  (feasible A b) -> 
  (forall x, x \in polyhedron A b -> '[c,x] >= z) <->
  (exists u, [/\ u >=m 0, A^T *m u = c & '[b,u] >= z]).
Proof.
move => Hfeas; split; last first.
- move => [u [Hu <- Hu']] x Hx'.
  rewrite -vdot_mulmx.
  suff: '[u, A *m x] >= '[u,b].
  + by rewrite vdotC; apply: ler_trans.
  + apply: vdot_lev; try by [done | rewrite inE in Hx'].
- move => Hbounded.
  case: (simplexP A b c) => [| [x d] /= [_ Hd Hd']| [x u] /= [Hx Hu  Hcsc]]; first by done.
  + suff: ~ (unbounded A b c) by move: (unbounded_certificate Hfeas Hd Hd'). 
    * by apply: bounded_is_not_unbounded; exists z.
  + move: (Hu); rewrite inE => /andP [/eqP Hu' Hu''].
    exists u; split; try by done.
    rewrite -(compl_slack_cond_duality_gap_equiv Hx Hu) // duality_gap_eq0_def in Hcsc.
    move/eqP: Hcsc <-.
    by apply: Hbounded.
Qed.

End Duality.