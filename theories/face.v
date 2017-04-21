(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
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

Section Def.

Variable R: realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Variable c : 'cV[R]_n.

Hypothesis Hbounded: bounded A b c.

Definition face := predI (polyhedron A b) [pred x | '[c,x] == opt_value A b c].

Definition faceA := col_mx A (- c^T).
Definition faceb := col_mx b (- (opt_value A b c))%:M.

Lemma faceW x : (x \in face) = (x \in polyhedron A b) && ('[c,x] <= opt_value A b c).
Proof.
rewrite 2!inE.
apply: andb_id2l => H.
move/boundedP: Hbounded => [_ /(_ x H) Hx].
by apply/idP/idP => [/eqP -> | Hx'];
  last by rewrite eqr_le; apply/andP; split.
Qed.

Lemma faceE x : (x \in face) = (x \in polyhedron faceA faceb).
Proof.
rewrite /face !inE mul_col_mx col_mx_lev.
rewrite mulNmx raddfN /= lev_opp2 -vdot_def ['[_,c]]vdotC. 
apply: andb_id2l => H.
move/boundedP: Hbounded => [_ /(_ x H) Hx].
apply/idP/idP; first by move/eqP => ->; apply: lev_refl.
- move/forallP/(_ 0); rewrite !mxE /= !mulr1n => Hx'.
  by rewrite eqr_le; apply/andP; split.
Qed.

Definition active_ineq_of_face :=
  if simplex A b c is Simplex_optimal_point (_, u) then
    [ set i | u i 0 > 0]
  else
    set0. (* not used *)

Lemma faceE_active_ineq :
  let: bas := active_ineq_of_face in
  face =i predI (polyhedron A b) [pred x | row_submx A bas *m x == row_submx b bas].
Proof.
move => x; rewrite 2![in RHS]inE 2!inE.
apply: andb_id2l => Hx.
move/(intro_existsT (feasibleP _ _)): (Hx) => Hfeas.
rewrite /opt_value /active_ineq_of_face.
case: (simplexP A b c) => [ d /(intro_existsT (infeasibleP _ _))/negP
                         | p /(intro_existsT (unboundedP_cert _ _ _)) 
                         | [x0 u] /= [Hx0 Hu Hcsc0] ]; try by done.
- move: (Hbounded); rewrite bounded_is_not_unbounded //.
  by move/negP.
- have ->: ('[ c, x] == '[ c, x0]) = (compl_slack_cond A b x u).
  + rewrite -(compl_slack_cond_duality_gap_equiv Hx Hu) duality_gap_eq0_def.
    by rewrite Hcsc0.
  rewrite -row_submx_mul.
  move: Hu; rewrite inE => /andP [_ Hu].
  apply: (sameP (compl_slack_condP _ _ _ _)); apply: (iffP idP) => [/eqP H i | H].
  + case: (ler0P (u i 0)) => [Hi | Hi].
    * move/forallP/(_ i): Hu; rewrite mxE.
      by move/(conj Hi)/andP/ler_anti; left.
    * have Hi': (i \in [set i | 0 < u i 0]) by rewrite inE.
      pose j := enum_rank_in Hi' i.
      move/colP/(_ j): H.
      by rewrite !row_submx_mxE enum_rankK_in //; right.
  + apply/eqP/colP => i.
    rewrite !row_submx_mxE.
    move/(_ (enum_val i)): H.
    move: (enum_valP i); rewrite inE; move/lt0r_neq0 => H.
    case; last by done.
    by move/eqP; move/negbTE: H => ->.
Qed.

End Def.