(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2018, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx hpolyhedron polyhedron affine_hull convex_hull.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\vert P " (at level 50, format "\vert  P").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section VertexSet.

Variable R : realFieldType.
Variable n : nat.

Definition vertex_set (P : 'poly[R]_n) :=
  [fset (pick_point F) | F in (\face P) & (hull_dim F == 0)%N]%fset.

Notation "\vert P" := (vertex_set P).

Lemma vertex_setP P v :
  reflect ([poly v] \in \face P) (v \in \vert P).
Proof.
apply: (iffP idP).
- move/imfsetP => [F /andP [/= F_face_P /eqP/hull_dim0P [w F_poly_eq_w]]].
  rewrite {}F_poly_eq_w in F_face_P *.
  by rewrite pick_point_poly_point => ->.
- move => poly_v_face_P.
  apply/imfsetP => /=; exists [poly v]; last by rewrite pick_point_poly_point.
  rewrite inE; apply/andP; split; first by done.
  by apply/eqP/hull_dim0P; exists v.
Qed.

Arguments vertex_setP [P v].

Lemma vertex_inclusion P :
  {subset \vert P <= P }.
Proof.
move => v /vertex_setP/face_subset poly_v_sub_P.
by apply: poly_v_sub_P; apply/poly_point_inP.
Qed.

Lemma vertex_face_inclusion (F P : 'poly[R]_n) :
  F \in \face P -> (\vert F `<=` \vert P)%fset.
Proof.
move => F_face_P; apply/fsubsetP => v /vertex_setP v_face_F.
move/fsubsetP/(_ _ v_face_F): (face_of_face F_face_P).
by move/vertex_setP.
Qed.

Lemma vertex_set_face (F P : 'poly[R]_n) :
  F \in \face P -> \vert F = [fset v in \vert P | v \in F]%fset.
Proof.
Admitted.

Lemma vertex_objP (P : 'poly[R]_n) (v : 'cV[R]_n) :
  reflect (v \in P /\ exists c, (forall x, x \in P -> x != v -> '[c,v] < '[c,x])) (v \in \vert P).
Proof.
apply: (iffP idP) => [v_vert | [v_in_P [c v_proper_min]]].
- split; first exact: vertex_inclusion.
  have P_non_empty : non_empty P by apply/non_emptyP; exists v; apply: vertex_inclusion.
  move/vertex_setP/(faceP P_non_empty) : v_vert => [c [_ c_face]].
  exists c.
  have c_v_min: forall x, x \in P -> '[ c, v] <= '[ c, x]
    by move/c_face: (poly_point_self_in v) => [_].
  move => x x_in_P x_neq_v.
  apply: (argmin_inN_lt c_face); by [ done | rewrite poly_point_inE ].
- have P_non_empty : non_empty P by apply/non_emptyP; exists v.
  have v_min : {over P, v minimizes c}.
  + split; first by done.
  + move => x x_in_P.
    case: (boolP (x == v)); first by move/eqP ->.
    move/(v_proper_min _  x_in_P); exact: ltrW.
  apply/vertex_setP/(faceP P_non_empty).
  exists c; split; first by apply/boundedP; exists v.
  move => x; split; last by move/poly_point_inP ->.
  move => [x_in_P /(_ _ v_in_P)].
  apply: contraTT; rewrite -ltrNge poly_point_inE; exact: v_proper_min.
Qed.

Lemma vertex_set_sep (P : 'poly[R]_n) (v : 'cV[R]_n) :
  v \in \vert P -> exists c, [forall (w : (\vert P) | val w != v), '[c, val w] > '[c, v]].
Proof.
Admitted.

Definition obj_of_vertex (P : 'poly[R]_n) (v : 'cV[R]_n) (v_vert : v \in \vert P) := xchoose (vertex_set_sep v_vert).

Lemma obj_of_vertexP (P : 'poly[R]_n) (v : 'cV[R]_n) (v_vert : v \in \vert P) :
  let c := obj_of_vertex v_vert in
  forall w, w \in \vert P -> w != v -> '[c, w] > '[c, v].
Proof.
Admitted.

End VertexSet.

Notation "\vert P" := (vertex_set P).

Section Minkowski.

Variable R : realFieldType.
Variable n : nat.

Theorem conv_vert (P : 'poly[R]_n) : compact P -> P =i \conv (\vert(P)).
Proof.
move => P_compact x; apply/idP/idP.
- case: (boolP (non_empty P)) => [P_non_empty | /non_emptyPn -> //=].
  apply: contraLR => /convPn [c /separationP c_sep].
  have c_bounded : bounded c P by apply/compactP.
  pose F := face_of_obj c_bounded.
  have vert_F : (exists v, v \in \vert F).
  + admit.
  pose v0 := xchoose vert_F.
  have v0_vert_P : v0 \in \vert P.
  + have: v0 \in \vert F by exact: xchooseP.
    by apply/fsubsetP; apply: vertex_face_inclusion; exact: face_of_obj_face.
  have v0_in_F : v0 \in F by apply: vertex_inclusion; exact: xchooseP.
  apply/negP => x_in_P.
  move: (face_of_objP c_bounded _ v0_in_F) => [_] /(_ _ x_in_P).
  apply/negP; rewrite -ltrNge; exact: c_sep.
- apply: poly_convex; exact: vertex_inclusion.
Admitted.

Variable P : 'poly[R]_n.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis P_base : [P has \base 'P(A,b)].

Lemma active_inPn_vert i :
  reflect (exists2 x, x \in \vert P & (A *m x) i 0 > b i 0) (i \notin { eq(P) on 'P(A,b) }).
Admitted.

End Minkowski.

Section VertexFigure.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'poly[R]_n.
Hypothesis P_non_empty : non_empty P.
Hypothesis P_compact : compact P.

Variable v : 'cV[R]_n.
Hypothesis v_vert : v \in \vert P.
Variable c : 'cV[R]_n.
Variable alpha : R.
Hypothesis c_v_lt_alpha : '[c,v] < alpha.
Hypothesis c_other_gt_alpha : forall w, w \in ((\vert P) `\ v)%fset -> '[c,w] > alpha.

Section Fun.

Let H := poly_hyperplane c alpha.
Let H_base := 'P(c^T, alpha%:M).
Fact H_has_base : [H has \base H_base].
  by exact: poly_hyperplane_base.

Definition vf_fun (Q : 'poly[R]_n) := polyI Q H.

Fact vf_fun_base (Q : 'poly[R]_n) (base: 'hpoly[R]_n) :
  [Q has \base base] -> [vf_fun Q has \base (hpolyI base H_base)].
Proof.
move => Q_base; apply: concat_base_polyI; by [done | exact: poly_hyperplane_base].
Qed.

Fact vf_fun_vert (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH -> ([fset v] `<` \vert Q)%fset.
Proof.
move => Q_face /andP [v_in_Q Q_not_sub_v].
rewrite poly_point_incl in v_in_Q.
have v_vtx : v \in \vert Q
  by rewrite (vertex_set_face Q_face) in_fsetE /=; apply/andP; split.
apply/andP; split; first by rewrite fsub1set.
move: Q_not_sub_v; apply: contraNN; rewrite fsubset1 => /orP.
case; last by move/eqP => vertQ_eq_fset0; rewrite vertQ_eq_fset0 in_fsetE in v_vtx.
move/eqP => vertQ_eq_v; move: (conv_vert (compact_face P_compact Q_face)).
rewrite vertQ_eq_v => Q_eq_v.
apply/poly_subsetP; move => x; rewrite Q_eq_v => /convP1 ->.
exact: poly_point_self_in.
Qed.

Fact vf_fun_non_empty (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH -> non_empty (vf_fun Q).
Proof.
move => Q_face v_proper_Q.
move: (vf_fun_vert Q_face v_proper_Q) => /andP [v_vtx /fsubsetPn [w w_vtx w_neq_v]].
rewrite fsub1set in v_vtx.
rewrite in_fset1 in w_neq_v.
have c_w_gt_alpha : '[c,w] > alpha.
- apply: c_other_gt_alpha; rewrite in_fsetD1; apply/andP; split; first by done.
  by apply/(fsubsetP (vertex_face_inclusion Q_face)).
move: (linear_ivt c_v_lt_alpha c_w_gt_alpha) => [x /osegm_subset x_in_v_w c_x_eq_alpha].
have x_in_Q : x \in Q.
- apply/(poly_subsetP (segm_subset _ _))/x_in_v_w; exact: vertex_inclusion.
apply/non_emptyP; exists x; rewrite polyI_inE poly_hyperplane_inE.
by apply/andP; split; last apply/eqP.
Qed.

Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Let base := 'P(A,b).
Hypothesis P_has_base : [P has \base base].

Fact vf_fun_eq (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH ->
    {eq (vf_fun Q) on (hpolyI base H_base)} = (rshift m ord0) |: (lshift 1) @: {eq Q on 'P(A,b) } .
Proof.
move => Q_face v_proper_Q.
move: (Q_face) => /(face_baseP P_has_base) [Q_base _ _].
apply/eqP; rewrite eq_sym eqEsubset; apply/andP; split.
- rewrite setUC.
  suff ->: [set rshift m ord0] = (@rshift m 1) @: {eq H on H_base} by exact: concat_base_eq_polyI.
  by rewrite poly_hyperplane_eq imset_set1.
- apply/subsetP => j; apply: contraTT.
  case: (splitP' j); last first.
  + by move => j' ->; move: (ord1_eq0 j') ->; rewrite setU11.
  + move => j' ->.
    rewrite in_setU1 negb_or lrshift_distinct andTb.
    move => j'_not_in_lset.
    have j'_not_in_eqQ : j' \notin {eq Q on 'P(A,b)}.
      by move: j'_not_in_lset; apply: contraNN => [j'_in_eqQ]; apply/imsetP; exists j'.
    rewrite {j j'_not_in_lset}.
    move: (vf_fun_vert Q_face v_proper_Q) => /andP [v_vtx /fsubsetPn [w' w'_vtx w'_neq_v]].
    rewrite fsub1set in v_vtx; rewrite in_fset1 in w'_neq_v.
    have [w w_vtx w_v_sat] : exists2 w, (w \in ((\vert Q) `\ v)%fset) & (((A *m w) j' 0 > b j' 0) || ((A *m v) j' 0 > b j' 0)).
    * move/(active_inPn_vert Q_base) : j'_not_in_eqQ => [w0 w0_vtx Aj_w0_gt_bj].
      case: (w0 =P v) => [ w0_eq_v | /eqP w0_neq_v].
      - exists w'; first by rewrite in_fsetD1; apply/andP; split.
        by apply/orP; right; rewrite -w0_eq_v.
      - exists w0; first by rewrite in_fsetD1; apply/andP; split.
        by apply/orP; left.
    have v_in_Q : v \in Q by exact: vertex_inclusion.
    have w_in_Q : w \in Q by move/(fsubsetP (fsubD1set _ _)): w_vtx;
      exact: vertex_inclusion.
    have c_w_gt_alpha : '[c,w] > alpha.
    * apply: c_other_gt_alpha.
      apply: (fsubsetP (fsetSD _ _) _ w_vtx); exact: vertex_face_inclusion.
    move: (linear_ivt c_v_lt_alpha c_w_gt_alpha) => [x x_in_v_w c_x_eq_alpha].
    have x_in_Q : x \in Q.
    * by apply/(poly_subsetP (segm_subset _ _)): (osegm_subset x_in_v_w).
    apply/active_inPn; first exact: vf_fun_base; exists x; split.
    * apply/polyI_inP; split; by [ done | rewrite poly_hyperplane_inE; apply/eqP ].
    * rewrite mul_col_mx 2!col_mxEu.
      by rewrite (active_osegm Q_base _ _ _ x_in_v_w) // orbC.
Qed.


Fact vf_fun_face (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH -> vf_fun Q \in \face (vf_fun P).
Proof.
move => Q_face v_proper_Q.
move/(face_baseP P_has_base): (Q_face) => [Q_base eqP_sub_eq_Q _].
apply/(face_baseP (vf_fun_base P_has_base)); split.
- exact: vf_fun_base.
- rewrite 2?vf_fun_eq; try by done.
  + by apply: setUS; apply: imsetS.
  + exact: self_face.
  + apply: (poly_proper_subset v_proper_Q).
    apply/poly_subsetP; exact: face_subset.
  + exact: vf_fun_non_empty.
Qed.

Fact vf_fun_inj : {on (\face P), injective vf_fun}.
Proof.
move => Q Q'.

End VertexFigure.