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

Lemma vertex_face (F P : 'poly[R]_n) :
  F \in \face P -> (\vert F `<=` \vert P)%fset.
Proof.
move => F_face_P; apply/fsubsetP => v /vertex_setP v_face_F.
move/fsubsetP/(_ _ v_face_F): (face_of_face F_face_P).
by move/vertex_setP.
Qed.

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

Variable P : 'poly[R]_n.
Hypothesis P_compact : compact P.

Theorem conv_vert : P =i \conv (\vert(P)).
Proof.
move => x; apply/idP/idP.
- case: (boolP (non_empty P)) => [P_non_empty | /non_emptyPn -> //=].
  apply: contraLR => /convPn [c /separationP c_sep].
  have c_bounded : bounded c P by apply/compactP.
  pose F := face_of_obj c_bounded.
  have vert_F : (exists v, v \in \vert F).
  + admit.
  pose v0 := xchoose vert_F.
  have v0_vert_P : v0 \in \vert P.
  + have: v0 \in \vert F by exact: xchooseP.
    by apply/fsubsetP; apply: vertex_face; exact: face_of_obj_face.
  have v0_in_F : v0 \in F by apply: vertex_inclusion; exact: xchooseP.
  apply/negP => x_in_P.
  move: (face_of_objP c_bounded _ v0_in_F) => [_] /(_ _ x_in_P).
  apply/negP; rewrite -ltrNge; exact: c_sep.
- apply: poly_convex; exact: vertex_inclusion.
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
Hypothesis c_sep_v : '[c,v] < alpha /\ forall w, w \in \vert P -> w != v -> '[c,w] >= alpha.

Section Fun.

Variable F : 'poly[R]_n.
Hypothesis v_in_F : v \in F.
Hypothesis F_face_P : F \in \face P.

Let H := poly_hyperplane c alpha.
Let F' := polyI F H.
Let P' := polyI P H.

Fact F'_face_P' : F' \in \face P'.
Admitted.


End VertexFigure.