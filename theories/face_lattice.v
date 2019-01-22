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

Lemma conv_vert1 (v : 'cV[R]_n) : [poly v] =i \conv ([fset v]%fset).
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
Hypothesis c_other_gt_alpha : forall w, w \in \vert P -> w != v -> '[c,w] > alpha.

Section Fun.

Let H := poly_hyperplane c alpha.

Definition vf_fun (Q : 'poly[R]_n) := polyI Q H.

Fact vf_fun_base (Q : 'poly[R]_n) (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) :
  let A' := col_mx A c^T in
  let b' := col_mx b (alpha%:M) in
  [Q has \base 'P(A,b)] -> [vf_fun Q has \base 'P(A',b')].
Admitted.

Fact vf_fun_eq_mono (Q : 'poly[R]_n) (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) :
  let A' := col_mx A c^T in
  let b' := col_mx b (alpha%:M) in
  [Q has \base 'P(A,b)] -> (lshift 1) @: {eq Q on 'P(A,b)} \subset {eq (vf_fun Q) on 'P(A',b')}.
Admitted.

Fact vf_fun_eq_hyper (Q : 'poly[R]_n) (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) :
  let A' := col_mx A c^T in
  let b' := col_mx b (alpha%:M) in
  [Q has \base 'P(A,b)] -> (rshift m ord0) \in {eq (vf_fun Q) on 'P(A',b')}.
Admitted.

Fact vf_fun_non_empty (Q : 'poly[R]_n) :
  Q \in \face P -> is_properly_included_in [poly v] Q -> non_empty (vf_fun Q).
Proof.
move => Q_face_P /andP [v_in_Q Q_not_sub_v].
rewrite poly_point_incl in v_in_Q.
have v_vtx_Q : v \in \vert Q
  by rewrite (vertex_set_face Q_face_P) in_fsetE /=; apply/andP; split.
have /fsubsetPn [w w_vtx_Q w_neq_v]: ~~ (\vert Q `<=` [fset v])%fset.
- move: Q_not_sub_v; apply: contraNN; rewrite fsubset1 => /orP.
  case; last by move/eqP => vertQ_eq_fset0; rewrite vertQ_eq_fset0 in_fsetE in v_vtx_Q.
  move/eqP => vertQ_eq_v; move: (conv_vert (compact_face P_compact Q_face_P)).
  rewrite vertQ_eq_v => Q_eq_v.
  apply/is_included_inP; move => x; rewrite Q_eq_v => /convP1 ->.
  exact: poly_point_self_in.
rewrite in_fset1 in w_neq_v.
have c_w_gt_alpha : '[c,w] > alpha
  by apply: c_other_gt_alpha; move/fsubsetP/(_ _ w_vtx_Q): (vertex_face_inclusion Q_face_P).
have [x x_in_v_w c_x_eq_alpha] : exists2 x, x \in \conv ([fset v; w])%fset & '[c,x] = alpha.
admit.
have x_in_Q : x \in Q.
- rewrite conv_vert; last exact: (compact_face P_compact).
  by move: x_in_v_w; apply: conv_mono; apply/fsubsetP => y; move/fset2P; case => ->.
apply/non_emptyP; exists x; rewrite in_polyI poly_hyperplane_inE.
by apply/andP; split; last apply/eqP.
Admitted.

Fact vf_fun_face (Q : 'poly[R]_n) :
  Q \in \face P -> vf_fun Q \in \face (vf_fun P).
Proof.



End VertexFigure.