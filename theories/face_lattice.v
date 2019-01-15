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
Admitted.

Lemma vertex_inclusion P :
  {subset \vert P <= P }.
Admitted.

Lemma vertex_face (F P : 'poly[R]_n) :
  F \in \face P -> (\vert F `<=` \vert P)%fset.
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
- admit. (* follow from convexity *)
Admitted.


End Minkowski.