(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm.
Require Import extra_misc inner_product vector_order extra_matrix row_submx hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''<' P >" (at level 0, format "''<'  P  >").
Reserved Notation "P ==e Q" (at level 70, no associativity, format "'[hv' P '/ '  ==e  Q ']'").
Reserved Notation "P =e Q" (at level 70, format "'[hv ' P '/ '  =e  Q ']'", no associativity).

Delimit Scope polyhedron_scope with poly.
Local Open Scope polyhedron_scope.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R : realFieldType.
Variable n : nat.

Notation hpolyhedron := (hpolyhedron R n).
Notation hpoly_rel := (hpolyhedron_eq_equiv_rel R n).

Definition polyhedron := {eq_quot hpoly_rel}%qT.
Canonical polyhedron_eqType := [eqType of polyhedron].
Canonical polyhedron_choiceType := [choiceType of polyhedron].
Canonical polyhedron_quotType := [quotType of polyhedron].
Canonical polyhedron_eqQuotType := [eqQuotType hpoly_rel of polyhedron].

Notation "''|' P |" := (\pi_(polyhedron)%qT P) : polyhedron_scope.
Notation "P ==e Q" := (P == Q %[mod polyhedron])%qT : polyhedron_scope.
Notation "P =e Q" := (P = Q %[mod polyhedron])%qT : polyhedron_scope.

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

Section Def.

CoInductive hpoly_spec (P : polyhedron) : hpolyhedron -> Type :=
  HpolySpec Q of (P = '| Q |) : hpoly_spec P Q.

Lemma hpolyP (P : polyhedron) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite reprK.
Qed.

Lemma hpoly_eqP (P Q : hpolyhedron) :
  (P =i Q) <-> (P =e Q).
Proof.
apply: (rwP2 (b := (hpolyhedron_eq P Q))).
- exact: hpolyhedron_eqP.
- exact: eqmodP.
Qed.

Definition mem_polyhedron : polyhedron -> pred_class :=
  lift_fun1 polyhedron id.

Lemma pi_mem x : {mono \pi : P / x \in P >-> x \in mem_polyhedron P}%qT.
Proof.
unlock mem_polyhedron => P /=.
case: (hpolyP '| P |) => Q.
by move/hpoly_eqP.
Qed.

Canonical pi_mem_morph x := Eval hnf in PiMono1 (pi_mem x).
Canonical polyhedron_predType :=
  Eval hnf in @mkPredType 'cV[R]_n polyhedron mem_polyhedron.
Coercion mem_polyhedron : polyhedron >-> pred_class.

End Def.


Section PolyhedronOfSubset.

Variable P : hpolyhedron.
Variable I : {set 'I_(m P)}.

Definition A_of_subset I := col_mx (A P) (- (row_submx (A P) I)).
Definition b_of_subset I := col_mx (b P) (- (row_submx (b P) I)).

Lemma hpolyhedron_of_subset_inE x :
  x \in HPolyhedron (A_of_subset I) (b_of_subset I) = (x \in P) && [forall i in I, ((A P) *m x) i 0 == (b P) i 0].
Proof.
rewrite inE mul_col_mx col_mx_lev mulNmx -row_submx_mul lev_opp2.
apply/andP/andP.
- move => [x_in_P ineqI]; split; try by done.
  suff /row_submx_colP H: row_submx (A P *m x) I = row_submx (b P) I.
  + apply/forall_inP => i i_in_I.
    move/(_ _ i_in_I): H ->; exact: eq_refl.
  + apply: lev_antisym; apply/andP; split; try by done.
    exact: row_submx_lev.
- move => [x_in_P /forall_inP eqI]; split; try by done.
  apply/row_submx_levP => i i_in_I.
  by move/(_ _ i_in_I)/eqP: eqI ->.
Qed.

Definition hpolyhedron_of_subset := HPolyhedronCustom hpolyhedron_of_subset_inE.

End PolyhedronOfSubset.
