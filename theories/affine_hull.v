(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com    *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import
  all_ssreflect ssralg ssrnum zmodp matrix mxalgebra bigop finset.
Require Import
  polyhedron simplex extra_misc extra_matrix inner_product vector_order row_submx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.
Import Decidable.

Section AffineHull.

Variable R : realFieldType.
Variables m n: nat.

(* P(A, b) definition of polyhedra *)
Variable A: 'M[R]_(m, n).
Variable b: 'cV[R]_m.

Hypothesis Hfeas: feasible A b.

Implicit Types (x : 'cV[R]_n) (i: 'I_m) (j: 'I_n).

Notation "A_[ i ]" := (row i A)^T. (* at this stage, we should stick with the form (A *m x) i 0 *)
Notation "b_[ i ]" := (b i 0).
Notation "A_[ i , j ]" := (A i j).

(* Lemmas relating the two notations followed in this module *)

Lemma mx_dbrack_eq_rowmx_brack i j : A_[i, j] = A_[i] j 0.
Proof. by rewrite !mxE. Qed.

Lemma mx_dbrack_eq_colmx_brack i j : A_[i, j] = A_[i]^T 0 j.
Proof. by rewrite !mxE. Qed.


Section EqIndices.

(*
  eq_indices: The indices of the set

  { i | A_i *m x == b_i }

  where A_i is the i'th row of the matrix A and b_i is the i'th element
  of the vector b.
*)
Definition eq_indices :=
  [set i: 'I_m |
   (bounded A b (-A_[i])) && ((opt_value A b (-A_[i])) == (-b_[i]))].

Lemma eq_indices_in_Im : (#|eq_indices| <= m)%N.
Proof.
  set P := fun i => bounded A b (-A_[i]) && ((opt_value A b (-A_[i])) == (-b_[i])).
  by apply: (card_sub_ord P).
Qed.

(* The definition of affine hull given in Schrijver's book *)
Definition affine_hull :=
  let (A_eq, b_eq) := (row_submx A eq_indices, row_submx b eq_indices) in
  [pred x | A_eq *m x == b_eq].

(* Inner product of matrix row with vector is the same as
   multiplication of the whole matrix and isolating the row
   after *)
Lemma vdot_row_col x i : '[A_[i], x] = ((A *m x) i 0).
Proof.
  rewrite !mxE /=.
  apply: eq_bigr => j _.
  by rewrite mx_dbrack_eq_rowmx_brack.
Qed.

(* If an inequality is satisfied with equality for all x, its index
   must be among eq_indices *)
Lemma eq_indicesP i :
  reflect (forall x, x \in polyhedron A b -> '[A_[i], x] = b_[i]) (i \in eq_indices).
Proof.
  apply: (iffP idP).
  (* Forward direction *)
  - rewrite inE => /andP [/boundedP [_ Hb] Hopt].
    move => x Hx.
    (* More verbosely: move: (Hb _ Hx). *)
    move/(_ _ Hx) : Hb.
    (* => -> : Rewrite immediately in LHS after, does not put it back in the top *)
    (* => <- : Rewrite immediately in RHS after, does not put it back in the top *)
    move/eqP: Hopt => ->.
    rewrite vdotNl ler_opp2 => Ax_leq_b. move: Hx. rewrite inE.
    move => b_leq_Ax. apply /eqP. rewrite eqr_le Ax_leq_b {Ax_leq_b} /=.
    move: b_leq_Ax. rewrite /lev. rewrite vdot_row_col => pp.
    by move/forallP: pp.
  (* Reverse direction *)
  - rewrite inE /andP => Hx.
    (* Name the fact: bounded A b (-A_[i]), as we will need it later. *)
    have Hb : bounded A b (-A_[i]).
      + apply /boundedP_lower_bound; rewrite //; exists (-b_[ i]).
        move => x x_in_poly; rewrite vdotNl ler_opp2.
        move/(_ _ x_in_poly)/eqP: Hx. rewrite eqr_le.
        move/andP => [Ax_leq_b] _. by apply: Ax_leq_b.
    + apply/andP; split; first exact: Hb.
      move/boundedP: Hb => [[x [Ha Hopt]] _].
      rewrite -Hopt vdotNl eqr_opp; apply/eqP.
      by apply: Hx.
Qed.

(* Lemma relating an i not belonging to the set of equalities
   with the existence of a point strictly satisfying the inequality. *)
Lemma neq_indices_strict_inequality i : (i \notin eq_indices) ->
  (exists x, (x \in polyhedron A b) /\ ('[A_[i], x] > b_[i])).
Proof.
  move/feasibleP: Hfeas => Px.
  rewrite inE => /nandP [nBound | nOpt].
  - move: nBound. rewrite -unbounded_is_not_bounded; last by done.
    (* move => /negPn /unboundedP /(_ (-b_[i])) can be written as
       move => /negPn /unboundedP => H; specialize (H (-b_[i])) *)
    move => /unboundedP /(_ (-b_[i])) [x [H1 H2]]. exists x.
    split; first by done.
    by rewrite vdotNl ltr_opp2 in H2.
  - case: (boolP (bounded A b (-A_[i]))).
    + (* Case 1: bounded *)
      move/boundedP => [[x [Ha Hopt]] _]. exists x; split; first by done.
      (* below can also be written as ... => /forallP H; specialize (H i) *)
      move: Ha; rewrite polyhedron_rowinE => /forallP /(_ i).
      rewrite -row_mul mxE -vdot_row_col ltr_def => ->.
      move: nOpt. rewrite -Hopt vdotNl. rewrite neqr_lt => /orP.
      by case; rewrite ltr_opp2 neqr_lt => ->; rewrite ?orbT.
    + (* Case 2: unbounded *)
      rewrite -unbounded_is_not_bounded; last by apply: Hfeas.
      (* use -b_[i] as K in forall K ... *)
      move => /unboundedP /(_ (-b_[i])) [x [Ha H]]; exists x.
      by move: H; rewrite Ha vdotNl ltr_opp2.
Qed.

(* Negation of the reflection view eq_indicesP *)
Lemma eq_indicesPn i : reflect
  (exists x, (x \in polyhedron A b) /\ ('[A_[i], x] > b_[i])) (i \notin eq_indices).
Proof.
apply: (iffP idP).
- exact: neq_indices_strict_inequality.
- move => [x [Hp Hx]].
  apply/eq_indicesP.
    (* contradiction *)
  move/(_ x Hp) => Heq.
  by rewrite Heq ltrr in Hx.
Qed.

(* Not in eq_indices means either unbounded or existence of x that
   satisfies inequality strictly. *)
Lemma eq_indicesPn_unbounded i : reflect
  ((unbounded A b (-A_[i])) \/
   (exists x, (x \in polyhedron A b) /\ ('[A_[i], x] > b_[i])))
  (i \notin eq_indices).
Proof.
  apply: (iffP idP).
  - move => /eq_indicesPn Hi. by tauto.
  - case => [Hnb | Hexist].
    + rewrite inE. apply/nandP. rewrite bounded_is_not_unbounded.
      apply/orP. rewrite Hnb //=. by apply: Hfeas.
    + by apply/eq_indicesPn.
Qed.

End EqIndices.

End AffineHull.
