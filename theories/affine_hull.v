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

Section RelintGen.

(* Candidates for points in the relative interior; see affine_hull.v *)
Definition relint_candidate c := match simplex A b c with
  | Simplex_optimal_point (x, _) => x
  | Simplex_unbounded (x, u) => x + u
  | _ => 0
  end.

(* The face of a bounded polyhedron, as computed by simplex,
   must belong to the polyhedron itself *)
Lemma face_eq_inpoly i : bounded A b (-A_[i]) ->
  opt_point A b (-A_[i]) \in polyhedron A b.
Proof.
  rewrite /opt_point /bounded.
  case: simplexP => //.
  by move => [x d] /= [? _ _].
Qed.

(* For a bounded polyhedron, if i is not in eq_indices, then the optimal
   point satisfies the corresponding inequality strictly. *)
Lemma face_eq_strict_bounded i :
  (bounded A b (-A_[i])) -> (i \notin eq_indices) ->
  '[ A_[i], (opt_point A b (-A_[i]))] > b_[i].
Proof.
  move => Hbounded /eq_indicesPn_unbounded Hi.
  case: Hi.
  - move: Hbounded. rewrite bounded_is_not_unbounded //. by move/negP.
  - move => [x [Hx1 ?]].
    set xopt := opt_point A b (-A_[i]).
    suff: '[A_[i], x] <= '[A_[i], xopt] by exact: ltr_le_trans.
    rewrite -ler_opp2 -2!vdotNl.
    by move/boundedP: Hbounded => [_ /(_ _ Hx1)].
Qed.

Lemma feasible_dir_in_polyhedron x u :
  (x \in polyhedron A b) -> (feasible_dir A u) -> (x + u) \in polyhedron A b.
Proof.
  rewrite !inE mulmxDr => Hx Hu.
  by move/andP/lev_add: (conj Hx Hu); rewrite addr0. (* TODO: modify lev_add *)
Qed.

(* A function returning the relint candidate for each inequality
   of the polyhedron P(A, b) - see relint_point_candidate in simplex.v *)
Function relint i := relint_candidate (-A_[i]).

Lemma relint_strict_bounded i :
  (bounded A b (-A_[i])) -> (i \notin eq_indices) ->
  '[ A_[i], (relint i)] > b_[i].
Proof.
  move => Hbounded /eq_indicesPn [x [Hx1 Hx2]].
    suff : '[(-A_[i]), (relint i)] = opt_value A b (-A_[i]).
    + move/(congr1 (-%R)). rewrite !vdotNl opprK => ->. rewrite ltr_oppr.
      move: Hx2. rewrite -ltr_opp2 -vdotNl.
      move/boundedP: Hbounded => [_ /(_ _ Hx1)].
      exact: ler_lt_trans.
    + move: Hbounded.
      rewrite /bounded /opt_value /opt_point /relint /relint_candidate.
      case: simplexP => //.
Qed.

(*RK: in the next lemma, it does not seem to be necessary to asumme (i \notin eq_indices),
so why should we do it?*)
Lemma relint_strict_unbounded i :
  (unbounded A b (-A_[i])) -> (i \notin eq_indices) ->
  '[ A_[i], (relint i)] > b_[i].
Proof.
  move => Hnb _. move: Hnb.
  rewrite /unbounded. rewrite /relint /relint_candidate.
  case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP | | ] //.
  move => [x u] /= [Hx Hd].
  rewrite vdotNl oppr_lt0 => Hxd _.
  move: Hx. rewrite polyhedron_rowinE => /forallP /(_ i).
  have -> : (row i A *m x) 0 0 = '[A_[i], x].
    - by rewrite vdot_row_col -row_mul mxE.
  move => Hx.
  by rewrite -[b_[i]]addr0 vdotDr ler_lt_add.
Qed.

Lemma relintP i : reflect
  ('[A_[i], (relint i)] > b_[i]) (i \notin eq_indices).
Proof.
  apply: (iffP idP); last first.
  (* Case 1: Have the inequality, need to prove i \notin eq_indices *)
  - move => Arel_gt_b. apply/eq_indicesPn.
    exists (relint i); split; last by done.
    rewrite /relint /relint_candidate.
    case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP |
        [x d] /= [Hx Hd] _ | [x u] /= [Hx Hu Hux] ] //.
    (* unbounded_relint point *)
    + move : Hx. rewrite !inE mulmxDr => Hx.
      by rewrite -[b]addr0; apply: lev_add; rewrite Hx Hd.
  (* Case 2: Have i \notin eq_indices, need to prove the inequality *)
  - move => Hi.
    case: (boolP (unbounded A b (-A_[i]))) => [?|].
    - exact: relint_strict_unbounded.
    - rewrite -bounded_is_not_unbounded // => Hb.
      exact: relint_strict_bounded.
Qed.

(* A simple lemma stating that every candidate returned for
   the relative interior cannot be outside the polyhedron *)
Lemma relint_candidate_in_polyhedron i : (relint i) \in polyhedron A b.
Proof.
  rewrite /relint /relint_candidate inE.
  case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP |
        [x d] /= [Hx Hd] _ | [_ _] /= [_ _ _] ] //.
  move: Hx. rewrite inE mulmxDr => Hx.
  by rewrite -[b]addr0; apply: lev_add; rewrite Hx Hd.
Qed.

(* The matrix of relint candidates *)
Let V := (\matrix_(j < n, i < m) (relint i) j 0) : 'M[R]_(n, m).

Lemma relint_in_vcol : forall i, col i V = relint i.
Proof.
  move => ?. by apply/colP => ?; rewrite !mxE.
Qed.

Lemma vcol_in_polyhedron : forall i, col i V \in polyhedron A b.
Proof.
  move => ?. rewrite relint_in_vcol.
  exact: relint_candidate_in_polyhedron.
Qed.

(* A constant vector *)
Let e := (const_mx 1) : 'cV[R]_m.

(* The scaling matrix E for the computation of the point in
   the strict convex hull. *)
Let l := (const_mx (m %:R)^-1) : 'cV[R]_m.

Lemma edotl_sum1 : (m > 0)%N -> '[e, l] = 1.
Proof.
  move => Hmpos.
  suff -> : 1 = \big[+%R/0]_(i < m) l i 0.
    apply: eq_bigr => i _; by rewrite mxE mul1r.
  have Hconst: l _ 0 = m%:R^-1 by move => ?; rewrite mxE.
  have -> : \big[+%R/0]_(i < m) l i 0 = \big[+%R/0]_(i < m) (m%:R^-1).
    by apply: eq_bigr => ? _; rewrite Hconst.
  rewrite sumr_const cardT size_enum_ord.
  rewrite -[RHS]mulr_natr mulVf; first by done.
  apply: lt0r_neq0; by rewrite ltr0n.
Qed.

(* The following lemma is obvious, but some manipulation is needed
   because l involves the inverse of a nat. *)
Lemma lpositive : l >=m 0.
Proof.
  rewrite /l /lev. apply/forallP => ?.
  by rewrite !mxE invr_ge0 ler0n.
Qed.

(* A point in the relative interior -- if m = 0, this can be any point,
   since the affine hull in that case is the whole space *)
Definition relint_point := if (m == 0)%N then 0 else (V *m l).

Lemma relint_point_in_polyhedron : relint_point \in polyhedron A b.
Proof.
rewrite /relint_point.
case: ifPn => [/eqP Hm | Hm]; last first.
- rewrite -lt0n in Hm.
  apply: polyhedron_is_convex; split.
  + exact: lpositive.
  + exact: edotl_sum1.
  + exact: vcol_in_polyhedron.
- apply/forallP => i.
  by case: (cast_ord Hm i).
Qed.

Lemma relint_point_in_relint :
  forall i, i \notin eq_indices -> (A *m relint_point) i 0 > b i 0.
Proof.
  move => i0 Hineq. rewrite /relint_point.
  case: ifPn => [/eqP Hm | Hm]; last first.
  - rewrite -lt0n in Hm.
    have Hli: l i0 0 > 0.
    + rewrite mxE. by rewrite invr_gt0 ltr0n.
    have Hrelint : (A *m (col i0 V)) i0 0 > b i0 0.
    + rewrite relint_in_vcol -vdot_row_col. by move/relintP: Hineq.
    apply: polyhedron_strictly_convex; split.
    + exact: lpositive.
    + exact: edotl_sum1.
    + exact: Hrelint.
    + exact: Hli.
    + exact: vcol_in_polyhedron.
  - by case: (cast_ord Hm i0).
Qed.

End RelintGen.

End AffineHull.
