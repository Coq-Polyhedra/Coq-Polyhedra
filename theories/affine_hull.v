(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
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
rewrite mxE.
apply: eq_bigr => j _.
by rewrite !mxE. 
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
      exact: Hx.
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
    apply: (polyhedron_strictly_convex (j := i0)); split; try by done.
    + exact: lpositive.
    + exact: edotl_sum1.
    + exact: vcol_in_polyhedron.
  - by case: (cast_ord Hm i0).
Qed.

End RelintGen.

Section LinearSpan.

Let Aeq := (row_submx A eq_indices).
Let beq := (row_submx b eq_indices).
Let Veq := kermx Aeq^T.
Let x0 := relint_point.

Lemma Aeq_mul_eqb : forall x, x \in polyhedron A b -> Aeq *m x = beq.
Proof.
  move => x Hx.
  apply/colP => ?. rewrite -row_submx_mul !row_submx_mxE -vdot_row_col.
  apply/eq_indicesP; last by done.
  apply/enum_valP.
Qed.

(* The "small enough" lambda required for a proper decrement of the
   product l * (A v) in A (x0 + l v), for an index i. *)
Definition l_dec i (v: 'cV[R]_n) :=
  let dec := (b i 0) - ((A *m x0) i 0) in
  ((A *m v) i 0)^-1 * dec.

(* Auxiliary Lemma for ldec *)
Lemma ldec_positive_case i (v: 'cV[R]_n) : (A *m v) i 0 < 0 ->
  i \notin eq_indices ->  l_dec i v > 0.
Proof.
  move => Av_geq0 Hin. rewrite /l_dec nmulr_rgt0.
  - have: (A *m x0) i 0 > b i 0 by rewrite relint_point_in_relint //.
    by rewrite -subr_lt0.
  - by rewrite invr_lt0.
Qed.

(* The minimum among all l_dec *)
Definition ldec_tot (v: 'cV[R]_n) :=
  let J := [ seq j <- (enum 'I_m) | j \notin eq_indices & (A *m v) j 0 < 0 ] in
  (min_seq [seq l_dec j v | j <- J] 1).

Lemma ldec_tot_positive (v: 'cV[R]_n) : ldec_tot v > 0.
Proof.
  set S := [seq l_dec j v | j <- enum 'I_m &
    ((j \notin eq_indices) && ((A *m v) j 0 < 0))].
  rewrite /ldec_tot min_seq_positive; last by right; rewrite ltr01.
  apply/allP => elm. move/mapP => [j]; rewrite mem_filter.
  move/andP => [/andP [Hj Hneg] _]. rewrite inE => ->.
  exact: ldec_positive_case.
Qed.

(* Auxiliary lemma, required for Veq_as_polypoint *)
Lemma ldec_tot_suffices (v: 'cV[R]_n) (i: 'I_m) :
  (i \notin eq_indices) ->
  b_[ i] - (A *m x0) i 0 <= ldec_tot v * (A *m v) i 0.
Proof.
  set S := [seq l_dec j v | j <- enum 'I_m &
    ((j \notin eq_indices) && ((A *m v) j 0 < 0))].
  move => Hneq.
  case: (boolP ((A *m v) i 0 < 0)) => [AvNeg | AvPos].
  - rewrite -ler_ndivl_mulr; last by done.
    rewrite mulrC /ldec_tot.
    suff : ((A *m v) i 0)^-1 * (b_[ i] - (A *m x0) i 0) \in
      [seq l_dec j v | j <- enum 'I_m &
       (j \notin eq_indices) && ((A *m v) j 0 < 0)].
    + exact: min_seq_ler.
    + suff -> : ((A *m v) i 0)^-1 * (b_[ i] - (A *m x0) i 0) \in S by done.
      rewrite /S /l_dec. apply/mapP; exists i; last by done.
      by rewrite mem_filter; rewrite Hneq AvNeg mem_enum.
  - rewrite -lerNgt in AvPos.
    have Hpos: ldec_tot v * (A *m v) i 0 >= 0.
      rewrite pmulr_rge0.
      + exact: AvPos.
      + exact: ldec_tot_positive.
    apply: (@ler_trans _ 0); last by exact: Hpos.
    rewrite subr_le0.
    by move/forallP/(_ i): relint_point_in_polyhedron.
Qed.

Lemma Veq_as_polypoint j :
  (x0 + ldec_tot (row j Veq)^T *: (row j Veq)^T \in polyhedron A b).
Proof.
  have Hs i (v: 'cV_n) : row i (A *m v) 0 0 = (A *m v) i 0 by rewrite mxE.
  rewrite polyhedron_rowinE; apply/forallP => i.
  rewrite mulmxDr mxE addrC -ler_subl_addr -row_mul -scalemxAr.
  (* Bring it closer to the way defined in l_dec *)
  have -> : (ldec_tot (row j Veq)^T *: (row i A *m (row j Veq)^T)) 0 0 =
    ldec_tot (row j Veq)^T * ((A *m (row j Veq)^T) i 0)
    by rewrite mxE -Hs row_mul.
  rewrite Hs.
  case: (boolP (i \in eq_indices)) => [Hin | Hnotin].
  - move/eq_indicesP : (Hin) => HinP.
    suff -> : (A *m (row j Veq)^T) i 0 = 0.
    + suff -> : b_[i] - (A *m x0) i 0 = 0 by rewrite mulr0.
      apply/eqP. rewrite subr_eq0 -vdot_row_col; apply/eqP; symmetry.
      by rewrite HinP // relint_point_in_polyhedron //.
    + rewrite -Hs.
      have [q Hq]: exists (j: 'I_#|eq_indices|), (row i A) = row j Aeq.
        by exists (enum_rank_in Hin i); rewrite row_submx_row enum_rankK_in.
      rewrite row_mul Hq -row_mul trmx_rmul -tr_col.
      (* Prove that Veq_j *m Aeq^T = 0, as Veq is the kermx *)
      suff -> : row j Veq *m Aeq^T = 0 by rewrite col0 trmx0 !mxE.
      by apply/sub_kermxP; rewrite -/Veq row_sub.
  - exact: ldec_tot_suffices.
Qed.


Variables (p : nat) (Vm : 'M[R]_(p, n)).

(* A Lemma relating the column span of Veq and any matrix Vm which
   is a generator for (x - x0), where x0 is the point in the relative
   interior of the polyhedron *)
Lemma kermx_interior_spanP : reflect
    (forall x, x \in polyhedron A b -> ((x - x0)^T <= Vm)%MS)
    ((Veq <= Vm)%MS).
Proof.
  apply: (iffP idP).
  (* Direction <- *)
  - move => HVx x Hx.
    (* Rely on transitivity *)
    suff Hxveq: ((x - x0)^T <= Veq)%MS.
    + apply: (submx_trans Hxveq HVx).
    + apply/sub_kermxP.
      suff -> : (x - x0)^T *m (Aeq^T) = (Aeq *m (x - x0))^T.
      * rewrite mulmxBr; rewrite !Aeq_mul_eqb.
        - by rewrite addrN trmx0.
        - exact: relint_point_in_polyhedron.
        - exact: Hx.
      * by rewrite trmx_mul.
  (* Direction -> *)
  - move => Hx. apply/row_subP => i.
    set v0 := (row i Veq)^T.
    set v := ldec_tot v0 *: v0.
    set x := x0 + v.
    have Hin : x \in polyhedron A b by exact: Veq_as_polypoint.
    have Heq : (x - x0) = v by rewrite /x addrC addrA addNr add0r.
    have: (v^T <= Vm)%MS by rewrite -Heq; exact: Hx.
    + (* Use the fact that if (l *: v <= V)%MS, (v <= V)%MS for l <> 0 *)
      rewrite trmx_mul_scalar eqmx_scale.
      * by rewrite trmxK.
      * by apply: lt0r_neq0; rewrite ldec_tot_positive.
Qed.

Lemma kermx_spanP : reflect
  (forall x y, x \in polyhedron A b ->
   y \in polyhedron A b -> ((x - y)^T <= Vm)%MS)
  ((Veq <= Vm)%MS).
Proof.
  apply: (iffP idP).
  (* Direction <- *)
  - move => HVx x y Hx Hy.
    have H1 : (x - y) = (x - x0) + (x0 - y).
    + rewrite [_ + (x0 - y)]addrA. rewrite [_ -_ + _]addrC [(x - x0)]addrC addrA.
      by rewrite addrN add0r.
    rewrite H1 trmx_add addmx_sub //; first by apply/kermx_interior_spanP.
    have H2 : (x0 - y)^T = (-1) *: (y - x0)^T.
    + apply/matrixP => i j; by rewrite !mxE mulN1r opprB.
      rewrite H2. apply: scalemx_sub; apply/kermx_interior_spanP.
      * exact: HVx.
      * exact: Hy.
  (* Direction -> *)
  - move => Hyx. apply/kermx_interior_spanP => ? Hx.
    move: Hx (relint_point_in_polyhedron); exact: Hyx.
Qed.

End LinearSpan.

End AffineHull.
