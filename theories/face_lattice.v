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
Require Import simplex extra_misc inner_product vector_order extra_matrix row_submx hpolyhedron polyhedron affine_hull convex_hull.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\vert P " (at level 50, format "\vert  P").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(*Section UpperSet.

Variable R : realFieldType.
Variable n : nat.

Implicit Types P F : 'poly[R]_n.

Definition ppus P (F: \face P) := (* proper principal upper set *)
  [fsetval F' : (\face P) | (val F < val F')%PH]%fset.

Variable P F : 'poly[R]_n.
Hypothesis H : F \in \face P.
Check val [`H]%fset.

Check ppus [`H]%fset.
 *)

Section VertexSet.

Variable R : realFieldType.
Variable n : nat.

Implicit Types P F : 'poly[R]_n.
Implicit Types v w x : 'cV[R]_n.

Definition vertex_set P :=
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

Lemma vertex_face_inclusion F P :
  F \in \face P -> (\vert F `<=` \vert P)%fset.
Proof.
move => F_face_P; apply/fsubsetP => v /vertex_setP v_face_F.
move/fsubsetP/(_ _ v_face_F): (face_of_face F_face_P).
by move/vertex_setP.
Qed.

Lemma vertex_set_face F P :
  F \in \face P -> \vert F = [fset v in \vert P | v \in F]%fset.
Proof.
Admitted.

Lemma vertex_objP P v :
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

Lemma vertex_set_sep P v :
  v \in \vert P -> exists c, [forall (w : (\vert P) | val w != v), '[c, val w] > '[c, v]].
Proof.
Admitted.

Definition obj_of_vertex P v (v_vert : v \in \vert P) := xchoose (vertex_set_sep v_vert).

Lemma obj_of_vertexP P v (v_vert : v \in \vert P) :
  let c := obj_of_vertex v_vert in
    forall w, w \in \vert P -> w != v -> '[c, w] > '[c, v].
Proof.
Admitted.
Lemma vertex1 v : \vert [poly v] = [fset v]%fset.
Proof.
Admitted.


Lemma vertex2 v w : \vert [poly v; w] = [fset v; w]%fset.
Proof.
Admitted.


Lemma vertex_pointedP (P : 'poly[R]_n) :
  reflect (exists v, v \in \vert P) ((non_empty P) && (pointed P)). (* RK *)
Proof.
apply: (iffP idP) => [/feasible_basic_point_pointedP [v v_is_basic_point] | [v /vertex_setP v_is_vertex]].
- exists v.
  rewrite feasible_basic_point_vertex hpolyK in v_is_basic_point.
  by apply/vertex_setP.
- apply/feasible_basic_point_pointedP.
  exists v.
  by rewrite feasible_basic_point_vertex hpolyK.
Qed.

(*Lemma vertex_feasible_point (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  \vert '['P(A,b)] = [fset (Simplex.point_of_basis b bas) | bas in Simplex.lex_feasible_basis A b]%fset.*)


Notation "\vert P" := (vertex_set P).

Section Minkowski.

Theorem conv_vert P : compact P -> P =i \conv (\vert(P)).
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
- apply/(convexP (poly_convex (P := P))); exact: vertex_inclusion.
Admitted.

Lemma active_inPn_vert P (m: nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) i :
  [P has \base 'P(A,b)] ->
  reflect (exists2 x, x \in \vert P & (A *m x) i 0 > b i 0) (i \notin { eq(P) on 'P(A,b) }).
Admitted.

Lemma vertex_set_homo P F F' :
  compact P -> F \in \face P -> F' \in \face P ->
    ((F <= F')%PH = (\vert F `<=` \vert F')%fset)
    * ((F < F')%PH = (\vert F `<` \vert F')%fset).
Proof.
move => P_compact; move: F F'.
have fst_part: forall F F', F \in \face P -> F' \in \face P ->
                 ((F <= F')%PH = (\vert F `<=` \vert F')%fset).
- move => F F' F_face F'_face; apply/idP/idP.
  + rewrite (vertex_set_face F_face) (vertex_set_face F'_face).
    move/poly_subsetP => F_sub_F'; apply/fsubsetP => v.
    rewrite in_fsetE inE => /andP [v_vtx_P /F_sub_F' v_in_F'].
    rewrite in_fsetE inE; by apply/andP; split.
  + move => F_vtx_sub_F'_vtx.
    apply/poly_subsetP => x.
    do 2![rewrite conv_vert; last exact: (compact_face P_compact)].
    exact: conv_mono.
- move => F F' F_face F'_face; split; first exact: fst_part.
  by rewrite /poly_proper 2?fst_part.
Qed.

End Minkowski.

End VertexSet.


Notation "\vert P" := (vertex_set P).
Arguments active_inPn_vert [R n P m A b i].

Section VertexFigure.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'poly[R]_n.
Hypothesis P_non_empty : non_empty P.
Hypothesis P_compact : compact P.

Variable v : 'cV[R]_n.
Hypothesis v_vert : v \in \vert P.
Hypothesis v_proper_P : ([poly v] < P)%PH.
Variable c : 'cV[R]_n.
Variable alpha : R.
Hypothesis c_v_lt_alpha : '[c,v] < alpha.
Hypothesis c_other_gt_alpha : forall w, w \in ((\vert P) `\ v)%fset -> '[c,w] > alpha.

Section Fun.

Let H := poly_hyperplane c alpha.
Let H_base := 'P(c^T, alpha%:M).
Fact H_has_base : [H has \base H_base].
  by exact: poly_hyperplane_base.

Definition vf_fun (Q : 'poly[R]_n) := (Q && H)%PH.

Fact vf_fun_base (Q : 'poly[R]_n) (base: 'hpoly[R]_n) :
  [Q has \base base] -> [vf_fun Q has \base (hpolyI base H_base)].
Proof.
move => Q_base; apply: polyI_concat_base; by [done | exact: poly_hyperplane_base].
Qed.

Fact vf_fun_non_empty (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH = non_empty (vf_fun Q).
Proof.
move => Q_face.
rewrite (vertex_set_homo P_compact) // ?vertex1; last exact: vertex_setP.
apply/idP/idP.
- move => /andP [v_vtx /fsubsetPn [w w_vtx w_neq_v]].
  rewrite fsub1set in v_vtx.
  rewrite in_fset1 in w_neq_v.
  have c_w_gt_alpha : '[c,w] > alpha.
  + apply: c_other_gt_alpha; rewrite in_fsetD1; apply/andP; split; first by done.
    by apply/(fsubsetP (vertex_face_inclusion Q_face)).
  move: (linear_ivt c_v_lt_alpha c_w_gt_alpha) => [x /osegm_subset x_in_v_w c_x_eq_alpha].
  have x_in_Q : x \in Q.
  + apply/(poly_subsetP (segm_subset _ _))/x_in_v_w; exact: vertex_inclusion.
  apply/non_emptyP; exists x; rewrite polyI_inE poly_hyperplane_inE.
  by apply/andP; split; last apply/eqP.
- move => /non_emptyP [x /polyI_inP [x_in_Q x_in_H]].
  rewrite conv_vert in x_in_Q; last exact: (compact_face P_compact).
  rewrite poly_hyperplane_inE in x_in_H.
  apply/andP; split; last first.
  + rewrite fsubset1. rewrite negb_or; apply/andP; split.
    * move: x_in_H; apply: contraTN; move/eqP => vtx_Q_eq_v.
      rewrite {}vtx_Q_eq_v in x_in_Q.
      move/convP1: x_in_Q ->; move: c_v_lt_alpha.
      by rewrite ltr_neqAle => /andP [].
    * move: x_in_Q; apply: contraTN.
      by move/eqP ->; rewrite convP0.
  + rewrite fsub1set; move: x_in_H; apply/contraTT => v_not_vtx.
    suff: '[c,x] > alpha by rewrite ltr_neqAle eq_sym => /andP [].
    move: x_in_Q; apply/(convexP (halfspace_gt_convex (c := c) (d := alpha))).
    move => w w_vtx_Q; rewrite inE; apply: c_other_gt_alpha.
    rewrite in_fsetD1; apply/andP; split; first by move/memPn/(_ _ w_vtx_Q): v_not_vtx.
    by apply/(fsubsetP (vertex_face_inclusion Q_face)).
Qed.

Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Let base := 'P(A,b).
Hypothesis P_has_base : [P has \base base].

Definition vf_eq (I : {set 'I_m}) := (rshift m ord0) |: ((lshift 1) @: I).

Lemma vf_eq_inj : injective vf_eq.
Proof.
move => I I'.
pose ord_m := rshift m ord0 : 'I_(m+1).
move/(congr1 (fun S => S :\ ord_m)); rewrite 2?setU1K;
  try by apply/negP; move/imsetP => [j _];
         apply/eqP; rewrite eq_sym; apply: lrshift_distinct.
by move/(imset_inj (@lshift_inj m 1)).
Qed.

Fact vf_fun_eq (Q : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH ->
    {eq (vf_fun Q) on (hpolyI base H_base)} = vf_eq {eq Q on 'P(A,b) } .
Proof.
move => Q_face v_proper_Q.
move/(face_has_base P_has_base): (Q_face) => Q_base.
apply/setP/subset_eqP/andP; split; last first.
- rewrite /vf_eq setUC.
  suff ->: [set rshift m ord0] = (@rshift m 1) @: {eq H on H_base} by exact: polyI_eq_concat_base.  by rewrite poly_hyperplane_eq imset_set1.
- apply/subsetP => j; apply: contraTT.
  case: (splitP' j); last first.
  + by move => j' ->; move: (ord1_eq0 j') ->; rewrite setU11.
  + move => j' ->.
    rewrite in_setU1 negb_or lrshift_distinct andTb.
    move => j'_not_in_lset.
    have j'_not_in_eqQ : j' \notin {eq Q on 'P(A,b)}.
      by move: j'_not_in_lset; apply: contraNN => [j'_in_eqQ]; apply/imsetP; exists j'.
    rewrite {j j'_not_in_lset}.
    move: v_proper_Q; rewrite (vertex_set_homo P_compact) // ?vertex1; last exact: vertex_setP.
    move => /andP [v_vtx /fsubsetPn [w' w'_vtx w'_neq_v]].
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
  + by rewrite -vf_fun_non_empty.
Qed.

Fact vf_fun_inj (Q Q' : 'poly[R]_n) :
  Q \in \face P -> ([poly v] < Q)%PH ->
        Q' \in \face P -> ([poly v] < Q')%PH -> vf_fun Q = vf_fun Q' -> Q = Q'.
Proof.
move => Q_face v_proper_Q Q'_face v_proper_Q' vf_Q_eq_vf_Q'.
move/(face_has_base P_has_base): (Q_face) => Q_base.
move/(face_has_base P_has_base): (Q'_face) => Q'_base.
apply/(eq_on_base_inj Q_base Q'_base).
apply: vf_eq_inj; do 2![rewrite -(vf_fun_eq _ _) //]; by rewrite vf_Q_eq_vf_Q'.
Qed.

Fact vf_fun_onto (Q : 'poly[R]_n) :
  Q \in \face (vf_fun P) -> exists Q', [/\ Q' \in \face P, ([poly v] < Q')%PH & vf_fun Q' = Q].
Proof.
move: (vf_fun_base P_has_base) => vf_P_base.
move/(face_baseP vf_P_base) => [Q_base eq_sub Q_non_empty].
rewrite vf_fun_eq // in eq_sub; last exact: self_face.
set I := (@lshift m 1) @^-1: {eq Q on (hpolyI base H_base)}.
pose Q' := '['P^=(base; I)].
have Q'_base : [Q' has \base base] by apply/has_baseP; exists I.
have Q'_face : Q' \in \face P.
- apply/(face_baseP P_has_base); split; first done.
  + suff eq_P_sub_I : {eq P on base} \subset I
      by apply: (subset_trans eq_P_sub_I); exact: activeP.
    rewrite -sub_imset_pre.
    apply: (subset_trans _ eq_sub); exact: subsetUr.
  + suff: (Q <= Q')%PH by exact: non_empty_subset.
    apply/poly_subsetP => x.
    move: (hpoly_of_baseP Q_base) ->; rewrite 2!mem_quotP.
    move/hpolyEq_inP => [x_in_base x_eq].
    apply/hpolyEq_inP; split.
    * suff /hpolyI_inP [? _]: x \in hpolyI base H_base by done.
      exact: x_in_base.
    * move => i; rewrite inE => /x_eq.
      by rewrite mul_col_mx 2!col_mxEu.
have vf_Q'_eq_Q : vf_fun Q' = Q.
- rewrite (hpoly_of_baseP Q_base).
  suff <- : vf_eq I = {eq Q on hpolyI base H_base}.
  + rewrite /vf_fun (polyI_quotP (hP := 'P^=(base; I)) (hQ := hpoly_hyperplane c alpha)) //.
    apply/poly_eqP; rewrite /vf_eq /hpoly_hyperplane ord1_setT setUC -imset_set1.
    exact: hpolyEqI_concat_base.
  + have m_in_eqQ : (@rshift m 1) ord0 \in {eq Q on hpolyI base H_base}.
    * apply/(subsetP eq_sub); exact: setU11.
    apply/setP/subset_eqP/andP; split.
    * apply/subUsetP; split; first by rewrite sub1set.
      rewrite sub_imset_pre; exact: subxx.
    * apply/subsetP => i; case: (splitP' i) => [i' -> l_i_in_eqQ | i' -> _].
      - suff i'_in_I : i' \in I
          by rewrite /vf_eq in_setU; apply/orP; right; apply/imsetP; exists i'.
        by rewrite inE.
      - rewrite [i']ord1_eq0; exact: setU11.
exists Q'; split; try by done.
by rewrite -vf_Q'_eq_Q -vf_fun_non_empty in Q_non_empty.
Qed.

End VertexFigure.