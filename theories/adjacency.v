(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx polyhedron small_enough.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Vertex.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Implicit Types x : 'cV[R]_n.

Definition is_vertex x (P : 'cV[R]_n -> Prop) :=
  P x /\ (exists c, forall y, P y  -> '[y,c] <= '[x,c] /\ ('[y,c] = '[x,c] -> y = x)).

Lemma cons_in_seg (a lambda : R) :
  lambda * a + (1-lambda) * a = a.
Proof.
by rewrite -mulrDl addrC -addrA [(- lambda + lambda)]addrC (addrN lambda) addr0 mul1r.
Qed.

Lemma imp_cons_in_seg (c x v w : 'cV[R]_n) (lambda : R) :
0 < lambda -> lambda < 1 -> x = lambda *: v + (1-lambda) *: w ->
    '[v , c] <=  '[x , c] -> '[w , c] <=  '[x , c] -> '[v , c] =  '[x , c].
Proof.
move => Hlambda Hlambda' Hx Hv Hw.
move/(congr1 (fun z => '[z , c])) in Hx.
rewrite vdotDl !vdotZl in Hx.
move: Hx.
apply: contra_eq.
move => Hvaux.
have Hvaux': ('[ v, c] != '[ x, c]) && ('[ v, c] <= '[ x, c]).
  by apply/andP.
rewrite -ltr_neqAle -subr_gte0 in Hvaux'.
move:(mulr_gt0 Hlambda Hvaux') => Hvaux''.
rewrite mulrBr subr_gte0 -(ltr_add2r ((1 - lambda) * '[ w, c]) (lambda * '[ v, c]) (lambda * '[ x, c]))in Hvaux''.
rewrite -subr_gt0 in Hlambda'.
rewrite -subr_gte0 -(pmulr_rge0 ('[ x, c] - '[ w, c]) Hlambda') mulrBr subr_gte0 -(ler_add2l (lambda * '[ x, c]) ((1 - lambda) * '[ w, c]) ((1 - lambda) * '[ x, c])) in Hw.
move: (ltr_le_trans Hvaux'' Hw).
rewrite cons_in_seg ltr_def.
by move/andP; apply: proj1.
Qed.

Lemma imp_cons_in_seg' (x v w : 'cV[R]_n) (lambda : R) (i : 'I_m) :
0 < lambda -> lambda < 1 -> x = lambda *: v + (1-lambda) *: w ->
    b i 0 <=  (A *m v) i 0 ->  b i 0 <=  (A *m w) i 0 -> b i 0 =  (A *m x) i 0 -> b i 0 = (A *m v) i 0.
Proof.
move => Hlambda Hlambda' Hx Hv Hw Hx'.
move/(congr1 (fun z => (A *m z) i 0)) in Hx.
rewrite mulmxDr -!scalemxAr [(lambda *: (A *m v) + (1 - lambda) *: (A *m w)) i 0]mxE [(lambda *: (A *m v)) i 0]mxE [((1 - lambda) *: (A *m w)) i 0]mxE in Hx.
move: Hx.
apply: contra_eq.
move => Hv'.
have Hvaux': (b i 0 != (A *m v) i 0) && (b i 0 <= (A *m v) i 0).
  by apply/andP.
rewrite -ltr_neqAle -subr_gte0 in Hvaux'.
move:(mulr_gt0 Hlambda Hvaux') => Huaux''.
rewrite mulrBr subr_gte0 -(ltr_add2r ((1 - lambda) * b i 0) (lambda * b i 0) (lambda * (A *m v) i 0))in Huaux''.
rewrite -subr_gt0 in Hlambda'.
rewrite -subr_gte0 -(pmulr_rge0 ((A *m w) i 0 - b i 0) Hlambda') mulrBr subr_gte0 -(ler_add2l (lambda * (A *m v) i 0) ((1 - lambda) * b i 0) ((1 - lambda) * (A *m w) i 0)) in Hw.
rewrite neqr_lt.
apply/orP.
apply: or_introl.
move: (ltr_le_trans Huaux'' Hw).
by rewrite cons_in_seg -Hx'.
Qed.

Lemma vdotsumr' (q : nat)  (y : 'cV[R]_n) (B : 'M[R]_(n,q)) :
  '[y, \sum_i col i B] = \sum_i '[y,col i B].
Proof.
rewrite (((big_morph (fun w => '[y,w])) 0%R) +%R).
apply: eq_bigr => v _.
  - by done.
  - by apply: vdotDr.
  - by apply: vdot0r.
Qed.

Lemma psumr_eq0P' (q : nat) (B : 'M[R]_(n,q)) (y x : 'cV[R]_n):
(forall i, i \in 'I_q ->'[y , col i B] -  '[x , col i B] >= 0 ) -> \sum_i ( '[y, col i B] - '[x , col i B] ) = 0
      -> (forall i, i \in 'I_q -> '[y, col i B] - '[x , col i B] = 0).
Proof.
move => H H'.
by apply: (psumr_eq0P H H').
Qed.

Lemma psumr_eq0P'' (q : nat) (B : 'M[R]_(n,q)) (y x : 'cV[R]_n) :
(forall i, i \in 'I_q -> '[y , col i B] >= '[x , col i B]) ->
  '[y, \sum_i  col i B] = \sum_i '[x , col i B] -> forall i, '[y, col i B] = '[x , col i B].
Proof.
move => H Hsum.
have H': forall i : 'I_q, i \in 'I_q -> '[y, col i B] - '[x , col i B] >=0.
  move => i; rewrite subr_gte0;  by apply: (H i).
move/eqP in Hsum; rewrite -subr_eq0 in Hsum; move/eqP in Hsum; rewrite vdotsumr' -sumrB in Hsum.
move: (psumr_eq0P' H' Hsum); move => H''; move => i.
apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: (H'' i).
Qed.

Lemma vertex_is_extreme (P : 'cV[R]_n -> Prop) (x : 'cV[R]_n) :
  is_vertex x P -> is_extreme x P.
Proof.
move => [Hx [c Hc]].
split; first by done.
  move => v w lambda Hv Hw /andP [Hlambda Hlambda'] Hx'.
  move: (Hc v Hv) => [Hv' Hv''].
  move: (Hc w Hw) => [Hw' Hw''].
  split.
    - symmetry; by move: (imp_cons_in_seg Hlambda Hlambda' Hx' Hv' Hw').
    - symmetry; rewrite -subr_gte0 in Hlambda'.
      rewrite -oppr_lt0 -(ltr_add2l 1 (-lambda) 0) addr0 in Hlambda.
      rewrite addrC in Hx'.
      have Hx'': x = (1 - lambda) *: w + (1- (1-lambda)) *: v
        by rewrite opprB addrA [1 + lambda - 1]addrC addrA [-1 + 1]addrC addrN add0r.
      by move: (imp_cons_in_seg Hlambda' Hlambda Hx'' Hw' Hv').
Qed.

Lemma extreme_is_vertex_in_poly (x : 'cV[R]_n) :
  is_extreme x (polyhedron A b: _ -> bool) -> is_vertex x (polyhedron A b: _ -> bool).
Proof.
move/extremality_active_ineq => /andP [Hx Hrk].
split; first by done.
  - pose s := active_ineq A b x.
    pose e := (\col_i 1):'cV[R]_#|s|.
    have He: e >=m 0 by apply/forallP => ?; rewrite 2!mxE; apply: ler01.
    pose Ax := active_ineq_mx A b x.
    set c:= - (Ax^T *m e).
    exists c.
    move => y Hy.
    move/polyhedron_submx: Hy; move/(_ (active_ineq A b x)).
    rewrite inE -/(active_ineq_col A b x) -active_ineq_mx_col_eq -/(active_ineq_mx A b x) -/Ax => Hy.
    rewrite 2!['[_,c]]vdotC.
    rewrite 2!vdotNl -2!vdot_mulmx ler_opp2.
    split; first by apply: (vdot_lev He).
      + move/oppr_inj/eqP; rewrite -subr_eq0 -vdotBr.
        rewrite -subv_ge0 in Hy.
        have He': [forall i, e i 0 > 0] by apply/forallP => ?; rewrite mxE; apply: ltr01.
        move/eqP/(vdot_lev_eq0 He' Hy)/subr0_eq.
        by apply: row_full_inj.
Qed.

Definition are_adjacent u v (P : 'cV[R]_n -> Prop) :=
  [/\ (is_vertex u P), (is_vertex v P), (u != v) & (exists c, (('[v,c] = '[u,c]) /\ (forall w, P w -> '[w,c] <= '[v,c] /\ ('[w,c] = '[v,c] ->
     (exists lambda, (0 <= lambda <= 1) /\ w = lambda *: v +(1-lambda)*: u )))))].

Lemma active_ineq_in_interior_seg (u v : 'cV_n) :
(u \in polyhedron A b) -> (v \in polyhedron A b) -> ( forall lambda, 0 < lambda < 1 ->
  (active_ineq A b (lambda *: v +(1-lambda)*: u)) = (active_ineq A b u) :&: (active_ineq A b v)).
Proof.
move => Hu Hv lambda /andP [Hlambda Hlambda'].
pose x:= lambda *: v +(1-lambda)*: u.
have Hx: x= lambda *: v +(1-lambda)*: u.
  by done.
apply:eqP.
rewrite eqEsubset.
apply/andP.
split.
  - apply/subsetP => i.
    rewrite /active_ineq !inE eq_sym.
    move/eqP => Hx'.
    rewrite inE in Hv.
    move/forallP in Hv.
    move: (Hv i) => Hvi.
    rewrite inE in Hu.
    move/forallP in Hu.
    move: (Hu i) => Hui.
    apply/andP.
    split.
      + apply/eqP; symmetry.
        rewrite -subr_gte0 in Hlambda'.
        rewrite -oppr_lt0 -(ltr_add2l 1 (-lambda) 0) addr0 in Hlambda.
        have Hx'': x = (1 - lambda) *: u + (1- (1-lambda)) *: v 
          by rewrite opprB addrA [1 + lambda - 1]addrC addrA [-1 + 1]addrC addrN add0r addrC.
        by apply: (imp_cons_in_seg' Hlambda' Hlambda Hx'' Hui Hvi Hx').
      + apply/eqP; symmetry.
        by apply: (imp_cons_in_seg' Hlambda Hlambda' Hx Hvi Hui Hx').
  - apply/subsetP => i.
    move/setIP.
    rewrite /active_ineq !inE.
    move => [/eqP Hu' /eqP Hv']; apply/eqP.
    by rewrite mulmxDr -!scalemxAr [(lambda *: (A *m v) + (1 - lambda) *: (A *m u)) i 0]mxE [(lambda *: (A *m v)) i 0]mxE [((1 - lambda) *: (A *m u)) i 0]mxE Hv' Hu' cons_in_seg.
Qed.

Lemma in_poly_imply_in_seg (u v : 'cV_n) (lambda : R) :
is_extreme u (polyhedron A b: _ -> bool) -> is_extreme v (polyhedron A b: _ -> bool) ->
      u != v -> (lambda *: u + (1-lambda) *: v) \in polyhedron A b ->  0 <= lambda  <= 1.
Proof.
move => [Hu Hu'] [Hv Hv'] Huv Hlambdauv.
apply/andP.
split.
  - apply: contraT.
    rewrite -ltrNge; move => Hlambda.
    have Hlambda': 0 < 1 - lambda 
      by move: (@ler_lt_trans R 0 lambda 1 (ltrW Hlambda) ltr01); rewrite subr_gt0.
    have Hlambda'': 0 < - lambda / (1 - lambda) < 1.
      apply/andP; split.
        + apply: divr_gt0; by [ rewrite oppr_gt0 | done].
        + rewrite ltr_pdivr_mulr; last by done.
          by rewrite mul1r ltr_subr_addr addNr; apply: ltr01.
    have Hv'': v = (- lambda / (1 - lambda)) *: u + (1 - - lambda / (1 - lambda)) *: (lambda *: u + (1 - lambda) *: v).
      rewrite mulNr opprK scalerDr !scalerA [((1 + lambda / (1 - lambda)) * (1 - lambda))]mulrDl mul1r -mulrA (mulVf (lt0r_neq0 Hlambda')).
      rewrite addrA mulr1 -[(1 - lambda + lambda)]addrA addNr addr0 scale1r.
      rewrite [- (lambda / (1 - lambda)) *: u + ((1 + lambda / (1 - lambda)) * lambda) *: u]addrC scaleNr -scalerBl.
      rewrite mulrDl -addrA -[-(lambda / (1 - lambda))]mulr1 mulNr -mulrBr -opprB mulrN -mulrA (mulVf (lt0r_neq0 Hlambda')).
      by rewrite mulr1 mul1r addrN scale0r add0r.
    move: (@Hv' u (lambda *: u + (1-lambda) *: v) ((-lambda)/(1-lambda)) Hu Hlambdauv Hlambda'' Hv'') => [H _].
    by move/eqP: H; rewrite eq_sym; apply: contraTT.
  - apply: contraT.
    rewrite -ltrNge; move => Hlambda.
    have Hlambda': 0 < lambda -1 
      by rewrite -subr_gt0 in Hlambda.
    have Hlambda'': 0 < 1/lambda < 1.
      apply/andP; split.
        + by apply: (@divr_gt0 R 1 lambda ltr01 (@ler_lt_trans R 1 0 lambda (ltrW ltr01) Hlambda)).
        + by rewrite (ltr_pdivr_mulr 1 1 (@ler_lt_trans R 1 0 lambda (ltrW ltr01) Hlambda)) mul1r.
    have Hu'': u = (1 / lambda) *: (lambda *: u + (1 - lambda) *: v) + (1 - 1 / lambda) *: v 
      by rewrite scalerDr !scalerA mul1r mulrDr mulr1 mulrN (mulVf (lt0r_neq0 (@ler_lt_trans R 1 0 lambda (ltrW ltr01) Hlambda))) scale1r -opprB -addrA [(- (1 - lambda^-1) *: v + (1 - lambda^-1) *: v)]addrC scaleNr -scalerBl addrN scale0r addr0.
    move: (@Hu' (lambda *: u + (1-lambda) *: v) v (1/lambda) Hlambdauv Hv Hlambda'' Hu'') => [_ H].
    by move/eqP: H; apply: contraTT.
Qed.

Lemma polyhedron_is_convex (u v : 'cV_n) (lambda : R) :
  0 < lambda  < 1 -> (u \in polyhedron A b) -> (v \in polyhedron A b) ->
              (lambda *: u + (1-lambda) *: v \in polyhedron A b).
Proof.
move => /andP [H0lambda Hlambda1] Hu Hv.
rewrite inE.
rewrite inE in Hu.
rewrite inE in Hv.
apply/forallP => i.
move/forallP in Hu.
move: (Hu i) => Hui.
move/forallP in Hv.
move: (Hv i) => Hvi.
rewrite mulmxDr -!scalemxAr 2!mxE [((1 - lambda) *: (A *m v)) i 0]mxE.
rewrite -subr_gt0 in Hlambda1.
rewrite -(ler_pmul2l H0lambda (b i 0) ((A *m u) i 0)) in Hui.
rewrite -(ler_pmul2l Hlambda1 (b i 0) ((A *m v) i 0)) in Hvi.
move: (ler_add Hui Hvi).
by rewrite -mulrDl addrC -addrA [(- lambda + lambda)]addrC addrN addr0 mul1r.
Qed.

Lemma mid_point_seg (u v : 'cV_n) :
let: lambda := (1 / (2%:R)): R in
(u \in polyhedron A b) -> (v \in polyhedron A b) ->
 ((lambda *: v +(1-lambda)*: u) \in polyhedron A b) /\ (active_ineq A b (lambda *: v +(1-lambda)*: u)) = (active_ineq A b u) :&: (active_ineq A b v).
Proof.
pose lambda := (1 / (2%:R)): R.
move => Hu Hv.
have Hlambda: 0 < lambda < 1.
  apply/andP; split; rewrite /lambda.
    + apply: divr_gt0; by [apply: ltr01 | apply: ltr0n].
    + rewrite ltr_pdivr_mulr; last by apply: ltr0n.
      * by rewrite mul1r ltr1n.
split.
  - by apply: (@polyhedron_is_convex v u lambda Hlambda Hv Hu).
  - by apply: (active_ineq_in_interior_seg Hu Hv Hlambda).
Qed.

Lemma active_ineq_mx_row (x v : 'cV_n) i :
    ((active_ineq_mx A b x) *m v) i 0 = (A *m v) (enum_val i) 0.
Proof.
by rewrite -row_submx_mul row_submx_mxE.
Qed.

Lemma poly_inactive_ineq_open_set i (x : 'cV_n) (v: 'cV_n) :
  (x \in polyhedron A b) -> i \notin (active_ineq A b x) ->
  holds_for_small_enough (fun eps => (A *m (x + eps *: v)) i 0 > b i 0).
Proof.
move => Hx Hi.
rewrite /holds_for_small_enough.
pose epsilon := if (A *m v) i 0 >= 0 then 1 else ((A *m x) i 0 - b i 0) /(- (A *m v) i 0 +1).
exists epsilon; split.
- rewrite /epsilon.
  case: ifP => H; first by apply: ltr01.
  apply negbT in H.
  rewrite -ltrNge -oppr_gt0 in H.
  move: (addr_gt0 H ltr01) => H'.
  rewrite (inactive_ineq Hx) -subr_gt0 in Hi.
  by apply: divr_gt0.
- move => eps' Heps'.
  move/andP: Heps' => [Heps' Hee].
  rewrite mulmxDr -scalemxAr mxE [(eps' *: (A *m v)) i 0]mxE.
  case Hvi: (0 <= (A *m v) i 0).
   + rewrite (inactive_ineq Hx) in Hi.
     rewrite addrC.
     apply ltr_paddl; last by done.
     apply mulr_ge0; last by done.
     by apply gt0_cp.
   + rewrite /epsilon ifF in Hee; last by done.
     rewrite ler_pdivl_mulr in Hee.
     rewrite mulrDr mulr1 mulrN addrC ler_sub_addr -addrA [(- b i 0 + eps' * (A *m v) i 0)]addrC in Hee.
     rewrite -subr_gt0 -addrA.
     by apply: (ltr_le_trans Heps' Hee).
     apply negbT in Hvi.
     rewrite -ltrNge -oppr_gt0 in Hvi.
     by apply: (addr_gt0 Hvi ltr01).
Qed.

Lemma poly_mem_perturbation (x : 'cV_n) (v : 'cV_n) :
  (x \in polyhedron A b) -> (active_ineq_mx A b x) *m v == 0 ->
  holds_for_small_enough (fun eps => (x + eps *: v) \in polyhedron A b).
Proof.
move => Hx Hv.
apply: small_enough_ordinal.
move => i.
case: (boolP (i \in active_ineq A b x)) => [H | H].
- apply/(@small_enough_eq R xpredT); last by apply:small_enough_cons.
  move => eps; rewrite mulmxDr -scalemxAr [X in _ <= X] mxE [X in _ + X]mxE.
  move/eqP/colP/(_ (enum_rank_in H i)): Hv; rewrite -row_submx_mul row_submx_mxE enum_rankK_in // [RHS]mxE.
  move => ->; rewrite mulr0 addr0.
  by move/forallP/(_ i): Hx.
- move: (poly_inactive_ineq_open_set v Hx H).
  apply: small_enough_imply.
  move => eps.
  by apply: ltrW.
Qed.

Lemma poly_mem_perturbation' (x : 'cV_n) (v : 'cV_n) :
  (x \in polyhedron A b) -> (active_ineq_mx A b x) *m v == 0 ->
  exists eps, (0 < eps) /\ ((x + eps *: v) \in polyhedron A b).
Proof.
move => Hx Hv.
move: (poly_mem_perturbation Hx Hv).
rewrite /holds_for_small_enough.
case => eps [Heps Heps'].
exists eps.
split; first by done.
  - have Haux : 0< eps <= eps.
      apply/andP; split; by [ done | apply:lerr].
    by apply: (Heps' eps Haux).
Qed.

Lemma fullrank_active_inter_imp_eq (u v : 'cV_n) :
let: K := (active_ineq A b u) :&: (active_ineq A b v) in
            \rank (row_submx A K) = n -> u = v.
Proof.
set K := (active_ineq A b u) :&: (active_ineq A b v).
set AK := row_submx A K.
move/eqP =>  Hrk.
suff: AK *m u = AK *m v by apply: row_full_inj.
 
apply/row_matrixP => i.
rewrite 2!row_mul row_submx_row.
move/setIP: (enum_valP i) => [Hiu Hiv].
set i' := enum_val i.
pose iu := enum_rank_in Hiu i'.
pose iv := enum_rank_in Hiv i'.
rewrite -[i' in LHS](enum_rankK_in Hiu) // -[i' in RHS](enum_rankK_in Hiv) //.
rewrite -2!row_submx_row -2!row_mul 2!active_ineq_mx_col_eq.
by rewrite 2!row_submx_row enum_rankK_in // enum_rankK_in //.
Qed.

Lemma trmx_eq0 (p q : nat) (C : 'M[R]_(p,q)) :
    (C == 0) = (C^T==0).
Proof.
apply/idP/idP.
  - move/eqP => H.
    by rewrite H; apply/eqP; apply: trmx0.
  - move/eqP/(congr1 (fun E => E^T)).
    by rewrite !trmxK trmx0; move/eqP.
Qed.

Lemma active_ineq_mx_col_poly' (y : 'cV_n) (I : {set 'I_m}) :
  y \in polyhedron A b -> y \in polyhedron (row_submx A I) (row_submx b I).
Proof.
move/forallP => Hy.
apply/forallP => i.
rewrite !mxE (eq_bigr (fun j => A (enum_val i) j * y j 0)); last by move => j _; rewrite row_submx_mxE.
by move: (Hy (enum_val i)); rewrite mxE.
Qed.

Lemma rank_active_ineq_mx_in_interior_seg (u v : 'cV_n) :
(u \in polyhedron A b) -> (v \in polyhedron A b) -> ( forall lambda, 0 < lambda < 1 ->
  ( \rank (active_ineq_mx A b (lambda *: v +(1-lambda)*: u)) = \rank (row_submx A ((active_ineq A b u) :&: (active_ineq A b v))))).
Proof.
move => Hu Hv lambda Hlambda.
move: (active_ineq_in_interior_seg Hu Hv Hlambda) => Hactiveineq.
by rewrite /active_ineq_mx Hactiveineq.
Qed.

Lemma subset_active_ineq (u : 'cV_n) (I : {set 'I_m}) :
  I \subset (active_ineq A b u) -> (row_submx A I) *m u = row_submx b I.
Proof.
move => HI.
apply/colP => i.
rewrite !mxE (eq_bigr (fun j => A (enum_val i) j * u j 0)); last by move => j _; rewrite row_submx_mxE.
move/subsetP/(_ _ (enum_valP i)): HI.
by rewrite inE mxE; move/eqP.
Qed.

Lemma adjacent_in_polyhedron (u v : 'cV_n) :
let: K := (active_ineq A b u) :&: (active_ineq A b v) in
  (n > 2)%N -> (\rank A = n) -> (are_adjacent u v (polyhedron A b: _ -> bool)) <->
    ([/\ (is_vertex u (polyhedron A b: _ -> bool)), (is_vertex v (polyhedron A b: _ -> bool)) & (\rank (row_submx A K) = n-1)%N]).
Proof.
set K := (active_ineq A b u) :&: (active_ineq A b v).
set AK := row_submx A K.
move => Hn HrkA.
split.
  - move => [Hu Hv Huv Hc].
    split; move => //.
      + move: Hu Hv; move => [[Hu _] [Hv _]].
        set lambda := (1 / (2%:R)): R.
        have Hlambda: 0 < lambda < 1.
          apply/andP; split.
            * apply: divr_gt0; by [apply: ltr01 | apply: ltr0n].
            * rewrite ltr_pdivr_mulr; last by apply: ltr0n.
              by rewrite mul1r ltr1n.
        set x := lambda *: v + (1 - lambda) *: u.
        move: (mid_point_seg Hu Hv) => [Hx HAIx].
        have HrkA': (\rank AK < n )%N.
          move: Huv; apply: contraTT.
          rewrite -ltnNge ltnS; move => Haux.
          move: (rank_leq_col AK) => Haux'.
          have HrkAK: \rank AK = n by apply/eqP; rewrite eqn_leq; apply/andP.
          rewrite negbK; apply/eqP.
          by apply: (fullrank_active_inter_imp_eq HrkAK).
        have HrkA'': (n - 1 <= \rank AK )%N.
          move: Hc; case => c [Hcuv Hcw]; apply: contraT.
          rewrite -ltnNge -(rank_active_ineq_mx_in_interior_seg Hu Hv Hlambda).
          move => HrkAIx.
          set d := u - v.
          set D := col_mx d^T (active_ineq_mx A b x).
          rewrite -(ltn_add2l (\rank d^T) (\rank (active_ineq_mx A b x)) (n-1)) in HrkAIx.
          move: (rank_leq_row d^T) => Haux.
          rewrite -(leq_add2r (n-1) (\rank d^T) 1) subn1 add1n (ltn_predK Hn) -subn1 in Haux.
          move: (leq_trans (leq_ltn_trans (mxrank_adds_leqif d^T (active_ineq_mx A b x)) HrkAIx) Haux) => HrkD.
          rewrite addsmxE in HrkD.
          have HrkcokerD: (\rank (cokermx D) >= 1)%N by rewrite mxrank_coker ltn_subRL addn0.
          have HcokerD: (cokermx D)^T != 0.
            move: HrkcokerD; rewrite lt0n; apply: contraTneq.
            move/eqP; rewrite -trmx_eq0; move/eqP => Haux'.
            by rewrite Haux' mxrank0.
          move: (rowV0Pn HcokerD).
          case => z; move/submxP; case => P.
          move/(congr1 (fun E => D *m (E^T))).
          rewrite trmx_mul trmxK mulmxA mulmx_coker mul0mx mul_col_mx -col_mx0.
          move/eqP; rewrite col_mx_eq; move/andP.
          move => [Hdz HzAIx] Hz.
          have Haux' : '[ z^T, c] = 0.
            apply:eqP; rewrite eqr_le; apply/andP.
            split.
            * move: (poly_mem_perturbation' Hx HzAIx).
              case => eps1 [Heps1 Hxeps1].
              move: (Hcw (x + eps1 *: z^T) Hxeps1) => [Hxeps1' _].
              by rewrite /x !vdotDl !vdotZl Hcuv cons_in_seg -ler_subr_addl addrN (@pmulr_rle0 R eps1 ('[ z^T, c]) Heps1) in Hxeps1'.
            * rewrite -oppr_eq0 -mulmxN in HzAIx.
              move: (poly_mem_perturbation' Hx HzAIx).
              case => eps2 [Heps2 Hxeps2].
              move: (Hcw (x + eps2 *: (-z^T)) Hxeps2) => [Hxeps2' _].
              by rewrite /x !vdotDl !vdotZl Hcuv cons_in_seg -ler_subr_addl addrN (@pmulr_rle0 R eps2 ('[ -z^T, c]) Heps2) vdotNl oppr_le0 in Hxeps2'.
          move: (poly_mem_perturbation' Hx HzAIx).
          case => eps [Heps Hxeps].
          have Hxeps': '[x + eps *: z^T , c] = '[ v,c]
            by rewrite /x !vdotDl !vdotZl Hcuv cons_in_seg Haux' mulr0 addr0.
          move: (Hcw (x + eps *: z^T) Hxeps) => [_ Haux''].
          move: (Haux'' Hxeps'); case => gamma [_ Hgamma'].
          move/(congr1 (fun y => y - x)) in Hgamma'.
          rewrite addrC addrA addNr add0r /x 2!scalerBl [(1 *: u - gamma *: u)]addrC [gamma *: v + (- (gamma *: u) + 1 *: u)]addrA -scalerBr [(lambda *: v + (1 *: u - lambda *: u))]addrC -addrA [(- (lambda *: u) + lambda *: v)]addrC -scalerBr -addrA -opprB !scalerN opprB [(lambda *: (u - v) - 1 *: u)]addrC [(1 *: u + (- (1 *: u) + lambda *: (u - v)))]addrA -scalerBl addrN scale0r add0r addrC -scalerBl in Hgamma'.
          move/(congr1 (fun y => z *m y)) in Hgamma'.
          rewrite -trmx_mul -trmx_eq0 in Hdz; move/eqP in Hdz.
          rewrite -!scalemxAr Hdz scaler0 in Hgamma'.
          move/eqP: Hgamma'; rewrite scalemx_eq0.
          apply: contraTT; move => _; rewrite negb_or.
          apply/andP.
          split; first by apply: lt0r_neq0.
            * move: Hz; apply: contraNneq.
              move/(congr1 (fun y => y^T)); rewrite trmx_mul trmx0 -vdot_def.
              move/eqP; rewrite scalar_mx_eq0 mxE.
              by rewrite vnorm_eq0 -trmx_eq0.
        apply/eqP; rewrite eqn_leq; apply/andP.
        split; by [rewrite subn1 -ltnS (ltn_predK Hn) | done].
  - move => [Hu Hv HrkAK].
    have Huv: (u-v)^T != 0.
      move: HrkAK; apply: contra_eqN.
      rewrite -trmx_eq0 subr_eq0; move/eqP => Haux.
      move: (vertex_is_extreme Hv).
      move/(@extremality_active_ineq _ _ _ A b v) => /andP [_ /eqP Haux'].
      rewrite /AK /K Haux setIid Haux' neq_ltn.
      apply/orP/or_intror.
      by rewrite subn1 -(ltn_add2r 1 n.-1 n) addn1 (ltn_predK Hn) addn1.
    rewrite /are_adjacent.
    split; move => //.
      + by rewrite -trmx_eq0 subr_eq0 in Huv.
      + set c:= \sum_i (col i (-AK)^T).
        exists c.
        split.
          * rewrite /c !vdotsumr' (eq_bigr (fun j => ('[u, col j (-AK)^T]))); first by done.
            move => j _; rewrite /vdot.
            rewrite (eq_bigr (fun k => ((-1)* (AK j k * v k 0))));
              last by move => i _; rewrite 3!mxE mulrA mulN1r mulrC.
            rewrite  [\sum_i u i 0 * (col j (- AK)^T) i 0](eq_bigr (fun k => ((-1) * (AK j k * u k 0))));
              last by move => i _; rewrite 3!mxE mulrA mulN1r mulrC.
            rewrite -2!mulr_sumr 2!mulN1r; apply:eqP; rewrite eqr_opp.
            move: (subset_active_ineq (subsetIr (active_ineq A b u) (active_ineq A b v))) => Haux.
            rewrite -(subset_active_ineq (subsetIl (active_ineq A b u) (active_ineq A b v))) in Haux.
            move/matrixP: Haux => Haux; move/eqP: (Haux j 0).
            by rewrite !mxE.
          * move => w Hw.
            have Hw': forall i, i \in 'I_(#|K|) -> '[w ,  col i (- AK)^T ] <= '[v , col i (- AK)^T ].
              move => i Hi.
              rewrite -tr_row /vdot (eq_bigr (fun j => ((-1) * (AK i j * w j 0 ))));
                last by move => j _; rewrite 3!mxE mulrA mulN1r mulrC.
              rewrite [\sum_i0 v i0 0 * (row i (- AK))^T i0 0](eq_bigr (fun j => ((-1) *(AK i j * v j 0 ))));
                last by move => j _; rewrite 3!mxE mulrA mulN1r mulrC.
              rewrite -2!mulr_sumr 2!mulN1r ler_oppr opprK.
              rewrite (eq_bigr (fun j => A (enum_val i) j * v j 0));
                last by move => j _; rewrite row_submx_mxE.
              have Haux: (A *m v) (enum_val i) 0 =  b (enum_val i) 0.
                move/subsetP/(_ _ (enum_valP i)): (subsetIr (active_ineq A b u) (active_ineq A b v)) => Hiv.
                set kv := enum_rank_in Hiv (enum_val i).
                move/matrixP: (active_ineq_mx_col_eq A b v) => Hv'; move: (Hv' kv 0).
                rewrite active_ineq_mx_row enum_rankK_in /active_ineq_col; last by done.
                by rewrite row_submx_mxE enum_rankK_in; last by done.
              rewrite [(A *m v) (enum_val i) 0]mxE in Haux.
              rewrite Haux.
              move/forallP: (active_ineq_mx_col_poly' K Hw) => Hw''; move: (Hw'' i).
              by rewrite row_submx_mxE [(row_submx A K *m w) i 0]mxE.
            split; first by rewrite /c !vdotsumr'; apply: ler_sum; move => i _; apply: Hw'.
              - rewrite /c vdotsumr'.
                move/eqP; rewrite eq_sym; move/eqP => Hw''.
                move: (leq_addl 2 1) => H13.
                rewrite addn1 in H13.
                have Haux1: ((u-v)^T <= (kermx AK^T))%MS.
                  apply/sub_kermxP/eqP.
                  rewrite -trmx_mul -trmx_eq0.
                  by rewrite mulmxBr (subset_active_ineq (subsetIr (active_ineq A b u) (active_ineq A b v))) (subset_active_ineq (subsetIl (active_ineq A b u) (active_ineq A b v))) subr_eq0.
                rewrite subn1 in HrkAK.
                move: (corank1_kermx (leq_trans H13 Hn) HrkAK) => HrkCokAK.
                move: (rank_rV (u - v)^T) => Hrkuv.
                rewrite Huv in Hrkuv.
                move/geq_leqif: (mxrank_leqif_eq Haux1) => Haux2.
                have Haux3: (\rank (kermx AK^T) <= \rank (u - v)^T)%N by rewrite HrkCokAK Hrkuv.
                rewrite Haux2 in Haux3; move/eqmxP in Haux3.
                have Haux4: exists a : R, (w - v)^T = a *: (u - v)^T.
                  apply: sub_rVP; rewrite Haux3; apply/sub_kermxP/eqP; rewrite -trmx_mul -trmx_eq0.
                  apply/eqP/colP => j; rewrite !mxE.
                  move: (psumr_eq0P'' Hw' Hw'').
                  move => / (_ j) H.
                  rewrite -tr_row /vdot (eq_bigr (fun i => ((-1) * (AK j i * v i 0 )))) in H;
                    last by move => i _; rewrite 3!mxE mulrA mulN1r mulrC.
                  rewrite [\sum_i w i 0 * (row j (- AK))^T i 0](eq_bigr (fun i => ((-1) * (AK j i * w i 0 )))) in H;
                    last by move => i _; rewrite 3!mxE mulrA mulN1r mulrC.
                  rewrite -2!mulr_sumr 2!mulN1r in H.
                  rewrite (eq_bigr (fun i => ((AK j i * w i 0 -AK j i * v i 0  ))));
                    last by move => i _; rewrite -mulrBr !mxE.
                  rewrite sumrB; apply/eqP; rewrite subr_eq0 -eqr_opp.
                  by apply/eqP.
                move: Haux4; case => lambda.
                rewrite -trmx_mul_scalar; move/(congr1 (fun y => y^T)); rewrite !trmxK scalerBr.
                move/(congr1 (fun y => y+v)); rewrite -addrA [- v + v]addrC addrN addr0 -addrA [-(lambda *: v) + v]addrC -[v in v-_]scale1r -scalerBl.
                move => Haux4.
                exists (1-lambda).
                split; last by rewrite addrC opprB [(1 + (lambda - 1))]addrC -addrA addNr addr0.
                  + rewrite Haux4 in Hw.
                    rewrite -trmx_eq0 subr_eq0 in Huv.
                    move: (@in_poly_imply_in_seg u v lambda (vertex_is_extreme Hu) (vertex_is_extreme Hv) Huv Hw).
                    move/andP => [Ha Ha'].
                    apply/andP; split; by [rewrite subr_ge0 | rewrite ler_subl_addl -ler_subl_addr addrN].
Qed.

End Vertex.
