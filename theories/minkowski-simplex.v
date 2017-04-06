(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp perm matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import polyhedron simplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R : realFieldType.
Variable n p : nat.

Section Def.

Variable V : 'M[R]_(n,p).

Definition e := (const_mx 1):'cV[R]_p.

Definition is_in_convex_hull (x : 'cV_n) :=
  exists l : 'cV[R]_p, [/\ (l >=m 0), '[e, l] = 1 & x = V *m l].

Definition A :=
  (col_mx (col_mx (col_mx V (-V)) (col_mx e^T (-e^T))) 1%:M).

Definition b (x: 'cV[R]_n) :=
  col_mx (col_mx (col_mx x (-x)) (col_mx 1 (-1))) (0:'cV_p).

Lemma is_in_convex_hullP (x: 'cV_n) :
  reflect (is_in_convex_hull x) (feasible A (b x)).
Proof.
apply: (iffP (feasibleP _ _)) => [[l] |[l [Hlpos Hlsum Hl]]].
- rewrite inE !mul_col_mx !col_mx_lev.
  move => /andP [/andP [Hl Hlsum] Hlpos].
  rewrite mul1mx in Hlpos.
  have Hlsum': '[e,l] = 1.
  + move: Hlsum; rewrite mulNmx -!vdot_def.
    rewrite lev_opp2; move/lev_antisym.
    by rewrite vdotC; move/colP/(_ 0); rewrite !mxE /= !mulr1n.
  have Hl' : x = V *m l.    
  + by move: Hl; rewrite mulNmx lev_opp2; move/lev_antisym.
  by exists l; split.
- exists l; rewrite inE !mul_col_mx !col_mx_lev.
  rewrite Hl mulNmx !lev_refl /=. 
  rewrite mul1mx Hlpos andbT.
  by rewrite mulNmx -vdot_def vdotC Hlsum !lev_refl.
Qed.  

Lemma separation (x: 'cV_n) :
  (~ (is_in_convex_hull x)) -> exists c, [forall i, '[c, col i V] > '[c, x]].
Proof.
- move/(introN (is_in_convex_hullP _))/infeasibleP => [d [/andP [HdA Hdpos] Hdb]].
  set d1 := usubmx (usubmx d).
  set d2 := dsubmx (usubmx d).
  set d3 := dsubmx d.
  set c := (usubmx d1) - (dsubmx d1).
  set y := ((usubmx d2) - (dsubmx d2)) 0 0.
  have Hineq1: ((V^T *m c) + (const_mx y)) <=m 0. 
  + move: HdA.
    rewrite !tr_col_mx !linearN /= trmxK trmx1.
    rewrite -[d]vsubmxK mul_row_col mul1mx.
    move: Hdpos; rewrite -{1}[d]vsubmxK; rewrite col_mx_gev0 => /andP [_].
    rewrite -lev_opp2 oppr0 => Hdpos.  
    rewrite addr_eq0 => /eqP => HdA. 
    move: Hdpos; rewrite -HdA.
    set d' := usubmx d.
    rewrite -[d']vsubmxK mul_row_col -/d1 -/d2.
    rewrite -[d1]vsubmxK mul_row_col mulNmx -mulmxN -mulmxDr -/c.
    rewrite -[d2]vsubmxK mul_row_col mulNmx -mulmxN -mulmxDr.
      by rewrite [_ - _]mx11_scalar mul_mx_scalar scalemx_const mulr1.
  have Hineq2: '[c, x] + y > 0.
  + move: Hdb.
    rewrite -[d]vsubmxK vdot_col_mx vdot0l addr0.
    set d' := usubmx d.
    rewrite -[d']vsubmxK vdot_col_mx -/d1 -/d2.
    rewrite -[d1]vsubmxK vdot_col_mx vdotNl -vdotNr -vdotDr -/c.
    rewrite -[d2]vsubmxK vdot_col_mx vdotNl -vdotNr -vdotDr.
    rewrite [_ - _]mx11_scalar -/y.
    suff: y%:M = (('[ 1, y%:M])%:M : 'cV_1).
    * by move/colP/(_ 0); rewrite 2!mxE /= 2!mulr1n => <-; rewrite vdotC.
    * by rewrite vdot_def tr_scalar_mx mulmx1.
  + exists (-c); apply/forallP => i.
    rewrite !vdotNl ltr_opp2.
    have: (row i ((V^T *m c + const_mx y))) <=m 0.
    * move/forallP/(_ i): Hineq1.
      rewrite [X in _ <= X]mxE => Hineq1.
      by apply/forallP => ?; rewrite mxE [X in _ <= X]mxE.
    rewrite linearD /= row_mul -tr_col -vdot_def row_const.
    move/forallP/(_ 0); rewrite !mxE /= mulr1n => Hineq1'.
    move: (ler_lt_trans Hineq1' Hineq2).
    by rewrite ltr_add2r.
Qed.
