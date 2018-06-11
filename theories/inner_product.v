(**************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect           *)
(*                                                                        *)
(* Parts taken from classfun.v:                                           *)
(* (c) Copyright Microsoft Corporation and Inria.                         *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(*                                                                        *)
(* Parts taken from dft.v:                                                *)
(* (c) Copyright 2015, CRI, MINES ParisTech, PSL Research University      *)
(* All rights reserved.                                                   *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(*                                                                        *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr)  *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)   *)
(* All rights reserved.                                                   *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(**************************************************************************)

From mathcomp Require Import all_ssreflect bigop ssralg ssrnum zmodp matrix vector fingroup perm.
Require Import extra_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section InnerProduct.
Variable n : nat.
Variable R : realFieldType.
Implicit Types u v w : 'cV[R]_n.

(* Inner product notation as in classfun *)
(* Reserved Notation "'[ u , v ]" *)
(*   (at level 80, format "'[hv' ''[' u , '/ '  v ] ']'"). *)

(* XXX: Issues with naming. Why vdot, why not dotu as in addr? *)

(* Inner product specialized to vectors of algebraic numbers *)
Definition vdot u v := \sum_i u i 0 * (v i 0).

(* Protected&reversed version for the Additive, etc... instances *)
Definition vdotr_head k u v := let: tt := k in vdot v u.
Definition vnorm_head k u   := let: tt := k in vdot u u.

Notation "''[' u , v ]" := (vdot u v) : ring_scope.
(* Recall: This is the squared norm *)
Notation "''[|' u |]^2" := '[u, u] : ring_scope.

Notation vdotr := (vdotr_head tt).
Notation vnorm := (vnorm_head tt).

Lemma vdotrE u v : vdotr v u = '[u, v].
Proof. by []. Qed.

(* Relation to matrix multiplication *)
Lemma vdot_def (u v : 'cV_n) : '[u,v]%:M = v^T *m u.
Proof.
  rewrite [_*m_]mx11_scalar; apply/congr1; rewrite !mxE.
by apply: eq_bigr => k _; rewrite !mxE mulrC.
Qed.

Lemma vdotr_is_linear u : linear (vdotr u : 'cV_n -> R^o).
Proof.
  move=> a v w.
  rewrite linear_sum -big_split //=; apply: eq_bigr => x _ /=.
    by rewrite !mxE mulrDl -mulrA.
Qed.

Canonical vdotr_additive u := Additive (vdotr_is_linear u).
Canonical vdotr_linear   u := Linear   (vdotr_is_linear u).

Lemma vdot0l u : '[0,u] = 0.
Proof. by rewrite -vdotrE linear0. Qed.
Lemma vdotNl u v : '[- u, v] = - '[u, v].
Proof. by rewrite -vdotrE linearN. Qed.
Lemma vdotDl u v w : '[u + v, w] = '[u, w] + '[v, w].
Proof. by rewrite -vdotrE linearD. Qed.
Lemma vdotBl u v w : '[u - v, w] = '[u, w] - '[v, w].
Proof. by rewrite -vdotrE linearB. Qed.
Lemma vdotMnl u v m : '[u *+ m, v] = '[u, v] *+ m.
Proof. by rewrite -!vdotrE linearMn. Qed.
Lemma vdotZl a u v : '[a *: u, v] = a * '[u, v].
Proof. by rewrite -vdotrE linearZ. Qed.

Lemma vdotC u v : '[u,v] = '[v,u].
Proof.
  by apply: eq_bigr => i _; rewrite mulrC.
Qed.

Lemma vdotr_delta_mx u i : '[u, delta_mx i 0] = u i 0.
Proof.
rewrite /vdot (bigD1 i _) //= mxE eq_refl mulr1.
suff ->: \sum_(j < n | j != i) u j 0 * ((delta_mx i 0):'cV_n) j 0 = 0 by apply:addr0.
by apply: big1 => j; rewrite mxE; move/negbTE ->; rewrite mulr0.
Qed.

Lemma vdotl_delta_mx u i : '[delta_mx i 0, u] = u i 0.
Proof.
by rewrite vdotC vdotr_delta_mx.
Qed.

Lemma vdotr_const_mx1 u : '[u, const_mx 1] = \sum_i u i 0.
Proof.
rewrite /vdot.
apply: eq_bigr => i _.
- by rewrite mxE mulr1.
Qed.

Lemma vdotBr u v w : '[u, v - w] = '[u, v] - '[u, w].
Proof. by rewrite !(vdotC u) vdotBl. Qed.
Canonical vdot_additive u := Additive (vdotBr u).

Lemma vdot0r u : '[u,0] = 0.
Proof. exact: raddf0. Qed.
Lemma vdotNr u v : '[u, - v] = - '[u, v].
Proof. exact: raddfN. Qed.
Lemma vdotDr u v w : '[u, v + w] = '[u, v] + '[u, w].
Proof. exact: raddfD. Qed.
Lemma vdotMnr u v m : '[u, v *+ m] = '[u, v] *+ m.
Proof. exact: raddfMn. Qed.
Lemma vdotZr a u v : '[u, a *: v] = a * '[u, v].
Proof. by rewrite !(vdotC u) vdotZl. Qed.

Lemma vdot_perm (s: 'S_n) u v :
  '[row_perm s u, row_perm s v] = '[u,v].
Proof.
suff: '[row_perm s u, row_perm s v]%:M = '[u,v]%:M :> 'M_1.
- by move/matrixP/(_ 0 0); rewrite !mxE.
- rewrite 2!vdot_def; exact: mulmx_tr_row_perm.
Qed.


Lemma vdot_sumDl (I: eqType) r (P: pred I) F x : '[\sum_(i <- r | P i) F i, x] = \sum_(i <- r | P i) '[F i, x].
Proof.
apply: (big_morph (fun y => '[y,x])).
- move => y y'; exact: vdotDl.
- exact: vdot0l.
Qed.

(* Order properties *)
Lemma vnorm_ge0 x : 0 <= '[| x |]^2.
Proof. by rewrite sumr_ge0 // => i _; exact: sqr_ge0. Qed.

Lemma vnorm_eq0 u : ('[| u |]^2 == 0) = (u == 0).
Proof.
apply/idP/eqP=> [|->]; last by rewrite vdot0r.
move/eqP/psumr_eq0P=> /= u0; apply/matrixP=> i j.
apply/eqP; rewrite ord1 !mxE -sqrf_eq0 expr2.
by rewrite u0 // => y _; exact: sqr_ge0.
Qed.

Lemma vnorm_gt0 u : ('[| u |]^2 > 0) = (u != 0).
Proof. by rewrite ltr_def vnorm_ge0 vnorm_eq0 andbT. Qed.

End InnerProduct.

Notation "''[' u , v ]" := (vdot u v) : ring_scope.
(* Recall: This is the squared norm *)
Notation "''[|' u |]^2" := '[u, u] : ring_scope.

Section Extra.

Variable n p : nat.
Variable R : realFieldType.

Lemma vdot_mulmx (A : 'M[R]_(n,p)) u v : '[u, A *m v] = '[A^T *m u, v].
Proof.
suffices: '[u, A *m v]%:M = ('[A^T *m u, v]%:M : 'M_1)
  by move/matrixP/(_ 0 0); rewrite !mxE //=.
by rewrite 2!vdot_def trmx_mul mulmxA.
Qed.

Lemma vdot_col_mx  (x y : 'cV[R]_n) (v w : 'cV[R]_p) :
  '[col_mx x v , col_mx y w] = '[ x , y] + '[v , w].
Proof.
rewrite /vdot big_split_ord /=.
by apply: congr2; apply: eq_bigr => i _; rewrite 2?col_mxEu 2?col_mxEd.
Qed.

Lemma vdot_castmx (epn : n = p) (u:'cV[R]_n) v : '[castmx (epn, erefl 1%N) u, castmx (epn, erefl 1%N) v] = '[u,v].
Proof.
suff: (castmx (epn, erefl 1%N) v)^T *m (castmx (epn, erefl 1%N) u) = v^T *m u.
- by rewrite -2!vdot_def; move/matrixP/(_ 0 0); rewrite !mxE /=.
- rewrite trmx_cast /= -{2}(esymK epn).
  have {1}->: erefl 1%N = esym (erefl 1%N) by done.
  by rewrite mulmx_cast esymK -{2}(esymK epn) castmx_id castmxKV.
Qed.

Lemma row_vdot (A : 'M[R]_(n,p)) x i : '[(row i A)^T, x] = ((A *m x) i 0).
Proof.
rewrite mxE.
apply: eq_bigr => j _.
by rewrite !mxE.
Qed.

End Extra.