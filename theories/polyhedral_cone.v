(**************************************************************************)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr)  *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)   *)
(* All rights reserved.                                                   *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(**************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Cone.

Variable R : realFieldType.
Variable m n : nat.

Definition cone (A : 'M[R]_(m,n)) := [pred x: 'cV_n | (A *m x) >=m 0].

Lemma cone_mem0 (A : 'M[R]_(m,n)) : 0 \in (cone A).
Proof.
rewrite inE mulmx0; apply: lev_refl. 
Qed.

Lemma cone_ineq_seq (A : 'M_(m,n)) :
  let: C := [seq (row i A)^T, i] in
  (cone A) =1 [pred x | all (fun c => '[c,x] >= 0) C].
Proof.
move => x.
have H i: '[ (row i A)^T, x] = (A *m x) i 0.
+ rewrite !mxE /vdot.
  apply: eq_bigr => j _; by rewrite tr_row !mxE.
rewrite !inE all_map /preim /=.
apply/idP/idP.
+ move/forallP => H'.
  apply/allP => i Hi.
  rewrite !inE H; by move: (H' i); rewrite !mxE.
+ move/allP => H'.
  apply/forallP => i; rewrite mxE.
  rewrite -H.
  move: (H' i) => Hi. by rewrite mem_enum inE in Hi; apply: Hi.
Qed.

Lemma cone_is_closed_by_sum (A : 'M_(m,n)) :
  forall (x y : 'cV_n), x \in cone A -> y \in cone A -> (x+y) \in cone A.
Proof.
move => x y; rewrite !inE mulmxDr => ?.
rewrite -(lev_add2l (A*m x)) addr0.
by apply: lev_trans.
Qed.

Lemma cone_is_closed_by_scaling (A : 'M[R]_(m,n)) (x : 'cV_n) (a : R) :
  (x \in cone A) -> a >= 0 -> (a *: x) \in cone A.
Proof.
move => /forallP Hx Ha.
apply/forallP => i; rewrite mxE -scalemxAr mxE.
by apply: mulr_ge0; last by move/(_ i): Hx; rewrite mxE.
Qed.

Section Conic_hull.

Definition is_in_conic_hull (S : seq 'cV[R]_n) (x : 'cV[R]_n) :=
  exists (l: 'cV[R]_n -> R), (forall v, v \in S -> l v >= 0) /\
                     x = \sum_(v <- S) (l v) *: v.

Definition is_convex_cone (P : 'cV_n -> Prop) :=
  (forall (x y : 'cV_n), P x -> P y -> P (x + y)) /\ (forall x : 'cV_n, forall a: R, P x -> a >= 0 -> P (a *: x)).

Lemma conic_hull_is_closed_by_sum (S : seq 'cV[R]_n) :
  forall (x y : 'cV_n), is_in_conic_hull S x -> is_in_conic_hull S y ->  is_in_conic_hull S (x + y).
Proof.
move => x y [lx [Hlx ->]] [ly [Hly ->]].
exists (fun v => (lx v) + (ly v)).
split.
- move => v Hv; apply: addr_ge0.
  by apply: Hlx. by apply: Hly.
- rewrite -big_split /=.
  by apply: eq_bigr => v _; last by rewrite scalerDl.
Qed.

Lemma conic_hull_is_closed_by_scaling (S : seq 'cV[R]_n) :
  forall x : 'cV_n, forall a : R, is_in_conic_hull S x -> a >= 0 -> is_in_conic_hull S (a *: x).
Proof.
move => x a [lx [Hlx ->]].
exists (fun v => a * (lx v)).
split.
- move => v Hv; by apply: mulr_ge0; last by apply: (Hlx v Hv).
- rewrite big_endo; last by apply: scaler0.
  + apply: eq_bigr => v _; apply: scalerA.
  + by apply: scalerDr.
Qed.

Lemma conic_hull_is_convex_cone (S : seq 'cV[R]_n) : is_convex_cone (is_in_conic_hull S).
Proof.
split.
- apply: conic_hull_is_closed_by_sum.
- apply: conic_hull_is_closed_by_scaling.
Qed.

Lemma zero_is_in_conic_hull (S : seq 'cV[R]_n) : is_in_conic_hull S 0.
Proof.
exists (fun v => 0).
split; first by done.
- rewrite big1 //=; move => v _; by apply: scale0r. 
Qed.

Lemma conic_hull_incl :
  forall (S1 S2 : seq 'cV[R]_n),
    (forall v : 'cV_n, v \in S1 -> is_in_conic_hull S2 v) ->
    (forall x : 'cV_n, is_in_conic_hull S1 x -> is_in_conic_hull S2 x).
Proof.
move => S1 S2 Hv x [lx [Hlx ->]].
rewrite big_seq.
apply: big_ind; first by apply: zero_is_in_conic_hull.
- apply/conic_hull_is_closed_by_sum.
  move => w Hw.
  apply: conic_hull_is_closed_by_scaling.
  + by apply: Hv.
  + by apply: Hlx.
Qed.

Lemma conic_hull_incl_cone :
  forall (S : seq 'cV[R]_n) (A : 'M[R]_(m,n)),
    (forall v : 'cV_n, v \in S -> v \in cone A) ->
    (forall x : 'cV_n, is_in_conic_hull S x -> x \in cone A).
Proof.
move => S A HS x [lx [Hlx ->]].
rewrite big_seq.
apply: (@big_ind _ (cone A: _ -> bool)); first by apply: cone_mem0.
- move => ? ?; apply: cone_is_closed_by_sum.
  + move => v Hv; move/(_ _ Hv): Hlx; move/(_ _ Hv): HS.
    apply: cone_is_closed_by_scaling.
Qed.

Lemma conic_hull_incl_self (S : seq 'cV_n) : (uniq S) -> forall v : 'cV_n, v \in S -> is_in_conic_hull S v.
Proof.
move => Huniq v HvS.
exists (fun w => if w == v then 1 else 0).
split.
- move => w Hw.
  case: ifP => H //.
  + by apply: ler01.
- rewrite (eq_big_perm (v:: (rem v S))) //=; last by apply: (perm_to_rem HvS).
  rewrite big_cons eq_refl scale1r.
  rewrite big_seq big1; first by rewrite addr0.
  + move => w Hw.
    rewrite (mem_rem_uniq _ _) // in Hw.
    move/andP: Hw => [Hw _].
    by rewrite ifN // scale0r.
Qed.

Lemma conic_hull_monotone :
  forall (S1 S2 : seq 'cV_n),
    (uniq S2) -> {subset S1 <= S2} ->
    (forall x : 'cV_n, is_in_conic_hull S1 x -> is_in_conic_hull S2 x).
Proof.
move => S1 S2 Huniq Hsubset.
apply: conic_hull_incl.
- move => v Hv.
  apply: (conic_hull_incl_self Huniq).
  + by apply: (Hsubset _ Hv).
Qed.

End Conic_hull.

End Cone.