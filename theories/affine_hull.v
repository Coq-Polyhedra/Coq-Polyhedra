(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2018, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm.
Require Import extra_misc inner_product vector_order extra_matrix row_submx hpolyhedron polyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module HullBase.

Section Hull.

Variable R : realFieldType.
Variable n : nat.
Variable P : 'poly[R]_n.

Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis P_non_empty : non_empty P.
Hypothesis P_base : [ P has \base 'P(A,b) ].

Definition relint_pt_ith i (H : i \notin { eq(P) on 'P(A,b) }) :=
  xchoose ((@exists_andP _ _ _).1 (active_inPn P_base _ H)).

Lemma relint_pt_ithP i (H : i \notin { eq(P) on 'P(A,b) }) :
  let x := relint_pt_ith H in
  (x \in P) /\ ((A *m x) i 0 > b i 0).
Proof.
rewrite /relint_pt_ith.
set Q := ((exists_andP _ _).1 _).
by move/andP: (xchooseP Q).
Qed.

Lemma poly_is_convex (I : finType) (lambda : I -> R) (V : I -> 'cV[R]_n) :
  (forall i, lambda i >= 0) -> (\sum_i (lambda i) = 1) -> (forall i, V i \in P) -> \sum_i (lambda i) *: (V i) \in P.
Admitted.

Definition relint_pt :=
  let x0 := xchoose (non_emptyP P_non_empty) in
  if (m > 0)%N then
    (m%:R^-1) *: \sum_i (if (@idPn (i \in { eq(P) on 'P(A,b) })) is ReflectT H then relint_pt_ith H else x0)
  else
    x0.

Lemma relint_ptP :
  let x := relint_pt in
  (x \in P) /\ (forall (i: 'I_m), i \notin { eq(P) on 'P(A,b) } -> (A *m x) i 0 > b i 0).
Proof.
rewrite /relint_pt; case: ifP => [ m_pos | /negbT m_eq0 ]; last first.
- split; first exact: xchooseP.
  move: m_eq0; rewrite -eqn0Ngt => /eqP m_eq0 i.
  by move: (ord0_false (cast_ord m_eq0 i)).
- have m_gt0 : m%:R > 0 :>R by rewrite ltr0n.
  split.
  + rewrite scaler_sumr; apply: poly_is_convex.
    * by move => _; apply: ltrW; rewrite invr_gt0.
    * rewrite sumr_const card_ord -[LHS]mulr_natr mulVf //.
      exact: lt0r_neq0.
    * move => i; case: {-}_/idPn => [ i_not_in_eq | _]; last exact: xchooseP.
      by move: (relint_pt_ithP i_not_in_eq) => [ ? _ ].
  + move => i i_not_in_eq.
    rewrite -scalemxAr [X in _ < X]mxE ltr_pdivl_mull // [X in X < _]mulrC mulmx_sumr summxE.
    have ->: b i 0 * m%:R = \sum_(j : 'I_m) (b i 0)
      by rewrite sumr_const card_ord -[RHS]mulr_natr.
    apply: sumr_ltrP.
    * move => j; set x := (X in _ <= (_ *m X) _ _).
      suff: x \in P by  move/(subset_base P_base); rewrite inE => /forallP/(_ i).
      rewrite /x; case : {-}_/idPn => [i_not_in_eq' | _]; last exact: xchooseP.
      by move: (relint_pt_ithP i_not_in_eq') => [? _].
    * exists i; case : {-}_/idPn => [i_not_in_eq' | i_in_eq ]; last by done.
      by move: (relint_pt_ithP i_not_in_eq') => [_].
Qed.

Definition hull :=
  (kermx (row_submx A { eq(P) on 'P(A, b)})^T).

Lemma hull_inP (d : 'cV[R]_n) : reflect (forall j : 'I__, j \in { eq (P) on 'P(A, b)} -> (A *m d) j 0 = 0) (d^T <= hull)%MS.
Proof.
apply: (equivP sub_kermxP); rewrite -trmx_mul -{1}[0]trmx0; split.
- by move/trmx_inj; rewrite -row_submx_mul => /row_submx_col0P.
- by move => ?; apply/congr1; rewrite -row_submx_mul; apply/row_submx_col0P.
Qed.

Arguments hull_inP [d].

Lemma hull_relintP (d : 'cV[R]_n) :
  reflect (exists eps, eps > 0 /\ relint_pt + eps *: d \in P) ((d^T <= hull)%MS).
Proof.
have P_eq: P =i 'P^=(A, b; {eq P}).
- move => x; move/hpoly_of_baseP : P_base => {1}->.
  by rewrite mem_quotP.
set x0 := relint_pt.
have x0_in_P : x0 \in 'P^=(A, b; {eq P})
  by rewrite -P_eq; move: relint_ptP => [?].
apply/(iffP hull_inP); last first.
- move => [eps [eps_gt0]].
  rewrite P_eq => /hpolyEq_act x_eps_eq j j_in_eq.
  move/(_ _ j_in_eq): x_eps_eq.
  rewrite mulmxDr -scalemxAr mxE [X in _ + X]mxE.
  suff ->: (A *m relint_pt) j 0 = b j 0.
  + move/(canRL (addKr _)); rewrite addNr.
    by move/(canRL (mulKf (lt0r_neq0 eps_gt0))); rewrite mulr0.
  + by apply/(hpolyEq_act _ j_in_eq).
- move => d_in_ker.
  pose I := [seq i <- (enum 'I_m) | i \notin { eq(P) on 'P(A, b) } & (A *m d) i 0 < 0].
  pose eps i := ((A *m d) i 0)^-1 * ((b i 0) - (A *m x0) i 0).
  have eps_gt0 : forall i, i \in I -> eps i > 0.
  + move => i; rewrite mem_filter => /andP [/andP [i_not_in_eq Adi_lt0] _].
    rewrite /eps ltr_ndivl_mull // mulr0 subr_lt0.
    by move: relint_ptP => [_ /(_ _ i_not_in_eq)].
  pose eps_min := min_seq [seq eps i | i <- I ] 1.
  have eps_min_gt0 : eps_min > 0.
  + rewrite min_seq_positive; last by right; exact: ltr01.
    apply/allP => x; rewrite inE => /mapP [i i_in_I ->]; exact: eps_gt0.
  exists eps_min; split; first by done.
  rewrite P_eq.
  have x_eps_eq :
    forall i, i \in { eq P on 'P(A,b)} -> (A *m (x0 + eps_min *: d)) i 0 = b i 0.
  + move => i i_in_eq. rewrite mulmxDr -scalemxAr mxE [X in _ + X]mxE.
    have ->: (A *m d) i 0 = 0 by apply: d_in_ker.
    rewrite mulr0 addr0; by apply/(hpolyEq_act _ i_in_eq).
  apply/hpolyEq_inP; split; last by done.
  rewrite inE; apply/forallP => i.
  case: (boolP (i \in { eq P on 'P(A,b) })) => [i_in_eq | i_notin_eq].
  + rewrite x_eps_eq //; exact: ltrr.
  + rewrite mulmxDr -scalemxAr mxE [X in _ + X]mxE.
  + case: (ger0P ((A *m d) i 0)) => [ Adi_ge0 | Adi_lt0].
    * apply: ler_paddr; first by rewrite pmulr_rge0.
      by move: x0_in_P => /hpolyEq_inP [/forallP ? _].
    * have i_in_I : i \in I by rewrite mem_filter i_notin_eq Adi_lt0 mem_enum.
      suff: eps_min <= eps i; last by apply: min_seq_ler; exact: map_f.
      by rewrite ler_ndivl_mull // {1}mulrC lter_sub_addl.
Qed.

Arguments hull_relintP [d].

Lemma hullP (d : 'cV[R]_n) :
  reflect (exists x y, [/\ x \in P, y \in P & ((x-y)^T :=: d^T)%MS]) (d^T <= hull)%MS.
Proof.
have P_eq: P =i 'P^=(A, b; {eq P}).
- move => x; move/hpoly_of_baseP : P_base => {1}->.
  by rewrite mem_quotP.
apply: (iffP idP); last first.
- move => [x [y [x_in_P y_in_P <-]]].
  apply/hull_inP => j j_in_eq.
  rewrite mulmxBr mxE [X in _ + X]mxE.
  move: x_in_P y_in_P; rewrite !P_eq.
  do 2![move/hpolyEq_act/( _ j_in_eq) ->]; exact: addrN.
- move/hull_relintP => [eps [eps_gt0]].
  set x_eps := (X in X \in P) => x_eps_in_P.
  exists x_eps; exists relint_pt; split; try by [done | move: relint_ptP => [?]].
  rewrite /x_eps [X in X - _ ]addrC addrK trmx_mul_scalar.
  apply: eqmx_scale; exact: lt0r_neq0.
Qed.

End Hull.

End HullBase.

Section Hull.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'poly[R]_n.

Definition hull :=
  let: 'P(A,b) := hpoly P in HullBase.hull P A b.

Hypothesis P_non_empty : non_empty P.

Lemma hull_quotP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  [P has \base 'P(A,b)] -> (hull == HullBase.hull P A b)%MS.
Proof.
move => P_base.
apply/rV_eqP => d; rewrite -[d]trmxK /hull.
case: (hpoly_splitP (hpoly P)) (hpoly_base P) => [m0 A0 b0] -> /= P_base0.
apply/(sameP (HullBase.hullP P_non_empty P_base0 d^T)).
exact: HullBase.hullP.
Qed.


Lemma hullP (d : 'cV[R]_n) :
   reflect (exists x y, [/\ x \in P, y \in P & ((x-y)^T :=: d^T)%MS]) (d^T <= hull)%MS.
Proof.
rewrite /hull; case: (hpoly_splitP (hpoly P)) (hpoly_base P) => [m0 A0 b0] -> /= P_base0.
exact: HullBase.hullP.
Qed.

Definition hull_dim := (\dim hull).

End Hull.

Section Dimension.

Variable R : realFieldType.
Variable n : nat.
