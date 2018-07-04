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
Require Import extra_misc inner_product vector_order extra_matrix row_submx exteqtype hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''poly[' R ]_ n" (at level 8, n at level 2, format "''poly[' R ]_ n").
Reserved Notation "''poly_' n" (at level 8, n at level 2).
Reserved Notation "''[' P ]" (at level 0, format "''[' P ]").
Reserved Notation "{ 'eq' P 'on' base }" (at level 0, format "{ 'eq' P  'on'  base }").
Reserved Notation "{ 'eq' P }" (at level 0, format "{ 'eq'  P }").
Reserved Notation "[ P 'has' '\base' base ]" (at level 0, format "[ P  'has'  '\base'  base ]").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section QuotDef.

Variable R : realFieldType.
Variable n : nat.

Definition canon (P : 'hpoly[R]_n) := choose (ext_eq_op P) P.

Record poly := Poly {
  hpoly : 'hpoly[R]_n;
  _ : canon hpoly == hpoly;
}.

Lemma canon_id P : canon (canon P) == canon P.
Proof.
rewrite /canon.
set P' := choose (ext_eq_op P) P.
have P_eq_P': (P ==i P') by exact: chooseP.
suff /eq_choose ->: ext_eq_op P' =1 ext_eq_op P.
- by apply/eqP; apply: choose_id.
- move => Q.
  by apply/idP/idP; apply: ext_eq_trans; last by rewrite ext_eq_sym.
Qed.

Definition class_of P := Poly (canon_id P).

End QuotDef.

Arguments hpoly [R n].
Prenex Implicits hpoly.
Notation "''poly[' R ]_ n" := (@poly R n).
Notation "''poly_' n" := ('poly[_]_n).
Notation "''[' P ]" := (class_of P).

Section QuotStruct.

Variable R : realFieldType.
Variable n : nat.

Canonical poly_subType := [subType for (@hpoly R n)].
Definition poly_eqMixin := Eval hnf in [eqMixin of 'poly[R]_n by <:].
Canonical poly_eqType := Eval hnf in EqType 'poly[R]_n poly_eqMixin.
Definition poly_choiceMixin := Eval hnf in [choiceMixin of 'poly[R]_n by <:].
Canonical poly_choiceType := Eval hnf in ChoiceType 'poly[R]_n poly_choiceMixin.
Definition mem_poly (P : 'poly[R]_n) := hpoly P : pred_class.

Lemma hpoly_inj : injective (@hpoly R n).
Proof.
exact: val_inj.
Qed.

Lemma hpolyK (P : 'poly[R]_n) : '[ hpoly P ] = P.
case: P => [P P_eq]; apply: hpoly_inj.
exact: eqP.
Qed.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpoly[R]_n -> Type :=
  HpolySpec Q of (P = '[Q]) : hpoly_spec P Q.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma poly_eqE (P Q : 'hpoly[R]_n) : ('[ P ] == '[ Q ]) = (P ==i Q).
Proof.
Admitted.

Lemma poly_eqP (P Q : 'hpoly[R]_n) : ('[ P ] = '[ Q ]) <-> (P =i Q).
Proof.
Admitted.

End QuotStruct.

Arguments hpolyP [R n].
Prenex Implicits hpolyP.
Coercion mem_poly : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

Lemma mem_quotP (P : 'hpoly[R]_n) : '[ P ] =i P.
Proof.
move => x; rewrite /mem_poly.
by case/hpolyP: '[P] => Q /poly_eqP.
Qed.

Let quotE := mem_quotP.

Definition non_empty (P : 'poly[R]_n) := (HPrim.non_empty (hpoly P)).

Lemma non_emptyP (P : 'poly[R]_n) :
  reflect (exists x, x \in P) (non_empty P).
Proof.
exact: (equivP HPrim.non_emptyP).
Qed.

Arguments non_emptyP [P].

Lemma non_empty_quotP (P : 'hpoly[R]_n) :
  non_empty '[ P ] = HPrim.non_empty P.
Proof.
apply/(sameP non_emptyP)/(equivP HPrim.non_emptyP).
by split; move => [x x_in]; exists x; rewrite ?quotE in x_in *.
Qed.

Definition is_included_in_hyperplane (P : 'poly[R]_n) c d :=
  HPrim.is_included_in_hyperplane (hpoly P) c d.

Lemma is_included_in_hyperplaneP (P : 'poly[R]_n) c d :
  reflect (forall x : 'cV_n, x \in P -> '[ c, x] = d)
          (is_included_in_hyperplane P c d).
Proof.
exact: (equivP HPrim.is_included_in_hyperplaneP).
Qed.

Arguments is_included_in_hyperplaneP [P c d].

Lemma is_included_in_hyperplane_quotP (P : 'hpoly[R]_n) c d :
  is_included_in_hyperplane '[ P ] c d = HPrim.is_included_in_hyperplane P c d.
Proof.
apply/(sameP is_included_in_hyperplaneP)/(equivP HPrim.is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite quotE.
Qed.

Definition is_included_in (P Q : 'poly[R]_n) :=
  HPrim.is_included_in (hpoly P) (hpoly Q).

Lemma is_included_inP (P Q : 'poly[R]_n) :
  reflect {subset P <= Q } (is_included_in P Q).
Admitted.

Lemma is_included_in_quotP (P Q : 'poly[R]_n) (P' Q' : 'hpoly[R]_n) :
  P = '[ P' ] -> Q = '[ Q' ] -> is_included_in P Q = HPrim.is_included_in P' Q'.
Admitted.

Variable c : 'cV[R]_n.

Definition bounded (P: 'poly[R]_n) := HPrim.bounded c (hpoly P).
Definition unbounded (P: 'poly[R]_n) := HPrim.unbounded c (hpoly P).
Definition opt_value (P: 'poly[R]_n) := HPrim.opt_value c (hpoly P).

CoInductive lp_state (P : 'poly[R]_n) : option R -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state P None false false false
| Bounded (v : R) of (exists x, x \in P /\ '[c,x] = v) * (forall x, x \in P -> v <= '[c,x]) : lp_state P (Some v) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P None true false true.

Lemma lp_stateP P :
  lp_state P (opt_value P) (non_empty P) (bounded P) (unbounded P).
Admitted.
(*
Proof. (* RK *)
unlock opt_value non_empty bounded unbounded; rewrite /HPrim.opt_value.
case: (HPrim.lp_stateP c (hpoly P)) =>
  [empty_hpoly_P | x [x_in_hpoly_P x_is_opt] | unbounded_hpoly_P].
- constructor.
  move => x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)) empty_hpoly_P.
- constructor.
  split.
  + exists x.
    split; last by done.
      by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
  + move => y.
    rewrite -{1}[P]reprK (mem_polyhedron_quotP y (hpoly P)).
    exact: x_is_opt.
- constructor.
  move => K.
  move: (unbounded_hpoly_P K) => [x ?].
  exists x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
Qed.*)

Lemma boundedP (P : 'poly[R]_n) :
  reflect (exists x, x \in P /\ (forall y, y \in P -> '[ c, x] <= '[ c, y]))
         (bounded P).
Proof.
exact: (equivP HPrim.boundedP).
Qed.

Lemma unboundedP (P : 'poly[R]_n) :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded P).
Proof.
exact: (equivP HPrim.unboundedP).
Qed.

Lemma bounded_certP P :
  non_empty P -> reflect (exists K, (forall z, z \in P -> '[c,z] >= K)) (bounded P).
Proof.
move => P_non_empty.
exact: (equivP (HPrim.bounded_certP _)).
Qed.

Lemma lp_quotE (P : 'hpoly[R]_n) :
  (non_empty '[ P ] = HPrim.non_empty P)
  * (bounded '[ P ] = HPrim.bounded c P)
  * (unbounded '[ P ] = HPrim.unbounded c P)
  * (opt_value '[ P ] = HPrim.opt_value c P).
Proof.
Admitted.

End Lift.

Arguments is_included_in_hyperplaneP [R n P c d].
Prenex Implicits is_included_in_hyperplaneP.

Section Base.

Variable R : realFieldType.
Variable n : nat.

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists I , P == '[ 'P^=(base; I) ]].

Notation "[ P 'has' '\base' base ]" := (has_base P base).

Lemma has_baseP (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  reflect (exists I, P = '[ 'P^=(base; I) ]) [P has \base base].
Proof.
exact: exists_eqP.
Qed.

Lemma repr_hpolyEq (P : 'poly[R]_n) (Q : 'hpoly[R]_n) :
  P = '[Q] -> P = '['P^=(Q; set0)].
Proof.
case: Q => [m A b] ->.
apply/poly_eqP => x; rewrite hpolyEq_inE.
suff ->: [forall j in set0, (A *m x) j 0 == b j 0]
  by rewrite andbT.
by apply/forall_inP => j; rewrite inE.
Qed.

Lemma self_base (P : 'poly[R]_n) (Q : 'hpoly[R]_n) :
  P = '[Q] -> has_base P Q.
Proof.
move/repr_hpolyEq => P_eq.
by apply/has_baseP; exists set0.
Qed.

Lemma hpoly_base (P : 'poly[R]_n) : has_base P (hpoly P).
Proof.
by apply/self_base; rewrite hpolyK.
Qed.

Definition active (P: 'poly[R]_n) base :=
  let: 'P(A,b) as base := base return {set 'I_(#ineq base)} in
  [ set i: 'I_(#ineq base) | is_included_in_hyperplane P (row i A)^T (b i 0) ].

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).

Lemma active_inP (P: 'poly[R]_n) (m: nat) (A:'M[R]_(m,n)) (b: 'cV[R]_m) i :
  reflect (forall x, x \in P -> (A *m x) i 0 = b i 0) (i \in { eq(P) on 'P(A,b) }).
Proof.
rewrite inE; apply/(equivP is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite row_vdot.
Qed.

Arguments active_inP [P m A b].
Prenex Implicits active_inP.

Lemma inclusion_on_base (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
  reflect {subset P <= Q} ({ eq Q on base } \subset { eq P on base }).
Proof. (* TODO: should follow from the relint point of P and/or Q *)
Admitted.

Variable P : 'poly[R]_n.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Hypothesis P_base : [ P has \base 'P(A,b) ].

Lemma activeP I :
  P = '['P^=(A, b; I)] -> I \subset { eq P }.
Proof.
move => P_eq.
apply/subsetP => i i_in_I; apply/active_inP => x.
rewrite P_eq mem_quotP.
by rewrite hpolyEq_inE => /andP [_ /forall_inP/(_ _ i_in_I)/eqP].
Qed.

Lemma hpoly_of_baseP : P = '[ 'P^=(A, b; { eq P }) ].
Proof.
move/has_baseP: P_base => [I P_eq_Pact].
move/activeP: (P_eq_Pact); rewrite {}P_eq_Pact.
set P' := 'P^=(A, b; I).
move => I_subset; apply/poly_eqP.
move => x; apply/idP/idP => [x_in |].
- have x_in_P': x \in '[P'] by rewrite mem_quotP.
  have x_in_Pab : x \in 'P(A, b)
    by rewrite hpolyEq_inE in x_in; move/andP: x_in => [?].
  rewrite hpolyEq_inE; rewrite x_in_Pab.
  by apply/forall_inP => i /active_inP/(_ _ x_in_P') ->.
- rewrite hpolyEq_inE => /andP [x_in_Pab /forall_inP act_eq].
  rewrite hpolyEq_inE; apply/andP; split; first by done.
  apply/forall_inP => i i_in_I.
  suff: i \in { eq '[P'] on 'P(A, b) } by exact: act_eq.
  + by move/subsetP/(_ _ i_in_I): I_subset.
Qed.

End Base.

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).
Notation "[ P 'has' '\base' base ]" := (has_base P base).

Module FaceBase.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Variable base : 'hpoly[R]_n.
Variable P : 'poly[R]_n.
Hypothesis P_base : [P has \base base].

Definition face :=
  [ pred Q : 'poly[R]_n |
    [ && non_empty Q, [ Q has \base base ]
                      & { eq P on base } \subset { eq Q on base } ]].

Definition face_empty : ~~ (non_empty P) -> face =i pred0.
Proof.
move => P_empty Q; rewrite !inE /= .
apply/negbTE; move: P_empty; apply: contra.
move => /and3P [ /non_emptyP [x x_in_Q] Q_base ].
move/(inclusion_on_base Q_base P_base) => Q_subset_P.
by apply/non_emptyP; exists x; apply: Q_subset_P.
Qed.

End Def.

Section FaceP.

Variable R : realFieldType.
Variable n : nat.

Lemma faceP (base: 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base ] -> non_empty P ->
  reflect
    (exists c, bounded c P /\ (forall x, (x \in P /\ Some '[c,x] = opt_value c P) <-> x \in Q))
    (Q \in (face base P)). (* RK *)
Proof.
case: base => [m A b] P_base P_non_empty.
apply/(iffP idP).
- move/and3P => [Q_non_empty Qbase eqP_sub_eqQ].
  pose e := (const_mx 1): 'rV[R]_(#|{ eq Q on 'P(A,b) }|).
  pose c := (e *m (row_submx A { eq Q on 'P(A, b) }))^T.
  exists c; admit.
- move/hpoly_of_baseP: P_base => P_repr.
  move => [c] [c_bounded c_opt].
  rewrite P_repr !lp_quotE in P_non_empty c_bounded *.


  rewrite lp_quotE in

Admitted.

End FaceP.

End FaceBase.

Arguments FaceBase.faceP [_ _ _ _ _ _ _].

Section Face.

Variable R : realFieldType.
Variable n : nat.

Definition face (P: 'poly[R]_n) := FaceBase.face (hpoly P) P.

Lemma face_empty (P : 'poly[R]_n) : ~~ (non_empty P) -> (face P) =i pred0.
Proof.
apply: FaceBase.face_empty; exact: hpoly_base.
Qed.

Lemma face_baseP (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] ->
  reflect ([/\ non_empty Q, has_base Q base &
                           { eq P on base } \subset { eq Q on base } ])
          (Q \in (face P)).
Proof.
move => P_base.
suff ->: (Q \in face P) = (Q \in (FaceBase.face base P)) by exact: and3P.
case: (boolP (non_empty P)) => [ P_non_empty | P_empty ].
- apply/(sameP FaceBase.faceP); try by done.
  + exact: hpoly_base.
  + exact: FaceBase.faceP.
- move/face_empty: (P_empty) ->.
  by move/FaceBase.face_empty: P_empty ->.
Qed.

Arguments face_baseP [P Q _].

Lemma faceP (P Q : 'poly[R]_n) :
  non_empty P ->
  reflect
    (exists c, bounded c P /\ (forall x, (x \in P /\ Some '[c,x] = opt_value c P) <-> x \in Q))
    (Q \in face P).
Proof.
move => P_non_empty.
apply/FaceBase.faceP; by [done | exact: hpoly_base].
Qed.

Lemma face_of_face (P Q: 'poly[R]_n) :
  Q \in (face P) -> {subset (face Q) <= (face P)}.
Proof.
move/(face_baseP (hpoly_base _)).
set base := (hpoly P).
move => [_ Q_base eqP_sub_eqQ].
move => Q' /(face_baseP Q_base) [Q'_non_empty Q'_base eqQ_sub_eqQ'].
apply/(face_baseP (hpoly_base _)); split; try by done.
by apply/(subset_trans _ eqQ_sub_eqQ').
Qed.

End Face.
