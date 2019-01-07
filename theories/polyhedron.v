(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx exteqtype simplex hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''poly[' R ]_ n" (at level 8, n at level 2, format "''poly[' R ]_ n").
Reserved Notation "''poly_' n" (at level 8, n at level 2).
Reserved Notation "''[' P ]" (at level 0, format "''[' P ]").
Reserved Notation "{ 'eq' P 'on' base }" (at level 0, format "{ 'eq' P  'on'  base }").
Reserved Notation "{ 'eq' P }" (at level 0, format "{ 'eq'  P }").
Reserved Notation "[ P 'has' '\base' base ]" (at level 0, format "[ P  'has'  '\base'  base ]").
Reserved Notation "[ 'poly' v ]" (at level 0, v at level 99, format "[ 'poly'  v ]").
Reserved Notation "\face P " (at level 50, format "\face  P").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section QuotDef.

Variable R : realFieldType.
Variable n : nat.

Definition canon (hP : 'hpoly[R]_n) :=
  choose (ext_eq_op hP) hP.

Record poly := Poly {
  hpoly : 'hpoly[R]_n;
  _ : canon hpoly == hpoly;
}.

Lemma canon_id hP :
  canon (canon hP) == canon hP.
Proof.
rewrite /canon.
set hQ := choose (ext_eq_op hP) hP.
have hP_eq_hQ: (hP ==i hQ) by exact: chooseP.
suff /eq_choose ->: ext_eq_op hQ =1 ext_eq_op hP
  by apply/eqP; apply: choose_id.
move => hR.
by apply/idP/idP; apply: ext_eq_trans; last by rewrite ext_eq_sym.
Qed.

Definition class_of hP := Poly (canon_id hP).

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

Lemma hpoly_inj :
  injective (@hpoly R n).
Proof.
exact: val_inj.
Qed.

Lemma hpolyK (P : 'poly[R]_n) :
  '[hpoly P] = P.
Proof.
case: P => [P P_eq]; apply: hpoly_inj.
exact: eqP.
Qed.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpoly[R]_n -> Type :=
  HpolySpec hQ of (P = '[hQ]) : hpoly_spec P hQ.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma poly_eqE (hP hQ : 'hpoly[R]_n) :
  ('[hP] == '[hQ]) = (hP ==i hQ).
Proof. (* RK: to be improved? *)
apply/idP/idP => [/eqP eq_classes | hP_eq_hQ].
- have canonhP : canon (hpoly '[hP]) = (hpoly '[hP])
    by exact: (eqP (canon_id hP)).
  have canonhQ : canon (hpoly '[hQ]) = (hpoly '[hQ])
    by exact: (eqP (canon_id hQ)).
  rewrite [in LHS]eq_classes canonhQ /= in canonhP.
  have: hQ ==i canon hQ
    by rewrite /canon; apply/chooseP.
  rewrite canonhP ext_eq_sym.
  apply: ext_eq_trans.
  by rewrite /canon; apply/chooseP.
- have H: ext_eq_op hQ =1 ext_eq_op hP
    by move => hR; apply/idP/idP; apply: ext_eq_trans; [done | rewrite ext_eq_sym].
  apply/eqP; apply: hpoly_inj.
  rewrite /= /canon (eq_choose H).
  by apply: choose_id.
Qed.

Lemma poly_eqP (hP hQ : 'hpoly[R]_n) :
  ('[hP] = '[hQ]) <-> (hP =i hQ).
Proof. (* RK: to be improved? *)
split.
- by move/eqP; rewrite poly_eqE; apply/HPrim.hpoly_ext_eqP.
- move/HPrim.hpoly_ext_eqP => ?.
  by apply/eqP; rewrite poly_eqE.
Qed.

End QuotStruct.

Arguments hpolyP [R n].
Prenex Implicits hpolyP.
Coercion mem_poly : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

Lemma mem_quotP (hP : 'hpoly[R]_n) :
  '[hP] =i hP.
Proof.
move => x; rewrite /mem_poly.
by case/hpolyP: '[hP] => hQ /poly_eqP.
Qed.

Let quotE := mem_quotP.

Definition non_empty (P : 'poly[R]_n) :=
  (HPrim.non_empty (hpoly P)).

Lemma non_emptyP (P : 'poly[R]_n) :
  reflect (exists x, x \in P) (non_empty P).
Proof.
exact: HPrim.non_emptyP.
Qed.

Arguments non_emptyP [P].
Prenex Implicits non_emptyP.

Lemma non_emptyPn (P : 'poly[R]_n) :
  reflect (P =i pred0) (~~ (non_empty P)).
Proof.
exact: HPrim.non_emptyPn.
Qed.

Arguments non_emptyPn [P].

Lemma non_empty_quotP (hP : 'hpoly[R]_n) :
  non_empty '[hP] = HPrim.non_empty hP.
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

Lemma is_included_in_hyperplane_quotP (hP : 'hpoly[R]_n) c d :
  is_included_in_hyperplane '[hP] c d = HPrim.is_included_in_hyperplane hP c d.
Proof.
apply/(sameP is_included_in_hyperplaneP)/(equivP HPrim.is_included_in_hyperplaneP).
by split; move => Hsubset x; move/(_ x): Hsubset; rewrite quotE.
Qed.

Definition is_included_in (P Q : 'poly[R]_n) :=
  HPrim.is_included_in (hpoly P) (hpoly Q).

Lemma is_included_inP (P Q : 'poly[R]_n) :
  reflect {subset P <= Q} (is_included_in P Q).
Proof.
exact: (equivP (HPrim.is_included_inP (hpoly P) (hpoly Q))).
Qed.

Arguments is_included_inP [P Q].

Lemma is_included_in_quotP (P Q : 'poly[R]_n) (hP hQ : 'hpoly[R]_n) :
  P = '[hP] -> Q = '[hQ] -> is_included_in P Q = HPrim.is_included_in hP hQ.
Proof.
move => PeqClasshP QeqClasshQ.
apply/(sameP is_included_inP)/(equivP (HPrim.is_included_inP hP hQ)).
by split; move => Hsubset x; move/(_ x): Hsubset; rewrite PeqClasshP QeqClasshQ 2!quotE.
Qed.

Lemma contains_non_empty (P Q : 'poly[R]_n) :
  non_empty P -> is_included_in P Q -> non_empty Q. (* RK *)
Proof.
move/non_emptyP => [x x_in_P].
move/is_included_inP => P_is_included_in_Q.
apply/non_emptyP.
exists x.
by apply/P_is_included_in_Q.
Qed.

Lemma empty_is_contained (P Q : 'poly[R]_n) :
  ~~ non_empty P -> is_included_in P Q. (* RK *)
Proof.
move/non_emptyPn => P_empty.
by apply/is_included_inP => x; rewrite P_empty inE.
Qed.

Lemma is_included_in_refl (P : 'poly[R]_n) :
  is_included_in P P. (* RK *)
Proof.
by apply/is_included_inP.
Qed.

Lemma is_included_in_trans (P Q S : 'poly[R]_n) :
  is_included_in P Q -> is_included_in Q S ->
    is_included_in P S. (* RK *)
Proof.
move => /is_included_inP P_incl_Q /is_included_inP Q_incl_R.
apply/is_included_inP => x.
by move/P_incl_Q/Q_incl_R.
Qed.

Variable c : 'cV[R]_n.

Definition bounded (P : 'poly[R]_n) := HPrim.bounded c (hpoly P).
Definition unbounded (P : 'poly[R]_n) := HPrim.unbounded c (hpoly P).
Definition opt_value (P : 'poly[R]_n) (H: bounded P) := HPrim.opt_value H.

CoInductive lp_state (P : 'poly[R]_n) : bool -> bool -> bool -> Prop :=
| Empty of P =i pred0 : lp_state P false false false
| Bounded of (exists x, { over P, x minimizes c }) : lp_state P true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P true false true.

Lemma lp_stateP P :
  lp_state P (non_empty P) (bounded P) (unbounded P).
Proof. (* RK *)
rewrite /opt_value /non_empty /bounded /unbounded.
case: (HPrim.lp_stateP c (hpoly P))
  => [empty_hP | [z] [z_in_hP z_is_opt] | unbounded_hP];
    constructor; try by [ done | exists z].
Qed.

Lemma boundedP (P : 'poly[R]_n) :
  reflect (exists x, { over P, x minimizes c })
         (bounded P).
Proof.
exact: (equivP HPrim.boundedP).
Qed.

Arguments boundedP [P].

Lemma bounded_quotP (hP : 'hpoly[R]_n) :
  bounded '[hP] = HPrim.bounded c hP. (* RK *)
Proof.
apply/(sameP boundedP)/(equivP HPrim.boundedP).
by split; move => [x [x_in x_is_opt]]; exists x; split;
  [rewrite quotE | move => y; rewrite quotE; exact: (x_is_opt y) |
    rewrite -quotE | move => y; rewrite -quotE; exact: (x_is_opt y)].
Qed.

Lemma opt_valueP (P : 'poly[R]_n) (H: bounded P) x :
  reflect ({ over P, x minimizes c }) ((x \in P) && ('[c,x] == opt_value H)).
Proof.
exact: HPrim.opt_valueP.
Qed.

Lemma bounded_lower_bound P :
  non_empty P -> reflect (exists K, (forall z, z \in P -> '[c,z] >= K)) (bounded P).
Proof.
move => P_non_empty.
exact: HPrim.bounded_lower_bound.
Qed.

Lemma bounded_opt_value P (H: bounded P) :
  (exists x, x \in P /\ '[c,x] = opt_value H) /\ (forall y, y \in P -> '[c,y] >= opt_value H).
Proof.
exact: HPrim.bounded_opt_value.
Qed.

Lemma opt_value_quotP (hP : 'hpoly[R]_n) (H: bounded '[hP]) (hH: HPrim.bounded c hP) :
  opt_value H = HPrim.opt_value hH.
Proof.
move: (bounded_opt_value H) => [[x [x_in_P <-]] x_is_opt].
move: (HPrim.bounded_opt_value hH) => [[y [y_in_P <-]] y_is_opt].
apply/eqP; rewrite eqr_le; apply/andP; split.
- by apply: x_is_opt; rewrite mem_quotP.
- by apply: y_is_opt; rewrite mem_quotP in x_in_P.
Qed.

Lemma unboundedP (P : 'poly[R]_n) :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded P).
Proof.
exact: (equivP HPrim.unboundedP).
Qed.

Arguments unboundedP [P].

Lemma unbounded_quotP (hP : 'hpoly[R]_n) :
  unbounded '[hP] = HPrim.unbounded c hP. (* RK *)
Proof.
apply/(sameP unboundedP)/(equivP HPrim.unboundedP).
by split; move => unbounded K; move: (unbounded K) => [x [x_in val_x]];
  exists x; [rewrite quotE | rewrite -quotE].
Qed.

Lemma lp_quotE (hP : 'hpoly[R]_n) : (* TODO: fix the dependency in c issue *)
  (non_empty '[hP] = HPrim.non_empty hP)
  * (bounded '[hP] = HPrim.bounded c hP)
  * (unbounded '[hP] = HPrim.unbounded c hP).
Proof.
by rewrite non_empty_quotP bounded_quotP unbounded_quotP.
Qed.

Lemma minimize_quotP (hP : 'hpoly[R]_n) x :
  { over '[hP], x minimizes c } <-> { over hP, x minimizes c }.
Proof.
split; rewrite mem_quotP; move => [x_in_P x_opt]; split;
  by [ done | move => y y_in_P; apply: x_opt; rewrite mem_quotP in y_in_P * ].
Qed.

End Lift.

Arguments is_included_in_hyperplaneP [R n P c d].
Prenex Implicits is_included_in_hyperplaneP.
Arguments non_emptyP [R n P].
Prenex Implicits non_emptyP.

Section PolyPoint.

Variable R : realFieldType.
Variable n : nat.

Definition pick_point (P : 'poly[R]_n) :=
  match (@non_emptyP _ _ P) with
  | ReflectT P_non_empty => xchoose P_non_empty
  | ReflectF _ => 0
  end.

Lemma pick_pointP P : non_empty P -> pick_point P \in P.
Admitted.

Definition poly_point (v : 'cV[R]_n) := '[ [hpoly v] ].

Notation "[ 'poly' v ]" := (poly_point v).

Lemma poly_point_inE (v x : 'cV[R]_n) :
  (x \in [poly v]) = (x == v).
Admitted.

Lemma poly_point_inP (v x : 'cV[R]_n) :
  reflect (x = v) (x \in [poly v]).
Admitted.

End PolyPoint.

Notation "[ 'poly' v ]" := (poly_point v).

Section Base.

Variable R : realFieldType.
Variable n : nat.

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists I , P == '['P^=(base; I)]].

Notation "[ P 'has' '\base' base ]" := (has_base P base).

Lemma has_baseP (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  reflect (exists I, P = '[ 'P^=(base; I) ]) [P has \base base].
Proof.
exact: exists_eqP.
Qed.

Lemma hpolyEq_base (base: 'hpoly[R]_n) I :
  [ '['P^=(base; I)] has \base base ].
Proof.
by apply/has_baseP; exists I.
Qed.

Lemma repr_hpolyEq (P : 'poly[R]_n) (hP : 'hpoly[R]_n) :
  P = '[hP] -> P = '['P^=(hP; set0)].
Proof.
case: hP => [m A b] ->.
apply/poly_eqP => x; rewrite hpolyEq_inE.
suff ->: [forall j in set0, (A *m x) j 0 == b j 0]
  by rewrite andbT.
by apply/forall_inP => j; rewrite inE.
Qed.

Lemma self_base (P : 'poly[R]_n) (hP : 'hpoly[R]_n) :
  P = '[hP] -> [P has \base hP].
Proof.
move/repr_hpolyEq => P_eq.
by apply/has_baseP; exists set0.
Qed.


Lemma hpoly_base (P : 'poly[R]_n) :
  [P has \base (hpoly P)].
Proof.
by apply/self_base; rewrite hpolyK.
Qed.

Lemma subset_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [ P has \base base ] -> { subset P <= base }.
Proof.
move/has_baseP => [I ->] x.
rewrite mem_quotP; exact: hpolyEq_antimono0.
Qed.

Definition active (P : 'poly[R]_n) base :=
  let: 'P(A,b) as base := base return {set 'I_(#ineq base)} in
    [ set i: 'I_(#ineq base) | is_included_in_hyperplane P (row i A)^T (b i 0) ].

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).

Section ActiveInP.

Variable P : 'poly[R]_n.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Lemma active_inP i :
reflect (forall x, x \in P -> (A *m x) i 0 = b i 0) (i \in { eq(P) on 'P(A,b) }).
Proof.
rewrite inE; apply/(equivP is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite row_vdot.
Qed.

End ActiveInP.

Arguments active_inP [P m A b].
Prenex Implicits active_inP.

Section ActiveInPn.

Variable P : 'poly[R]_n.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis P_base : [P has \base 'P(A,b)].

Lemma active_inPn i :
  reflect (exists x, x \in P /\ (A *m x) i 0 > b i 0) (i \notin { eq(P) on 'P(A,b) }).
Proof.
apply: (iffP idP); last first.
- move => [x [x_in_P Ai_x_gt_bi]]; apply/negP; move/active_inP/(_ _ x_in_P) => Ai_x_eq_bi.
  by move: Ai_x_gt_bi; rewrite Ai_x_eq_bi ltrr.
- move => i_not_active; set Ai := (row i A)^T.
  case: (lp_stateP (-Ai) P)
  => [P_empty | [x [x_in_P x_opt]] | /(_ (- (b i 0))) [x [x_in_P Ai_x_gt_bi]]].
  + suff: (i \in {eq P on 'P(A,b)}) by move/negP: i_not_active.
    by apply/active_inP => x; rewrite P_empty inE.
  + exists x; split; first by done.
    move: i_not_active; apply: contraR.
    rewrite -lerNgt => Ai_x_le_bi.
    move/has_baseP: P_base => [I P_eq_PAbI].
    apply/active_inP => y y_in_P.
    apply/eqP; rewrite eqr_le; apply/andP; split; last first.
    * by move: y_in_P; rewrite P_eq_PAbI mem_quotP => /hpolyEq_inP [/forallP].
    * move: Ai_x_le_bi; move/(_ _ y_in_P): x_opt.
      rewrite !vdotNl !row_vdot ler_opp2; exact: ler_trans.
  + exists x; split; first by done.
    by rewrite !vdotNl !row_vdot ltr_opp2 in Ai_x_gt_bi.
Qed.

End ActiveInPn.

Section ActiveP.

Variable P : 'poly[R]_n.

Lemma activeP (base : 'hpoly[R]_n) I :
  P = '['P^=(base; I)] -> I \subset { eq P }.
Proof.
case: base I => [m A b] I P_eq.
apply/subsetP => i i_in_I; apply/active_inP => x.
rewrite P_eq mem_quotP.
by rewrite hpolyEq_inE => /andP [_ /forall_inP/(_ _ i_in_I)/eqP].
Qed.

Lemma hpoly_of_baseP (base : 'hpoly[R]_n) :
  [P has \base base] -> P = '[ 'P^=(base; { eq P }) ].
Proof.
case: base => [m A b] P_base.
move/has_baseP : (P_base) => [I P_eq_Pact].
move/activeP : (P_eq_Pact); rewrite {}P_eq_Pact.
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

End ActiveP.

Arguments activeP [P base I].
Prenex Implicits activeP.
Arguments hpoly_of_baseP [P base].
Prenex Implicits hpoly_of_baseP.

Section InclusionOnBase.
  Lemma inclusion_on_base (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
  reflect {subset P <= Q} ({ eq Q on base } \subset { eq P on base }).
Proof.
case: base => m A b P_base Q_base;
rewrite {1}(hpoly_of_baseP P_base) {1}(hpoly_of_baseP Q_base).
apply: (iffP idP) => [eqQ_sub_eqP| incl].
- suff incl: {subset 'P^=(A, b; {eq P}) <= 'P^=(A, b; {eq Q})}.
  move => x; rewrite !mem_quotP; exact: incl. (* TODO: same here, takes a long time to rewrite *)
  exact: hpolyEq_antimono.
- apply/subsetP => i; apply: contraLR.
  move/(active_inPn P_base) => [x [x_in_P Ai_x_gt_bi]].
  apply/(active_inPn Q_base); exists x; split; last by done.
  rewrite (hpoly_of_baseP Q_base); apply: incl.
  by rewrite (hpoly_of_baseP P_base) in x_in_P.
Qed.

End InclusionOnBase.

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

Definition face_set :=
  ([fset '['P^=(base; I)] | I : {set 'I_(#ineq base)} & (({ eq P on base } \subset I) && non_empty '['P^=(base; I)])])%fset : {fset 'poly[R]_n}.

Definition face_empty : ~~ (non_empty P) -> face_set = fset0.
Proof.
move => P_empty; apply/fsetP => /= Q; rewrite in_fsetE /=.
apply/negbTE; move: P_empty; apply: contra.
move/imfsetP => /= [I] /andP [eqP_sub_I /non_emptyP [x x_in_Q]] _.
suff Q_subset_P: {subset '['P^=(base; I)] <= P} by apply/non_emptyP; exists x; apply: Q_subset_P.
apply/(inclusion_on_base (base := base)); try by done.
- exact: hpolyEq_base.
- by apply/(subset_trans eqP_sub_I)/activeP.
Qed.

End Def.

Section FaceP.

Variable R : realFieldType.
Variable n : nat.

Lemma faceP (base: 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base ] -> non_empty P ->
  reflect
    (exists c, bounded c P /\ (forall x, { over P, x minimizes c } <-> x \in Q))
    (Q \in (face_set base P)).
Proof.
case: base => [m A b] P_base P_non_empty.
apply/(iffP idP).
- move/imfsetP => [J] /and3P [_ eqP_sub_J Q_non_empty] Q_repr.
  move/hpoly_of_baseP: P_base => P_repr.
  rewrite {}P_repr non_empty_quotP in P_non_empty *.
  rewrite non_empty_quotP in Q_non_empty *.
  set I := ({eq P}) in eqP_sub_J *.

  pose u := col_mx (\col_i (if i \in J then 1 else 0)) 0: 'cV[R]_(m+#|I|).
  have u_ge0 : u >=m 0.
  + rewrite col_mx_gev0 lev_refl andbT.
    apply/gev0P => i; rewrite mxE.
    case: ifP => [_|_]; [exact: ler01 | exact: lerr].
  have u_i_gt0 : forall i, (u (lshift #|I| i) 0 > 0) = (i \in J).
  + move => i; rewrite col_mxEu mxE.
    case: ifP => [_|_]; [exact: ltr01 | exact: ltrr].

  pose AI := col_mx A (-(row_submx A I)).
  pose bI := col_mx b (-(row_submx b I)).
  pose c := AI^T *m u; exists c.
  have c_bounded : HPrim.bounded c 'P^=(A, b; I) by exact: HPrim.normal_cone_bounded.

  have opt_val: HPrim.opt_value c_bounded = '[bI, u].
  move/HPrim.bounded_opt_value: (c_bounded) => [[x [x_in_P <-]] x_opt].
  apply/eqP; rewrite eqr_le; apply/andP; split; last first.
    * exact: HPrim.normal_cone_lower_bound.
    * move/HPrim.non_emptyP: Q_non_empty => [y y_in_Q].
      suff <-: '[c,y] = '[bI,u].
      - apply: x_opt; exact: (hpolyEq_antimono eqP_sub_J).
      - rewrite -vdot_mulmx mul_col_mx !vdot_col_mx vdot0l vdot0r !addr0.
        apply: eq_bigr => i _; rewrite mxE.
        case: ifP => [ i_in_J | _]; last by rewrite mulr0 mul0r.
        rewrite mul1r mulr1; exact: (hpolyEq_act y_in_Q).
  split; first by rewrite lp_quotE.
  move => x; split.
  + move/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    move/andP => [x_in_PAbI].
    move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_csc.
    rewrite Q_repr mem_quotP; apply/hpolyEq_inP.
    split; first exact: (hpolyEq_antimono0 x_in_PAbI).
    move => j; rewrite -u_i_gt0; move/x_csc.
    by rewrite mul_col_mx !col_mxEu => ->.
  + rewrite Q_repr mem_quotP; move => x_in_PAbJ. (* TODO: the rewrite mem_quotP takes time, why? *)
    apply/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    have x_in_PAbI : x \in 'P^=(A, b; I) by exact: (hpolyEq_antimono eqP_sub_J).
    apply/andP; split; first by done.
    apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i; rewrite mxE.
      case: (splitP' i) => [i' -> |?]; rewrite mxE; last by rewrite ltrr.
      case: ifP => [i'_in_J _ | ?]; last by rewrite ltrr.
      rewrite mul_col_mx !col_mxEu; exact: (hpolyEq_act x_in_PAbJ).

- move/hpoly_of_baseP: P_base => P_repr.
  move => [c] [c_bounded c_opt].
  (*apply/andP; split.
  + *)
  set I := ({eq P}) in P_repr *. (* TODO: parsing error if parenthesis are removed *)
  suff: exists (J: {set 'I_(#ineq 'P(A, b))}), (I \subset J /\ Q = '['P^=(A, b; J)]).
  + move => [J] [I_sub_J Q_eq_PabJ].
    apply/imfsetP; exists J; last by done.
    rewrite /= inE; apply/andP; split; first by done.
    move/boundedP: c_bounded => [x /c_opt x_in_Q].
    by rewrite -Q_eq_PabJ; apply/non_emptyP; exists x.
  + rewrite P_repr non_empty_quotP !lp_quotE in P_non_empty c_bounded c_opt.
    move/HPrim.dual_opt_sol: (c_bounded) => [u] [u_ge0 c_eq c_optval].
    pose J := I :|: [set i | (usubmx u) i 0 > 0].
    exists J; split; first exact: subsetUl.
    suff PAbJ_eq_Q : 'P^=(A, b; J) =i Q. (* we should introduce a lemma for that: P = '[Q] <-> P =i Q *)
    * case: (hpolyP Q) => [Q' Q_eq_Q'].
      rewrite Q_eq_Q'; apply/poly_eqP => x.
      by rewrite PAbJ_eq_Q Q_eq_Q' mem_quotP.
    * move => x; apply/idP/idP => [x_in_PAbJ | x_in_Q].
      - have x_in_PAbI : x \in 'P^=(A, b; I).
        move: x_in_PAbJ; apply/hpolyEq_antimono; exact: subsetUl.
        apply/c_opt/minimize_quotP/HPrim.opt_valueP/andP; split; first by done.
        rewrite -c_optval c_eq; apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i.
        case: (splitP' i) => [j -> | j -> _].
        + rewrite -[u]vsubmxK mul_col_mx !col_mxEu => u_j_gt0.
          have j_in_J : (j \in J) by rewrite !inE; apply/orP; right.
          exact: (hpolyEq_act x_in_PAbJ).
        + rewrite mul_col_mx !col_mxEd mulNmx -row_submx_mul.
          rewrite 2![in LHS]mxE 2![in RHS]mxE.
          apply: congr1; apply: (hpolyEq_act x_in_PAbI); exact: enum_valP.
      - move/c_opt/minimize_quotP/(HPrim.opt_valueP c_bounded)/andP: x_in_Q => [x_in_PAbI].
        rewrite {1}c_eq -c_optval; move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_act.
        apply/hpolyEq_inP; split; first exact: (hpolyEq_antimono0 x_in_PAbI).
        move => j; rewrite inE; case/orP => [j_in_I | u_j_gt0].
        + exact: (hpolyEq_act x_in_PAbI).
        + rewrite inE mxE in u_j_gt0.
          by move/(_ _ u_j_gt0): x_act; rewrite mul_col_mx !col_mxEu.
Qed.

End FaceP.

End FaceBase.

Arguments FaceBase.faceP [_ _ _ _ _].

Section Face.

Variable R : realFieldType.
Variable n : nat.

Definition face_set (P: 'poly[R]_n) := FaceBase.face_set (hpoly P) P.

Notation "\face P" := (face_set P).

Lemma face_empty (P : 'poly[R]_n) : ~~ (non_empty P) -> \face P = fset0.
Proof.
apply: FaceBase.face_empty; exact: hpoly_base.
Qed.

Lemma face_baseP (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] ->
  reflect ([/\ has_base Q base, { eq P on base } \subset { eq Q on base } & non_empty Q ])
          (Q \in \face P).
Proof.
move => P_base.
suff ->: (Q \in \face P) = (Q \in (FaceBase.face_set base P)).
- apply: (iffP idP).
  + move/imfsetP => [J] /and3P [_ eqP_sub_J Q_non_empty] ->; split; last by done.
    * exact: hpolyEq_base.
    * by apply: (subset_trans eqP_sub_J); apply: activeP.
  + move => [Q_base eqP_sub_eqQ Q_non_empty].
    apply/imfsetP; exists {eq Q on base}; last exact: hpoly_of_baseP.
    * by rewrite inE /=; apply/andP; split; last by rewrite -hpoly_of_baseP.
case: (boolP (non_empty P)) => [ P_non_empty | P_empty ].
- apply/(sameP (FaceBase.faceP (hpoly_base _) P_non_empty)); try by done.
  + exact: FaceBase.faceP.
- move/face_empty: (P_empty) ->.
  by move/FaceBase.face_empty: P_empty ->.
Qed.

Arguments face_baseP [P Q _].

Lemma faceP (P Q : 'poly[R]_n) :
  non_empty P ->
  reflect
    (exists c, bounded c P /\ (forall x, { over P, x minimizes c } <-> x \in Q))
    (Q \in \face P).
Proof.
move => P_non_empty.
apply/FaceBase.faceP; by [done | exact: hpoly_base].
Qed.

Lemma face_of_face (P Q: 'poly[R]_n) :
  Q \in (\face P) -> (\face Q `<=` \face P)%fset.
Proof.
move/(face_baseP (hpoly_base _)).
set base := (hpoly P).
move => [Q_base eqP_sub_eqQ _].
apply/fsubsetP => Q' /(face_baseP Q_base) [Q'_base eqQ_sub_eqQ' Q'_non_empty].
apply/(face_baseP (hpoly_base _)); split; try by done.
by apply/(subset_trans _ eqQ_sub_eqQ').
Qed.

Fact self_face (P : 'poly[R]_n) :
  non_empty P -> P \in \face P. (* RK *)
Proof.
move => P_non_empty; apply/(face_baseP (hpoly_base P)); split;
  by [ exact: hpoly_base | exact: subxx | done].
Qed.

Fact face_subset (P Q : 'poly[R]_n) :
  Q \in \face P -> {subset Q <= P}. (* RK *)
Proof.
move/(face_baseP (hpoly_base P)) => [[Q_has_base ?] _].
by apply: (inclusion_on_base Q_has_base (hpoly_base P)).
Qed.

Fact face_of_face_incl_rel (P F F' : 'poly[R]_n) :
  F \in \face P ->
    ((F' \in \face F) = ((F' \in \face P) && (is_included_in F' F))). (* RK *)
Proof.
move => F_is_face_of_P.
apply/idP/idP => [F'_is_face_of_F | /andP [F'_is_face_of_P /is_included_inP F'_is_included_in_F]].
- apply/andP; split.
  + by move/fsubsetP/(_ _ F'_is_face_of_F): (face_of_face F_is_face_of_P).
  + apply/is_included_inP.
    exact: (face_subset F'_is_face_of_F).
- move/(face_baseP (hpoly_base P)): F_is_face_of_P => [F_base eq_P_subset_eq_F F_non_empty].
  move/(face_baseP (hpoly_base P)): F'_is_face_of_P => [F'_base eq_P_subset_eq_F' F'_non_empty].
  apply/(face_baseP F_base).
  split.
  + exact: F'_base.
  + by apply/(inclusion_on_base F'_base F_base).
  + exact: F'_non_empty.
Qed.

Fact has_face_imp_non_empty (P Q : 'poly[R]_n) :
  Q \in \face P -> non_empty P. (* RK *)
Proof.
move => Q_is_face_of_P.
apply: contraT => empty_P.
by rewrite (face_empty empty_P) in Q_is_face_of_P.
Qed.

Fact face_is_non_empty (P Q : 'poly[R]_n) :
  Q \in \face P -> non_empty Q. (* RK *)
Proof.
move => Q_is_face_of_P.
by move: (face_baseP (hpoly_base P) Q_is_face_of_P) => [_ _ ?].
Qed.

Variable P : 'poly[R]_n.
Variable c : 'cV[R]_n.
Hypothesis c_bounded : bounded c P.

Definition face_of_obj := (* this should be defined by using a proper intersection operation *)
  let: 'P(A, b) := hpoly P in
  let A' := col_mx c^T A in
  let b' := col_mx ((opt_value c_bounded)%:M) b in
  '[ 'P^=(A', b'; [set ord0]) ].

Fact face_of_objP x :
  reflect ({ over P, x minimizes c }) (x \in face_of_obj).
Admitted.

Arguments face_of_objP [x].

Hypothesis P_non_empty : non_empty P.

Lemma face_of_obj_face : face_of_obj \in \face P.
Proof.
apply/faceP; first by done.
exists c; split; first by done.
move => x; exact: (rwP face_of_objP).
Qed.

End Face.

Notation "\face P" := (face_set P).

Section Compactness.

Variable R : realFieldType.
Variable n : nat.

Implicit Type P F : 'poly[R]_n.

Definition compact P := (non_empty P) ==> ([forall i, bounded (delta_mx i 0) P && bounded (-(delta_mx i 0)) P]).

Lemma compactP_Linfty P :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Proof.
Admitted.

Lemma compactP P :
  reflect (forall c, bounded c P) (compact P).
Admitted.

Lemma compact_face P F :
  compact P -> F \in \face P -> compact F.
Admitted.

End Compactness.

Module PointednessBase.

Section Pointedness.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'poly[R]_n.
Variable base : 'hpoly[R]_n.

Hypothesis P_base : [P has \base base].

Definition feasible_dir (d: 'cV[R]_n) := false.
(*  let: 'P(A, _) := base in HPrim.feasible_dir A d.*)

Lemma feasible_dirP d :
  reflect (forall x, forall λ, x \in P -> λ >= 0 -> x + λ *: d \in P) (feasible_dir d).
Admitted.

End Pointedness.

End PointednessBase.

Arguments non_emptyP [R n P].
