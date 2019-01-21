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
Require Import extra_misc inner_product vector_order extra_matrix row_submx exteqtype simplex hpolyhedron convex_hull.

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

Definition is_properly_included_in (P Q : 'poly[R]_n) :=
  (is_included_in P Q) && (~~ (is_included_in Q P)).

Lemma is_properly_included_inP (P Q : 'poly[R]_n) :
  reflect (is_included_in P Q /\ (exists2 x, x \in Q & x \notin P)) (is_properly_included_in P Q).
Admitted.

Lemma is_prop_included_inP (P Q : 'poly[R]_n) :
  reflect {subset P <= Q} (is_included_in P Q).
Proof.
exact: (equivP (HPrim.is_included_inP (hpoly P) (hpoly Q))).
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
Definition opt_value (P : 'poly[R]_n) (H : bounded P) := HPrim.opt_value H.
Definition pointed (P : 'poly[R]_n) := HPrim.pointed (hpoly P). (* RK *)
Definition feasible_dir (d : 'cV[R]_n) (P : 'poly[R]_n) := HPrim.feasible_dir d (hpoly P). (* RK *)

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

Lemma opt_valueP (P : 'poly[R]_n) (H : bounded P) x :
  reflect ({ over P, x minimizes c }) ((x \in P) && ('[c,x] == opt_value H)).
Proof.
exact: HPrim.opt_valueP.
Qed.

Lemma bounded_lower_bound P :
  non_empty P ->
    reflect (exists K, (forall z, z \in P -> '[c,z] >= K)) (bounded P).
Proof.
move => P_non_empty.
exact: HPrim.bounded_lower_bound.
Qed.

Lemma bounded_opt_value P (H : bounded P) :
  (exists x, x \in P /\ '[c,x] = opt_value H) /\ (forall y, y \in P -> '[c,y] >= opt_value H).
Proof.
exact: HPrim.bounded_opt_value.
Qed.

Lemma opt_value_quotP (hP : 'hpoly[R]_n) (H : bounded '[hP]) (hH : HPrim.bounded c hP) :
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

Lemma feasible_dirP d (P : 'poly[R]_n) :
  non_empty P ->
    reflect (forall x, forall λ, x \in P -> λ >= 0 -> x + λ *: d \in P) (feasible_dir d P). (* RK *)
Proof.
exact: HPrim.feasible_dirP.
Qed.

Arguments feasible_dirP [d P].

Lemma feasible_dir_quotP (d : 'cV[R]_n) (hP : 'hpoly[R]_n) :
  HPrim.non_empty hP ->
    feasible_dir d '[hP] = HPrim.feasible_dir d hP. (* RK *)
Proof.
move => non_empty_hP.
have non_empty_hpoly_P: HPrim.non_empty (hpoly '[hP]).
  by rewrite -non_empty_quotP in non_empty_hP.
apply/idP/idP => [/(HPrim.feasible_dirP _ non_empty_hpoly_P) ray_incl | /(HPrim.feasible_dirP _ non_empty_hP) ray_incl].
- apply/(HPrim.feasible_dirP _ non_empty_hP) => x λ x_in_hP λ_eq_0.
  rewrite -mem_quotP; rewrite -mem_quotP in x_in_hP.
  exact: (ray_incl x λ x_in_hP λ_eq_0).
- apply/(HPrim.feasible_dirP _ non_empty_hpoly_P) => x λ x_in_hP λ_eq_0.
  rewrite mem_quotP; rewrite mem_quotP in x_in_hP.
  exact: (ray_incl x λ x_in_hP λ_eq_0).
Qed.

Lemma pointedPn (P : 'poly[R]_n) :
  reflect (exists d, [/\ d != 0, feasible_dir d P & feasible_dir (-d) P]) (~~pointed P). (* RK *)
Proof.
exact: HPrim.pointedPn.
Qed.

Arguments pointedPn [P].

Lemma pointed_quotP (hP : 'hpoly[R]_n) :
  HPrim.non_empty hP ->
    pointed '[hP] = HPrim.pointed hP. (* RK *)
Proof.
move => non_empty_hP.
by apply/idP/idP; apply/contraTT; move/HPrim.pointedPn => [d [d_neq_0 feasible_dir_d feasible_dir_minus_d]];
  [apply/pointedPn | apply/HPrim.pointedPn]; exists d; split; rewrite ?feasible_dir_quotP //;
    rewrite -feasible_dir_quotP.
Qed.

End Lift.

Arguments is_included_inP [R n P Q].
Prenex Implicits is_included_inP.
Arguments is_included_in_hyperplaneP [R n P c d].
Prenex Implicits is_included_in_hyperplaneP.
Arguments non_emptyP [R n P].
Prenex Implicits non_emptyP.

Section PolyProp.

Variable R : realFieldType.
Variable n : nat.

Lemma poly_convex (V : {fset 'cV[R]_n}) (P : 'poly[R]_n) :
  {subset V <= P} -> {subset \conv V <= P}.
Proof.
exact: hpoly_convex.
Qed.

End PolyProp.

Section PolyPoint.

Variable R : realFieldType.
Variable n : nat.

Definition pick_point (P : 'poly[R]_n) :=
  match (@non_emptyP _ _ P) with
  | ReflectT P_non_empty => xchoose P_non_empty
  | ReflectF _ => 0
  end.

Lemma pick_pointP P :
  non_empty P -> pick_point P \in P.
Proof. (* RK *)
rewrite /pick_point.
case: non_emptyP => [? _ | _] //.
exact: xchooseP.
Qed.

Definition poly_point (v : 'cV[R]_n) := '[ [hpoly v] ].

Notation "[ 'poly' v ]" := (poly_point v).

Lemma poly_point_inE (v x : 'cV[R]_n) :
  (x \in [poly v]) = (x == v).
Proof. (* RK *)
by rewrite mem_quotP hpoly_point_inE.
Qed.

Lemma poly_point_inP (v x : 'cV[R]_n) :
  reflect (x = v) (x \in [poly v]).
Proof. (* RK *)
rewrite mem_quotP.
exact: hpoly_point_inP.
Qed.

Lemma poly_point_self_in (v: 'cV[R]_n) : v \in [poly v].
Proof.
by apply/poly_point_inP.
Qed.

Lemma poly_point_non_empty (v: 'cV[R]_n) :
  non_empty [poly v].
Proof.
by apply/non_emptyP; exists v; apply/poly_point_inP.
Qed.

Lemma pick_point_poly_point (v: 'cV[R]_n) : pick_point [poly v] = v.
Proof.
move/pick_pointP: (poly_point_non_empty v).
by apply/poly_point_inP.
Qed.

Lemma poly_point_incl (v : 'cV[R]_n) (P : 'poly[R]_n) :
  is_included_in [poly v] P = (v \in P).
Proof.
apply: (sameP is_included_inP); apply: (iffP idP).
- by move => v_in_P x /poly_point_inP ->.
- by move/(_ _  (poly_point_self_in _)).
Qed.

End PolyPoint.

Notation "[ 'poly' v ]" := (poly_point v).

Section PolyHyperplane. (* RK *)

Variable R : realFieldType.
Variable n : nat.

Definition poly_hyperplane (c : 'cV[R]_n)  (d : R) := '[ hpoly_hyperplane c d ].

Lemma poly_hyperplane_inE c d x :
  (x \in poly_hyperplane c d) = ('[c,x] == d).
Proof.
by rewrite mem_quotP hpoly_hyperplane_inE.
Qed.

End PolyHyperplane.

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

Section Intersection. (* RK *)

Variable R : realFieldType.
Variable n : nat.

Definition polyI_of_hpoly (hP hQ : 'hpoly[R]_n) :=
  let: 'P(AP,bP) := hP in
  let: 'P(AQ,bQ) := hQ in
    '['P((col_mx AP AQ), (col_mx bP bQ))].

Fact in_polyI_of_hpoly (hP hQ : 'hpoly[R]_n) x :
  (x \in polyI_of_hpoly hP hQ) = ((x \in hP) && (x \in hQ)).
Proof.
rewrite /polyI_of_hpoly.
case: hP => mP AP bP; case: hQ => mQ AQ bQ.
by rewrite !mem_quotP !inE mul_col_mx col_mx_lev.
Qed.

Definition polyI (P Q : 'poly[R]_n) :=
  polyI_of_hpoly (hpoly P) (hpoly Q).

Fact in_polyI (P Q : 'poly[R]_n) x :
  (x \in polyI P Q) = ((x \in P) && (x \in Q)).
Proof.
by rewrite in_polyI_of_hpoly -2!mem_quotP.
Qed.

Fact in_polyIP (P Q : 'poly[R]_n) x :
  reflect (x \in P /\ x \in Q) (x \in polyI P Q).
Admitted.

Lemma polyI_quotP (P Q : 'poly[R]_n) (hP hQ : 'hpoly[R]_n) :
  P = '[hP] -> Q = '[hQ] ->
    polyI P Q = polyI_of_hpoly hP hQ.
Proof.
move => PeqClasshP QeqClasshQ.
rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
by rewrite in_polyI in_polyI_of_hpoly -2!mem_quotP PeqClasshP QeqClasshQ.
Qed.

Fact polyIC (P Q : 'poly[R]_n) :
  polyI P Q = polyI Q P.
Proof.
rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
by rewrite !in_polyI andbC.
Qed.

Fact polyIA (P Q S : 'poly[R]_n) :
  polyI P (polyI Q S) = polyI (polyI P Q) S.
Proof.
rewrite -[polyI P _]hpolyK -[polyI _ S in RHS]hpolyK; apply/poly_eqP => x.
by rewrite !in_polyI andbA.
Qed.

Fact polyIid (P : 'poly[R]_n) :
  polyI P P = P.
Proof.
rewrite -[LHS]hpolyK -[P in RHS]hpolyK; apply/poly_eqP => x.
rewrite in_polyI /=.
by case: (x \in P).
Qed.

Fact includedIl (P Q : 'poly[R]_n) :
  is_included_in (polyI P Q) P.
Proof.
apply/is_included_inP => x.
rewrite in_polyI.
by move/andP/proj1.
Qed.

Fact includedIr (P Q : 'poly[R]_n) :
  is_included_in (polyI P Q) Q.
Proof.
apply/is_included_inP => x.
rewrite in_polyI.
by move/andP/proj2.
Qed.

Fact includedI (P Q S : 'poly[R]_n) :
  (is_included_in S (polyI P Q)) = ((is_included_in S P) && (is_included_in S Q)).
Proof.
apply/idP/idP => [S_is_included_in_I | /andP [S_is_included_in_P S_is_included_in_Q]].
- apply/andP; split.
  + by apply/(is_included_in_trans _ (includedIl P Q)).
  + by apply/(is_included_in_trans _ (includedIr P Q)).
- apply/is_included_inP => x x_in_S.
  rewrite in_polyI.
  apply/andP; split.
  + by apply/(is_included_inP S_is_included_in_P).
  + by apply/(is_included_inP S_is_included_in_Q).
Qed.

Fact polyIidPl (P Q : 'poly[R]_n) :
  reflect ((polyI P Q) = P) (is_included_in P Q).
Proof.
apply: (iffP idP) => [/is_included_inP P_subset_Q | polyI_P_Q_eq_P].
- rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
  rewrite in_polyI.
  apply: andb_idr.
  exact: (P_subset_Q x).
- apply/is_included_inP => x.
  rewrite -polyI_P_Q_eq_P.
  exact: ((is_included_inP (includedIr P Q)) x).
Qed.

Fact polyIidPr (P Q : 'poly[R]_n) :
  reflect ((polyI P Q) = Q) (is_included_in Q P).
Proof.
apply: (iffP idP) => [/is_included_inP Q_subset_P | polyI_P_Q_eq_Q].
- rewrite -[LHS]hpolyK -[RHS]hpolyK; apply/poly_eqP => x.
  rewrite in_polyI.
  apply: andb_idl.
  exact: (Q_subset_P x).
- apply/is_included_inP => x.
  rewrite -polyI_P_Q_eq_Q.
  exact: ((is_included_inP (includedIl P Q)) x).
Qed.

(*Fact in_face_affine_hull_rel (P Q : 'poly[R]_n) x :
  Q \in face P ->
    (x \in Q) = ((x \in P) && (x \in affine_hull_of_poly Q)).
Proof.
rewrite inE.
move: (hpoly_base P).
case: (hpoly P) => m A b.
move => P_base /andP [non_empty_Q /andP [Q_base eq_set_incl]].
apply/idP/idP => [x_in_Q | /andP [x_in_P x_in_aff_hull_Q]].
- apply/andP; split.
  + exact: (((inclusion_on_base P_base Q_base) eq_set_incl) _ x_in_Q).
  + rewrite /affine_hull_of_poly.
    exact: in_poly_imp_in_affine_hull_on_base.
- rewrite (hpoly_of_baseP P_base) mem_quotP inE in x_in_P.
  rewrite (hpoly_of_baseP Q_base) mem_quotP inE.
  apply/andP; split.
  + exact: (proj1 (andP x_in_P)).
  + apply/forallP => i.
    apply/implyP => i_in_eq_Q.
    rewrite (affine_hullP Q_base) (in_affine_hull_on_base _ x non_empty_Q) in x_in_aff_hull_Q.
    move/colP: (eqP x_in_aff_hull_Q) => eq_Q_sat.
    move/eqP: (eq_Q_sat (enum_rank_in i_in_eq_Q i)).
    by rewrite -row_submx_mul 2!row_submx_mxE enum_rankK_in.
Qed.*)

(*Lemma polyI_face_affine_hull (P F : 'poly[R]_n) :
  F \in face P ->
    F = polyI P (affine_hull_of_poly F). (* RK: Proposition 2.3 (iv) of Ziegler's book *)
Proof.
move => F_is_face_of_P.
rewrite -[F]hpolyK -[polyI _ _]hpolyK; apply/poly_eqP => x.
by rewrite in_polyI (in_face_affine_hull_rel _ F_is_face_of_P) hpolyK.
Qed.*)

Fact eqU_subset_eq_polyI (base : 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
    ({eq(P) on base} :|: {eq(Q) on base}) \subset {eq((polyI P Q)) on base}.
Proof.
case: base => m A b.
move => /has_baseP [IP P_eq] /has_baseP [IQ Q_eq].
apply/subsetP => j.
rewrite in_setU.
move/orP => [/active_inP cond_in_eq_P | /active_inP cond_in_eq_Q];
  apply/active_inP => x x_in_polyI; rewrite in_polyI in x_in_polyI.
- apply: (cond_in_eq_P x).
  exact: (proj1 (andP x_in_polyI)).
- apply: (cond_in_eq_Q x).
  exact: (proj2 (andP x_in_polyI)).
Qed.

Fact has_base_polyI (base : 'hpoly[R]_n) (P Q : 'poly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
    [(polyI P Q) has \base base].
Proof.
case: base => m A b.
move => /has_baseP [IP P_eq] /has_baseP [IQ Q_eq].
apply/has_baseP.
exists (IP :|: IQ).
rewrite -[LHS]hpolyK.
apply/poly_eqP => x.
rewrite -mem_quotP hpolyK in_polyI P_eq Q_eq 2!mem_quotP !hpolyEq_inE.
apply/idP/idP => [/andP [/andP [x_in_base sat_IP] /andP [_ sat_IQ]] | /andP [x_in_base sat_Int]].
- apply/andP; split.
  + exact: x_in_base.
  + apply/forallP => j.
    apply/implyP.
    rewrite in_setU.
    move/orP => [j_in_IP | j_in_IQ].
    * exact: ((implyP ((forallP sat_IP) j)) j_in_IP).
    * exact: ((implyP ((forallP sat_IQ) j)) j_in_IQ).
- apply/andP; split.
  + apply/andP; split.
    * exact: x_in_base.
    * apply/forallP => j.
      apply/implyP => j_in_IP.
      apply: (implyP ((forallP sat_Int) j)).
      rewrite in_setU.
      by apply/orP; left.
  + apply/andP; split.
    * exact: x_in_base.
    * apply/forallP => j.
      apply/implyP => j_in_IQ.
      apply: (implyP ((forallP sat_Int) j)).
      rewrite in_setU.
      by apply/orP; right.
Qed.

End Intersection.

Module FaceBase.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Variable base : 'hpoly[R]_n.
Variable P : 'poly[R]_n.
Hypothesis P_base : [P has \base base].

Definition face_set :=
  ([fset '['P^=(base; I)] | I : {set 'I_(#ineq base)} & (({ eq P on base } \subset I) && non_empty '['P^=(base; I)])])%fset : {fset 'poly[R]_n}.

Definition face_empty :
  ~~ (non_empty P) -> face_set = fset0.
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
    reflect (exists c, bounded c P /\ { over P, Q argmin c })
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

Definition face_set (P : 'poly[R]_n) := FaceBase.face_set (hpoly P) P.

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
    reflect (exists c, bounded c P /\ { over P, Q argmin c })
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
  by [exact: hpoly_base | exact: subxx | done].
Qed.

Fact face_subset (P Q : 'poly[R]_n) :
  Q \in \face P -> {subset Q <= P}. (* RK *)
Proof.
move/(face_baseP (hpoly_base P)) => [Q_has_base ? _].
by apply: (inclusion_on_base Q_has_base (hpoly_base P)).
Qed.

Fact face_of_face_incl_rel (P F : 'poly[R]_n) :
  F \in \face P -> \face F = [fset F' in \face P | is_included_in F' F]%fset.
Proof.
move => F_face_P.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP.
- move => F' F'_face_F.
  rewrite in_fsetE inE; apply/andP; split.
  + by move/fsubsetP/(_ _ F'_face_F): (face_of_face F_face_P).
  + apply/is_included_inP; exact: face_subset.
- move => F'; rewrite in_fsetE inE => /andP [F'_face_P /is_included_inP F'_sub_F].
  move/(face_baseP (hpoly_base P)): F_face_P => [F_base eqP_sub_eqF F_non_empty].
  move/(face_baseP (hpoly_base P)): F'_face_P => [F'_base eq_P_sub_eq_F' F'_non_empty].
  apply/(face_baseP F_base); split.
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

Lemma polyI_face_is_face (P F F' : 'poly[R]_n) :
  (F \in \face P) -> (F' \in \face P) -> non_empty (polyI F F') ->
    (polyI F F') \in \face P. (* RK: Proposition 2.3 (ii) of Ziegler's book *)
Proof.
move => /(face_baseP (hpoly_base P)) [F_base eq_P_subset_eq_F _].
move => /(face_baseP (hpoly_base P)) [F'_base eq_P_subset_eq_F' _].
move => non_empty_polyI.
apply/(face_baseP (hpoly_base P)).
split.
- exact: (has_base_polyI F_base F'_base).
- apply: (subset_trans _ (eqU_subset_eq_polyI F_base F'_base)).
  rewrite -[{eq(P) on _}]setUid.
  exact: (setUSS eq_P_subset_eq_F eq_P_subset_eq_F').
- exact: non_empty_polyI.
Qed.

Variable P : 'poly[R]_n.
Variable c : 'cV[R]_n.
Hypothesis c_bounded : bounded c P.

(*Definition face_of_obj := (* this should be defined by using a proper intersection operation *)
  let: 'P(A, b) := hpoly P in
  let A' := col_mx c^T A in
  let b' := col_mx ((opt_value c_bounded)%:M) b in
    '[ 'P^=(A', b'; [set ord0]) ].*)
Definition face_of_obj := polyI P (poly_hyperplane c (opt_value c_bounded)).

Fact face_of_objP x :
  reflect ({ over P, x minimizes c }) (x \in face_of_obj).
Proof. (* RK *)
rewrite in_polyI poly_hyperplane_inE.
apply: (iffP idP) => [/andP [x_in_P x_optimal] | /opt_valueP H].
- by apply/opt_valueP/andP; split.
- move/andP: (H c_bounded) => [x_in_P x_optimal].
  by apply/andP; split.
Qed.

Arguments face_of_objP [x].

Hypothesis P_non_empty : non_empty P.

Lemma face_of_obj_face :
  face_of_obj \in \face P.
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

Definition compact P :=
  (non_empty P) ==> ([forall i, bounded (delta_mx i 0) P && bounded (-(delta_mx i 0)) P]).

Lemma compactP_Linfty P :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Proof. (* RK *)
apply: (iffP idP) => [/implyP compact_P | [K P_contained_in_box]].
- case: (boolP (non_empty P)) => [non_empty_P| empty_P].
  + set bound_x_i := fun (i : 'I_n) =>
      match (@idP (bounded (delta_mx i 0) P)) with
      | ReflectT bounded_delta_mx_i_P => opt_value bounded_delta_mx_i_P
      | ReflectF _ => 0
      end.
    set bound_minus_x_i := fun (i : 'I_n) =>
      match (@idP (bounded (- delta_mx i 0) P)) with
      | ReflectT bounded_minus_delta_mx_i_P => opt_value bounded_minus_delta_mx_i_P
      | ReflectF _ => 0
      end.
    set K := Num.max (-(min_seq [seq bound_minus_x_i i | i :'I_n] 0)) (-(min_seq [seq bound_x_i i | i :'I_n] 0)).
    exists K.
    move => x x_in_P i.
    rewrite ler_norml.
    apply/andP; split.
    * rewrite oppr_max ler_minl 2!opprK.
      apply/orP; right.
      suff l_bound_x_i: bound_x_i i <= x i 0
        by apply/(ler_trans _ l_bound_x_i)/min_seq_ler/map_f; rewrite mem_enum.
      rewrite /bound_x_i.
      case: {-}_/idP  => [bounded_delta_mx_i_P| /negP not_bounded_delta_mx_i_P].
      - rewrite -vdotl_delta_mx.
        exact: ((proj2 (bounded_opt_value bounded_delta_mx_i_P)) x x_in_P).
      - by rewrite (proj1 (andP (forallP (compact_P non_empty_P) i))) in not_bounded_delta_mx_i_P.
    * rewrite ler_maxr.
      apply/orP; left.
      rewrite ler_oppr.
      suff l_bound_minus_x_i: bound_minus_x_i i <= -x i 0
        by apply/(ler_trans _ l_bound_minus_x_i)/min_seq_ler/map_f; rewrite mem_enum.
      rewrite /bound_minus_x_i.
      case: {-}_/idP  => [bounded_minus_delta_mx_i_P| /negP not_bounded_minus_delta_mx_i_P].
      - rewrite -vdotl_delta_mx -vdotNl.
        exact: ((proj2 (bounded_opt_value bounded_minus_delta_mx_i_P)) x x_in_P).
      - by rewrite (proj2 (andP (forallP (compact_P non_empty_P) i))) in not_bounded_minus_delta_mx_i_P.
  + exists 0.
    move => x x_in_P.
    have non_empty_P: non_empty P
      by apply/non_emptyP; exists x.
    by rewrite non_empty_P in empty_P.
- apply/implyP => non_empty_P.
  apply/forallP => i.
  apply/andP; split; apply/bounded_lower_bound; try by done.
  + exists (-K).
    move => x x_in_P.
    move: (((P_contained_in_box x) x_in_P) i) => x_i_bound.
    rewrite ler_norml in x_i_bound.
    rewrite vdotl_delta_mx.
    exact: (proj1 (andP x_i_bound)).
  + exists (-K).
    move => x x_in_P.
    move: (((P_contained_in_box x) x_in_P) i) => x_i_bound.
    rewrite ler_norml in x_i_bound.
    rewrite vdotNl vdotl_delta_mx ler_oppr opprK.
    exact: (proj2(andP x_i_bound)).
Qed.

Lemma compactP P :
  reflect (non_empty P -> forall c, bounded c P) (compact P). (*RK: statement slightly modified: added the non_empty condition *)
Proof. (* RK *)
apply: (iffP idP) => [/compactP_Linfty [K P_contained_in_box] non_empty_P c | bounded_if_non_empty].
- apply/(bounded_lower_bound c non_empty_P).
  exists (\sum_i (-(`|c i 0| * K))).
  move => x x_in_P.
  rewrite -subr_le0 -sumrB.
  apply: sumr_le0 => i _.
  move/ler_normlP: (((P_contained_in_box x) x_in_P) i) => [? ?].
  rewrite subr_le0 ler_oppl.
  case: (boolP (0 <= c i 0)) => [c_i_geq_0 | c_i_lt_0].
  + rewrite (ger0_norm c_i_geq_0) -mulrN -subr_ge0 -mulrBr.
    apply: mulr_ge0; first exact: c_i_geq_0.
    by rewrite subr_ge0.
  + rewrite -ltrNge in c_i_lt_0.
    rewrite -mulNr -(ltr0_norm c_i_lt_0) -subr_ge0 -mulrBr.
    apply: mulr_ge0; first exact: (normr_ge0 (c i 0)).
    by rewrite subr_ge0.
- case: (boolP (non_empty P)) => [non_empty_P| empty_P].
  + apply/implyP => _; apply/forallP => i.
    by apply/andP; split; exact: (bounded_if_non_empty non_empty_P).
  + apply/implyP => non_empty_P.
    by rewrite non_empty_P in empty_P.
Qed.

Lemma compact_face P F :
  compact P -> F \in \face P -> compact F.
Proof. (* RK *)
move/compactP_Linfty => [K bounded_on_P].
move => F_is_face_of_P.
apply/compactP_Linfty; exists K.
move => x x_in_F i.
exact: (((bounded_on_P x) ((face_subset F_is_face_of_P) _ x_in_F)) i).
Qed.

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
Arguments faceP [R n P Q].