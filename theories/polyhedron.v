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
Require Import extra_misc inner_product vector_order extra_matrix row_submx exteqtype hpolyhedron simplex.

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

Lemma non_emptyPn (P : 'poly[R]_n) :
  reflect (P =i pred0) (~~ (non_empty P)).
Proof.
exact: HPrim.non_emptyPn.
Qed.

Arguments non_emptyP [P].

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
  P = '[hP] -> has_base P hP.
Proof.
move/repr_hpolyEq => P_eq.
by apply/has_baseP; exists set0.
Qed.

Lemma hpoly_base (P : 'poly[R]_n) :
  has_base P (hpoly P).
Proof.
by apply/self_base; rewrite hpolyK.
Qed.

Definition active (P : 'poly[R]_n) base :=
  let: 'P(A,b) as base := base return {set 'I_(#ineq base)} in
    [ set i: 'I_(#ineq base) | is_included_in_hyperplane P (row i A)^T (b i 0) ].

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).

Lemma active_inP (P : 'poly[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) i :
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

Lemma hpoly_of_baseP :
  P = '[ 'P^=(A, b; { eq P }) ].
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
    (exists c, bounded c P /\ (forall x, { over P, x minimizes c } <-> x \in Q))
    (Q \in (face base P)).
Proof.
case: base => [m A b] P_base P_non_empty.
apply/(iffP idP).
- move/and3P => [Q_non_empty Q_base eqP_sub_eqQ].
  move/hpoly_of_baseP: P_base => P_repr.
  rewrite {}P_repr non_empty_quotP in P_non_empty *.
  move/hpoly_of_baseP: Q_base => Q_repr.
  rewrite {}Q_repr non_empty_quotP in Q_non_empty *.
  set I := ({eq P}) in eqP_sub_eqQ *.
  set J := ({eq Q}) in eqP_sub_eqQ *.

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
      - apply: x_opt; exact: (hpolyEq_antimono eqP_sub_eqQ).
      - rewrite -vdot_mulmx mul_col_mx !vdot_col_mx vdot0l vdot0r !addr0.
        apply: eq_bigr => i _; rewrite mxE.
        case: ifP => [ i_in_J | _]; last by rewrite mulr0 mul0r.
        rewrite mul1r mulr1; exact: (hpolyEq_act y_in_Q).
  split; first by rewrite lp_quotE.
  move => x; split.
  + move/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    move/andP => [x_in_PAbI].
    move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_csc.
    rewrite mem_quotP; apply/hpolyEq_inP.
    split; first exact: (hpolyEq_antimono0 x_in_PAbI).
    move => j; rewrite -u_i_gt0; move/x_csc.
    by rewrite mul_col_mx !col_mxEu => ->.
  + rewrite mem_quotP; move => x_in_PAbJ. (* TODO: the rewrite mem_quotP takes time, why? *)
    apply/minimize_quotP/(HPrim.opt_valueP c_bounded); rewrite opt_val.
    have x_in_PAbI : x \in 'P^=(A, b; I) by exact: (hpolyEq_antimono eqP_sub_eqQ).
    apply/andP; split; first by done.
    apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i; rewrite mxE.
      case: (splitP' i) => [i' -> |?]; rewrite mxE; last by rewrite ltrr.
      case: ifP => [i'_in_J _ | ?]; last by rewrite ltrr.
      rewrite mul_col_mx !col_mxEu; exact: (hpolyEq_act x_in_PAbJ).

- move/hpoly_of_baseP: P_base => P_repr.
  move => [c] [c_bounded c_opt].
  apply/andP; split.
  + move/boundedP: c_bounded => [x /c_opt x_in_Q].
    by apply/non_emptyP; exists x.
  + set I := ({eq P}) in P_repr *. (* TODO: parsing error if parenthesis are removed *)
    suff: exists (J: {set 'I_(#ineq 'P(A, b))}), (I \subset J /\ Q = '['P^=(A, b; J)]).
    * move => [J] [I_sub_J Q_eq_PabJ]; apply/andP; split.
      - by apply/has_baseP; exists J.
      - by move/activeP: Q_eq_PabJ; apply: subset_trans.
    * rewrite P_repr non_empty_quotP !lp_quotE in P_non_empty c_bounded c_opt.
      move/HPrim.dual_opt_sol: (c_bounded) => [u] [u_ge0 c_eq c_optval].
      pose J := I :|: [set i | (usubmx u) i 0 > 0].
      exists J; split; first exact: subsetUl.
      suff PAbJ_eq_Q : 'P^=(A, b; J) =i Q. (* we should introduce a lemma for that: P = '[Q] <-> P =i Q *)
      - case: (hpolyP Q) => [Q' Q_eq_Q'].
        rewrite Q_eq_Q'; apply/poly_eqP => x.
        by rewrite PAbJ_eq_Q Q_eq_Q' mem_quotP.
      - move => x; apply/idP/idP => [x_in_PAbJ | x_in_Q].
        + have x_in_PAbI : x \in 'P^=(A, b; I).
          move: x_in_PAbJ; apply/hpolyEq_antimono; exact: subsetUl.
          apply/c_opt/minimize_quotP/HPrim.opt_valueP/andP; split; first by done.
          rewrite -c_optval c_eq; apply/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => i.
          case: (splitP' i) => [j -> | j -> _].
            - rewrite -[u]vsubmxK mul_col_mx !col_mxEu => u_j_gt0.
              have j_in_J : (j \in J) by rewrite !inE; apply/orP; right.
              exact: (hpolyEq_act x_in_PAbJ).
            - rewrite mul_col_mx !col_mxEd mulNmx -row_submx_mul.
              rewrite 2![in LHS]mxE 2![in RHS]mxE.
              apply: congr1; apply: (hpolyEq_act x_in_PAbI); exact: enum_valP.
       + move/c_opt/minimize_quotP/(HPrim.opt_valueP c_bounded)/andP: x_in_Q => [x_in_PAbI].
         rewrite {1}c_eq -c_optval; move/(HPrim.opt_value_csc u_ge0 x_in_PAbI) => x_act.
         apply/hpolyEq_inP; split; first exact: (hpolyEq_antimono0 x_in_PAbI).
         move => j; rewrite inE; case/orP => [j_in_I | u_j_gt0].
         * exact: (hpolyEq_act x_in_PAbI).
         * rewrite inE mxE in u_j_gt0.
           by move/(_ _ u_j_gt0): x_act; rewrite mul_col_mx !col_mxEu.
Qed.

End FaceP.

End FaceBase.

Arguments FaceBase.faceP [_ _ _ _ _].

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
