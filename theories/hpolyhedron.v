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
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import simplex.
(*Module S := simplex.*) (* to be fixed, simplex.v should be organized into a module *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''hpoly[' R ]_ n" (at level 8, n at level 2, format "''hpoly[' R ]_ n").
Reserved Notation "''hpoly_' n" (at level 8, n at level 2).
Reserved Notation "'#ineq' P" (at level 10, P at level 0, format "'#ineq'  P").
Reserved Notation "''P' ( m , A , b )" (at level 0, m at level 99, A at level 99, b at level 99, format "''P' ( m  , A ,  b )").
Reserved Notation "''P' ( A , b )" (at level 0, A at level 99, b at level 99, format "''P' ( A ,  b )").
Reserved Notation "P =e Q" (at level 70, format "'[hv' P '/ '  =e  Q ']'", no associativity).
Reserved Notation "''hpolyEq(' base )" (at level 8, base at level 99, format "''hpolyEq(' base )").
Reserved Notation "\eq P" (at level 10, P at level 8, format "\eq  P").
Reserved Notation "\active P" (at level 10, P at level 8, format "\active  P").
Reserved Notation "''hpolyEq[' R ]_ n" (at level 8, n at level 2, format "''hpolyEq[' R ]_ n").
Reserved Notation "''hpolyEq_' n" (at level 8, n at level 2).
Reserved Notation "\base P" (at level 10, P at level 8, format "\base  P").
Reserved Notation "''P^=' ( P ; J )"
         (at level 0, P at level 99, J at level 99, format "''P^=' ( P ; J )").
Reserved Notation "''P^=' ( A , b ; J )"
         (at level 0, A at level 99, b at level 99, J at level 99, format "''P^=' ( A ,  b ;  J )").
Reserved Notation "''hpolyNF(' base )" (at level 8, base at level 99, format "''hpolyNF(' base )").
Reserved Notation "''hpolyNF[' R ]_ n" (at level 8, n at level 2, format "''hpolyNF[' R ]_ n").
Reserved Notation "''hpolyNF_' n" (at level 8, n at level 2).

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section HPoly.

Section Def. (* TODO: reorganize this section so that we can introduce the notation 'hpoly as soon as possible*)

Variable R : realFieldType.
Variable n : nat.

Record hpoly :=
  Hpoly { nb_ineq : nat ;
          _ : 'M[R]_(nb_ineq,n) ;
          _ : 'cV[R]_nb_ineq }.

End Def.

Notation "''hpoly[' R ]_ n" := (hpoly R n).
Notation "''hpoly_' n" := (hpoly _ n).
Notation "'#ineq' P" := (nb_ineq P).
Notation "''P' ( m , A , b )" := (@Hpoly _ _ m A b).
Notation "''P' ( A , b )" := (Hpoly A b).

Section HPolyStruct.

Definition mem_hpoly (R : realFieldType) (n : nat) (P : 'hpoly[R]_n) :=
  let: 'P(A,b) := P in
    [pred x : 'cV_n | (A *m x) >=m b] : pred_class.

Coercion mem_hpoly : hpoly >-> pred_class.

Variable R : realFieldType.
Variable n : nat.
Canonical hpoly_predType := @mkPredType _ 'hpoly[R]_n (@mem_hpoly R n).
Canonical mem_hpoly_predType := mkPredType (@mem_hpoly R n).

Definition matrix_from_hpoly (P : 'hpoly[R]_n) :=
  let: 'P(A,b) := P in
    Tagged (fun m => 'M[R]_(m,n+1)) (row_mx A b).

Definition hpoly_from_matrix (M : {m : nat & 'M[R]_(m, n+1)}) :=
  let Ab := tagged M in
    Hpoly (lsubmx Ab) (rsubmx Ab).

Lemma matrix_from_hpolyK :
  cancel matrix_from_hpoly hpoly_from_matrix.
Proof.
move => hP; destruct hP.
by rewrite /matrix_from_hpoly /hpoly_from_matrix row_mxKl row_mxKr.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyK.
Canonical hpoly_eqType := Eval hnf in EqType 'hpoly[R]_n hpoly_eqMixin.

Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType 'hpoly[R]_n hpoly_choiceMixin.

Definition matrix_of (P : 'hpoly[R]_n) := (* TODO: not sure that these functions are so useful *)
  let: 'P(A,_) := P return 'M[R]_(#ineq P, n) in A.

Definition vector_of (P : 'hpoly[R]_n) :=
  let: 'P(_,b) := P return 'cV[R]_(#ineq P) in b.

End HPolyStruct.

End HPoly.

Notation "''hpoly[' R ]_ n" := (hpoly R n).
Notation "''hpoly_' n" := (hpoly _ n).
Notation "'#ineq' P" := (nb_ineq P).
Notation "''P' ( m , A , b )" := (@Hpoly _ _ m A b).
Notation "''P' ( A , b )" := (Hpoly A b).

Module HPrim.

Section Basic.

Variable R : realFieldType.
Variable n : nat.

Implicit Type c : 'cV[R]_n.
Implicit Type P : 'hpoly[R]_n.

Definition non_empty P :=
  let: 'P(A,b) := P in
    Simplex.feasible A b.

Definition bounded c P :=
  let: 'P(A,b) := P in
    Simplex.bounded A b c.

Definition unbounded c P :=
  let: 'P(A,b) := P in
    Simplex.unbounded A b c.

Definition opt_point c P :=
  if bounded c P then
    let: 'P(A,b) := P in
      Some (Simplex.opt_point A b c)
  else None.

Definition opt_value c P := omap (vdot c) (opt_point c P).

(*TODO: Simplify the lp_state statement and remove the option type*)
CoInductive lp_state c P : option ('cV[R]_n) -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state c P None false false false
| Bounded (z : 'cV_n) of (z \in P) * (forall x, x \in P -> '[c, z] <= '[c,x]) : lp_state c P (Some z) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state c P None true false true.

Lemma lp_stateP c P : (* TODO: prove it! *)
  lp_state c P (opt_point c P) (non_empty P) (bounded c P) (unbounded c P).
Proof.
Admitted.

Lemma non_emptyP P :
  reflect (exists x, x \in P) (non_empty P).
Proof.
case: P => m A b.
exact: Simplex.feasibleP.
Qed.

Lemma boundedP c P :
  reflect (exists x, (x \in P /\ (forall y, y \in P -> '[c,x] <= '[c,y]))) (bounded c P).
Proof.
case: P => m A b.
apply: (iffP idP).
- move/Simplex.boundedP => [[x [x_in_P x_eq_opt_val] x_is_opt]].
  exists x.
  split; first exact: x_in_P.
    move => y y_in_P.
    rewrite x_eq_opt_val.
    exact: (x_is_opt _ y_in_P).
- move => [x [x_in_P x_is_opt]].
  move: (Simplex.opt_value_is_optimal x_in_P x_is_opt) => x_eq_opt_val.
  apply/Simplex.boundedP.
  split.
  + by exists x.
  + move => y y_in_P.
    rewrite -x_eq_opt_val.
    exact: x_is_opt.
Qed.

Lemma bounded_certP c P :
  non_empty P -> reflect (exists K, (forall z, z \in P -> '[c,z] >= K)) (bounded c P).
Proof.
case: P => m A b.
move => P_non_empty.
suff ->: bounded c 'P(A,b) = ~~ (non_empty 'P(A,b)) || bounded c 'P(A,b)
  by exact: Simplex.infeasible_or_boundedP.
by rewrite P_non_empty /=.
Qed.

Lemma opt_value_is_optimal c P x :
  (x \in P) -> (forall y, y \in P -> '[c,x] <= '[c,y]) -> opt_value c P = Some '[c,x].
Proof.
case: P => m A b.
move => x_in_P x_is_opt.
suff opt_point_P_c: opt_point c 'P(A, b) = Some (Simplex.opt_point A b c)
 by rewrite /opt_value opt_point_P_c (Simplex.opt_value_is_optimal x_in_P x_is_opt).
apply/ifT/boundedP.
by exists x.
Qed.

Lemma unboundedP c P :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded c P).
Proof.
case: P => m A b.
exact: Simplex.unboundedP.
Qed.

Lemma bounded_xor_unbounded c P :
  non_empty P -> (bounded c P) (+) (unbounded c P).
Proof.
case: P => m A b.
by move/(Simplex.unbounded_is_not_bounded c)/esym/addbP.
Qed.

End Basic.

Section Inclusion.

Variable R : realFieldType.
Variable n : nat.
Variable P : 'hpoly[R]_n.

Definition is_included_in_halfspace c d :=
  (non_empty P) ==> match opt_value c P with
                    | Some opt_val => opt_val >= d
                    | None => false
                    end.

Lemma is_included_in_halfspaceP c d :
  reflect (forall x, x \in P -> '[c,x] >= d)
          (is_included_in_halfspace c d).
Proof.
rewrite /is_included_in_halfspace; apply: (iffP implyP).
- rewrite /opt_value.
  case: (lp_stateP c P) => /=  [ P_is_empty _
  | z [opt_in_P opt_is_opt] /=
  | /= _ /(_ is_true_true)]; last by done.
  + by move => x; rewrite P_is_empty.
  + move/(_ is_true_true) => d_le_opt.
    move => x x_in_P; move/(_ _ x_in_P): opt_is_opt.
    exact: ler_trans.
- move => inclusion.
  rewrite /opt_value.
  case: (lp_stateP c P) => [/= | opt [opt_in_P _] /= _ | /= ]; first by done.
  + exact: inclusion.
  + move/(_ d) => [x [x_in_P cx_lt_d] _].
    move/(_ _ x_in_P): inclusion.
    by rewrite lerNgt => /negP.
Qed.

Definition is_included_in_hyperplane c d :=
  (is_included_in_halfspace c d) && (is_included_in_halfspace (-c) (-d)).

Lemma is_included_in_hyperplaneP c d :
  reflect (forall x, x \in P -> '[c,x] = d)
          (is_included_in_hyperplane c d).
Proof.
apply: (iffP idP) => [/andP [is_included is_included_opp] x x_in_P | sat_eq].
- apply/eqP; rewrite eqr_le.
  apply/andP; split.
  + move: ((is_included_in_halfspaceP _ _ is_included_opp) x x_in_P).
    by rewrite vdotNl ler_opp2.
  + exact: ((is_included_in_halfspaceP _ _ is_included) x x_in_P).
- apply/andP; split; apply/is_included_in_halfspaceP => x x_in_P.
  + by rewrite (sat_eq _ x_in_P).
  + by rewrite -(sat_eq _ x_in_P) vdotNl.
Qed.

Definition hpoly_is_included_in Q :=
  let: 'P(A,b) := Q in
    [forall i, is_included_in_halfspace (row i A)^T (b i 0)].

Lemma hpoly_is_included_inP Q :
  reflect {subset P <= Q} (hpoly_is_included_in Q).
Proof.
case: Q => m A b.
apply: (iffP idP).
- move => /forallP H x Hx.
  apply/forallP => i.
  move/is_included_in_halfspaceP: (H i) => Hi.
  move: (Hi x Hx).
  by rewrite -[(A *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
- move => H.
  apply/forallP => i.
  apply/is_included_in_halfspaceP => x Hx.
  move/forallP: (H x Hx) => Hx'.
  move: (Hx' i).
  by rewrite -[(A *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
Qed.

End Inclusion.

Section ExtensionalEquality.

Variable R : realFieldType.
Variable n : nat.

Definition hpoly_ext_eq : rel 'hpoly[R]_n :=
    fun P Q => (hpoly_is_included_in P Q) && (hpoly_is_included_in Q P).

Definition hpoly_ext_eqP P Q :
  reflect (P =i Q) (hpoly_ext_eq P Q).
Proof.
apply: (iffP idP).
- move/andP => [/hpoly_is_included_inP H1 /hpoly_is_included_inP H2] x.
  apply/idP/idP; [exact: (H1 x) | exact: (H2 x)].
- move => H.
  by apply/andP; split; apply/hpoly_is_included_inP => x; rewrite (H x).
Qed.

Lemma hpoly_ext_eq_refl :
  reflexive hpoly_ext_eq.
Proof.
by move => P; apply/hpoly_ext_eqP.
Qed.

Lemma hpoly_ext_eq_sym :
  symmetric hpoly_ext_eq.
Proof.
move => P Q.
by apply/idP/idP; move/hpoly_ext_eqP => H;
  apply/hpoly_ext_eqP => x; move: (H x).
Qed.

Lemma hpoly_ext_eq_trans :
  transitive hpoly_ext_eq.
Proof.
move => ? ? ? /hpoly_ext_eqP H /hpoly_ext_eqP H'.
apply/hpoly_ext_eqP => x.
by move: (H x); rewrite (H' x).
Qed.

Lemma hpoly_ext_eq_is_equivalence_rel :
  equivalence_rel hpoly_ext_eq.
Proof.
apply/equivalence_relP; split.
- exact: hpoly_ext_eq_refl.
- move => ? ? ?.
  rewrite /eqfun => ?.
  by apply/idP/idP; apply: hpoly_ext_eq_trans; [rewrite hpoly_ext_eq_sym | done].
Qed.

Canonical hpoly_equiv_rel : equiv_rel 'hpoly[R]_n :=
  EquivRel hpoly_ext_eq hpoly_ext_eq_refl hpoly_ext_eq_sym hpoly_ext_eq_trans.

End ExtensionalEquality.

End HPrim.

Import HPrim.

Section HPolyEq.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Inductive hpolyEq (base : 'hpoly[R]_n) := HPolyEq of {set 'I_(#ineq base)}.

Definition equality_set base (Q : hpolyEq base) := let: HPolyEq J := Q in J.

End Def.

Notation "''hpolyEq(' base )" := (@hpolyEq _ _ base).
Notation "\eq P" := (equality_set P).

Section HPolyEqStruct.

Fact hpolyEqKey : unit. by []. Qed.

Definition hpoly_of_hpolyEq (R : realFieldType) (n : nat) (base : 'hpoly[R]_n) :=
  locked_with hpolyEqKey (let: 'P(A,b) as P := base in
                            fun (Q : 'hpolyEq(P)) =>
                              let: HPolyEq J := Q in
                              let AJ := col_mx A (- (row_submx A J)) in
                              let bJ := col_mx b (- (row_submx b J)) in
                                'P(AJ, bJ)).

Coercion hpoly_of_hpolyEq : hpolyEq >-> hpoly.

Variable R : realFieldType.
Variable n : nat.
Variable base : 'hpoly[R]_n.

Fact eq_setK : cancel (@equality_set _ _ base) (@HPolyEq _ _ base).
Proof.
by case.
Qed.

Definition hpolyEq_eqMixin := CanEqMixin eq_setK.
Canonical hpolyEq_eqType := Eval hnf in EqType 'hpolyEq(base) hpolyEq_eqMixin.
Definition hpolyEq_choiceMixin := CanChoiceMixin eq_setK.
Canonical hpolyEq_choiceType := Eval hnf in ChoiceType 'hpolyEq(base) hpolyEq_choiceMixin.
Definition hpolyEq_countMixin := CanCountMixin eq_setK.
Canonical hpolyEq_countType := Eval hnf in CountType 'hpolyEq(base) hpolyEq_countMixin.
Definition hpolyEq_finMixin := CanFinMixin eq_setK.
Canonical hpolyEq_finType := Eval hnf in FinType 'hpolyEq(base) hpolyEq_finMixin.

End HPolyEqStruct.

End HPolyEq.

Notation "''hpolyEq(' base )" := (@hpolyEq _ _ base).
Notation "\eq P" := (equality_set P).

Section ActiveIneq.

Variable R : realFieldType.
Variable n : nat.

Definition active_set (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :=
  let: 'P(A,b) as P' := base return {set 'I_(#ineq P')} in
    [ set i : 'I_(#ineq P') | is_included_in_hyperplane Q (row i A)^T (b i 0) ].

Notation "\active Q" := (active_set Q).

Lemma activeP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (Q : 'hpolyEq('P(A,b))) i :
  reflect (forall x, x \in Q -> (A *m x) i 0 = b i 0)
          (i \in \active Q).
Proof.
apply: (iffP idP) => [i_in_implicit_eq_set x x_in_P | ineq_i_is_sat].
- rewrite inE in i_in_implicit_eq_set.
  rewrite -row_vdot.
  exact: ((is_included_in_hyperplaneP _ _  _ i_in_implicit_eq_set) x x_in_P).
- rewrite inE.
  apply/is_included_in_hyperplaneP => x x_in_P.
  rewrite row_vdot.
  by apply: ineq_i_is_sat.
Qed.

Definition has_normal_form (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :=
  \eq Q == \active Q.

End ActiveIneq.

Notation "\active Q" := (active_set Q).

Section HPolyEqS.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Record hpolyEqS :=
  HPolyEqS { base: 'hpoly[R]_n; hpolyEq_with_base :> 'hpolyEq(base) }.

End Def.

Notation "''hpolyEq[' R ]_ n" := (hpolyEqS R n).
Notation "''hpolyEq_' n" := (hpolyEqS _ n).
Notation "\base P" := (base P).
Notation "''P^=' ( P ; J )" := (@HPolyEqS _ _ P (HPolyEq J)).
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J).

Section HPolyEqStruct.

Variable R : realFieldType.
Variable n : nat.

Let of_hpolyEqS (P : 'hpolyEq[R]_n) : { Q : 'hpoly[R]_n & 'hpolyEq(Q) } :=
  Tagged (fun Q : ('hpoly[R]_n) => 'hpolyEq(Q)) (hpolyEq_with_base P).

Fact of_hpolyEqSK : cancel of_hpolyEqS (fun P => HPolyEqS (tagged P)).
Proof.
by move => P; case: P.
Qed.

Definition hpolyEqS_eqMixin := CanEqMixin of_hpolyEqSK.
Canonical hpolyEqS_eqType := Eval hnf in EqType 'hpolyEq[R]_n hpolyEqS_eqMixin.

Definition hpolyEqS_choiceMixin := CanChoiceMixin of_hpolyEqSK.
Canonical hpolyEqS_choiceType :=
  Eval hnf in ChoiceType 'hpolyEq[R]_n hpolyEqS_choiceMixin.

End HPolyEqStruct.

End HPolyEqS.

Notation "''hpolyEq[' R ]_ n" := (hpolyEqS R n).
Notation "''hpolyEq_' n" := (hpolyEqS _ n).
Notation "\base P" := (base  P).
Notation "''P^=' ( P ; J )" := (@HPolyEqS _ _ P (HPolyEq J)).
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J).

Section HPolyNF.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Inductive hpolyNF := HPolyNF (P : 'hpolyEq[R]_n) of (has_normal_form P).

End Def.

Notation "''hpolyNF[' R ]_ n" := (hpolyNF R n).
Notation "''hpolyNF_' n" := (hpolyNF _ n).

Section HPolyNFStruct.

Definition hpolyEq_of_hpolyNF (R : realFieldType) (n : nat) (Q : 'hpolyNF[R]_n) :=
  let: HPolyNF Q' _ := Q in Q'.

Coercion hpolyEq_of_hpolyNF : hpolyNF >-> hpolyEqS.

Variable R : realFieldType.
Variable n : nat.

(*Variable base : 'hpoly[R]_n.

Canonical hpolyNF_subType := [subType for (@hpolyEq_of_hpolyNF _ _ base)].
Definition hpolyNF_eqMixin := Eval hnf in [eqMixin of hpolyNF base by <:].
Canonical hpolyNF_eqType := Eval hnf in EqType 'hpolyNF(base) hpolyNF_eqMixin.
Definition hpolyNF_choiceMixin := [choiceMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_choiceType := Eval hnf in ChoiceType 'hpolyNF(base) hpolyNF_choiceMixin.
Definition hpolyNF_countMixin := [countMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_countType := Eval hnf in CountType 'hpolyNF(base) hpolyNF_countMixin.
Canonical hpolyNF_subCountType := [subCountType of 'hpolyNF(base)].
Definition hpolyNF_finMixin := [finMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_finType := Eval hnf in FinType 'hpolyNF(base) hpolyNF_finMixin.
Canonical hpolyNF_subFinType := [subFinType of 'hpolyNF(base)].*)

Canonical hpolyNF_subType := [subType for (@hpolyEq_of_hpolyNF R n)].
Definition hpolyNF_eqMixin := Eval hnf in [eqMixin of 'hpolyNF[R]_n by <:].
Canonical hpolyNF_eqType := Eval hnf in EqType 'hpolyNF[R]_n hpolyNF_eqMixin.
Definition hpolyNF_choiceMixin := [choiceMixin of 'hpolyNF[R]_n by <:].
Canonical hpolyNF_choiceType := Eval hnf in ChoiceType 'hpolyNF[R]_n hpolyNF_choiceMixin.

Lemma normal_form_has_normal_form (Q : 'hpolyNF[R]_n) :
  has_normal_form Q.
Proof.
by apply: (valP Q).
Qed.

End HPolyNFStruct.

End HPolyNF.

Notation "''hpolyNF[' R ]_ n" := (hpolyNF R n).
Notation "''hpolyNF_' n" := (hpolyNF _ n).

Section PropEqNF.

Variable R : realFieldType.
Variable n : nat.

Fact hpolyEq_inE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) J :
  (x \in 'P^=(A, b; J)) = (x \in 'P(A, b)) && [forall j in J, (A *m x) j 0 == b j 0].
Proof.
rewrite /hpoly_of_hpolyEq unlock /=.
rewrite !inE mul_col_mx col_mx_lev mulNmx -row_submx_mul lev_opp2 /=.
apply/andP/andP.
- move => [x_in_P ineqJ]; split; try by done.
  suff /row_submx_colP H: row_submx (A *m x) J = row_submx b J.
  + apply/forall_inP => j j_in_J.
    move/(_ _ j_in_J): H ->; exact: eq_refl.
  + apply: lev_antisym; apply/andP; split; try by done.
    exact: row_submx_lev.
- move => [x_in_P /forall_inP eqJ]; split; try by done.
  apply/row_submx_levP => j j_in_J.
  by move/(_ _ j_in_J)/eqP: eqJ ->.
Qed.

Fact eq_subset_active (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :
  \eq Q \subset \active Q.
Proof.
case: base Q => m A b [JQ].
apply/subsetP => i i_in_JQ; rewrite /= in i_in_JQ.
apply/activeP => x x_in_HPolyEq_JQ.
rewrite hpolyEq_inE in x_in_HPolyEq_JQ.
move/andP: x_in_HPolyEq_JQ => [_ /forallP sat_in_JQ].
by apply/eqP/(implyP (sat_in_JQ i)).
Qed.

Fact activee (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :
  \active (HPolyEq (\active Q)) = \active Q.
Proof.
case: base Q => m A b [JQ].
apply/eqP; rewrite eqEsubset.
apply/andP; split.
- apply/subsetP => i.
  move/activeP => charact_active.
  apply/activeP => x x_in_HPolyEq_JQ.
  apply/(charact_active x).
  rewrite hpolyEq_inE.
  apply/andP; split.
  + rewrite hpolyEq_inE in x_in_HPolyEq_JQ.
    by move/andP: x_in_HPolyEq_JQ => [?].
  + apply/forallP => j.
    apply/implyP => /activeP j_in_active_Q.
    by apply/eqP/(j_in_active_Q x).
- set Q' := HPolyEq (\active _).
  have ->: \active (HPolyEq JQ) = \eq Q' by done.
  exact: eq_subset_active.
Qed.

(* TODO: do we need this statement? looks redundant with the activee statement *)
(* RK: That's right, but it might be needed in this form *)
Fact has_normal_form_base_with_implicit_eq_set (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :
  has_normal_form (HPolyEq (\active Q)).
Proof.
by rewrite /has_normal_form activee /=.
Qed.

(* TODO: split this statement into two pieces. *)
(* RK: Done? I believe that one of the implication below does not hold, see below *)
(*Fact eq_set_anti_monotone (Q : 'hpolyNF[R]_n) (P : 'hpolyEq(\base Q)) :
  \eq P \subset \eq Q <-> {subset Q <= P}.
Proof.
case: base P Q => [m A b] P [[JQ]] nfQ.
split.
- move => eq_set_inclusion x.
  rewrite 2!hpolyEq_inE.
  move/andP => [x_in_base /forallP eq_set_Q_sat].
  apply/andP; split; first exact: x_in_base.
  apply/forallP => i.
  apply/implyP => i_in_eq_set_P.
  exact: ((implyP (eq_set_Q_sat i)) (((subsetP eq_set_inclusion) i) i_in_eq_set_P)).
- move => Q_subset_P.
  apply/subsetP => i i_in_eq_set_P.
  rewrite (eqP (normal_form_has_normal_form (HPolyNF nfP))) in i_in_eq_set_P.
  rewrite (eqP (normal_form_has_normal_form (HPolyNF nfQ))).
  apply/implicit_eq_setP => x x_in_Q.
  exact: (((implicit_eq_setP _ _ i_in_eq_set_P) x) ((Q_subset_P x) x_in_Q)).
Qed.*)

Fact subset_active_antimonotonicity (base : 'hpoly[R]_n) (Q P : 'hpolyEq(base)) :
  {subset Q <= P} -> \active P \subset \active Q.
Proof.
case: base P Q => [m A b] P Q.
move => Q_subset_P.
apply/subsetP => i /activeP i_active_in_P.
apply/activeP => x x_in_Q.
apply: (i_active_in_P x).
by apply: (Q_subset_P x).
Qed.

Fact eqset_subset_antimonotonicity (base : 'hpoly[R]_n) (Q P : 'hpolyEq(base)) :
  \eq P \subset \eq Q -> {subset Q <= P}.
Proof.
case: base P Q => [m A b] [JP] [JQ].
move => eq_set_inclusion x.
rewrite 2!hpolyEq_inE => /andP [x_in_base /forallP sat_in_JQ].
apply/andP; split; first exact: x_in_base.
apply/forallP => i.
apply/implyP => i_in_eq_set_P.
exact: ((implyP (sat_in_JQ i)) (((subsetP eq_set_inclusion) i) i_in_eq_set_P)).
Qed.

(* TODO: define a point in the relative interior *)
Section RelativeInterior.

Lemma hpolyNF_relint_pointP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) 
      (Q : 'hpolyNF('P(A,b))) :
        exists x, (x \in Q /\ (forall i, i \notin (\eq Q) -> (A *m x) i 0 > b i 0)).
Proof.
Admitted.let: HPolyNF Q' _ := Q in Q'

End RelativeInterior.

Section Ex2.
Variable Q : 'hpolyEq[R]_n.

Fact bar x : x \in Q.
Proof.
case: Q => [[m A b] [[J] ?]] /=.
rewrite hpolyEq_inE.
Abort.

End Ex2.

(*Section Ex.

(* TODO: none below is working, why? *)

(*Let foo (Q : hpolyEq) :=
  let: 'P^=(A, b ; J) := Q return 'M[R]_(#ineq \base Q, n) in A.*)

(* This one is working *)
(* but is there a way to shorten it? *)
(*Let foo (Q : hpolyEq) :=
  let: 'P^=(P; _) := Q return 'M[R]_(#ineq \base Q, n) in
  let: 'P(A,_) := P return 'M[R]_(#ineq P, n) in A.*)

(* This one is also working _but_ we need the 'as P' and to
   use the type 'M[R]_(#ineq P, n) as a return type *)
(*Let foo (base: 'hpoly[R]_n) (Q : hpolyEq base) :=
  let: 'P(A,b) as P := base return 'M[R]_(#ineq P, n) in A.*)

Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Check ('P (A,b)).
Variable I : {set 'I_m}.
Check 'P^= (A,b;I).
End Ex.*)


Definition poly_inE := hpolyEq_inE.
Definition inE := (poly_inE, inE).

Section Mixins.

Let of_hpolyNFS (P : 'hpolyEq[R]_n) : { Q : 'hpoly[R]_n & 'hpolyNF(Q) } :=
  Tagged (fun Q : ('hpoly[R]_n) => 'hpolyNF(Q)) (hpolyeq_with_base P).

Fact of_hpolyNFSK : cancel of_hpolyNFS (fun x => HPolyNFS (tagged x)).
Proof.
by move => P; case: P.
Qed.

Definition hpolyNFS_eqMixin := CanEqMixin of_hpolyNFSK.
Canonical hpolyNFS_eqType := Eval hnf in EqType 'hpolyEq[R]_n hpolyNFS_eqMixin.

Definition hpolyNFS_choiceMixin := CanChoiceMixin of_hpolyNFSK.
Canonical hpolyNFS_choiceType :=
  Eval hnf in ChoiceType 'hpolyEq[R]_n hpolyNFS_choiceMixin.

End Mixins.

(* TODO: not working, why ??? *)
(*
Definition implicit_eq_set (Q: hpolyEq) :=
  let: 'P^= (P; _) := Q in
  let: 'P(A,b) as P := P in
  [ set i : 'I_(#ineq P) |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].

Definition implicit_eq_set (Q: hpolyEq) :=
  match Q return {set 'I_(#ineq (\base Q))} with
  | HPolyEq (Hpoly _ A b as P) _ =>
  [ set i | is_included_in_hyperplane Q (row i A)^T (b i 0) ]
  end.
*)

(* This work but apparently this is not very usable *)
(*Definition implicit_eq_set (Q: hpolyEq) :=
  let: 'P(A, b) as P := \base Q in
  [ set i : 'I_(#ineq P) |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].*)


End UnfixedBase.

End HPolyEq.

Notation "''hpolyNF(' base )" := (@hpolyNF _ _ base) (at level 0, format "''hpolyNF(' base )").
Notation "''hpolyEq(' base )" := (@hpolyEq _ _ base) (at level 0, format "''hpolyEq(' base )").
Notation "''hpolyEq[' R ]_ n" := (hpolyNFS R n) (at level 0, format "''hpolyEq[' R ]_ n").
Notation "''hpolyEq_' n" := (hpolyEq _ n) (at level 0, only parsing). (* RK: Isn't it hpolyNFS here?*)
Notation "\base P" := (base P) (at level 0, format "\base P").
Notation "\eq P" := (eq_set P) (at level 0, format "\eq P").
Notation "''P^=' ( P ; J )" := (@HPolyNFS _ _ P (HPolyEq J)) (at level 0, format "''P^=' ( P ; J )").
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J) (at level 0, format "''P^=' ( A ,  b ;  J )").

Section ExtensionalEqualityEq.

Variable R : realFieldType.
Variable n : nat.

Definition hpolyEq_ext_eq := [ rel P Q : 'hpolyEq[R]_n | hpoly_ext_eq P Q ].

Lemma hpolyEq_ext_eq_refl :
  reflexive hpolyEq_ext_eq.
Proof.
move => P /=; rewrite ?eqmodE.
exact: equiv_refl.
Qed.

Lemma hpolyEq_ext_eq_sym :
  symmetric hpolyEq_ext_eq.
Proof.
move => P Q /=; rewrite ?eqmodE.
exact: equiv_sym.
Qed.

Lemma hpolyEq_ext_eq_trans :
  transitive hpolyEq_ext_eq.
Proof.
move => P Q S /=; rewrite ?eqmodE.
exact: equiv_trans.
Qed.

Canonical hpolyEq_equiv_rel : equiv_rel 'hpolyEq[R]_n :=
  EquivRel hpolyEq_ext_eq hpolyEq_ext_eq_refl hpolyEq_ext_eq_sym hpolyEq_ext_eq_trans.

End ExtensionalEqualityEq.


Notation "P ==e Q" := (P == Q %[mod_eq (hpolyEq_equiv_rel _ _)])%qT (at level 0).
Notation "P =e Q" := (P = Q %[mod_eq (hpolyEq_equiv_rel _ _)])%qT.

Lemma hpoly_eqP (R : realFieldType) (n : nat) (P Q : 'hpolyEq[R]_n) :
  (P =i Q) <-> (P =e Q).
Proof.
apply: (rwP2 (b := hpolyEq_ext_eq _ _ P Q)).
- exact: hpoly_ext_eqP.
- exact: eqmodP.
Qed.

Section HFace.

Variable n : nat.
Variable R : realFieldType.
Variable base : 'hpoly[R]_n.
Variable P : 'hpolyNF(base).

Definition hface_of :=
  [ pred Q : 'hpolyEq[R]_n |
    non_empty Q && [exists R : 'hpolyNF(base), (\eq P \subset \eq R) && (Q ==e (HPolyNFS R)) ] ].

Hypothesis P_non_empty : non_empty P.

Lemma hface_ofP (Q : 'hpolyEq[R]_n) :
  reflect (exists c, bounded c P /\ forall x, (x \in P -> (Some '[c,x] = opt_value c P <-> x \in Q)))
          (hface_of Q).
Proof.
Admitted.

End HFace.

Lemma has_face_imp_non_empty (R : realFieldType) (n : nat) (base : 'hpoly[R]_n) (P : 'hpolyNF(base)) (F : 'hpolyEq[R]_n) :
  hface_of P F -> non_empty P.
Proof.
case: base P => [m A b] P.
move/andP => [/non_emptyP [x x_in_F] /existsP [Q /andP [eq_set_inclusion /eqP/hpoly_eqP F_eqi_Q]]].
have Q_subset_F : {subset Q <= P} by apply/(eq_set_anti_monotone P Q).
apply/non_emptyP.
exists x.
apply: (Q_subset_F x).
by rewrite -F_eqi_Q.
Qed.

Module HPolyPrim.

Definition non_empty := non_empty.
Definition bounded := bounded.
Definition unbounded := unbounded.
Definition opt_point := opt_point.
Definition opt_value := opt_value.

End HPolyPrim.

(*
Definition normal_form P := HPolyEq (implicit_eq_set P).

Lemma normal_formP (P : hpolyEq) :
  (* TODO: perhaps we should use ext_eq over polyhedra rather than over boolean predicates *)
  (P : 'hpoly[R]_n) =i (normal_form P).
Proof.
move => x.
apply/idP/idP => [x_in_P | x_in_nf].
Admitted.
(*
- rewrite hpolyEq_inE /=.
  apply/andP; split.
  + rewrite hpolyEq_inE in x_in_P.
    exact: (proj1 (andP x_in_P)).
  + apply/forallP => i.
    apply/implyP => i_in_implicit.
    rewrite inE in i_in_implicit.
    move/is_included_in_hyperplaneP: i_in_implicit => in_hyperplane.
    by rewrite -((in_hyperplane x) x_in_P) row_vdot.
- rewrite hpolyEq_inE.
  apply/andP; split; rewrite hpolyEq_inE /= in x_in_nf.
  + exact: (proj1 (andP x_in_nf)).
  + apply/forallP => i.
    apply/implyP => i_in_I_P.
    exact: ((implyP ((forallP (proj2 (andP x_in_nf))) i)) ((subsetP (subset_of_implicit_eq_set P)) _ i_in_I_P)).
Qed.*)

End HPolyEq.

Section HPolyNF.

Variable R : realFieldType.
Variable n : nat.

Definition has_normal_form (P : 'hpolyEq[R]_n) :=
  (\eq P == implicit_eq_set P).

Lemma has_normal_formP P :
  has_normal_form P = (P == normal_form P).
Proof.
apply/idP/idP => [has_nf_P | P_eq_nf].
- apply/andP.
  split; first by done.
  by rewrite tagged_asE.
- move/andP/proj2: P_eq_nf.
  by rewrite tagged_asE.
Qed.

Inductive hpolyNF := HPolyNF (P : 'hpolyEq[R]_n) of has_normal_form P.

Fact normal_form_has_normal_form P :
  has_normal_form (normal_form P).
Proof. (*RK*)
rewrite /has_normal_form eqEsubset.
apply/andP; split.
- exact: subset_of_implicit_eq_set.
- apply/subsetP => i /implicit_eq_setP i_in_I_nfP.
  rewrite /normal_form /=.
  apply/implicit_eq_setP => x x_in_P.
  apply: i_in_I_nfP.
  by rewrite -(normal_formP P x).
Qed.

Definition hpolyNF_of_hpolyEq P :=
  HPolyNF (normal_form_has_normal_form P).
Coercion hpoly_of_subset_of_hpoly_nf P :=
  let: HPolyNF Q _ := P in Q.

Canonical hpoly_nf_subtype := [subType for hpoly_of_subset_of_hpoly_nf].

Lemma hpolyNF_has_normal_form (P : hpolyNF) : has_normal_form P.
Proof. exact: valP. Qed.

Section Mixins.

Definition hpoly_nf_eqMixin := Eval hnf in [eqMixin of hpolyNF by <:].
Canonical hpoly_nf_eqType := Eval hnf in EqType hpolyNF hpoly_nf_eqMixin.
Definition hpoly_nf_choiceMixin := Eval hnf in [choiceMixin of hpolyNF by <:].
Canonical hpoly_nf_choiceType := Eval hnf in ChoiceType hpolyNF hpoly_nf_choiceMixin.

End Mixins.

Lemma nf_hpolyNF (P: hpolyNF) : hpolyNF_of_hpolyEq P = P.
Proof.
move: (hpolyNF_has_normal_form P).
rewrite has_normal_formP => /eqP H.
by apply: val_inj => /=; rewrite -H.
Qed.

End HPolyNF.

Notation "\nf P" := (hpolyNF_of_hpolyEq P) (at level 0).
Notation "''hpolyNF[' R ]_ n" := (hpolyNF R n) (at level 0, format "''hpolyNF[' R ]_ n").
Notation "''hpolyNF_' n" := (hpolyNF _ n) (at level 0, only parsing).





Section HFace.

Variable n : nat.
Variable R : realFieldType.


Variable P : 'hpolyNF[R]_n.

Definition hface_of :=
  [qualify a Q: 'hpolyEq[R]_n |
    non_empty Q &&
    [exists J : {set 'I_(#ineq \base P)},
        (\eq P \subset J) && (Q ==e 'P^=(\base P; J)) ]].

Hypothesis P_non_empty : non_empty P.

Lemma hface_ofP Q :
  reflect (exists c, bounded P c /\ forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in Q)))
          (Q \is a hface_of).
Proof.
Admitted.

End HFace.

Module HPolyPrim.

Definition non_empty := non_empty.
Definition bounded := bounded.
Definition unbounded := unbounded.
Definition opt_point := opt_point.
Definition opt_value := opt_value.

End HPolyPrim.*)


(*Definition recession_dir (P : hpoly) d :=
  let: 'P(A,b) := P in
    (Simplex.feasible A b) && (feasible_dir A d).

Lemma recession_dirP (P : hpoly) d :
  reflect ((exists y, y \in P) /\ (forall x, forall lambda, x \in P -> lambda >= 0 -> x + lambda *: d \in P))
          (recession_dir P d).
Proof.
case: P => m A b.
apply: (iffP idP) => [/andP [feasible feasible_dir] | [feasible recession_cond]].
- split.
  + exact: (Simplex.feasibleP _ _ feasible).
  + move => x lambda x_in_P lambda_pos.
    rewrite inE mulmxDr -[b]addr0.
    apply: lev_add; first exact: x_in_P.
    rewrite -scalemxAr -(scaler0 _ lambda).
    by apply: lev_wpscalar.
- apply/andP; split.
  + by apply/Simplex.feasibleP.
  + apply/contraT.
    rewrite negb_forall.
    move/existsP => [i infeasible_dir_i].
    rewrite -ltrNge ![X in _ < X]mxE in infeasible_dir_i.
    move: feasible => [y y_in_P].
    set lambda := ((b i 0 -(A *m y) i 0 - 1)*((A *m d) i 0)^-1).
    have lambda_is_pos: 0 <= lambda.
      rewrite -invr_lt0 in infeasible_dir_i.
      rewrite (nmulr_lge0 _ infeasible_dir_i) subr_le0 ler_subl_addl.
      apply: ler_paddr; [exact: ler01 | exact: ((forallP y_in_P) i)].
    move: (recession_cond _ _  y_in_P lambda_is_pos) => contradic.
    rewrite inE mulmxDr -scalemxAr in contradic.
    move: ((forallP contradic) i).
    rewrite mxE [(lambda *: (A *m d)) i 0]mxE -mulrA mulVf; last by apply: ltr0_neq0.
    by rewrite mulr1 -ler_subl_addl ler_addl ler0N1.
Qed.

End Def.*)
