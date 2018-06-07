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
Require simplex.
Module S := simplex. (* to be fixed, simplex.v should be organized into a module *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Record hpolyhedron :=
  HPolyhedron { nb_ineq : nat ;
                _ : 'M[R]_(nb_ineq,n) ;
                _ : 'cV[R]_nb_ineq }.

Notation "'#ineq' P" := (nb_ineq P) (at level 0, format "'#ineq' P").
Notation "''P' ( m , A , b )" := (@HPolyhedron m A b) (at level 0, format "''P' ( m  , A ,  b )").
Notation "''P' ( A , b )" := (HPolyhedron A b) (at level 0, format "''P' ( A ,  b )").

Definition mem_hpolyhedron (P : hpolyhedron) :=
  let: 'P(A,b) := P in
    [pred x : 'cV_n | (A *m x) >=m b].

Coercion pred_of_hpolyhedron (P : hpolyhedron) : pred_class := mem_hpolyhedron P.
Canonical hpolyhedron_predType := @mkPredType _ hpolyhedron pred_of_hpolyhedron.
Canonical mem_hpolyhedron_predType := mkPredType mem_hpolyhedron.

(* TODO: we keep that just to recall an example of return ... construction *)
Definition matrix_of (P : hpolyhedron) :=
  let: 'P(A,_) := P return 'M[R]_(#ineq P, n) in A.

Definition vector_of (P : hpolyhedron) :=
  let: 'P(_,b) := P return 'cV[R]_(#ineq P) in b.

Section Ex.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Fact foo : matrix_of 'P(A,b) = A.
done.
Qed.

End Ex.
(* end of TODO *)

Definition recession_dir (P : hpolyhedron) d :=
  let: 'P(A,b) := P in
    (S.Simplex.feasible A b) && (S.feasible_dir A d).

Lemma recession_dirP (P : hpolyhedron) d :
  reflect ((exists y, y \in P) /\ (forall x, forall lambda, x \in P -> lambda >= 0 -> x + lambda *: d \in P))
          (recession_dir P d).
Proof.
case: P => m A b.
apply: (iffP idP) => [/andP [feasible feasible_dir] | [feasible recession_cond]].
- split.
  + exact: (S.Simplex.feasibleP _ _ feasible).
  + move => x lambda x_in_P lambda_pos.
    rewrite inE mulmxDr -[b]addr0.
    apply: lev_add; first exact: x_in_P.
    rewrite -scalemxAr -(scaler0 _ lambda).
    by apply: lev_wpscalar.
- apply/andP; split.
  + by apply/S.Simplex.feasibleP.
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

Definition matrix_from_hpolyhedron (P : hpolyhedron) :=
  let: 'P(A,b) := P in
    Tagged (fun m => 'M[R]_(m,n+1)) (row_mx A b).

Definition hpolyhedron_from_matrix (M : {m: nat & 'M[R]_(m, n+1)}) :=
  let Ab := tagged M in
    HPolyhedron (lsubmx Ab) (rsubmx Ab).

Lemma matrix_from_hpolyhedronK :
  cancel matrix_from_hpolyhedron hpolyhedron_from_matrix.
Proof.
move => hP; destruct hP.
by rewrite /matrix_from_hpolyhedron /hpolyhedron_from_matrix row_mxKl row_mxKr.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyhedronK.
Canonical hpoly_eqType := Eval hnf in EqType hpolyhedron hpoly_eqMixin.

Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyhedronK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType hpolyhedron hpoly_choiceMixin.

End Def.

Notation "'#ineq' P" := (nb_ineq P) (at level 0, format "'#ineq' P").
Notation "''P' ( m , A , b )" := (@HPolyhedron _ _ m A b) (at level 0, format "''P' ( m  , A ,  b )").
Notation "''P' ( A , b )" := (HPolyhedron A b) (at level 0, format "''P' ( A ,  b )").
Notation "''hpoly[' R ]_ n" := (hpolyhedron R n) (at level 0, format "''hpoly[' R ]_ n").
Notation "''hpoly_' n" := (hpolyhedron _ n) (at level 0, only parsing).

Section BasicPrimitives.

Variable R : realFieldType.
Variable n : nat.

Implicit Type P : 'hpoly[R]_n.
Implicit Type c : 'cV[R]_n.

Definition non_empty P :=
  let: 'P(A,b) := P in
    S.Simplex.feasible A b.

Definition bounded P c :=
  let: 'P(A,b) := P in
    S.Simplex.bounded A b c.

Definition unbounded P c :=
  let: 'P(A,b) := P in
    S.Simplex.unbounded A b c.

Definition opt_point P c :=
  let: 'P(A,b) := P in
    S.Simplex.opt_point A b c.

Definition opt_value P c := '[c, opt_point P c].

CoInductive lp_state P c z : bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state P c z false false false
| Bounded of (z \in P) * (forall x, x \in P -> '[c,z] <= '[c,x]) : lp_state P c z true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P c z true false true.

Lemma lp_stateP P c :
  lp_state P c (opt_point P c) (non_empty P) (bounded P c) (unbounded P c).
Proof.
Admitted.

Lemma non_emptyP P :
  reflect (exists x, x \in P) (non_empty P).
Proof.
case: P => m A b.
exact: S.Simplex.feasibleP.
Qed.

Lemma boundedP P c : (*RK*)
  reflect ((exists x, x \in P /\ '[c,x] = opt_value P c) /\ (forall y, y \in P -> opt_value P c <= '[c,y])) (bounded P c).
Proof.
case: P => m A b.
exact: S.Simplex.boundedP.
Qed.

Lemma opt_value_is_optimal P c x : (*RK*)
  (x \in P) -> (forall y, y \in P -> '[c,x] <= '[c,y]) -> '[c,x] = opt_value P c.
Proof.
case: P => m A b.
exact: S.Simplex.opt_value_is_optimal.
Qed.

Lemma unboundedP P c : (*RK*)
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded P c).
Proof.
case: P => m A b.
exact: S.Simplex.unboundedP.
Qed.

End BasicPrimitives.

Section Inclusion.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'hpoly[R]_n.

Definition is_included_in_halfspace c d :=
  (non_empty P) ==> (bounded P c && (opt_value P c >= d)).

Lemma is_included_in_halfspaceP c d :
  reflect (forall x, x \in P -> '[c,x] >= d)
          (is_included_in_halfspace c d).
Proof.
rewrite /is_included_in_halfspace; apply: (iffP implyP).
- case: lp_stateP =>
  [ P_is_empty _
  | [opt_in_P opt_is_opt] /=
  | /= _ /(_ is_true_true)]; last by done.
  + by move => x; rewrite P_is_empty.
  + move/(_ is_true_true) => d_le_opt.
    move => x x_in_P; move/(_ _ x_in_P): opt_is_opt.
    exact: ler_trans.
- move => inclusion.
  case: lp_stateP => [/= | [opt_in_P _] /= _ | /= ]; first by done.
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

Definition hpolyhedron_is_included_in Q :=
  let: 'P(A,b) := Q in
    [forall i, is_included_in_halfspace (row i A)^T (b i 0)].

Lemma hpolyhedron_is_included_inP Q :
  reflect {subset P <= Q} (hpolyhedron_is_included_in Q).
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

Definition hpolyhedron_ext_eq : rel 'hpoly[R]_n :=
    fun P Q => (hpolyhedron_is_included_in P Q) && (hpolyhedron_is_included_in Q P).

Definition hpolyhedron_ext_eqP P Q :
  reflect (P =i Q) (hpolyhedron_ext_eq P Q).
Proof.
apply: (iffP idP).
- move/andP => [/hpolyhedron_is_included_inP H1 /hpolyhedron_is_included_inP H2] x.
  apply/idP/idP; [exact: (H1 x) | exact: (H2 x)].
- move => H.
  by apply/andP; split; apply/hpolyhedron_is_included_inP => x; rewrite (H x).
Qed.

Lemma hpolyhedron_ext_eq_refl :
  reflexive hpolyhedron_ext_eq.
Proof.
by move => P; apply/hpolyhedron_ext_eqP.
Qed.

Lemma hpolyhedron_ext_eq_sym :
  symmetric hpolyhedron_ext_eq.
Proof.
move => P Q.
by apply/idP/idP; move/hpolyhedron_ext_eqP => H;
  apply/hpolyhedron_ext_eqP => x; move: (H x).
Qed.

Lemma hpolyhedron_ext_eq_trans :
  transitive hpolyhedron_ext_eq.
Proof.
move => ? ? ? /hpolyhedron_ext_eqP H /hpolyhedron_ext_eqP H'.
apply/hpolyhedron_ext_eqP => x.
by move: (H x); rewrite (H' x).
Qed.

Lemma hpolyhedron_ext_eq_is_equivalence_rel :
  equivalence_rel hpolyhedron_ext_eq.
Proof.
apply/equivalence_relP; split.
- exact: hpolyhedron_ext_eq_refl.
- move => ? ? ?.
  rewrite /eqfun => ?.
  by apply/idP/idP; apply: hpolyhedron_ext_eq_trans; [rewrite hpolyhedron_ext_eq_sym | done].
Qed.

Canonical hpoly_equiv_rel : equiv_rel 'hpoly[R]_n :=
  EquivRel hpolyhedron_ext_eq hpolyhedron_ext_eq_refl hpolyhedron_ext_eq_sym hpolyhedron_ext_eq_trans.

End ExtensionalEquality.

(*Notation "P ==e Q" := (P == Q %[mod_eq (hpoly_equiv_rel _ _)])%qT (at level 0).
Notation "P =e Q" := (P = Q %[mod_eq (hpoly_equiv_rel _ _)])%qT (at level 0).*)

Section HPolyEq.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Inductive hpolyEq (base : 'hpoly[R]_n) := HPolyEq of {set 'I_(#ineq base)}.

Definition eq_set base (Q : hpolyEq base) := let: HPolyEq J := Q in J.

End Def.

Notation "''hpolyEq(' base )" := (@hpolyEq _ _ base) (at level 0, format "''hpolyEq(' base )").
Notation "\eq_set P" := (eq_set P) (at level 0, format "\eq_set P").

Definition hpoly_of_hpolyEq (R : realFieldType) (n : nat) (base : 'hpoly[R]_n) :=
  (* why do we need to specify R and n as arguments if we want to avoid UIP failure in the coercion? *)
  let: 'P(A,b) as P := base in
  fun (Q: 'hpolyEq(P)) =>
    let: HPolyEq J := Q in
    let A' := col_mx A (- (row_submx A J)) in
    let b' := col_mx b (- (row_submx b J)) in
    locked 'P(A', b').

Coercion hpoly_of_hpolyEq : hpolyEq >-> hpolyhedron.

Section StructEq.

Variable R : realFieldType.
Variable n : nat.
Variable base : 'hpoly[R]_n.

Fact eq_setK : cancel (@eq_set _ _ base) (@HPolyEq _ _ base).
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

End StructEq.

Section PolyNF.

Variable R : realFieldType.
Variable n : nat.

Definition implicit_eq (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :=
  let: 'P(A,b) as P' := base return {set 'I_(#ineq P')} in
  [ set i : 'I_(#ineq P') |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].

Lemma implicit_eqP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (Q : 'hpolyEq('P(A,b))) i :
  reflect (forall x, x \in Q -> (A *m x) i 0 = b i 0)
          (i \in implicit_eq Q).
Proof.
apply: (iffP idP) => [i_in_implicit_eq x x_in_P | ineq_i_is_sat].
- rewrite /implicit_eq //= in i_in_implicit_eq;
    rewrite inE in i_in_implicit_eq.
  rewrite -row_vdot.
  exact: ((is_included_in_hyperplaneP _ _  _ i_in_implicit_eq) x x_in_P).
- rewrite inE.
  apply/is_included_in_hyperplaneP => x x_in_P.
  rewrite row_vdot.
  by apply: ineq_i_is_sat.
Qed.

Definition has_normal_form (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :=
  \eq_set Q == implicit_eq Q.

Inductive hpolyNF (base : 'hpoly[R]_n) :=
  HPolyNF (Q : 'hpolyEq(base)) of (has_normal_form Q).

Notation "''hpolyNF(' base )" := (hpolyNF base) (at level 0, format "''hpolyNF(' base )").

Section StructNF.

Variable base: 'hpoly[R]_n.
Coercion hpolyEq_of_hpolyNF (Q : 'hpolyNF(base)) := let: HPolyNF Q' _ := Q in Q'.
Canonical hpolyNF_subType := [subType for hpolyEq_of_hpolyNF].
Definition hpolyNF_eqMixin := Eval hnf in [eqMixin of hpolyNF base by <:].
Canonical hpolyNF_eqType := Eval hnf in EqType 'hpolyNF(base) hpolyNF_eqMixin.
Definition hpolyNF_choiceMixin := [choiceMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_choiceType := Eval hnf in ChoiceType 'hpolyNF(base) hpolyNF_choiceMixin.
Definition hpolyNF_countMixin := [countMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_countType := Eval hnf in CountType 'hpolyNF(base) hpolyNF_countMixin.
Canonical hpolyNF_subCountType := [subCountType of 'hpolyNF(base)].
Definition hpolyNF_finMixin := [finMixin of 'hpolyNF(base) by <:].
Canonical hpolyNF_finType := Eval hnf in FinType 'hpolyNF(base) hpolyNF_finMixin.
Canonical hpolyNF_subFinType := [subFinType of 'hpolyNF(base)].

End StructNF.

End PolyNF.

Notation "''hpolyNF(' base )" := (@hpolyNF _ _ base) (at level 0, format "''hpolyNF(' base )").

Section UnfixedBase.

Record hpolyEqS (R : realFieldType) (n : nat) :=
  (* the Sigma-type based on hpolyNF *)
  HPolyEqS { base: 'hpoly[R]_n; hpolyeq_with_base :> 'hpolyNF(base) }.

Notation "''hpolyEq[' R ]_ n" := (hpolyEqS R n) (at level 0, format "''hpolyEq[' R ]_ n").
Notation "''hpolyEq_' n" := (hpolyEq _ n) (at level 0, only parsing).
Notation "\base P" := (base P) (at level 0, format "\base P").
Notation "''P^=' ( P ; J )" := (@HPolyEqS _ _ P (HPolyEq J)) (at level 0, format "''P^=' ( P ; J )").
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J) (at level 0, format "''P^=' ( A ,  b ;  J )").

Variable R : realFieldType.
Variable n : nat.

Lemma hpolyEq_inE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  let P := 'P(A,b) in
    forall J : {set 'I_(#ineq P)},
      (x \in HPolyEq J) = (x \in P) && [forall j in J, (A *m x) j 0 == b j 0].
Proof.
move => P J /=.
unlock.
rewrite inE mul_col_mx col_mx_lev mulNmx -row_submx_mul lev_opp2 /=.
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


(* TODO: define a point in the relative interior *)
Section RelativeInterior.

Lemma hpolyNF_relint_pointP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m)
      (Q : 'hpolyNF('P(A,b))) :
        exists x, (x \in Q /\ (forall i, i \notin (\eq_set Q) -> (A *m x) i 0 > b i 0)).
Proof.
Admitted.

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

Let of_hpolyEqS (P : 'hpolyEq[R]_n) : { Q : 'hpoly[R]_n & 'hpolyNF(Q) } :=
  Tagged (fun Q : ('hpoly[R]_n) => 'hpolyNF(Q)) (hpolyeq_with_base P).

Fact of_hpolyEqSK : cancel of_hpolyEqS (fun x => HPolyEqS (tagged x)).
Proof.
by move => P; case: P.
Qed.

Definition hpolyEqS_eqMixin := CanEqMixin of_hpolyEqSK.
Canonical hpolyEqS_eqType := Eval hnf in EqType 'hpolyEq[R]_n hpolyEqS_eqMixin.

Definition hpolyEqS_choiceMixin := CanChoiceMixin of_hpolyEqSK.
Canonical hpolyEqS_choiceType :=
  Eval hnf in ChoiceType 'hpolyEq[R]_n hpolyEqS_choiceMixin.

End Mixins.

(* TODO: not working, why ??? *)
(*
Definition implicit_eq (Q: hpolyEq) :=
  let: 'P^= (P; _) := Q in
  let: 'P(A,b) as P := P in
  [ set i : 'I_(#ineq P) |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].

Definition implicit_eq (Q: hpolyEq) :=
  match Q return {set 'I_(#ineq (\base Q))} with
  | HPolyEq (HPolyhedron _ A b as P) _ =>
  [ set i | is_included_in_hyperplane Q (row i A)^T (b i 0) ]
  end.
*)

(* This work but apparently this is not very usable *)
(*Definition implicit_eq (Q: hpolyEq) :=
  let: 'P(A, b) as P := \base Q in
  [ set i : 'I_(#ineq P) |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].*)


End UnfixedBase.

End HPolyEq.

Notation "''hpolyNF(' base )" := (@hpolyNF _ _ base) (at level 0, format "''hpolyNF(' base )").
Notation "''hpolyEq(' base )" := (@hpolyEq _ _ base) (at level 0, format "''hpolyEq(' base )").
Notation "''hpolyEq[' R ]_ n" := (hpolyEqS R n) (at level 0, format "''hpolyEq[' R ]_ n").
Notation "''hpolyEq_' n" := (hpolyEq _ n) (at level 0, only parsing).
Notation "\base P" := (base P) (at level 0, format "\base P").
Notation "\eq_set P" := (eq_set P) (at level 0, format "\eq_set P").
Notation "''P^=' ( P ; J )" := (@HPolyEqS _ _ P (HPolyEq J)) (at level 0, format "''P^=' ( P ; J )").
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J) (at level 0, format "''P^=' ( A ,  b ;  J )").

Section ExtensionalEqualityEq.

Variable R : realFieldType.
Variable n : nat.

Definition hpolyEq_ext_eq := [ rel P Q : 'hpolyEq[R]_n | hpolyhedron_ext_eq P Q ].

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
Notation "P =e Q" := (P = Q %[mod_eq (hpolyEq_equiv_rel _ _)])%qT (at level 0).

Section HFace.

Variable n : nat.
Variable R : realFieldType.
Variable base : 'hpoly[R]_n.
Variable P : 'hpolyNF(base).

Definition hface_of :=
  [ pred Q : 'hpolyEq[R]_n |
    non_empty Q && [exists R : 'hpolyNF(base), (\eq_set P \subset \eq_set R) && (Q ==e (HPolyEqS R)) ] ].

Hypothesis P_non_empty : non_empty P.

Lemma hface_ofP (Q : 'hpolyEq[R]_n) :
  reflect (exists c, bounded P c /\ forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in Q)))
          (hface_of Q).
Proof.
Admitted.

End HFace.

Module HPolyPrim.

Definition non_empty := non_empty.
Definition bounded := bounded.
Definition unbounded := unbounded.
Definition opt_point := opt_point.
Definition opt_value := opt_value.

End HPolyPrim.

(*
Definition normal_form P := HPolyEq (implicit_eq P).

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
    exact: ((implyP ((forallP (proj2 (andP x_in_nf))) i)) ((subsetP (subset_of_implicit_eq P)) _ i_in_I_P)).
Qed.*)

End HPolyEq.

Section HPolyNF.

Variable R : realFieldType.
Variable n : nat.

Definition has_normal_form (P : 'hpolyEq[R]_n) :=
  (\eq_set P == implicit_eq P).

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
- exact: subset_of_implicit_eq.
- apply/subsetP => i /implicit_eqP i_in_I_nfP.
  rewrite /normal_form /=.
  apply/implicit_eqP => x x_in_P.
  apply: i_in_I_nfP.
  by rewrite -(normal_formP P x).
Qed.

Definition hpolyNF_of_hpolyEq P :=
  HPolyNF (normal_form_has_normal_form P).
Coercion hpoly_of_subset_of_hpoly_nf P :=
  let: HPolyNF Q _ := P in Q.

Canonical hpolyhedron_nf_subtype := [subType for hpoly_of_subset_of_hpoly_nf].

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
        (\eq_set P \subset J) && (Q ==e 'P^=(\base P; J)) ]].

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