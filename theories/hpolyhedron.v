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
Definition matrix_of (P: hpolyhedron) :=
  let: 'P(A,_) := P return 'M[R]_(#ineq P, n) in A.

Definition vector_of (P: hpolyhedron) :=
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

(* TODO: feasible_dir is a bad name, this should be recession direction, or
   asymptotic direction *)
Definition feasible_dir (P : hpolyhedron) :=
  let: 'P(A,_) := P in
  S.feasible_dir A.

Lemma feasible_dirP (P : hpolyhedron) d :
  reflect (forall x, forall lambda, x \in P -> lambda >= 0 -> x + lambda *: d \in P)
          (feasible_dir P d).
Proof.
case: P => m A b.
apply: (iffP idP) => [/= feasible_dir_d x lambda x_in_P lambda_pos | H].
- rewrite inE mulmxDr -[b]addr0.
  apply: lev_add; first exact: x_in_P.
  rewrite -scalemxAr -(scaler0 _ lambda).
  by apply: lev_wpscalar.
- (* RK: this implication does not seem to hold if we do not assume, for example, that P is non_empty*)
Admitted.

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

Implicit Types P Q : 'hpoly[R]_n.
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

(*Lemma boundedP P c :
  reflect ((exists x, x \in P /\ '[c,x] = opt_value P c) /\ (forall y, y \in P -> opt_value P c <= '[c,y])) (bounded P c).
Admitted.

Lemma opt_value_is_optimal P c x :
  (x \in P) -> (forall y, y \in P -> '[c,x] <= '[c,y]) -> '[c,x] = opt_value P c.
Admitted.

Lemma unboundedP P c :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded P c).
Admitted.*)

End BasicPrimitives.

Section Inclusion.

Variable R : realFieldType.
Variable n : nat.

Variable P : 'hpoly[R]_n.

Definition is_included_in_halfspace c d :=
  (non_empty P) ==> (bounded P c && (opt_value P c >= d)).

Lemma is_included_in_halfspaceP c d :
  reflect (forall x, x \in P -> '[c,x] >= d) (is_included_in_halfspace c d).
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

Notation "P ==e Q" := (P == Q %[mod_eq (hpoly_equiv_rel _ _)])%qT (at level 0).
Notation "P =e Q" := (P = Q %[mod_eq (hpoly_equiv_rel _ _)])%qT (at level 0).

Section ImplicitEqualities.

Section HPolyEq.

Variable R : realFieldType.
Variable n : nat.

Record hpolyEq :=
  HPolyEq { base: 'hpoly[R]_n;
            eq_set: {set 'I_(#ineq base)} }.

Notation "\base P" := (base P) (at level 0).
Notation "\eq_set P" := (eq_set P) (at level 0).

Coercion hpoly_of_hpolyEq (Q: hpolyEq) :=
  (* TODO : remove calls to matrix_of and vector_of,
   * and use destructive assignments instead *)
  let P := \base Q in
  let I := \eq_set Q in
  let A := matrix_of P in
  let b := vector_of P in
  let AI := col_mx A (- (row_submx A I)) in
  let bI := col_mx b (- (row_submx b I)) in
  'P(AI, bI).

Notation "''P^=' ( P ; J )" := (@HPolyEq P J) (at level 0, format "''P^=' ( P ; J )").
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J) (at level 0, format "''P^=' ( A ,  b ;  J )").

Section Ex.

(* TODO: none below is working, why? *)
(*
Let foo (Q : hpoly_eq) :=
  let: 'P^= (A, b; J) := P return 'M[R]_(#ineq (\base Q), n) in A.

Let foo (Q : hpoly_eq) :=
  let: 'P^= (P ; _) := Q in
  let: 'P (A, b) := P return 'M[R]_(#ineq (\base Q), n) in A.

Let foo (Q : hpoly_eq) :=
  let: 'P(A,b) := \base Q return 'M[R]_(#ineq (\base Q), n) in A.
*)
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Check ('P (A,b)).
Variable I : {set 'I_m}.
Check 'P^= (A,b;I).
End Ex.


Lemma hpolyEq_inE (m: nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) (J : {set 'I_m}) x :
  (x \in 'P^= (A, b; J)) = (x \in 'P(A, b)) && [forall j in J, (A *m x) j 0 == b j 0].
(*Proof.
rewrite inE mul_col_mx col_mx_lev mulNmx -row_submx_mul lev_opp2.
apply/andP/andP.
- move => [x_in_P ineqI]; split; try by done.
  suff /row_submx_colP H: row_submx (A P *m x) I = row_submx (b P) I.
  + apply/forall_inP => i i_in_I.
    move/(_ _ i_in_I): H ->; exact: eq_refl.
  + apply: lev_antisym; apply/andP; split; try by done.
    exact: row_submx_lev.
- move => [x_in_P /forall_inP eqI]; split; try by done.
  apply/row_submx_levP => i i_in_I.
  by move/(_ _ i_in_I)/eqP: eqI ->.
Qed.*)
Admitted.

Definition poly_inE := hpolyEq_inE.
Definition inE := (poly_inE, inE).

Section Mixins.

Let f (P : hpolyEq) : { Q : 'hpoly[R]_n & {set 'I_(#ineq Q)} } :=
  Tagged (fun Q : ('hpoly[R]_n) => {set 'I_(#ineq Q)}) (\eq_set P).
Let g (x : { Q : 'hpoly[R]_n & {set 'I_(#ineq Q)} }) :=
  'P^= (tag x; tagged x).

Fact cancel_f_g : cancel f g.
Proof.
by move => P; case: P.
Qed.

Definition hpolyEq_eqMixin := CanEqMixin cancel_f_g.
Canonical hpolyEq_eqType := Eval hnf in EqType hpolyEq hpolyEq_eqMixin.

Definition hpolyEq_choiceMixin := CanChoiceMixin cancel_f_g.
Canonical hpolyEq_choiceType := Eval hnf in ChoiceType hpolyEq hpolyEq_choiceMixin.

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

Definition implicit_eq (Q : hpolyEq) :=
  let P := \base Q in
  let A := matrix_of P in
  let b := vector_of P in
  [ set i : 'I_(#ineq P) |
    is_included_in_hyperplane Q (row i A)^T (b i 0) ].

Lemma implicit_eqP Q i :
  let P := \base Q in
  let A := matrix_of P in
  let b := vector_of P in
  reflect (forall x, x \in Q -> (A *m x) i 0 = b i 0)
          (i \in implicit_eq Q).
Proof.
move => P A b.
apply: (iffP idP) => [i_in_implicit_eq x x_in_P | H].
- rewrite inE in i_in_implicit_eq.
  rewrite -row_vdot.
  exact: ((is_included_in_hyperplaneP _ _  _ i_in_implicit_eq) x x_in_P).
- rewrite inE.
  apply/is_included_in_hyperplaneP => x x_in_P.
  rewrite row_vdot.
  by apply: H.
Qed.

Lemma subset_of_implicit_eq P :
  \eq_set P \subset implicit_eq P.
Proof.
apply/subsetP => i i_in_I_P.
rewrite inE.
apply/andP; split;
apply/is_included_in_halfspaceP => x x_in_P;
rewrite inE in x_in_P; move/andP: x_in_P => [/forallP x_in_baseP in_I_P].
+ rewrite row_vdot.
  exact: (x_in_baseP i).
+ by rewrite vdotNl row_vdot (eqP (implyP ((forallP in_I_P) i) i_in_I_P)).
Qed.

Definition normal_form P := HPolyEq (implicit_eq P).

Lemma normal_formP (P : hpolyEq) :
  (* TODO: perhaps we should use ext_eq over polyhedra rather than over boolean predicates *)
  (P : 'hpoly[R]_n) =i (normal_form P).
Proof.
move => x.
apply/idP/idP => [x_in_P | x_in_nf].
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
Qed.

End HPolyEq.

Notation "\base P" := (base P) (at level 0).
Notation "\eq_set P" := (eq_set P) (at level 0).
Notation "''P^=' ( P ; J )" := (@HPolyEq _ _ P J) (at level 0, format "''P^=' ( P ; J )").
Notation "''P^=' ( A , b ; J )" := 'P^=('P (A,b);J) (at level 0, format "''P^=' ( A ,  b ;  J )").
Notation "''hpolyEq[' R ]_ n" := (hpolyEq R n) (at level 0, format "''hpolyEq[' R ]_ n").
Notation "''hpolyEq_' n" := (hpolyEq _ n) (at level 0, only parsing).

Section HPolyNF.

Variable R : realFieldType.
Variable n : nat.

Definition has_normal_form (P: 'hpolyEq[R]_n) := (\eq_set P == implicit_eq P).

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

Coercion hpoly_of_subset_of_hpoly_nf P :=
  let: HPolyNF Q _ := P in Q.
Canonical hpolyhedron_nf_subtype := [subType for hpoly_of_subset_of_hpoly_nf].

Section Mixins.
Definition hpoly_nf_eqMixin := Eval hnf in [eqMixin of hpolyNF by <:].
Canonical hpoly_nf_eqType := Eval hnf in EqType hpolyNF hpoly_nf_eqMixin.
Definition hpoly_nf_choiceMixin := Eval hnf in [choiceMixin of hpolyNF by <:].
Canonical hpoly_nf_choiceType := Eval hnf in ChoiceType hpolyNF hpoly_nf_choiceMixin.
End Mixins.

End HPolyNF.

Notation "''hpolyNF[' R ]_ n" := (hpolyNF R n) (at level 0, format "''hpolyNF[' R ]_ n").
Notation "''hpolyNF_' n" := (hpolyNF _ n) (at level 0, only parsing).

Section HFace.

Variable n : nat.
Variable R : realFieldType.

Variable P : 'hpolyNF[R]_n.

Definition face_of :=
  [ qualify a Q : 'hpolyNF[R]_n |
    [exists J : {set 'I_(#ineq \base P)},
        (\eq_set P \subset J) && (Q ==e 'P^=(\base P; J)) ]].

Lemma face_ofP (Q : 'hpolyNF[R]_n) :
  reflect (exists c, forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in Q)))
          (Q \is a face_of).
Admitted.

End HFace.