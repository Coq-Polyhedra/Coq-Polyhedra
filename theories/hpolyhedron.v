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
  HPolyhedron { m : nat ;
                A : 'M[R]_(m,n) ;
                b : 'cV[R]_m }.

Definition mem_hpolyhedron (P : hpolyhedron) :=
  [pred x : 'cV_n | ((A P) *m x) >=m (b P)].

Coercion pred_of_hpolyhedron (P : hpolyhedron) : pred_class := mem_hpolyhedron P.
Canonical hpolyhedron_predType := @mkPredType _ hpolyhedron pred_of_hpolyhedron.
Canonical mem_hpolyhedron_predType := mkPredType mem_hpolyhedron.

Notation "''P' ( A , b )" := (HPolyhedron A b) (at level 0, format "''P' ( A ,  b )").

Definition extract_matrix (P: hpolyhedron) := let: 'P(A,_) := P return 'M[R]_(m P, n) in A.

Section Ex.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Fact foo : extract_matrix 'P(A,b) = A.
done.
Qed.

End Ex.


Definition feasible_dir (P : hpolyhedron) := S.feasible_dir (A P).

Lemma feasible_dirP (P : hpolyhedron) d :
  reflect (forall x, forall lambda, x \in P -> lambda >= 0 -> x + lambda *: d \in P)
          (feasible_dir P d).
Proof.
apply: (iffP idP) => [/= feasible_dir_d x lambda x_in_P lambda_pos | H].
- rewrite inE mulmxDr -[(b P)]addr0.
  apply: lev_add; first exact: x_in_P.
  rewrite -scalemxAr -(scaler0 _ lambda).
  by apply: lev_wpscalar.
- (* RK: this implication does not seem to hold if we do not assume, for example, that P is non_empty*)
Admitted.

Definition matrix_from_hpolyhedron (P : hpolyhedron) :=
  Tagged (fun m => 'M[R]_(m,n+1)) (row_mx (A P) (b P)).

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

Notation "''P' ( A , b )" := (HPolyhedron A b) (at level 0, format "''P' ( A ,  b )").


Section BasicPrimitives.

Variable R : realFieldType.
Variable n : nat.

Implicit Types P Q : (hpolyhedron R n).
Implicit Type c : 'cV[R]_n.

Definition non_empty P := (S.Simplex.feasible (A P) (b P)).
Definition bounded P c := (S.Simplex.bounded (A P) (b P) c).
Definition unbounded P c := (S.Simplex.unbounded (A P) (b P) c).
Definition opt_point P c := (S.Simplex.opt_point (A P) (b P) c).
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

Variable P : hpolyhedron R n.

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
apply: (iffP idP) => [/andP [is_included is_included_opp] x x_in_P | H].
- apply/eqP; rewrite eqr_le.
  apply/andP; split.
  + move: ((is_included_in_halfspaceP _ _ is_included_opp) x x_in_P).
    by rewrite vdotNl ler_opp2.
  + exact: ((is_included_in_halfspaceP _ _ is_included) x x_in_P).
- apply/andP; split; apply/is_included_in_halfspaceP => x x_in_P.
  + by rewrite (H x x_in_P).
  + by rewrite -(H x x_in_P) vdotNl.
Qed.

Variable Q : hpolyhedron R n.

Definition hpolyhedron_is_included_in :=
  [forall i, is_included_in_halfspace (row i (A Q))^T ((b Q) i 0)].

Lemma hpolyhedron_is_included_inP :
  reflect {subset P <= Q} hpolyhedron_is_included_in.
Proof.
apply: (iffP idP).
- move => /forallP H x Hx.
  apply/forallP => i.
  move/is_included_in_halfspaceP: (H i) => Hi.
  move: (Hi x Hx).
  by rewrite -[(A Q *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
- move => H.
  apply/forallP => i.
  apply/is_included_in_halfspaceP => x Hx.
  move/forallP: (H x Hx) => Hx'.
  move: (Hx' i).
  by rewrite -[(A Q *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
Qed.

End Inclusion.

Section ExtensionalEquality.

Variable R : realFieldType.
Variable n : nat.

Definition hpolyhedron_ext_eq : rel (hpolyhedron R n) :=
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

Canonical hpolyhedron_equiv_rel : equiv_rel (hpolyhedron R n) :=
  EquivRel hpolyhedron_ext_eq hpolyhedron_ext_eq_refl hpolyhedron_ext_eq_sym hpolyhedron_ext_eq_trans.

End ExtensionalEquality.

Section HPolyhedronWithImplicitEq.

Variable R : realFieldType.
Variable n : nat.

Section HPolyhedronOfSubset.

(* TODO: introduction notation *)
(*Notation "{ x | A *m x >=m b }" := (HPolyhedron A b).
Notation "{ x | A *m x >=m b with eq on I }" ...*)

Definition A_of_subset (P : hpolyhedron R n) I :=
  col_mx (A P) (- (row_submx (A P) I)).
Definition b_of_subset (P : hpolyhedron R n) I :=
  col_mx (b P) (- (row_submx (b P) I)).

Record hpoly_of_subset :=
  HPolyhedronOfSubset {
      base : hpolyhedron R n;
      I : {set 'I_(m base)} }.

Notation "''P' ( A , b , I )" := (@HPolyhedronOfSubset 'P(A,b) I) (at level 0, format "''P' ( A ,  b ,  I )").

Section Ex.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Check ('P (A,b)).
Variable I : {set 'I_m}.
Check 'P(A,b,I).
End Ex.

Coercion hpoly_of_hpoly_of_subset P :=
  HPolyhedron (A_of_subset (I P)) (b_of_subset (I P)).

Lemma hpoly_of_subset_inE P (I : {set 'I_(m P)}) x :
  x \in HPolyhedron (A_of_subset I) (b_of_subset I) = (x \in P) && [forall i in I, ((A P) *m x) i 0 == (b P) i 0].
Proof.
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
Qed.

Definition poly_inE := hpoly_of_subset_inE.
Definition inE := (poly_inE, inE).

Section Mixins.

Let f (P : hpoly_of_subset) : { Q : hpolyhedron R n & {set 'I_(m Q)} } :=
  Tagged (fun Q : (hpolyhedron R n) => {set 'I_(m Q)}) (I P).
Let g (x : { Q : hpolyhedron R n & {set 'I_(m Q)} }) :=
  HPolyhedronOfSubset (tagged x).

Fact cancel_f_g : cancel f g.
Proof.
by move => P; case: P.
Qed.

Definition hpoly_of_subset_eqMixin := CanEqMixin cancel_f_g.
Canonical hpoly_of_subset_eqType := Eval hnf in EqType hpoly_of_subset hpoly_of_subset_eqMixin.

Definition hpoly_of_subset_choiceMixin := CanChoiceMixin cancel_f_g.
Canonical hpoly_of_subset_choiceType := Eval hnf in ChoiceType hpoly_of_subset hpoly_of_subset_choiceMixin.

End Mixins.

Definition implicit_eq P :=
  let P0 := base P in
  let A0 := A P0 in
  let b0 := b P0 in
  [ set i : 'I_(m P0) |
    is_included_in_hyperplane P (row i A0)^T (b0 i 0) ].

Lemma implicit_eqP P i :
  let P0 := base P in
  let A0 := A P0 in
  let b0 := b P0 in
  reflect (forall x, x \in P -> (A0 *m x) i 0 = b0 i 0)
          (i \in implicit_eq P).
Proof.
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
  I P \subset implicit_eq P.
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

Definition normal_form P :=
  HPolyhedronOfSubset (implicit_eq P).

Lemma normal_formP (P : hpoly_of_subset) :
  (* TODO: perhaps we should use ext_eq over polyhedra rather than over boolean predicates *)
  (P : (hpolyhedron R n)) =i (normal_form P).
Proof.
move => x.
apply/idP/idP => [x_in_P | x_in_nf].
- rewrite hpoly_of_subset_inE /=.
  apply/andP; split.
  + rewrite hpoly_of_subset_inE in x_in_P.
    exact: (proj1 (andP x_in_P)).
  + apply/forallP => i.
    apply/implyP => i_in_implicit.
    rewrite inE in i_in_implicit.
    move/is_included_in_hyperplaneP: i_in_implicit => in_hyperplane.
    by rewrite -((in_hyperplane x) x_in_P) row_vdot.
- rewrite hpoly_of_subset_inE.
  apply/andP; split; rewrite hpoly_of_subset_inE /= in x_in_nf.
  + exact: (proj1 (andP x_in_nf)).
  + apply/forallP => i.
    apply/implyP => i_in_I_P.
    exact: ((implyP ((forallP (proj2 (andP x_in_nf))) i)) ((subsetP (subset_of_implicit_eq P)) _ i_in_I_P)).
Qed.

End HPolyhedronOfSubset.

Section HPolyhedronNF.

Definition has_normal_form P := (I P == implicit_eq P).

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

Inductive hpolyhedron_nf := HPolyhedronEq (P : hpoly_of_subset) of has_normal_form P.

Coercion hpoly_of_subset_of_hpoly_nf P :=
  let: HPolyhedronEq Q _ := P in Q.
Canonical hpolyhedron_nf_subtype := [subType for hpoly_of_subset_of_hpoly_nf].

Section Mixins.
Definition hpoly_nf_eqMixin := Eval hnf in [eqMixin of hpolyhedron_nf by <:].
Canonical hpoly_nf_eqType := Eval hnf in EqType hpolyhedron_nf hpoly_nf_eqMixin.
Definition hpoly_nf_choiceMixin := Eval hnf in [choiceMixin of hpolyhedron_nf by <:].
Canonical hpoly_nf_choiceType := Eval hnf in ChoiceType hpolyhedron_nf hpoly_nf_choiceMixin.
End Mixins.

End HPolyhedronNF.


Section HFace.

Variable n : nat.
Variable R : realFieldType.

Variable P : hpolyhedron_eq R n.

Definition face_of :=
  [qualify a Q | [exists J : {set 'I_(m (base P))}, ((I P) \subset J) && hpolyhedron_ext_eq Q (HPolyhedronEq (base P) J ... ...)]].

                                                                                            hpolyhedron_of_subset J) ]].
