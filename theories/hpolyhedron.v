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

Section CustomPred.

Variable custom_pred : pred 'cV[R]_n.

Record hpolyhedron_custom :=
  HPolyhedronCustom { P :> hpolyhedron; pred_equiv: forall x, x \in P = custom_pred x }.

Definition inE := (pred_equiv, inE).

End CustomPred.

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

Definition hpolyhedron_eq : rel (hpolyhedron R n) :=
    fun P Q => (hpolyhedron_is_included_in P Q) && (hpolyhedron_is_included_in Q P).

Definition hpolyhedron_eqP P Q :
  reflect (P =i Q) (hpolyhedron_eq P Q).
Proof.
apply: (iffP idP).
- move/andP => [/hpolyhedron_is_included_inP H1 /hpolyhedron_is_included_inP H2] x.
  apply/idP/idP; [exact: (H1 x) | exact: (H2 x)].
- move => H.
  by apply/andP; split; apply/hpolyhedron_is_included_inP => x; rewrite (H x).
Qed.

Lemma hpolyhedron_eq_refl :
  reflexive hpolyhedron_eq.
Proof.
by move => P; apply/hpolyhedron_eqP.
Qed.

Lemma hpolyhedron_eq_sym :
  symmetric hpolyhedron_eq.
Proof.
move => P Q.
by apply/idP/idP; move/hpolyhedron_eqP => H;
  apply/hpolyhedron_eqP => x; move: (H x).
Qed.

Lemma hpolyhedron_eq_trans :
  transitive hpolyhedron_eq.
Proof.
move => ? ? ? /hpolyhedron_eqP H /hpolyhedron_eqP H'.
apply/hpolyhedron_eqP => x.
by move: (H x); rewrite (H' x).
Qed.

Lemma hpolyhedron_eq_is_equivalence_rel :
  equivalence_rel hpolyhedron_eq.
Proof.
apply/equivalence_relP; split.
- exact: hpolyhedron_eq_refl.
- move => ? ? ?.
  rewrite /eqfun => ?.
  by apply/idP/idP; apply: hpolyhedron_eq_trans; [rewrite hpolyhedron_eq_sym | done].
Qed.

Canonical hpolyhedron_eq_equiv_rel : equiv_rel (hpolyhedron R n) :=
  EquivRel hpolyhedron_eq hpolyhedron_eq_refl hpolyhedron_eq_sym hpolyhedron_eq_trans.

End ExtensionalEquality.
