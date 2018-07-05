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
Require Import simplex exteqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''hpoly[' R ]_ n" (at level 8, n at level 2, format "''hpoly[' R ]_ n").
Reserved Notation "''hpoly_' n" (at level 8, n at level 2).
Reserved Notation "'#ineq' P" (at level 10, P at level 0, format "'#ineq'  P").
Reserved Notation "''P' ( m , A , b )" (at level 0, m at level 99, A at level 99, b at level 99, format "''P' ( m  , A ,  b )").
Reserved Notation "''P' ( A , b )" (at level 0, A at level 99, b at level 99, format "''P' ( A ,  b )").
Reserved Notation "''hpolyEq(' base )" (at level 8, base at level 99, format "''hpolyEq(' base )").
Reserved Notation "\eq P" (at level 10, P at level 8, format "\eq  P").
Reserved Notation "\active P" (at level 10, P at level 8, format "\active  P").
Reserved Notation "''hpolyEq[' R ]_ n" (at level 8, n at level 2, format "''hpolyEq[' R ]_ n").
Reserved Notation "''hpolyEq_' n" (at level 8, n at level 2).
Reserved Notation "\base P" (at level 10, P at level 8, format "\base  P").
Reserved Notation "''P^=' ( P ; J )" (at level 0, P at level 99, J at level 99, format "''P^=' ( P ; J )").
Reserved Notation "''P^=' ( A , b ; J )" (at level 0, A at level 99, b at level 99, J at level 99, format "''P^=' ( A ,  b ;  J )").
Reserved Notation "''hpolyNF(' base )" (at level 8, base at level 99, format "''hpolyNF(' base )").
Reserved Notation "''hpolyNF[' R ]_ n" (at level 8, n at level 2, format "''hpolyNF[' R ]_ n").
Reserved Notation "''hpolyNF_' n" (at level 8, n at level 2).

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section HPoly.

Section Def. (* TODO: reorganize this section so that we can introduce the notation 'hpoly as soon as possible*)

Variable R : realFieldType.
Variable n : nat.

Record hpoly := Hpoly {
  nb_ineq : nat ;
  _ : 'M[R]_(nb_ineq,n) ;
  _ : 'cV[R]_nb_ineq
}.

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
Canonical mem_hpoly_PredType := mkPredType (@mem_hpoly R n). (* RK: It seems that this is not used and it causes a warning *)

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

Lemma lp_stateP c P :
  lp_state c P (opt_point c P) (non_empty P) (bounded c P) (unbounded c P).
Proof.
case: P => m A b.
rewrite /opt_point /non_empty /bounded /unbounded.
case: (Simplex.simplexP A b c) =>
  [ d /(intro_existsT (Simplex.infeasibleP _ _))/negP P_empty
  | [x d] /= [Hx Hd Hd'] | [x d] /= [Hx Hd Hdx] ].
- move/negP/negbTE: (P_empty) ->.
  have /negP/negbTE ->: ~ (Simplex.bounded A b c).
    move/Simplex.boundedP => [[x] [x_in_P _]] _.
    by move/(intro_existsT (Simplex.feasibleP _ _)): x_in_P.
  have /negP/negbTE ->: ~ (Simplex.unbounded A b c).
    move/Simplex.unboundedP/(_ 0) => [x [x_in_P _]].
    by move/(intro_existsT (Simplex.feasibleP _ _)): x_in_P.
  constructor.
  move => x; rewrite [RHS]inE; apply/negbTE/negP.
  by move/(intro_existsT (Simplex.feasibleP _ _)).
- have feasible_A_b: Simplex.feasible A b.
    by apply/Simplex.feasibleP; exists x.
  have unbounded_A_b_c: Simplex.unbounded A b c.
    apply/Simplex.unboundedP_cert.
    by exists (x , d).
  have /negbTE ->: ~~ (Simplex.bounded A b c).
    by rewrite -(Simplex.unbounded_is_not_bounded c feasible_A_b).
  rewrite feasible_A_b unbounded_A_b_c.
  constructor.
  move => K.
  exact: (unbounded_certificate K Hx Hd Hd').
- have feasible_A_b: Simplex.feasible A b.
    by apply/Simplex.feasibleP; exists x.
  have bounded_A_b_c: Simplex.bounded A b c.
    apply/Simplex.boundedP_lower_bound; first exact: feasible_A_b.
    exists '[ b, d].
    by apply/dual_feasible_bounded.
  have /negbTE ->: ~~ (Simplex.unbounded A b c).
    by rewrite -(Simplex.bounded_is_not_unbounded c feasible_A_b).
  rewrite feasible_A_b bounded_A_b_c.
  constructor.
  split.
  + exact: Simplex.opt_point_is_feasible.
  + exact: (proj2 (Simplex.boundedP _ _ _ bounded_A_b_c)).
Qed.

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
  non_empty P ->
    reflect (exists K, (forall z, z \in P -> '[c,z] >= K))
            (bounded c P).
Proof.
case: P => m A b.
move => P_non_empty.
suff ->: bounded c 'P(A,b) = ~~ (non_empty 'P(A,b)) || bounded c 'P(A,b)
  by exact: Simplex.infeasible_or_boundedP.
by rewrite P_non_empty /=.
Qed.

Lemma bounded_normal_cone (m: nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) (c: 'cV[R]_n) :
  bounded c 'P(A,b) ->
  exists u, [/\ u >=m 0, c = A^T *m u & opt_value c 'P(A, b) = Some '[b, u]].
Admitted.
(*Proof.
rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _.
move/and3P => [_ u_dual _]; exists u.
by rewrite inE in u_dual; move/andP: u_dual => [/eqP ? ?].
Qed.*)

Lemma normal_cone_bounded (m: nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) (u: 'cV[R]_m) :
  non_empty 'P(A, b) -> u >=m 0 -> bounded (A^T *m u) 'P(A,b).
Proof.
move => P_non_empty u_ge0; apply/bounded_certP; first by done.
exists '[u, b]; move => z z_in_P.
by rewrite -vdot_mulmx; apply: vdot_lev.
Qed.

Lemma opt_value_is_optimal c P x :
  (x \in P) -> (forall y, y \in P -> '[c,x] <= '[c,y]) ->
    opt_value c P = Some '[c,x].
Proof.
case: P => m A b.
move => x_in_P x_is_opt.
suff opt_point_P_c: opt_point c 'P(A, b) = Some (Simplex.opt_point A b c)
 by rewrite /opt_value opt_point_P_c (Simplex.opt_value_is_optimal x_in_P x_is_opt).
apply/ifT/boundedP.
by exists x.
Qed.

Lemma opt_value_csc (m : nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) (u: 'cV[R]_m) (x: 'cV[R]_n) :
  u >=m 0 -> x \in 'P(A,b) ->
  let c := A^T *m u in
  reflect (forall i, u i 0 > 0 -> (A *m x) i 0 = b i 0)
          ('[c,x] == '[b, u]).
Admitted.
(*
Proof.
move => u_ge0 x_in_P /=.
set c := A^T *m u.
have c_bounded: bounded c 'P(A, b).
- apply/normal_cone_bounded; try by done.
  by apply/non_emptyP; exists x.
have u_in_dual : u \in dual_polyhedron A c.
- by rewrite inE eq_refl.
set csc := forall i, _.
have csc_equiv_gap : reflect csc (compl_slack_cond A b x u).
- apply/(iffP idP).
(* stupid proof, because of the fact that compl_slack_cond has not the right formulation (and compl_slack_condP doesn't help) *)
  + move => Hcsc i u_i_gt0.
    move/forallP/(_ i): Hcsc; rewrite inE.
    by move/lt0r_neq0/negbTE: u_i_gt0 => -> /= /eqP.
  + move => Hcsc; apply/forallP => i; rewrite -[X in X || _]negbK.
    have ->: (u i 0 != 0) = (u i 0 > 0).
      by rewrite lt0r; move/gev0P/(_ i): u_ge0 ->; rewrite andbT.
    by rewrite -implybE; apply/implyP; rewrite inE; move/Hcsc ->.
rewrite -(compl_slack_cond_duality_gap_equiv (c := c)) // in csc_equiv_gap.
Search _ Simplex.bounded.

suff <-: (duality_gap b c x u == 0) = (opt_value c 'P(A, b) == Some '[c,x]) by [].
apply/eqP/eqP => [gap_eq0 |].
- apply/opt_value_is_optimal; try by done.
  exact: (duality_gap_eq0_optimality (u := u)).
- Search _ duality_gap.
  Search _ Simplex.opt_value.

  Search _ duality_gap.


Admitted.*)

Lemma unboundedP c P :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K)
          (unbounded c P).
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

Arguments non_empty [R n].
Arguments bounded [R n].
Arguments unbounded [R n].
Arguments non_emptyP [R n P].
Arguments boundedP [R n c P].
Arguments bounded_certP [R n c P].
Arguments unboundedP [R n c P].
Prenex Implicits non_emptyP boundedP bounded_certP unboundedP.

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
  case: (lp_stateP c P) => /= [ P_is_empty _
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

Definition is_included_in Q :=
  let: 'P(A,b) := Q in
    [forall i, is_included_in_halfspace (row i A)^T (b i 0)].

Lemma is_included_inP Q :
  reflect {subset P <= Q} (is_included_in Q).
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

Arguments is_included_in_hyperplaneP [R n P c d].
Prenex Implicits is_included_in_hyperplaneP.

Section ExtensionalEquality.

Variable R : realFieldType.
Variable n : nat.

Definition hpoly_ext_eq : rel 'hpoly[R]_n :=
    fun P Q => (is_included_in P Q) && (is_included_in Q P).

Definition hpoly_ext_eqP P Q :
  reflect (P =i Q) (hpoly_ext_eq P Q).
Proof.
apply: (iffP idP).
- move/andP => [/is_included_inP H1 /is_included_inP H2] x.
  apply/idP/idP; [exact: (H1 x) | exact: (H2 x)].
- move => H.
  by apply/andP; split; apply/is_included_inP => x; rewrite (H x).
Qed.

Definition hpolyExtEqMixin := ExtEqMixin hpoly_ext_eqP.
Canonical hpoly_extEqType := Eval hnf in ExtEqType _ _ hpolyExtEqMixin.

End ExtensionalEquality.

End HPrim.

Canonical HPrim.hpoly_extEqType.

Import HPrim.

Section HPolyEq.

Variable R : realFieldType.
Variable n : nat.

Definition hpolyEq_of_set (base : 'hpoly[R]_n) :=
  let: 'P(A,b) as P := base in
    fun (J : {set 'I_(#ineq P)}) =>
      let AJ := col_mx A (-(row_submx A J)) in
      let bJ := col_mx b (-(row_submx b J)) in
        'P(AJ, bJ).

Notation "''P^=' ( P ; J )" := (@hpolyEq_of_set P J).
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J).

Fact hpolyEq_inE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) :
  (x \in 'P^=(A, b; J)) = (x \in 'P(A, b)) && [forall j in J, ((A *m x) j 0 == b j 0)].
Proof.
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

Lemma hpolyEq_antimono (base: 'hpoly[R]_n) (I J : {set 'I_(#ineq base)}) :
  I \subset J -> {subset 'P^=(base; J) <= 'P^=(base; I)}.
Admitted.

End HPolyEq.

Arguments hpolyEq_of_set [R n].
Prenex Implicits hpolyEq_of_set.
Notation "''P^=' ( P ; J )" := (hpolyEq_of_set P J).
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J).
Definition inE := (hpolyEq_inE, inE).

(*

Definition has_base (base : 'hpoly[R]_n) (P : 'hpoly[R]_n) :=
  [exists I : {set 'I_(#ineq base)}, P == hpolyEq_of_set I].

Section FixedBase.

Variable base : 'hpoly[R]_n.

Inductive hpolyEq := HPolyEq (P : 'hpoly[R]_n) of has_base base P.

Coercion hpoly_of_hpolyEq Q := let: HPolyEq P _ := Q in P.
Canonical hpolyEq_subType := [subType for hpoly_of_hpolyEq].
Definition hpolyEq_eqMixin := Eval hnf in [eqMixin of hpolyEq by <:].
Canonical hpolyEq_eqType := Eval hnf in EqType hpolyEq hpolyEq_eqMixin.
Definition hpolyEq_choiceMixin := [choiceMixin of hpolyEq by <:].
Canonical hpolyEq_choiceType := Eval hnf in ChoiceType hpolyEq hpolyEq_choiceMixin.

Lemma hpolyEq_of_setP (J : {set 'I_(#ineq base)}) :
  has_base base (hpolyEq_of_set J).
Proof.
by apply/existsP; exists J.
Qed.

End FixedBase.

Notation "''hpolyEq(' base )" := (hpolyEq base).
Notation "''P^=' ( P ; J )" := (HPolyEq (@hpolyEq_of_setP P J)).
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J).

Fact hpolyEq_inE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J: {set 'I_m}) :
  (x \in 'P^=(A, b; J)) = (x \in 'P(A, b)) && [forall j in J, ((A *m x) j 0 == b j 0)].
Proof.
rewrite /hpoly_of_hpolyEq.
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

(* TODO: add all the relevant lemmas (monotonicity of active, etc) *)

Lemma relint (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (Q : 'hpolyEq('P(A,b))) :
  exists x, x \in Q /\ (forall i, i \notin \active Q -> (A *m x) i 0 > b i 0).
Proof.
Admitted.

Lemma active_inj (base : 'hpoly[R]_n) : injective (@active_set base).
Proof.
Admitted.

Lemma active_idem (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :
  let Q' := HPolyEq (hpolyEq_of_setP (\active Q)) in
    \active Q' = \active Q.
Proof.
Admitted.

Definition active_inv (base : 'hpoly[R]_n) (J : {set 'I_(#ineq base)}) :=
  (HPolyEq (hpolyEq_of_setP J)).

Lemma activeK (base : 'hpoly[R]_n) :
  cancel (@active_set base) (@active_inv base).
Proof.
move => Q.
by apply: active_inj; apply: active_idem.
Qed.

Section FinType.

Variable base : 'hpoly[R]_n.

Definition hpolyEq_countMixin := CanCountMixin (@activeK base).
Canonical hpolyEq_countType  :=
  Eval hnf in CountType 'hpolyEq(base) hpolyEq_countMixin.
Definition hpolyEq_finMixin := CanFinMixin (@activeK base).
Canonical hpolyEq_finType  :=
  Eval hnf in FinType 'hpolyEq(base) hpolyEq_finMixin.

End FinType.

End HPolyEq.

Arguments active_set [R n base].
Notation "''hpolyEq(' base )" := (hpolyEq base).
Notation "''P^=' ( P ; J )" := (HPolyEq (@hpolyEq_of_setP _ _ P J)).
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J).
Notation "\active P" := (active_set P).

Section HFace.

Variable R : realFieldType.
Variable n : nat.
Variable base : 'hpoly[R]_n.
Variable P : 'hpolyEq(base).

Definition hface_of (F : 'hpoly[R]_n) :=
  non_empty F &&
    [exists Q: 'hpolyEq(base), (F ==i Q :> 'hpoly[R]_n) && ((\active P) \subset \active Q)].

Lemma hface_ofP (F : 'hpoly[R]_n) :
  non_empty P ->
    reflect (exists c, bounded c P /\ (forall x, (x \in P /\ (Some '[c,x] = opt_value c P)) <-> (x \in F)))
            (hface_of F).
Proof.
Admitted.

Lemma has_hface_imp_non_empty (F : 'hpoly[R]_n) :
  hface_of F -> non_empty P.
Proof.
Admitted.

End HFace.
*)