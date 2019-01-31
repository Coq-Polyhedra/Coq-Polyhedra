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

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "{ 'over' P , x 'minimizes' c }" (at level 70, format "{ 'over'  P ,  x  'minimizes'  c }").
Reserved Notation "{ 'over' P , F 'argmin' c }" (at level 70, format "{ 'over'  P ,  F  'argmin'  c }").
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
Reserved Notation "[ 'hpoly' v ]" (at level 0, v at level 99, format "[ 'hpoly'  v ]").
Reserved Notation "[ 'hpoly' v ; w ]" (at level 0, v at level 99, format "[ 'hpoly'  v ;  w ]").

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

CoInductive hpoly_split_spec (P : 'hpoly[R]_n) :=
  HpolySplit m (A : 'M[R]_(m,n)) (b : 'cV[R]_m) of P = 'P(A,b) : hpoly_split_spec P.

Lemma hpoly_splitP (P : 'hpoly[R]_n) : hpoly_split_spec P.
Proof.
by case: P => [m A b] /=; exists m A b.
Qed.

End HPolyStruct.

End HPoly.

Notation "''hpoly[' R ]_ n" := (hpoly R n).
Notation "''hpoly_' n" := (hpoly _ n).
Notation "'#ineq' P" := (nb_ineq P).
Notation "''P' ( m , A , b )" := (@Hpoly _ _ m A b).
Notation "''P' ( A , b )" := (Hpoly A b).
Notation "{ 'over' P , x 'minimizes' c }" :=
  (is_true (x%R \in P) /\ forall y, (is_true (y%R \in P) -> is_true ('[c,x] <= '[c,y]))) : ring_scope.
Notation "{ 'over' P , F 'argmin' c }" :=
  (forall y, ({over P, y minimizes c} <-> (y \in F))) : ring_scope.

Section MinProp.

Variable R: realFieldType.
Variable n : nat.

Variable P F : pred 'cV[R]_n.
Variable c : 'cV[R]_n.

Lemma minimize_eq v x :
  { over P , v minimizes c } -> ({ over P , x minimizes c } <-> (x \in P) /\ '[c,x] = '[c,v]).
Proof.
move => [v_in_P c_v_min]; split.
- move => [x_in_P c_x_min]; split; first by done.
  apply/eqP; rewrite -lter_anti; apply/andP; split; [exact: c_x_min | exact: c_v_min].
- move => [x_in_P c_x_eq_c_v]; split; first by done.
  by rewrite c_x_eq_c_v.
Qed.

Arguments minimize_eq [v x].

Lemma argmin_eq_in v x : {over P, F argmin c} -> v \in F -> x \in P -> '[c,x] = '[c,v] -> x \in F.
Proof.
move => F_argmin v_in_F x_in_P c_x_eq_c_v.
move/F_argmin: v_in_F => v_min.
apply/F_argmin; apply/(minimize_eq v_min); split; done.
Qed.

Arguments argmin_eq_in [v x].

Lemma argmin_le_in v x : {over P, F argmin c} -> v \in F -> x \in P -> '[c,x] <= '[c,v] -> x \in F.
Proof.
move => F_argmin v_in_F x_in_P c_x_le_c_v.
suff: '[c,x] = '[c,v] by apply: argmin_eq_in.
apply/ler_anti/andP; split; first by done.
by move/F_argmin: v_in_F => [_ /(_ _ x_in_P)].
Qed.

Arguments argmin_le_in [v x].

Lemma argmin_inN_lt v x : { over P , F argmin c } -> v \in F -> x \in P -> x \notin F -> '[c,v] < '[c,x].
Proof.
move => F_argmin v_in_F x_in_P x_not_in_F.
have [_ c_v_min] : {over P, v minimizes c} by apply/F_argmin.
rewrite ltr_def; apply/andP; split; last by exact: c_v_min.
move: x_not_in_F; apply: contraNneq => c_x_eq_c_v.
apply/F_argmin; split; by [done | rewrite c_x_eq_c_v].
Qed.

Arguments argmin_inN_lt [v x].

End MinProp.

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

Definition opt_point c P (_: bounded c P) :=
  let: 'P(A,b) := P in
    Simplex.opt_point A b c.

Definition opt_value c P (H: bounded c P) := '[c, opt_point H].

CoInductive lp_state c P : bool -> bool -> bool -> Prop :=
| Empty of P =i pred0 : lp_state c P false false false
| Bounded of (exists x, { over P, x minimizes c }) : lp_state c P true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state c P true false true.

Lemma lp_stateP c P :
  lp_state c P (non_empty P) (bounded c P) (unbounded c P).
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
  exact: (Simplex.unbounded_certificate K Hx Hd Hd').
- have feasible_A_b: Simplex.feasible A b.
    by apply/Simplex.feasibleP; exists x.
  have bounded_A_b_c: Simplex.bounded A b c.
    apply/Simplex.boundedP_lower_bound; first exact: feasible_A_b.
    exists '[ b, d].
    by apply/Simplex.dual_feasible_bounded.
  have /negbTE ->: ~~ (Simplex.unbounded A b c).
    by rewrite -(Simplex.bounded_is_not_unbounded c feasible_A_b).
    rewrite feasible_A_b bounded_A_b_c /=.
  constructor; exists (Simplex.opt_point A b c).
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

Lemma non_emptyPn P :
  reflect (P =i pred0) (~~ (non_empty P)).
Proof.
apply: (iffP idP); case: (lp_stateP 0 P) => /=;
  try by [ done
         | do ?[move => /(_ 0)]; by [ move => [x [x_in_P _]] /(_ x); rewrite inE x_in_P] ].
Qed.

Lemma non_emptyPn_cert (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  reflect (exists u, [/\ u >=m 0, A^T *m u = 0 & '[b, u] > 0]) (~~ (non_empty 'P(A,b))).
Proof.
Admitted.

Lemma boundedP c P :
  reflect (exists x, { over P, x minimizes c }) (bounded c P).
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

Lemma bounded_opt_value c P (H : bounded c P) :
  (exists x, x \in P /\ '[c,x] = opt_value H) /\ (forall y, y \in P -> '[c,y] >= opt_value H).
Proof.
case: P H => m A b H; move: (H) => H0.
by move: H; rewrite /bounded => /Simplex.boundedP.
Qed.

Lemma bounded_lower_bound c P :
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

Lemma opt_valueP c P (H : bounded c P) x :
  reflect ({ over P, x minimizes c }) ((x \in P) && ('[c,x] == opt_value H)).
Proof.
case: P H => m A b H; apply/(iffP andP) => [[x_in_P /eqP ->] |].
- split; first by done.
  by move/(Simplex.boundedP A b c): (H) => [_].
- by move => [x_in_P] /(Simplex.opt_value_is_optimal x_in_P) ->.
Qed.

Lemma dual_opt_sol (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (c : 'cV[R]_n) (H : bounded c 'P(A,b)) :
    exists u, [/\ u >=m 0, c = A^T *m u & '[b, u] = opt_value H].
Proof.
move: (H) => H0. (* duplicate assumption *)
move: H; rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _ .
by move/and3P => [opt_point_in_P /andP [/eqP Au_eq_c u_le0] /eqP eq_value]; exists u.
Qed.

Lemma normal_cone_lower_bound (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) :
  u >=m 0 -> forall x, x \in 'P(A, b) -> '[A^T *m u,x] >= '[b,u].
Proof.
move => u_ge0 x x_in_P.
by rewrite -vdot_mulmx vdotC; apply: vdot_lev.
Qed.

Lemma normal_cone_bounded (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) :
  non_empty 'P(A, b) -> u >=m 0 ->
    bounded (A^T *m u) 'P(A,b).
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound; first by done.
exists '[b, u]; exact: normal_cone_lower_bound.
Qed.

Lemma opt_value_csc (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) (x : 'cV[R]_n) :
  u >=m 0 -> x \in 'P(A,b) ->
    let c := A^T *m u in
      reflect (forall i, u i 0 > 0 -> (A *m x) i 0 = b i 0)
              ('[c,x] == '[b, u]).
Proof.
move => u_ge0 x_in_P /=.
have u_in_dual : u \in Simplex.dual_polyhedron A (A^T *m u)
 by rewrite inE eq_refl.
rewrite -subr_eq0 (Simplex.compl_slack_cond_duality_gap_equiv x_in_P u_in_dual).
apply/(iffP idP).
(* stupid proof, because of the fact that compl_slack_cond has not the right formulation (and compl_slack_condP doesn't help) *)
- move => Hcsc i u_i_gt0.
  move/forallP/(_ i): Hcsc; rewrite inE.
  by move/lt0r_neq0/negbTE: u_i_gt0 => -> /= /eqP.
- move => Hcsc; apply/forallP => i; rewrite -[X in X || _]negbK.
  have ->: (u i 0 != 0) = (u i 0 > 0)
      by rewrite lt0r; move/gev0P/(_ i): u_ge0 ->; rewrite andbT.
  by rewrite -implybE; apply/implyP; rewrite inE; move/Hcsc ->.
Qed.

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

Definition feasible_dir d P :=
  let: 'P(A, _) := P in Simplex.feasible_dir A d. (* RK *)

Lemma feasible_dirP d P :
  non_empty P ->
    reflect (forall x, forall λ, x \in P -> λ >= 0 -> x + λ *: d \in P) (feasible_dir d P). (* RK *)
Proof.
case: P => m A b.
move => non_empty_P.
apply/(iffP idP) => [feasible_dir_d x λ x_in_P λ_ge_0 | d_recession_dir].
- rewrite inE mulmxDr -scalemxAr -[b]addr0.
  apply/lev_add; first exact: x_in_P.
  have ->: 0 = λ *: (0 : 'cV[R]_m) by rewrite scaler0.
  by apply/lev_wpscalar.
- apply/contraT.
  rewrite negb_forall.
  move/existsP => [i A_d_i_neq].
  rewrite mxE in A_d_i_neq.
  move/non_emptyP: non_empty_P => [x x_in_P].
  set λ := ((A *m d) i 0 + b i 0 - (A *m x) i 0) * ((A *m d) i 0)^-1.
  have λ_ge_0: 0 <= λ.
    rewrite ler_ndivl_mulr; last by rewrite -ltrNge in A_d_i_neq.
    rewrite mul0r ler_subl_addr.
    apply: ler_add; last exact: ((forallP x_in_P) i).
    apply: ltrW.
    by rewrite -ltrNge in A_d_i_neq.
  move: (forallP (d_recession_dir _ _ x_in_P λ_ge_0) i) => H.
  rewrite mulmxDr -scalemxAr mxE [(λ *: (A *m d)) i 0]mxE -mulrA mulVf in H;
    last by apply: ltr0_neq0; rewrite -ltrNge in A_d_i_neq.
  rewrite mulr1 [(A *m x) i 0 + _]addrC -3!ler_subl_addr opprK -addrA -opprB addNr in H.
  by rewrite H in A_d_i_neq.
Qed.

Definition pointed P :=
  let: 'P(A,_) := P in Simplex.pointed A.

Lemma pointedPn P :
  reflect (exists d, [/\ d != 0, feasible_dir d P & feasible_dir (-d) P]) (~~pointed P). (* RK *)
Proof.
case: P => m A b.
exact: Simplex.pointedPn.
Qed.

End Basic.

Arguments non_empty [R n].
Arguments bounded [R n].
Arguments unbounded [R n].
Arguments non_emptyP [R n P].
Arguments non_emptyPn [R n P].
Arguments boundedP [R n c P].
Arguments bounded_lower_bound [R n c P].
Arguments unboundedP [R n c P].
Arguments opt_valueP [R n c P].
Prenex Implicits non_emptyP boundedP bounded_lower_bound unboundedP opt_valueP.

Section Subset.

Variable R : realFieldType.
Variable n : nat.
Variable P : 'hpoly[R]_n.

Definition hpoly_subset_halfspace c d :=
  non_empty P ==> (if (@idP (bounded c P)) is ReflectT H then opt_value H >= d else false).

Lemma hpoly_subset_halfspaceP c d :
  reflect (forall x, x \in P -> '[c,x] >= d)
          (hpoly_subset_halfspace c d).
Proof.
rewrite /hpoly_subset_halfspace.
case: {-}_/idP => [H | c_unbounded].
- apply: (iffP implyP).
  + move/bounded_opt_value : (H) => [[x] [x_in_P x_val] opt_val].
    have P_non_empty: non_empty P by exact: (intro_existsT non_emptyP x_in_P).
    move/(_ P_non_empty) => d_le_opt_value.
    move => y y_in_P; apply: (ler_trans d_le_opt_value).
    exact: opt_val.
  + move => lb _.
    move/bounded_opt_value: (H) => [[x] [x_in_P <-] _].
    exact: lb.
- case: (boolP (non_empty P)) => /= [P_non_empty | /negP P_empty]; constructor.
  + by move/(intro_existsT (bounded_lower_bound P_non_empty)).
  + by move => x /(intro_existsT non_emptyP).
Qed.

Definition hpoly_subset_hyperplane c d :=
  (hpoly_subset_halfspace c d) && (hpoly_subset_halfspace (-c) (-d)).

Lemma hpoly_subset_hyperplaneP c d :
  reflect (forall x, x \in P -> '[c,x] = d)
          (hpoly_subset_hyperplane c d).
Proof.
apply: (iffP idP) => [/andP [is_included is_included_opp] x x_in_P | sat_eq].
- apply/eqP; rewrite eqr_le.
  apply/andP; split.
  + move: ((hpoly_subset_halfspaceP _ _ is_included_opp) x x_in_P).
    by rewrite vdotNl ler_opp2.
  + exact: ((hpoly_subset_halfspaceP _ _ is_included) x x_in_P).
- apply/andP; split; apply/hpoly_subset_halfspaceP => x x_in_P.
  + by rewrite (sat_eq _ x_in_P).
  + by rewrite -(sat_eq _ x_in_P) vdotNl.
Qed.

Definition hpoly_subset Q :=
  let: 'P(A,b) := Q in
    [forall i, hpoly_subset_halfspace (row i A)^T (b i 0)].

Lemma hpoly_subsetP Q :
  reflect {subset P <= Q} (hpoly_subset Q).
Proof.
case: Q => m A b.
apply: (iffP idP).
- move => /forallP H x Hx.
  apply/forallP => i.
  move/hpoly_subset_halfspaceP: (H i) => Hi.
  move: (Hi x Hx).
  by rewrite -[(A *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
- move => H.
  apply/forallP => i.
  apply/hpoly_subset_halfspaceP => x Hx.
  move/forallP: (H x Hx) => Hx'.
  move: (Hx' i).
  by rewrite -[(A *m x) i 0]vdotl_delta_mx vdot_mulmx rowE trmx_mul trmx_delta.
Qed.

End Subset.

Arguments hpoly_subset_hyperplaneP [R n P c d].
Prenex Implicits hpoly_subset_hyperplaneP.

Section ExtensionalEquality.

Variable R : realFieldType.
Variable n : nat.

Definition hpoly_ext_eq : rel 'hpoly[R]_n :=
    fun P Q => (hpoly_subset P Q) && (hpoly_subset Q P).

Definition hpoly_ext_eqP P Q :
  reflect (P =i Q) (hpoly_ext_eq P Q).
Proof.
apply: (iffP idP).
- move/andP => [/hpoly_subsetP H1 /hpoly_subsetP H2] x.
  apply/idP/idP; [exact: (H1 x) | exact: (H2 x)].
- move => H.
  by apply/andP; split; apply/hpoly_subsetP => x; rewrite (H x).
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

Lemma hpolyEqT_inE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  (x \in 'P^=(A, b; setT)) = (A *m x == b).
Proof. (* RK *)
rewrite hpolyEq_inE.
apply/idP/idP => [/andP [_ /forallP forall_cond] | /eqP A_x_eq_b].
- apply/eqP/colP => j.
  by apply/eqP/(implyP (forall_cond j)).
- apply/andP; split.
  + rewrite inE A_x_eq_b.
    exact: lev_refl.
  + apply/forallP => j.
    apply/implyP => _.
    by rewrite A_x_eq_b.
Qed.

Lemma hpolyEq_inP (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) :
  reflect (x \in 'P(A, b) /\ forall j, j \in J -> (A *m x) j 0 = b j 0) (x \in 'P^=(A, b; J)).
Proof.
by rewrite hpolyEq_inE; apply: (equivP andP);
  split; move => [x_in_PAb /eqfun_inP x_sat].
Qed.

Lemma hpolyEq_act (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) j :
  x \in 'P^=(A, b; J) -> j \in J -> (A *m x) j 0 = b j 0.
Proof.
move => /hpolyEq_inP [_ x_act] j_in_J; exact: x_act.
Qed.

Lemma hpolyEq_antimono (base : 'hpoly[R]_n) (I J : {set 'I_(#ineq base)}) :
  I \subset J -> {subset 'P^=(base; J) <= 'P^=(base; I)}.
Proof.
case: base I J => [m A b] I J.
move => /subsetP I_subset_J x.
rewrite 2!hpolyEq_inE.
move/andP => [x_in_P /forallP sat_in_J].
apply/andP; split.
- exact: x_in_P.
- apply/forallP => j.
  apply/implyP => j_in_I.
  apply: (implyP (sat_in_J j)).
  exact: (I_subset_J _ j_in_I).
Qed.

Lemma hpolyEq_antimono0 (base : 'hpoly[R]_n) I :
  {subset 'P^=(base; I) <= base }.
Proof.
case : base I => [m A b] I.
by move => x /hpolyEq_inP [].
Qed.

Lemma hpolyEq_non_emptyPn_cert (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) :
  reflect (exists (u: 'cV[R]_m), [/\ (forall j, j \notin J -> u j 0 >= 0), A^T *m u = 0 & '[b, u] > 0]) (~~ (non_empty 'P^=(A,b; J))).
Proof.
Admitted.

Definition hpoly_point v := 'P^=(1%:M, v; setT).

Notation "[ 'hpoly' v ]" := (hpoly_point v).

Lemma hpoly_point_inE v x :
  (x \in [ hpoly v ]) = (x == v).
Proof. (* RK *)
by rewrite hpolyEqT_inE mul1mx.
Qed.

Lemma hpoly_point_inP v x :
  reflect (x = v) (x \in [hpoly v]).
Proof. (* RK *)
rewrite hpoly_point_inE.
exact: eqP.
Qed.

Definition hpoly_hyperplane (c : 'cV[R]_n) (d : R)  := 'P^=(c^T, d%:M; setT). (* RK *)

Lemma hpoly_hyperplane_inE c d x : (* RK *)
  (x \in hpoly_hyperplane c d) = ('[c,x] == d).
Proof.
rewrite hpolyEqT_inE -vdot_def vdotC.
apply: inj_eq; exact: scalar_mx_inj.
Qed.

End HPolyEq.

Arguments hpolyEq_of_set [R n].
Prenex Implicits hpolyEq_of_set.
Arguments hpolyEq_inP [R n x m A b J].
Arguments hpolyEq_non_emptyPn_cert [R n m A b J].
Notation "''P^=' ( P ; J )" := (hpolyEq_of_set P J).
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J).
Notation "[ 'hpoly' v ]" := (hpoly_point v).

Section HPolyI.

Variable R : realFieldType.
Variable n : nat.

Definition hpolyI (P Q : 'hpoly[R]_n) :=
  let: 'P(AP,bP) := P in
  let: 'P(AQ,bQ) := Q in
  'P((col_mx AP AQ), (col_mx bP bQ)).

Lemma hpolyI_inE (P Q : 'hpoly[R]_n) x :
  (x \in hpolyI P Q) = ((x \in P) && (x \in Q)).
Proof.
case: P => mP AP bP; case: Q => mQ AQ bQ.
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Lemma hpolyI_inP (P Q : 'hpoly[R]_n) x :
  reflect (x \in P /\ x \in Q) (x \in hpolyI P Q).
Proof.
rewrite hpolyI_inE; exact: andP.
Qed.

Lemma hpolyEqI_same_base (m: nat) (A: 'M[R]_(m,n)) (b: 'cV[R]_m) (I I' : {set 'I_m}) :
  hpolyI 'P^=(A, b; I) 'P^=(A, b; I') =i 'P^=(A, b; I :|: I').
Proof.
move => x.
rewrite hpolyI_inE !hpolyEq_inE.
apply/idP/idP =>
  [ /andP [/andP [x_in_base /forall_inP sat_IP] /andP [_ /forall_inP sat_IQ]]
  | /andP [x_in_base /forall_inP sat_Int]].
- apply/andP; split; try by done.
  apply/forall_inP => j; rewrite in_setU => /orP [j_in_IP | j_in_IQ];
    [exact: sat_IP | exact: sat_IQ].
- apply/andP; split; apply/andP; split; try by [ done |
  apply/forall_inP => j j_in_IP; apply: sat_Int;
  apply/setUP; by [left | right]].
Qed.

Lemma hpolyEqI_concat_base  (m m': nat) (A: 'M[R]_(m,n)) (A' : 'M[R]_(m',n))
      (b: 'cV[R]_m) (b' : 'cV[R]_m') (I : {set 'I_m}) (I' : {set 'I_m'}) :
  let J := (@lshift m m') @: I :|: (@rshift m m') @: I' in
  hpolyI 'P^=(A, b; I) 'P^=(A', b'; I') =i 'P^=(hpolyI 'P(A,b) 'P(A',b'); J).
Proof.
move => J x.
rewrite !hpolyI_inE 3!hpolyEq_inE.
rewrite andbACA; apply: congr2; first by rewrite -hpolyI_inE.
apply/andP/forall_inP.
- move => [ /forall_inP eq_P /forall_inP eq_Q ] i /setUP;
    case; move/imsetP => [j j_in ->]; rewrite mul_col_mx ?col_mxEu ?col_mxEd;
  by [apply: eq_P | apply: eq_Q].
- move => eq''; split; apply/forall_inP => i i_in.
  + move/(_ (lshift m' i)): eq''.
    by rewrite in_setU mem_imset //= mul_col_mx 2!col_mxEu => /(_ isT).
  + move/(_ (rshift m i)): eq''.
    by rewrite in_setU mem_imset // orbT mul_col_mx 2!col_mxEd => /(_ isT).
Qed.

End HPolyI.

Section Segments.

Variable R : realFieldType.
Variable n : nat.

Fact segment_key : unit. by []. Qed.

Definition hpoly_segment (v w : 'cV[R]_n) :=
  locked_with segment_key ('P(1%:M, 0)): 'hpoly[R]_n.
(* XA: to be changed by the correct definition, which is not trivial *)

Notation "[ 'hpoly' v ; w ]" := (hpoly_segment v w).

Lemma hpoly_segment_inP (v w x: 'cV[R]_n) :
  reflect (exists2 a, 0 <= a <= 1 & x = (1-a) *: v + a *: v) (x \in [hpoly v; w]).
Admitted.

Lemma hpoly_segment_point v : [hpoly v; v] = [hpoly v].
Admitted.

End Segments.

Notation "[ 'hpoly' v ; w ]" := (hpoly_segment v w).

Definition inE := (hpoly_point_inE, hpolyEqT_inE, hpolyEq_inE, inE).

Section FeasibleBasicPoints. (* RK *)

Variable R : realFieldType.
Variable n : nat.

Definition is_feasible_basic_point (hP : 'hpoly[R]_n) (x : 'cV_n) :=
  let: 'P(A,b) := hP in
    (x \in 'P(A,b)) && (\rank (row_submx A (Simplex.active_ineq A b x)) >= n)%N.

Lemma is_feasible_basic_pointP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (x : 'cV_n) :
  reflect (exists bas : Simplex.basis A, ((Simplex.is_feasible b) bas) /\ x = Simplex.point_of_basis b bas)
          (is_feasible_basic_point 'P(A,b) x).
Proof.
apply: (iffP idP) => [/andP [x_in rank_ineq] | [bas [bas_is_feasible ->]]].
- move: (row_base_correctness rank_ineq) => [H1 /eqP H2 H3].
  have is_basis: Simplex.is_basis A (Simplex.Prebasis H2) by apply/Simplex.is_basisP_rank.
  exists (Simplex.Basis is_basis).
  suff x_eq: x = Simplex.point_of_basis b (Simplex.Basis is_basis).
    by split; [rewrite /Simplex.is_feasible -Simplex.polyhedron_equiv_lex_polyhedron -x_eq | done].
  apply: Simplex.basis_subset_active_ineq_eq.
  by rewrite -Simplex.active_ineq_equal_active_lex_ineq.
- apply/andP; split.
  + rewrite Simplex.polyhedron_equiv_lex_polyhedron.
    exact: (Simplex.feasible_basis_is_feasible (Simplex.FeasibleBasis bas_is_feasible)).
  + apply: (@leq_trans (\rank (row_submx A (Simplex.set_of_prebasis (Simplex.prebasis_of_basis bas)))) _ _).
    * by rewrite (Simplex.is_basisP_rank A (Simplex.prebasis_of_basis bas) (Simplex.basis_is_basis bas)).
    * apply: mxrank_leqif_sup.
      apply: row_submx_subset_submx.
      rewrite Simplex.active_ineq_equal_active_lex_ineq.
      exact: (Simplex.basis_subset_of_active_ineq b bas).
Qed.

Lemma is_feasible_basic_point_pointedP (hP : 'hpoly[R]_n) :
  reflect (exists x, is_feasible_basic_point hP x) ((non_empty hP) && (pointed hP)).
Proof.
case: hP => m A b.
apply: (iffP idP) => [feasible_and_pointed | [x /andP [x_in_hP rank_ineq]]].
- rewrite -Simplex.exists_feasible_basis in feasible_and_pointed.
  move/set0Pn: feasible_and_pointed => [bas bas_is_feasible].
  exists (Simplex.point_of_basis b bas).
  apply/is_feasible_basic_pointP.
  exists bas.
  by split; [rewrite in_set in bas_is_feasible | done].
- apply/andP; split.
  + by apply/non_emptyP; exists x.
  + apply: (@leq_trans (\rank (row_submx A (Simplex.active_ineq A b x))) _ _); first exact: rank_ineq.
    apply: mxrank_leqif_sup.
    exact: (row_submx_submx A (Simplex.active_ineq A b x)).
Qed.

End FeasibleBasicPoints.

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
    [ set i : 'I_(#ineq P') | hpoly_subset_hyperplane Q (row i A)^T (b i 0) ].

Notation "\active Q" := (active_set Q).

Lemma activeP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (Q : 'hpolyEq('P(A,b))) i :
  reflect (forall x, x \in Q -> (A *m x) i 0 = b i 0)
          (i \in \active Q).
Proof.
apply: (iffP idP) => [i_in_implicit_eq_set x x_in_P | ineq_i_is_sat].
- rewrite inE in i_in_implicit_eq_set.
  rewrite -row_vdot.
  exact: ((hpoly_subset_hyperplaneP _ _  _ i_in_implicit_eq_set) x x_in_P).
- rewrite inE.
  apply/hpoly_subset_hyperplaneP => x x_in_P.
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