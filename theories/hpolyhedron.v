(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import simplex barycenter polypred.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

(*Section Test.

Variable (R : realFieldType) (n : nat) (m : nat) (base : m.-base[R,n]) (I : {set 'I_m}).

Goal baseEq base I = baseEq base I.
rewrite /=.
 *)

Module HPolyhedron.

Section Def.

Variable (R : realFieldType) (n : nat).

Record hpoly := HPoly { nb_ineq : nat; _ : nb_ineq.-base[R, n] }.

Definition base_to_hpoly (m : nat) (base : m.-base) := HPoly base.

End Def.

Coercion base_to_hpoly : base >-> hpoly.
Notation "''hpoly[' R ]_ n" := (hpoly R n) (at level 8).
Notation "''hpoly_' n" := (hpoly _ n) (at level 8).
Notation "'#ineq' P" := (nb_ineq P) (at level 0).

Section ChoicePred.

Variable R : realFieldType.
Variable n : nat.

Definition mem_hpoly (P : 'hpoly[R]_n) :=
  let: HPoly _ (A,b) := P in
    [pred x : 'cV_n | (A *m x) >=m b] : pred_class.

Canonical hpoly_predType := mkPredType mem_hpoly.

Definition matrix_from_hpoly (P : 'hpoly[R]_n) : { m & m.-base } :=
  let: HPoly _ base := P in Tagged _ base.

Definition hpoly_from_matrix (x : { m & m.-base }) : 'hpoly[R]_n := (tagged x).

Lemma matrix_from_hpolyK :
  cancel matrix_from_hpoly hpoly_from_matrix.
Proof.
by move => [m [A b]]; rewrite /matrix_from_hpoly /hpoly_from_matrix.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyK.
Canonical hpoly_eqType := Eval hnf in EqType 'hpoly[R]_n hpoly_eqMixin.
Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType 'hpoly[R]_n hpoly_choiceMixin.
Canonical hpoly_choicePredType := ChoicePredType _ 'hpoly[R]_n.

End ChoicePred.

Section PolyPred.

Variable R : realFieldType.
Variable n : nat.

Implicit Type (P : 'hpoly[R]_n).

Definition mk_hs c d : 'hpoly[R]_n := HPoly (c^T, d%:M).

Lemma in_hs c d x : x \in (mk_hs c d) = ('[c,x] >= d).
Proof.
rewrite inE vdotC -vdot_def.
by apply/forallP/idP => [ /(_ 0) | H i]; rewrite ?[i]ord1_eq0 !mxE /= !mulr1n.
Qed.

Definition poly0 := mk_hs 0 1.

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => x; rewrite in_hs vdot0l inE ler10.
Qed.

Definition polyT : 'hpoly[R]_n := HPoly (const_mx 0 : 'M_(0,n), 0).

Lemma in_polyT : polyT =i predT.
Proof.
by move => x; rewrite !inE mul0mx lev_refl.
Qed.

Definition polyI (P Q : 'hpoly[R]_n) : 'hpoly[R]_n :=
  let: HPoly _ base := P in
  let: HPoly _ base' := Q in
  HPoly (concat_base base base').

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
move => x.
case: P => mP [AP bP]; case: Q => mQ [AQ bQ].
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Definition bounded P c :=
  let: HPoly _ (A, b) := P in
    Simplex.bounded A b c.

Definition opt_value P c :=
  let: HPoly _ (A, b) := P in
    Simplex.opt_value A b c.

Definition poly_subset P Q :=
  let: HPoly _ (A, b) := P in
  let: HPoly _ (A', b') := Q in
    (~~ Simplex.feasible A b) ||
      [forall i, (Simplex.bounded A b (row i A')^T) && (Simplex.opt_value A b (row i A')^T >= b' i 0)].

Lemma poly_subsetP P Q :
  reflect {subset P <= Q} (poly_subset P Q).
Proof. (* RK *)
case: P => m [A b]; case: Q => m' [A' b'].
apply: (iffP idP) => [/orP poly_subset_P_Q | subset_P_Q].
- case: poly_subset_P_Q => [empty_P | /forallP hs_incl x x_in_P].
  + move => x x_in_P.
    move: empty_P; apply/contraR => _.
    by apply/Simplex.feasibleP; exists x.
  + apply/forallP => i.
    move/andP: (hs_incl i) => [/Simplex.boundedP [_ opt_is_opt] ?].
    apply: (@ler_trans _ (Simplex.opt_value A b (row i A')^T) _ _); first by done.
    by rewrite -row_vdot; apply: opt_is_opt.
- apply/orP.
  case: (boolP (Simplex.feasible A b)) => [feasible_P | _]; last by left.
  right.
  apply/forallP => i.
  suff bounded_P_row_i_A': Simplex.bounded A b (row i A')^T.
    apply/andP; split; first exact: bounded_P_row_i_A'.
    move/Simplex.boundedP: bounded_P_row_i_A' => [[x [/subset_P_Q  x_in_Q <-]] _].
    rewrite row_vdot.
    exact: ((forallP x_in_Q) i).
  apply/(Simplex.boundedP_lower_bound _ feasible_P).
  exists (b' i 0).
  move => x /subset_P_Q x_in_Q.
  rewrite row_vdot.
  exact: ((forallP x_in_Q) i).
Qed.

Lemma poly_subsetPn P Q :
  reflect (exists2 x, x \in P & x \notin Q) (~~ (poly_subset P Q)).
Proof. (* RK *)
case: P => m [A b]; case: Q => m' [A' b'].
apply: (iffP idP) => [| [?] ? not_in_Q];
  last by move: not_in_Q; apply/contra; move/poly_subsetP ->.
rewrite negb_or negbK negb_forall.
move/andP => [feasible_P /existsP [i /nandP unbounded_or]].
have unbounded_suff:
  ~~ Simplex.bounded A b (row i A')^T -> exists2 x : 'cV_n, (x \in HPoly (A, b)) & (x \notin HPoly (A', b')).
  rewrite -(Simplex.unbounded_is_not_bounded _ feasible_P) => /Simplex.unboundedP unbounded_P_row_i_A'.
  move: (unbounded_P_row_i_A' (b' i 0)) => [x [x_in_P ineq]].
  exists x; try by done.
  move: ineq; apply: contraL => x_in_Q.
  rewrite -lerNgt row_vdot.
  exact: ((forallP x_in_Q) i).
case: unbounded_or; first exact: unbounded_suff.
case: (boolP (Simplex.bounded A b (row i A')^T)) => [? | ? _]; last by apply: unbounded_suff.
rewrite -ltrNge => ineq.
exists (Simplex.opt_point A b (row i A')^T); first exact: Simplex.opt_point_is_feasible.
move: ineq; apply: contraL => opt_point_in_Q.
rewrite -lerNgt /Simplex.opt_value row_vdot.
exact: ((forallP opt_point_in_Q) i).
Qed.

Lemma boundedP P c :
  reflect (exists2 x, (x \in P) & poly_subset P (mk_hs c '[c,x])) (bounded P c).
Proof. (* RK *)
case: P => m [A b].
apply/(equivP (Simplex.boundedP A b c) _);
  split => [[[x [? opt_value_eq]] opt_value_is_opt] | [x ? /poly_subsetP incl_hs]].
- exists x; first by done.
  apply/poly_subsetP => y y_in_P.
  rewrite in_hs opt_value_eq.
  by apply: opt_value_is_opt.
- have opt_value_eq: '[ c, x] = Simplex.opt_value A b c.
    apply: Simplex.opt_value_is_optimal; first by done.
    move => y y_in_P.
    rewrite -in_hs.
    exact: (incl_hs _ y_in_P).
  split.
  + by exists x.
  + move => y y_in_P.
    rewrite -in_hs -opt_value_eq.
    exact: (incl_hs _ y_in_P).
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs c K))) (~~ bounded P c).
Proof. (* RK *)
case: P => m [A b] non_empty_P.
have feasible_P: Simplex.feasible A b
  by move/poly_subsetPn: non_empty_P => [x ? _];
  apply/Simplex.feasibleP; exists x.
rewrite /bounded (Simplex.bounded_is_not_unbounded c feasible_P) negbK.
apply/(equivP (Simplex.unboundedP A b c) _);
  split => [unbounded_cond_point K | unbounded_cond_hs K].
- apply/poly_subsetPn.
  move: (unbounded_cond_point K) => [x [? val_x_sineq]].
  exists x; first by done.
  by rewrite in_hs -ltrNge.
- move/poly_subsetPn: (unbounded_cond_hs K) => [x ? x_not_in_hs].
  exists x; split; first by done.
  by rewrite in_hs -ltrNge in x_not_in_hs.
Qed.

Definition pointed P :=
  let: HPoly _ (A, _) := P in
    Simplex.pointed A.

Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
case: P => m [A b] non_empty_P.
have feasible_P: exists x, x \in HPoly (A, b)
  by move/poly_subsetPn: non_empty_P => [x ? _]; exists x.
apply/(equivP (Simplex.pointedPn A) _); split =>
  [[d [? /Simplex.feasible_dirP d_feas_dir /Simplex.feasible_dirP md_feas_dir]] | [d [? d_recession_dir]]];
    exists d; split; try by done.
- move => x x_in_P λ.
  case: (boolP (0 <= λ)) => [? | ?].
  + by apply: d_feas_dir.
  + rewrite -[d]opprK scalerN -scaleNr.
    apply: md_feas_dir; try by done.
    by rewrite oppr_ge0; apply: ltrW; rewrite ltrNge.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  by move => x x_in_P λ _; apply: d_recession_dir.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  move => x x_in_P λ _; rewrite scalerN -scaleNr.
  by apply: d_recession_dir.
Qed.

(* TO BE FIXED. The lock is here to prevent unfolding the definition. *)
Fact conv_key : unit. by []. Qed.
Definition conv (V : {fset 'cV[R]_n}) := locked_with conv_key poly0.

Lemma convP V x :
  reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V).
Admitted. (* cannot be proved yet *)

(* In contrast, convexP can be proved immediately,
   this follows from the convexity of halfspaces *)
Lemma convexP P (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> poly_subset (conv V) P.
Admitted.

Definition hpoly_polyPredMixin :=
  PolyPred.Mixin in_poly0 in_polyT in_polyI poly_subsetP poly_subsetPn
                 in_hs boundedP boundedPn pointedPn convP convexP.
Canonical hpoly_polyPredType := PolyPredType R n hpoly_polyPredMixin.

Definition poly_sort :=
  PolyPred.sort (Quotient.quot_polyPredType hpoly_polyPredType).
End PolyPred.

Module Import Exports.
Canonical hpoly_eqType.
Canonical hpoly_predType.
Canonical hpoly_choiceType.
Canonical hpoly_choicePredType.
Canonical hpoly_polyPredType.
Identity Coercion poly_sort_to_polypred: poly_sort >-> PolyPred.sort.
Notation "''hpoly[' R ]_ n" := (@hpoly R n) (at level 8).
Notation "''hpoly_' n" := (hpoly _ n) (at level 8).
Notation "''poly[' R ]_ n" := (@poly_sort R n) (at level 8).
Notation "''poly_' n" := 'poly[_]_n (at level 8).
Notation "'#ineq' P" := (nb_ineq P) (at level 0).
End Exports.
End HPolyhedron.

Export HPolyhedron.Exports.

(*
Section HPolyhedronSpec.
(* YOUR ATTENTION PLEASE: hpolyP (provisional name) is intended to replace
 * every occurence of the ugly -reprK rewriting rule.
 * This is because hpolyP avoids specifying precisely which occurence
 * of (P : 'poly[R]_n) should be replaced by \repr P.
 * In this way, we just have a simple
 * case/hpoly: P => m A b
 * instead of a complicated
 * rewrite -{X,Y,-Z}[P]reprK; case: (\repr P) => m A b
 *)

Variable (R : realFieldType) (n : nat).

Variant hpoly_spec : 'poly[R]_n -> 'hpoly[R]_n -> {m & m.-base[R,n]} -> Type :=
  HpolySpec (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
    hpoly_spec '['P(A,b)] 'P(A,b) (Tagged _ (A, b)).

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (\repr P) (HPolyhedron.matrix_from_hpoly (\repr P)).
Proof.
by rewrite -{1}[P]reprK; case: (\repr P) => ? [??].
Qed.

End HPolyhedronSpec.*)

(*Section Test.

Local Open Scope poly_scope.

Variable (R : realFieldType) (n : nat) (P : {quot 'hpoly[R]_n}) (c x : 'cV[R]_n) (Q : 'hpoly[R]_n).

Hypothesis H : bounded P c.
Check (x \in \repr P).
Check (x \in Q).
Check (opt_point H).
Check (`[line c & x] : 'hpoly[R]_n).
Check (\repr P) : 'hpoly[R]_n.

Goal P = '[\repr P].
Proof.
by rewrite reprK.
Qed.
End Test.*)

Section Duality.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n).
Variable (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m).

Lemma dual_opt_sol (c : 'cV[R]_n) (H : bounded ('P(A,b) : T) c) :
    exists u, [/\ u >=m 0, c = A^T *m u & '[b, u] = opt_value H].
Admitted.
(*Proof.
move: (H) => H0. (* duplicate assumption *)
move: H; rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _ .
by move/and3P => [opt_point_in_P /andP [/eqP Au_eq_c u_le0] /eqP eq_value]; exists u.
Qed.*)

Variable (u : 'cV[R]_m).

Lemma dual_sol_lower_bound :
  u >=m 0 -> ('P(A, b) : T) `<=` `[hs (A^T *m u) & '[b,u]].
Proof.
move => u_ge0; apply/poly_subsetP => x x_in.
by rewrite inE -vdot_mulmx vdotC; apply: vdot_lev;
  last by rewrite in_poly_of_base in x_in.
Qed.

Lemma dual_sol_bounded :
  (('P(A, b) : T) `>` `[poly0]) -> u >=m 0 -> bounded ('P(A,b) : T) (A^T *m u).
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists '[b,u]; exact: dual_sol_lower_bound.
Qed.

Hypothesis u_ge0 : u >=m 0.
Variable (I : {set 'I_m}).
Hypothesis u_supp : forall i, (u i 0 > 0) = (i \in I).

Lemma compl_slack_cond x :
  x \in ('P(A,b) : T) -> reflect ('[A^T *m u, x] = '[b, u]) (x \in ('P^=(A, b; I) : T)).
Admitted.

Lemma dual_sol_argmin : (('P^=(A, b; I) : T) `>` `[poly0]) -> argmin ('P(A,b) : T) (A^T *m u) `=~` 'P^=(A, b; I).
Proof.
move => PI_non_empty.
have P_non_empty : (('P(A,b) : T) `>` `[poly0]).
- apply: (poly_proper_subset PI_non_empty); exact: polyEq_antimono0.
move/proper0P : PI_non_empty => [x x_in_PI].
set c := _ *m _; have c_bounded := (dual_sol_bounded P_non_empty u_ge0).
rewrite argmin_polyI.
suff ->: opt_value c_bounded = '[b,u].
- apply/poly_equivP => y; rewrite inE.
  apply/andP/idP => [[y_in_P c_y_eq]| y_in_PI].
  + apply/compl_slack_cond => //.
    by rewrite ?inE in c_y_eq; apply/eqP.
  + have y_in_P: y \in ('P(A,b) : T).
    * move: y y_in_PI; apply/poly_subsetP; exact: polyEq_antimono0.
    split; first by done.
    by rewrite inE; apply/eqP/compl_slack_cond.
- have x_in_P : x \in ('P(A,b) : T).
  + move: x x_in_PI; apply/poly_subsetP; exact: polyEq_antimono0.
  apply/eqP; rewrite eqr_le; apply/andP; split.
  - have <- : '[c,x] = '[b,u] by apply/compl_slack_cond.
    move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound c_bounded).
    by rewrite inE.
  - move: (opt_point c_bounded) => [y y_in_P <-].
    move/poly_subsetP/(_ _ y_in_P): (dual_sol_lower_bound u_ge0).
    by rewrite inE.
Qed.


(*
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
Qed.*)

End Duality.

(*
Section FeasibleBasicPoints. (* RK *)

Variable R : realFieldType.
Variable n : nat.

Definition feasible_basic_point (hP : 'hpoly[R]_n) (x : 'cV_n) :=
  let: 'P(A,b) := hP in
    (x \in 'P(A,b)) && (\rank (row_submx A (Simplex.active_ineq A b x)) >= n)%N.

Lemma feasible_basic_pointP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (x : 'cV_n) :
  reflect (exists bas : Simplex.basis A, ((Simplex.is_feasible b) bas) /\ x = Simplex.point_of_basis b bas)
          (feasible_basic_point 'P(A,b) x).
Proof.
apply: (iffP idP) => [/andP [x_in rank_ineq] | [bas [bas_is_feasible ->]]].
- move: (row_base_correctness rank_ineq) => [H1 /eqP H2 H3].
  have is_basis: Simplex.is_basis A (Simplex.Prebasis H2) by apply/Simplex.is_basisP_rank.
  exists (Simplex.Basis is_basis).
  suff x_eq: x = Simplex.point_of_basis b (Simplex.Basis is_basis)
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

Lemma feasible_basic_point_pointedP (hP : 'hpoly[R]_n) :
  reflect (exists x, feasible_basic_point hP x) ((non_empty hP) && (pointed hP)).
Proof.
case: hP => m A b.
apply: (iffP idP) => [feasible_and_pointed | [x /andP [x_in_hP rank_ineq]]].
- rewrite -Simplex.exists_feasible_basis in feasible_and_pointed.
  move/set0Pn: feasible_and_pointed => [bas bas_is_feasible].
  exists (Simplex.point_of_basis b bas).
  apply/feasible_basic_pointP.
  exists bas.
  by split; [rewrite in_set in bas_is_feasible | done].
- apply/andP; split.
  + by apply/non_emptyP; exists x.
  + apply: (@leq_trans (\rank (row_submx A (Simplex.active_ineq A b x))) _ _); first exact: rank_ineq.
    apply: mxrank_leqif_sup.
    exact: (row_submx_submx A (Simplex.active_ineq A b x)).
Qed.

End FeasibleBasicPoints.
 *)
