(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp fingroup perm matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx polyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Simplex.

Variable R : realFieldType.
Variable m n: nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Section Prebasis.

Inductive prebasis : predArgType := Prebasis (I : {set 'I_m}) of (#|I| == n)%N.

Coercion set_of_prebasis bas := let: Prebasis s _ := bas in s.
Canonical prebasis_subType := [subType for set_of_prebasis].
Definition prebasis_eqMixin := Eval hnf in [eqMixin of prebasis by <:].
Canonical prebasis_eqType := Eval hnf in EqType prebasis prebasis_eqMixin.
Definition prebasis_choiceMixin := [choiceMixin of prebasis by <:].
Canonical prebasis_choiceType := Eval hnf in ChoiceType prebasis prebasis_choiceMixin.
Definition prebasis_countMixin := [countMixin of prebasis by <:].
Canonical prebasis_countType := Eval hnf in CountType prebasis prebasis_countMixin.
Canonical prebasis_subCountType := [subCountType of prebasis].

Lemma prebasis_card (bas : prebasis) : #|bas| = n.
Proof.
by move/eqP: (valP bas).
Qed.

Definition matrix_of_prebasis (p : nat) (M : 'M[R]_(m,p)) (bas : prebasis) :=
  (castmx (prebasis_card bas, erefl p) (row_submx M bas)).

Definition prebasis_enum : seq prebasis := pmap insub (enum [set bas : {set 'I_m} | #|bas| == n]).

Lemma prebasis_enum_uniq : uniq prebasis_enum.
Proof.
by apply: pmap_sub_uniq; apply: enum_uniq.
Qed.

Lemma mem_prebasis_enum bas : bas \in prebasis_enum.
Proof.
rewrite mem_pmap_sub mem_enum in_set.
by move/eqP: (prebasis_card bas).
Qed.

Definition prebasis_finMixin :=
  Eval hnf in UniqFinMixin prebasis_enum_uniq mem_prebasis_enum.
Canonical prebasis_finType := Eval hnf in FinType prebasis prebasis_finMixin.
Canonical prebasis_subFinType := Eval hnf in [subFinType of prebasis].

End Prebasis.

Section Basis.

Definition is_basis (bas: prebasis) := (matrix_of_prebasis A bas) \in unitmx.

Inductive basis : predArgType := Basis (bas: prebasis) of is_basis bas.
Coercion prebasis_of_basis bas := let: Basis s _ := bas in s.
Canonical basis_subType := [subType for prebasis_of_basis].
Definition basis_eqMixin := Eval hnf in [eqMixin of basis by <:].
Canonical basis_eqType := Eval hnf in EqType basis basis_eqMixin.
Definition basis_choiceMixin := [choiceMixin of basis by <:].
Canonical basis_choiceType := Eval hnf in ChoiceType basis basis_choiceMixin.
Definition basis_countMixin := [countMixin of basis by <:].
Canonical basis_countType := Eval hnf in CountType basis basis_countMixin.
Canonical basis_subCountType := [subCountType of basis].

Lemma matrix_of_basis_in_unitmx (bas : basis) : (matrix_of_prebasis A bas) \in unitmx.
Proof.
by apply: (valP bas).
Qed.

Definition point_of_basis (bas : basis) :=
  (invmx (matrix_of_prebasis A bas)) *m (matrix_of_prebasis b bas).

Definition is_feasible (bas: basis) :=
  (point_of_basis bas) \in (polyhedron A b).

Lemma row_submx_is_feasible (bas : basis) :
  (forall x, (row_submx A bas) *m x = (row_submx b bas) -> x \in polyhedron A b) -> is_feasible bas.
Proof.
set v := point_of_basis bas.
have: ((matrix_of_prebasis A bas) *m v) = matrix_of_prebasis b bas.
- rewrite mulmxA mulmxV; last exact: (matrix_of_basis_in_unitmx bas).
  by rewrite mul1mx.
rewrite cast_mulmx; move/castmx_inj => H.
by move/(_ _ H).
Qed.

Definition basis_enum : seq basis := pmap insub [seq bas <- prebasis_enum | is_basis bas].

Lemma basis_enum_uniq : uniq basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: prebasis_enum_uniq.
Qed.

Lemma mem_basis_enum bas : bas \in basis_enum.
Proof.
rewrite mem_pmap_sub mem_filter.
apply/andP; split; last by apply: mem_prebasis_enum.
by apply: matrix_of_basis_in_unitmx.
Qed.

Definition basis_finMixin :=
  Eval hnf in UniqFinMixin basis_enum_uniq mem_basis_enum.
Canonical basis_finType := Eval hnf in FinType basis basis_finMixin.
Canonical basis_subFinType := Eval hnf in [subFinType of basis].

End Basis.

Section FeasibleBasis.

Inductive feasible_basis : predArgType := FeasibleBasis (bas : basis) of is_feasible bas.

Coercion basis_of_feasible_basis bas := let: FeasibleBasis s _ := bas in s.
Canonical feasible_basis_subType := [subType for basis_of_feasible_basis].
Definition feasible_basis_eqMixin := Eval hnf in [eqMixin of feasible_basis by <:].
Canonical feasible_basis_eqType := Eval hnf in EqType feasible_basis feasible_basis_eqMixin.
Definition feasible_basis_choiceMixin := [choiceMixin of feasible_basis by <:].
Canonical feasible_basis_choiceType := Eval hnf in ChoiceType feasible_basis feasible_basis_choiceMixin.
Definition feasible_basis_countMixin := [countMixin of feasible_basis by <:].
Canonical feasible_basis_countType := Eval hnf in CountType feasible_basis feasible_basis_countMixin.
Canonical feasible_basis_subCountType := [subCountType of feasible_basis].

Lemma feasible_basis_is_feasible (bas : feasible_basis) :
  is_feasible bas.
Proof.
by apply: (valP bas).
Qed.

Definition feasible_basis_enum : seq feasible_basis := pmap insub [seq bas <- basis_enum | is_feasible bas].

Lemma feasible_basis_enum_uniq : uniq feasible_basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: basis_enum_uniq.
Qed.

Lemma mem_feasible_basis_enum bas : bas \in feasible_basis_enum.
Proof.
rewrite mem_pmap_sub mem_filter.
apply/andP; split; last by apply: mem_basis_enum.
by apply: feasible_basis_is_feasible.
Qed.

Definition feasible_basis_finMixin :=
  Eval hnf in UniqFinMixin feasible_basis_enum_uniq mem_feasible_basis_enum.
Canonical feasible_basis_finType := Eval hnf in FinType feasible_basis feasible_basis_finMixin.
Canonical feasible_basis_subFinType := Eval hnf in [subFinType of feasible_basis].

Lemma basis_subset_of_active_ineq (bas : basis) :
   (bas \subset (active_ineq A b (point_of_basis bas))).
Proof.
set x := point_of_basis bas.
apply/subsetP => i Hi.
rewrite inE; apply/eqP.
have H: (matrix_of_prebasis A bas) *m x = (matrix_of_prebasis b bas).
- rewrite mulmxA mulmxV; last by apply: matrix_of_basis_in_unitmx.
  by rewrite mul1mx.
move/matrixP/(_ (cast_ord (prebasis_card bas) (enum_rank_in Hi i)) 0): H. 
rewrite castmxE cast_ordK cast_ord_id row_submx_mxE enum_rankK_in //.
by rewrite -{1}[x](castmx_id (erefl n, erefl 1%N)) -castmx_mul castmxE /= cast_ordK cast_ord_id -row_submx_mul row_submx_mxE enum_rankK_in //.
Qed.

Lemma active_ineq_in_point_of_basis (bas : basis) :
  (matrix_of_prebasis A bas <= active_ineq_mx A b (point_of_basis bas))%MS.
Proof.
rewrite eqmx_cast; apply/row_subP => i.
rewrite row_submx_row.
move/subsetP/(_ _ (enum_valP i)): (basis_subset_of_active_ineq bas) => Hbas_i.
suff ->: row (enum_val i) A = row (enum_rank_in Hbas_i (enum_val i)) (active_ineq_mx A b (point_of_basis bas)) by apply: row_sub.
by rewrite row_submx_row enum_rankK_in //.
Qed.

Lemma feasible_point_of_basis_is_extreme (bas : feasible_basis) :
    is_extreme (point_of_basis bas) (polyhedron A b: _ -> bool).
Proof.
apply/extremality_active_ineq/andP; split; first by apply: feasible_basis_is_feasible.
- apply/eqP; move: (mxrank_unit (matrix_of_basis_in_unitmx bas)).
  apply: contra_eq => HrkAI.
  have H: (\rank (active_ineq_mx A b (point_of_basis bas)) < n)%N.
  + rewrite ltn_neqAle; apply/andP.
    split; by [done | apply: (rank_leq_col (active_ineq_mx A b (point_of_basis bas)))].
  move/leq_of_leqif: (mxrank_leqif_eq (active_ineq_in_point_of_basis bas)) => H'.
  by move: (leq_ltn_trans H' H); rewrite ltn_neqAle; move/andP => [? _].
Qed.

Lemma extract_prebasis_card (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :
  #|build_row_base A (active_ineq A b x) n| == n.
Proof.
move: (leqnn n).
move/extremality_active_ineq: Hextr => /andP [_ /eqP {2} <-].
move/row_base_correctness => [_ {2} -> _].
apply: eq_refl.
Qed.

Definition extract_prebasis (x : 'cV[R]_n) (Hextr: is_extreme x (polyhedron A b: _ -> bool)) :=
  Prebasis (extract_prebasis_card Hextr).

Lemma extract_prebasis_is_basis (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :
  is_basis (extract_prebasis Hextr).
Proof.
rewrite /is_basis -row_free_unit -row_leq_rank rank_castmx.
move: (leqnn n).
move/extremality_active_ineq: (Hextr) => /andP [_ /eqP {2} <-].
move/row_base_correctness => [_ _ ->].
apply: leqnn.
Qed.

Definition extract_basis (x : 'cV[R]_n) (Hextr: is_extreme x (polyhedron A b: _ -> bool)) :=
    Basis (extract_prebasis_is_basis Hextr).

Lemma basis_subset_active_ineq_eq (bas : basis) (x : 'cV[R]_n) :
  bas \subset (active_ineq A b x) -> x = point_of_basis bas.
Proof.
move => H.
move: (matrix_of_basis_in_unitmx bas) => Hbas.
suff: (matrix_of_prebasis A bas) *m x = matrix_of_prebasis b bas.
- by move/(congr1 (mulmx (invmx (matrix_of_prebasis A bas)))); rewrite mulmxA mulVmx // mul1mx.
- apply/row_matrixP => i.
  rewrite row_mul row_castmx /= row_submx_row -row_mul row_castmx /= row_submx_row.
  set i' := enum_val _; move/subsetP/(_ i' (enum_valP _)): H.
  by apply: active_ineq_eq.
Qed.

Lemma extract_basis_point_of_basis (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :
  x = point_of_basis (extract_basis Hextr).
Proof.
apply: basis_subset_active_ineq_eq.
move: (leqnn n).
move/extremality_active_ineq: (Hextr) => /andP [_ /eqP {2} <-].
by move/row_base_correctness => [H _ _].
Qed.

Lemma extract_basis_is_feasible (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :
  is_feasible (extract_basis Hextr).
Proof.
rewrite /is_feasible -(extract_basis_point_of_basis Hextr).
by move/extremality_active_ineq: Hextr => /andP [H _].
Qed.

Definition extract_feasible_basis (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :=
  FeasibleBasis (extract_basis_is_feasible Hextr).

Lemma extract_feasible_basis_point_of_basis (x : 'cV[R]_n) (Hextr: is_extreme x (polyhedron A b: _ -> bool)) :
  x = point_of_basis (extract_feasible_basis Hextr).
Proof.
by apply: extract_basis_point_of_basis.
Qed.

End FeasibleBasis.

Section Cost.

Implicit Types c : 'cV[R]_n.
Implicit Types bas : basis.
Implicit Types x : 'cV[R]_n.
Implicit Types u : 'cV[R]_m.

Definition reduced_cost_of_basis c bas :=
  (invmx (matrix_of_prebasis A bas)^T) *m c.

Definition reduced_cost_of_basis_def c bas :
  (matrix_of_prebasis A bas)^T *m (reduced_cost_of_basis c bas) = c.
Proof.
rewrite /reduced_cost_of_basis mulmxA mulmxV; last by rewrite unitmx_tr; apply: (matrix_of_basis_in_unitmx bas).
by rewrite mul1mx.
Qed.

Definition ext_reduced_cost_of_basis c bas :=
  let: u := reduced_cost_of_basis c bas in
  \col_i (if (@idP (i \in bas)) is ReflectT Hi then
            u (cast_ord (prebasis_card bas) (enum_rank_in Hi i)) 0
          else 0).

Lemma ext_reduced_cost_of_basis_in_bas c bas i (Hi : (i \in bas)) :
  let: j := cast_ord (prebasis_card bas) (enum_rank_in Hi i) in
  (ext_reduced_cost_of_basis c bas) i 0 = (reduced_cost_of_basis c bas) j 0.
Proof.
rewrite /ext_reduced_cost_of_basis mxE.
case: {-}_ /idP => [Hi' |]; last by done.
suff ->: enum_rank_in Hi i = enum_rank_in Hi' i by done.
- apply: enum_val_inj; by do 2![rewrite enum_rankK_in //].
Qed.

Lemma ext_reduced_cost_of_basis_notin_bas c bas i :
  (i \notin bas) -> (ext_reduced_cost_of_basis c bas) i 0 = 0.
Proof.
move/negP => H; rewrite /ext_reduced_cost_of_basis mxE.
by case: {-}_ /idP => [ ? | _].
Qed.

Lemma non_neg_reduced_cost_equiv c bas :
  ((ext_reduced_cost_of_basis c bas) >=m 0) = ((reduced_cost_of_basis c bas) >=m 0).
Proof.
apply/idP/idP => [/forallP H | /forallP H].
- apply/forallP => i; rewrite mxE.
  set j := cast_ord (esym (prebasis_card bas)) i.
  move: (ext_reduced_cost_of_basis_in_bas c (enum_valP j)).
  rewrite enum_valK_in /j cast_ordKV => <-.
  by move/(_ (enum_val j)): H; rewrite mxE.
- apply/forallP => i; rewrite mxE; case: (boolP (i \in bas)) => [Hi | Hi].
  + rewrite (ext_reduced_cost_of_basis_in_bas c Hi).
    by set j := cast_ord _ _; move/(_ j): H; rewrite mxE.
  + by rewrite (ext_reduced_cost_of_basis_notin_bas c Hi).
Qed.

Lemma ext_reduced_cost_of_basis_def c bas :
  A^T *m (ext_reduced_cost_of_basis c bas) = c.
Proof.
apply/colP => i; rewrite !mxE.
rewrite (bigID (fun j => j \in bas)) /= [X in _ + X]big1;
  last by move => j /ext_reduced_cost_of_basis_notin_bas ->; rewrite mulr0.
rewrite addr0.
rewrite (reindex (@enum_val _ (mem bas))) /=;
        last by apply: (enum_val_bij_in (enum_valP (cast_ord (esym (prebasis_card bas)) i))).
 
rewrite (eq_bigl predT) /=; last by move => k /=; apply: (enum_valP k).
rewrite (reindex (cast_ord (esym (prebasis_card bas)))) /=; last first.
- apply: onW_bij; apply: inj_card_bij;
  by [apply: cast_ord_inj | rewrite 2!card_ord (prebasis_card bas)].
 
rewrite -[in RHS](reduced_cost_of_basis_def c bas) mxE.
apply: eq_bigr => j _; apply: congr2.
- by rewrite trmx_cast /= castmxE /= cast_ord_id !mxE.
- set k := cast_ord _ _; rewrite (ext_reduced_cost_of_basis_in_bas c (enum_valP k)).
  by rewrite enum_valK_in cast_ordKV.
Qed.

Lemma ext_reduced_cost_dual_feasible c bas :
  let: u := ext_reduced_cost_of_basis c bas in
  (reduced_cost_of_basis c bas) >=m 0 = (u \in dual_polyhedron A c).
Proof.
rewrite inE.
move/eqP: (ext_reduced_cost_of_basis_def c bas) ->; rewrite /=.
by symmetry; apply: non_neg_reduced_cost_equiv.
Qed.

(*Lemma compl_slack_cond_on_basis c bas :
  let: x := point_of_basis bas in
  let: u := ext_reduced_cost_of_basis c bas in
  compl_slack_cond A b x u.
Proof.
set x := point_of_basis bas.
set u := ext_reduced_cost_of_basis c bas.
apply/compl_slack_condP => i.
case: (boolP (i \in bas)) => [Hi | Hi].
- by move/subsetP/(_ i Hi): (basis_subset_of_active_ineq bas); rewrite inE => /eqP ->; right.
- by move: (ext_reduced_cost_of_basis_notin_bas c Hi) => ->; left.
Qed.*)

Lemma eq_primal_dual_value c bas :
  let: x := point_of_basis bas in
  let: u := ext_reduced_cost_of_basis c bas in
  '[c, x] = '[b, u].
Proof.
set x := point_of_basis bas.
set u := ext_reduced_cost_of_basis c bas.
apply/eqP; rewrite -duality_gap_eq0_def; apply/eqP.
apply: (compl_slack_cond_duality_gap_eq0 (ext_reduced_cost_of_basis_def c bas)).
apply/compl_slack_condP => i.
case: (boolP (i \in bas)) => [Hi | Hi].
- by move/subsetP/(_ i Hi): (basis_subset_of_active_ineq bas); rewrite inE => /eqP ->; right.
- by move: (ext_reduced_cost_of_basis_notin_bas c Hi) => ->; left.
Qed.

Lemma optimal_cert_on_basis c (bas : feasible_basis) :
  let: x := point_of_basis bas in
  (reduced_cost_of_basis c bas) >=m 0 ->
  forall y, y \in polyhedron A b -> '[c,x] <= '[c,y].
Proof.
set x := point_of_basis bas.
set u := ext_reduced_cost_of_basis c bas.
rewrite ext_reduced_cost_dual_feasible => Hu.
apply: (duality_gap_eq0_optimality (feasible_basis_is_feasible bas) Hu).
move: Hu; rewrite inE; move/andP => [/eqP Hu _].
by apply/eqP; rewrite subr_eq0 eq_primal_dual_value.
Qed.

Definition direction bas i :=
  let: ei := (delta_mx i 0):'cV_n in
  (invmx (matrix_of_prebasis A bas)) *m ei.

Lemma direction_neq0 bas i: direction bas i != 0.
Proof.
apply: contraT; rewrite negbK.
move/eqP/(congr1 (mulmx (matrix_of_prebasis A bas))).
rewrite mulmxA mulmxV; last by apply: matrix_of_basis_in_unitmx.
rewrite mul1mx mulmx0.
move/matrixP/(_ i 0); rewrite !mxE !eq_refl /=.
move/eqP; rewrite pnatr_eq0.
by move: (oner_neq0 R).
Qed.

Lemma direction_improvement c bas i:
  let: u := reduced_cost_of_basis c bas in
  let: d := direction bas i in
  u i 0 < 0 -> '[c, direction bas i] < 0.
Proof.
by rewrite vdot_mulmx trmx_inv vdot_delta_mx.
Qed.

Lemma unbounded_cert_on_basis c (bas : feasible_basis) i M:
  let: u := reduced_cost_of_basis c bas in
  let: d := direction bas i in
  feasible_dir A d -> u i 0 < 0 ->
  exists x, (x \in polyhedron A b) /\ ('[c,x] < M).
Proof.
set d := direction _ _.
move => Hd Hui.
apply: (unbounded_certificate (x0 := point_of_basis bas) (d:=d)); try by [ apply: (feasible_basis_is_feasible bas) | done].
by rewrite /d vdot_mulmx trmx_inv vdot_delta_mx.
Qed. 

Lemma direction_prop (bas : basis) (i : 'I_n) (j : 'I_m) :
  let: d := direction bas i in
  j \in bas -> (A *m d) j 0 = (j == enum_val (cast_ord (esym (prebasis_card bas)) i))%:R.
Proof.
set d := direction bas i.
move => Hj.
move: (matrix_of_basis_in_unitmx bas) => Hbas.
suff ->: (A *m d) j 0 = ((matrix_of_prebasis A bas) *m d) (cast_ord (prebasis_card bas) (enum_rank_in Hj j)) 0.
- rewrite /d /direction mulmxA mulmxV // mul1mx mxE /= andbT.
  rewrite -{1}[i](cast_ordKV (prebasis_card bas)).
  apply/(congr1 (fun y => (nat_of_bool y)%:R)); apply/idP/idP.
  + move/eqP/cast_ord_inj <-; by rewrite enum_rankK_in //.
  + by move/eqP => H; rewrite {}[X in enum_rank_in _ X]H enum_valK_in.
rewrite /matrix_of_prebasis -{2}[d](castmx_id (erefl n, erefl (1%N))).
by rewrite -castmx_mul castmxE /= cast_ordK cast_ord_id -row_submx_mul row_submx_mxE enum_rankK_in //.
Qed.

Lemma mulmx_direction (bas : basis) (i : 'I_n):
  let: d := direction bas i in
  (row_submx A (bas :\ enum_val (cast_ord (esym (prebasis_card bas)) i))) *m d = 0.
Proof.
rewrite -row_submx_mul.
apply/colP => j; rewrite mxE [X in _ = X]mxE.
move: (enum_valP j); rewrite in_setD1; move/andP => [Hj Hj'].
rewrite direction_prop //.
by move/negbTE: Hj ->.
Qed.

End Cost.

Section Lexicographic_rule.

Variable s : 'S_m.

Definition b_pert := row_mx b (-(perm_mx s)).

Definition point_of_basis_pert bas :=
  (invmx (matrix_of_prebasis A bas)) *m (matrix_of_prebasis b_pert bas).

Lemma rel_points_of_basis bas :
  point_of_basis bas = col 0 (point_of_basis_pert bas).
Proof.
rewrite /point_of_basis_pert col_mul /matrix_of_prebasis.
rewrite row_submx_row_mx cast_row_mx.
set E := (row_mx _ _).
suff ->: (col 0 E) = castmx (prebasis_card bas, erefl 1%N) (row_submx b bas);
  first by done.
by apply/colP => i; rewrite 2!mxE split1 unlift_none.
Qed.

Section LexFeasibleBasis.

Definition is_lex_feasible (bas : basis) := 
  let: x := point_of_basis_pert bas in 
  [forall i, ((row i A) *m x) >=lex (row i b_pert)].

Inductive lex_feasible_basis : predArgType := LexFeasibleBasis (bas: basis) of is_lex_feasible bas.
Coercion basis_of_lex_feasible_basis bas := let: LexFeasibleBasis s _ := bas in s.
Canonical lex_feasible_basis_subType := [subType for basis_of_lex_feasible_basis].
Definition lex_feasible_basis_eqMixin := Eval hnf in [eqMixin of lex_feasible_basis by <:].
Canonical lex_feasible_basis_eqType := Eval hnf in EqType lex_feasible_basis lex_feasible_basis_eqMixin.
Definition lex_feasible_basis_choiceMixin := [choiceMixin of lex_feasible_basis by <:].
Canonical lex_feasible_basis_choiceType := Eval hnf in ChoiceType lex_feasible_basis lex_feasible_basis_choiceMixin.
Definition lex_feasible_basis_countMixin := [countMixin of lex_feasible_basis by <:].
Canonical lex_feasible_basis_countType := Eval hnf in CountType lex_feasible_basis lex_feasible_basis_countMixin.
Canonical lex_feasible_basis_subCountType := [subCountType of lex_feasible_basis].

Lemma lex_feasible_basis_is_lex_feasible (bas : lex_feasible_basis) :
  is_lex_feasible bas.
Proof.
by apply: (valP bas).
Qed.

Lemma lex_feasible_basis_is_feasible (bas : lex_feasible_basis) :
  is_feasible bas.
Proof.
rewrite /is_feasible (rel_points_of_basis bas).
apply/forallP => i; rewrite -col_mul mxE.
move/forallP/(_ i)/lex_ord0: (lex_feasible_basis_is_lex_feasible bas).
by rewrite -row_mul mxE [X in _ <= X]mxE mxE split1 unlift_none /=.
Qed.

Definition lex_feasible_basis_enum : seq lex_feasible_basis := pmap insub [seq bas <- basis_enum | is_lex_feasible bas].

Lemma lex_feasible_basis_enum_uniq : uniq lex_feasible_basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: basis_enum_uniq.
Qed.

Lemma mem_lex_feasible_basis_enum bas : bas \in lex_feasible_basis_enum.
Proof.
rewrite mem_pmap_sub mem_filter.
apply/andP; split; last by apply: mem_basis_enum.
by apply: lex_feasible_basis_is_lex_feasible.
Qed.

Definition lex_feasible_basis_finMixin :=
  Eval hnf in UniqFinMixin lex_feasible_basis_enum_uniq mem_lex_feasible_basis_enum.
Canonical lex_feasible_basis_finType := Eval hnf in FinType lex_feasible_basis lex_feasible_basis_finMixin.
Canonical lex_feasible_basis_subFinType := Eval hnf in [subFinType of lex_feasible_basis].

(* the next 3 lemmas should be merged with the analogous statements in Section Basis. *)
Lemma row_submx_point_of_basis_pert (bas : basis) :
  (row_submx A bas) *m (point_of_basis_pert bas) = row_submx b_pert bas.
Proof.
apply: (@castmx_inj _ _ _ _ _ (prebasis_card bas) (erefl (1+m)%N)).
rewrite castmx_mul castmx_id.
by rewrite /point_of_basis_pert mulKVmx; last exact: matrix_of_basis_in_unitmx.
Qed.

Lemma is_point_of_basis_pert (bas : basis) x :
  (row_submx A bas) *m x = row_submx b_pert bas -> x = point_of_basis_pert bas.
Proof.
move/(congr1 (castmx (prebasis_card bas, erefl (1+m)%N))); rewrite castmx_mul castmx_id.
by move/(canRL (mulKmx (matrix_of_basis_in_unitmx _))).
Qed.

Lemma is_point_of_basis_pert_active (bas : basis) x :
  (forall i, i \in bas -> row i (A *m x) = row i b_pert) -> x = point_of_basis_pert bas.
Proof.
move/row_submx_row_matrixP; rewrite row_submx_mul => H.
exact: is_point_of_basis_pert.
Qed.

Lemma col_b_pert_not_in_basis (I : {set 'I_m}) j :
  (j \notin I) -> col (rshift 1 (s j)) (row_submx b_pert I) = 0.
Proof.
move => Hj.
rewrite row_submx_row_mx colKr.
rewrite row_submx_col.
apply/row_submx_col0P => k Hk.
rewrite !mxE (inj_eq (@perm_inj _ s)).
move/memPn/(_ _ Hk)/negbTE: Hj => -> /=.
by rewrite mulr0n oppr0.
Qed.

Lemma col_point_of_basis_pert_not_in_basis (bas : basis) j :
  (j \notin bas) -> col (rshift 1 (s j)) (point_of_basis_pert bas) = 0.
Proof.
rewrite /point_of_basis_pert col_mul => Hj.
suff ->: col (rshift 1 (s j)) (matrix_of_prebasis b_pert bas) = 0 by rewrite mulmx0.
move/col_b_pert_not_in_basis: Hj =>  Hj'.
apply/colP => i; rewrite !mxE castmxE /= cast_ord_id.
set j' := cast_ord _ _.
by move/colP/(_ j'): Hj'; rewrite mxE [RHS]mxE.
Qed.

Lemma col_point_of_basis_pert_in_basis (bas : basis) j :
  (j \in bas) -> col (rshift 1 (s j)) (point_of_basis_pert bas) != 0.
Proof.
move => Hj.
rewrite col_mul.
set k := rshift _ _.
suff: col k (matrix_of_prebasis b_pert bas) != 0.
- apply: contraTneq.
  move/(congr1 (mulmx (matrix_of_prebasis A bas))).
  rewrite mulKVmx; last exact: matrix_of_basis_in_unitmx. 
  by rewrite mulmx0 => ->; rewrite eq_refl /=.
- apply/(contraTneq _ isT) => /=.
  pose j' := cast_ord (prebasis_card bas) (enum_rank_in Hj j).
  move/colP/(_ j').
  rewrite mxE [RHS]mxE castmxE /= cast_ordK cast_ord_id row_submx_mxE enum_rankK_in //.
  rewrite row_mxEr.
  rewrite !mxE eq_refl /= mulr1n.
  move/eqP; rewrite oppr_eq0.
  by move/lt0r_neq0/negP: (@ltr01 R).
Qed.

Lemma neg_subset_bas_imp_neq_pert_points (bas bas' : basis) :
  ~~ (bas \subset bas') -> point_of_basis_pert bas != point_of_basis_pert bas'.
Proof.
rewrite -setD_eq0.
move/set0Pn => [i Hi].
move: (setDP Hi).
move => [Hibas Hibas'].
move/eqP: (col_point_of_basis_pert_not_in_basis Hibas').
apply: contraTneq.
move => H; rewrite -H.
exact: (col_point_of_basis_pert_in_basis Hibas).
Qed.

Lemma eq_pert_point_imp_eq_bas (bas bas' : basis) :
  (point_of_basis_pert bas = point_of_basis_pert bas') -> bas == bas'.
Proof.
move/eqP => H; rewrite [bas == bas']eqEsubset.
move: H; apply contraLR.
rewrite negb_and.
move/orP.
case; [ exact: neg_subset_bas_imp_neq_pert_points | rewrite eq_sym; exact: neg_subset_bas_imp_neq_pert_points]. 
Qed.

End LexFeasibleBasis.

Variable c : 'cV[R]_n.

Implicit Types bas : lex_feasible_basis.

Definition lex_gap bas (d : 'cV_n) j :=
  let: x := point_of_basis_pert bas in
  ((A *m d) j 0)^-1 *: ((row j b_pert) - ((row j A) *m x)).

Definition lex_ent_var_nat bas i :=
  let: d := direction bas i in
  let: J := [ seq j <- (enum 'I_m) | (A *m d) j 0 < 0 ] in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- J] in
  find (fun j => (j \in J) && (lex_min_gap == lex_gap bas d j)) (enum 'I_m).

Lemma lex_ent_var_bound bas i :
  let: d := direction bas i in
  ~~ (feasible_dir A d) -> (lex_ent_var_nat bas i < m)%N.
Proof.
move => /existsP [k Hk].
rewrite mxE in Hk.
rewrite -[X in (_ < X)%N]size_enum_ord -has_find.
set d := direction bas i.
set J := filter (fun j => (A *m d) j 0 < 0) (enum 'I_m).
set lex_gaps := [seq lex_gap bas d j | j <- J].
have Hlex_gaps : lex_gaps != [::].
+ rewrite -size_eq0 size_map size_eq0 -has_filter.
  apply/hasP; exists k; first by rewrite mem_enum.
  by rewrite ltrNge.
apply/hasP.
move/hasP: (lex_min_seq_eq Hlex_gaps) => [x /mapP [j' Hj' ->]] /= /eqP ->.
exists j'; by [rewrite mem_enum | apply/andP].
Qed.

Variable bas : lex_feasible_basis.
Variable i : 'I_n.
Hypothesis infeas_dir : ~~(feasible_dir A (direction bas i)).

Definition lex_ent_var := Ordinal (lex_ent_var_bound infeas_dir).

Lemma lex_ent_var_properties :
  let: d := direction bas i in
  let: J := [ seq j <- (enum 'I_m) | (A *m d) j 0 < 0 ] in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- J] in
  let: j := lex_ent_var in
  (j \in J) && (lex_min_gap == lex_gap bas d j).
Proof.
set d := direction bas i.
set J := filter (fun j => (A *m d) j 0 < 0) (enum 'I_m).
set lex_gaps := [seq lex_gap bas d j | j <- J].
set j_nat := lex_ent_var_nat bas i.
set j := lex_ent_var.
move: (lex_ent_var_bound infeas_dir).
rewrite -[X in (_ < X)%N]size_enum_ord -has_find.
move/(nth_find j).
move: (nth_enum_ord j (lex_ent_var_bound infeas_dir)).
rewrite -/j_nat.
have ->: j_nat = (nat_of_ord j) by rewrite /=.
move/ord_inj ->.
move/andP => [Hj /eqP <-].
by rewrite eq_refl Hj /=.
Qed.

Definition lex_rule_set :=
  let: j := lex_ent_var in
  j |: (bas :\ (enum_val (cast_ord (esym (prebasis_card bas)) i))).

Lemma lex_ent_var_not_in_basis:
  lex_ent_var \notin bas.
Proof.
set d := direction bas i.
set j := lex_ent_var.
move: (matrix_of_basis_in_unitmx bas) => Hbas.
apply: contraT; rewrite negbK.
move => Hj.
set k := enum_rank_in Hj j.
have Hk: j = enum_val (A := mem bas) k
  by rewrite (enum_rankK_in Hj).
have H: (matrix_of_prebasis A bas *m d) (cast_ord (prebasis_card bas) k) 0 >= 0.
- rewrite mulmxA mulmxV // mul1mx mxE.
  by apply: ler0n.
move: H.
rewrite /matrix_of_prebasis -[d](castmx_id (erefl n, erefl (1%N))).
rewrite -castmx_mul castmxE cast_ordK cast_ord_id -row_submx_mul row_submx_mxE -{}Hk.
move => H.
move/andP: lex_ent_var_properties => [H' _].
move: H'; rewrite -/j mem_filter -/d; move/andP => [H' _].
move/andP: (conj H H').
by rewrite ler_lt_asym.
Qed.

Lemma lex_rule_card : #|lex_rule_set| == n.
Proof.
rewrite cardsU1 in_setD1 negb_and lex_ent_var_not_in_basis orbT /=.
rewrite cardsD.
move: (enum_valP (cast_ord (esym (prebasis_card bas)) i)).
rewrite -sub1set => Hibas.
move/subset_leq_card: (Hibas).
move/setIidPr: Hibas ->; rewrite cards1 => Hbas.
by rewrite subn1 addnC addn1 prednK // (prebasis_card bas).
Qed.

Definition lex_rule_pbasis := Prebasis lex_rule_card.

Lemma lex_rule_is_basis : is_basis lex_rule_pbasis.
Proof.
move: (matrix_of_basis_in_unitmx bas) => Hbas.
set d := direction bas i.
set j := lex_ent_var.
set J := lex_rule_set.
 
move/andP: lex_ent_var_properties => [Hj /eqP Hj'].
move: Hj; rewrite mem_filter; move/andP => [Hj _].
rewrite -/j -/d in Hj, Hj'.
 
move: Hbas.
rewrite /is_basis -!row_free_unit -!row_leq_rank !rank_castmx.
rewrite (row_submx_spanD1 A (enum_valP (cast_ord (esym (prebasis_card bas)) i))).
set AIi := row_submx A (bas :\ enum_val (cast_ord (esym (prebasis_card bas)) i)).
set Ai := row (enum_val (cast_ord (esym (prebasis_card bas)) i)) A.
move => HrkI.
 
have HrkIi: (n <= 1+\rank AIi)%N.
+ move: (leq_trans HrkI (leq_of_leqif (mxrank_adds_leqif Ai AIi))).
  move/(leq_add (rank_leq_row Ai)).
  by rewrite addnA [X in (_ <= X + _)%N]addnC -addnA leq_add2l addnC.
 
set Aj := row j A.
rewrite row_submx_spanU1 -/AIi -/j -/Aj;
  last by move: lex_ent_var_not_in_basis;
  apply: contra; rewrite in_setD1; move/andP => [_].
 
have Hw_inter_AIi : (Aj :&: AIi <= (0:'M_n))%MS.
+ apply/rV_subP => ?; rewrite submx0 sub_capmx.
  move/andP => [/sub_rVP [a ->] /submxP [z]].
  move/(congr1 (mulmx^~ d)).
  rewrite -mulmxA -scalemxAl mulmx_direction // mulmx0.
  move/rowP/(_ 0); rewrite mxE [X in _ = X]mxE -row_mul mxE.
  move/eqP; rewrite mulf_eq0.
  move/ltr0_neq0/negbTE: Hj ->; rewrite orbF.
  by move/eqP ->; rewrite scale0r eq_refl.
 
move/leqifP: (mxrank_adds_leqif Aj AIi).
rewrite ifT //; move/eqP ->.
rewrite rank_rV.
suff ->: (Aj != 0); first by done.
+ apply:contraT; rewrite negbK; move/eqP.
  move/(congr1 (mulmx^~ d)); rewrite mul0mx.
  move/rowP/(_ 0); rewrite [X in _ = X]mxE -row_mul mxE => H'.
  by move/ltr0_neq0: Hj; rewrite H' eq_refl.
Qed.

Definition lex_rule_bas := Basis lex_rule_is_basis.

Lemma lex_rule_rel_succ_points :
let: d := direction bas i in
let: v := point_of_basis_pert bas in
let: next_bas := lex_rule_bas in
let: next_v := point_of_basis_pert next_bas in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
 next_v = v + d *m lex_min_gap.
Proof.
set d := direction bas i.
set j := lex_ent_var.
set next_bas := lex_rule_bas.
set v := point_of_basis_pert bas.
set next_v := point_of_basis_pert next_bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
set u := v + d *m lex_min_gap.
move: (matrix_of_basis_in_unitmx bas) => Hbas.
move: (matrix_of_basis_in_unitmx next_bas) => Hnext_bas.
move/andP: lex_ent_var_properties => [Hj /eqP Hj'].
move: Hj; rewrite mem_filter; move/andP => [Hj _].
rewrite -/j -/d in Hj, Hj'.
have Hv: (matrix_of_prebasis A bas) *m v = (matrix_of_prebasis b_pert bas)
  by rewrite mulmxA mulmxV // mul1mx.
move: Hv; rewrite -[v](castmx_id (erefl n, erefl ((1+m)%N))) -castmx_mul.
move/(congr1 (castmx (esym (prebasis_card bas), esym (erefl ((1+m)%N))))); rewrite 2!castmxK => Hv.
 
have Hu': (matrix_of_prebasis A next_bas) *m u = (matrix_of_prebasis b_pert next_bas).
- rewrite -[u](castmx_id (erefl n, erefl (1+m)%N)) -castmx_mul.
  apply/(congr1 (castmx (_, _)))/row_matrixP => h.
  rewrite row_mul 2!row_submx_row.
  set k := enum_val h.
  rewrite mulmxDr.
 
  case: (altP (k =P j)) => [-> | H].
  + rewrite -[X in _ + X]row_mul.
    rewrite [X in _ + row _ X]mulmxA row_mul.
    rewrite [X in _ + X *m _]mx11_scalar mul_scalar_mx mxE.
    rewrite /lex_min_gap Hj' scalerA mulfV; last by apply: ltr0_neq0.
    by rewrite scale1r addrC -addrA addNr addr0.
 
  + have HkI: (k \in bas :\ enum_val (cast_ord (esym (prebasis_card bas)) i)).
    * move: (enum_valP h); rewrite in_setU1; move/negbTE: H ->.
      by rewrite /=.
    have HkI': (k \in bas) by move: HkI; rewrite in_setD1; move/andP => [_].
    move/row_matrixP/(_ (enum_rank_in HkI' k)): Hv.
    rewrite row_mul 2!row_submx_row enum_rankK_in // => ->.
    move/row_matrixP/(_ (enum_rank_in HkI k)): (mulmx_direction bas i).
    rewrite row_mul row_submx_row enum_rankK_in // row0 [X in _ + X]mulmxA => ->.
    by rewrite mul0mx addr0.
 
set B := invmx (matrix_of_prebasis A next_bas).
move/(congr1 (mulmx B)): Hu'.
by rewrite mulmxA mulVmx // mul1mx.
Qed.

Lemma lex_min_gap_lex_non_neg :
let: d := direction bas i in
let: j := lex_ent_var in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
   0 <=lex lex_min_gap.
Proof.
set d := direction bas i.
set j := lex_ent_var.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
move: (lex_feasible_basis_is_lex_feasible bas) => Hfeas.
move/andP: lex_ent_var_properties => [Hj /eqP Hj'].
move: Hj; rewrite mem_filter; move/andP => [Hj _].
rewrite -/j -/d in Hj, Hj'.
rewrite /lex_min_gap Hj' /lex_gap.
rewrite -[0](scaler0 _ ((A *m d) j 0)^-1).
move: (Hj); rewrite -oppr_gt0 => Hj''.
rewrite -(lex_pscalar Hj'') 2!scalerA -mulN1r -mulrA mulfV; last by apply: ltr0_neq0.
rewrite scaler0 mulr1 scaleN1r oppv_gelex0 -(lex_add2r (row j A *m point_of_basis_pert bas)) -addrA addNr addr0 add0r.
by move/forallP: Hfeas.
Qed.

Lemma lex_min_gap_non_null :
  let: d := direction bas i in
  let: j := lex_ent_var in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
  lex_min_gap != 0.
Proof.
set d := direction bas i.
set j := lex_ent_var.
move: (lex_feasible_basis_is_lex_feasible bas) => Hfeas.
move/andP: lex_ent_var_properties => [Hj /eqP ->].
move: Hj; rewrite mem_filter; move/andP => [Hj _].
rewrite scalemx_eq0 negb_or; apply/andP; split.
- apply: invr_neq0; exact: ltr0_neq0. 
- apply/eqP => /subr0_eq-/esym H.  
  suff /eq_pert_point_imp_eq_bas/eqP Hbas: point_of_basis_pert bas = point_of_basis_pert lex_rule_bas.
  + by move: lex_ent_var_not_in_basis; rewrite Hbas setU11 /=.
  + apply: is_point_of_basis_pert_active => k.
    rewrite in_setU1; move/orP; case. 
    * by move/eqP ->; rewrite row_mul.
    * rewrite in_setD1 => /andP [_ Hk].
      move: (row_submx_point_of_basis_pert bas).
      by rewrite -row_submx_mul; move/row_submx_row_matrixP/(_ _ Hk).
Qed.      

Lemma lex_min_gap_lex_pos :
  let: d := direction bas i in
  let: j := lex_ent_var in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
  lex_min_gap >lex 0.
Proof.
apply/andP; split. 
- rewrite eq_sym; exact: lex_min_gap_non_null.
- exact: lex_min_gap_lex_non_neg.
Qed.
  
Lemma lex_min_gap_lex_prop (h : 'I_m) :
let: d := direction bas i in
let: v := point_of_basis_pert bas in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
   (A *m d) h 0 < 0 -> (row h b_pert) <=lex (row h A *m v + (A *m d) h 0 *: lex_min_gap).
Proof.
set d := direction bas i.
set v := point_of_basis_pert bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
move => H.
move: (H); rewrite -invr_lt0 => H'.
rewrite lex_subr_addr (lex_negscalar (row h b_pert - row h A *m v) ((A *m d) h 0 *: lex_min_gap) H') scalerA mulVr;
  last by rewrite unitfE; apply: (ltr0_neq0 H).
rewrite scale1r.
apply: lex_min_seq_ler; apply: map_f.
rewrite mem_filter; apply/andP; split; by rewrite ?mem_enum.
Qed.

Lemma lex_rule_lex_feasibility : is_lex_feasible lex_rule_bas.
Proof.
set d := direction bas i.
set j := lex_ent_var.
set bas' := lex_rule_bas.
set v := point_of_basis_pert bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
set u := v + d *m lex_min_gap.
move: (lex_feasible_basis_is_lex_feasible bas) => Hfeas.
move: lex_min_gap_lex_non_neg => Hmin_gap.
move: lex_rule_rel_succ_points => Hvu.
rewrite -/u in Hvu.
have Hu: [forall j, ((row j A) *m u) >=lex (row j b_pert)].
- apply/forallP => h.
  rewrite mulmxDr [X in _ + X]mulmxA -[X in _ + X *m _]row_mul.
  rewrite [X in _ + X *m _]mx11_scalar mul_scalar_mx mxE.
  case: (ltrgt0P ((A *m d) h 0)) => [H | H | ->].
  + rewrite -[X in X <=lex _]addr0.
    apply: (@lex_trans _ _ (row h A *m v + 0)).
    - rewrite lex_add2r; by move/forallP: Hfeas.
    - rewrite lex_add2l -[0](scaler0 _ ((A *m d) h 0)) lex_pscalar //.
  + by apply: (lex_min_gap_lex_prop H).
  + by rewrite scale0r addr0; move/forallP: Hfeas.
by rewrite -Hvu in Hu.
Qed.

Definition lex_rule_lex_bas := LexFeasibleBasis lex_rule_lex_feasibility.

Lemma lex_rule_dec :
  let: bas' := lex_rule_lex_bas in
  let: u := reduced_cost_of_basis c bas in
  u i 0 < 0 -> (c^T *m point_of_basis_pert bas') <lex (c^T *m point_of_basis_pert bas).
Proof.
set d := direction bas i.
set j := lex_ent_var.
set bas' := lex_rule_lex_bas.
set v := point_of_basis_pert bas.
set v' := point_of_basis_pert bas'.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
set u := v + d *m lex_min_gap.
 
move => Hui.
move: lex_rule_rel_succ_points => Hv'u.
rewrite -/u -/v' in Hv'u.
rewrite Hv'u /u mulmxDr lex_ltrNge -subv_gelex0 addrC addrA addNr add0r -lex_ltrNge mulmxA.
rewrite -vdot_def vdotC mul_scalar_mx.
rewrite lex_ltrNge -[0](scaler0 _ ('[c,d])) -lex_negscalar; last exact: direction_improvement.
rewrite -lex_ltrNge; exact: lex_min_gap_lex_pos.
Qed.

End Lexicographic_rule.

Section LexPhase2.

Variable s : 'S_m.

Inductive lex_final_result :=
| Lex_res_unbounded of (lex_feasible_basis s) * 'I_n
| Lex_res_optimal_basis of (lex_feasible_basis s).

Inductive lex_intermediate_result :=
| Lex_final of lex_final_result
| Lex_next_basis of (lex_feasible_basis s).

Variable c : 'cV[R]_n.
Implicit Types bas : (lex_feasible_basis s).

Definition basic_step bas :=
  let u := reduced_cost_of_basis c bas in
  if [pick i | u i 0 < 0] is Some i then
    let d := direction bas i in
    if (@idPn (feasible_dir A d)) is ReflectT infeas_dir then
      Lex_next_basis (lex_rule_lex_bas infeas_dir)
    else Lex_final (Lex_res_unbounded (bas, i))
  else
    Lex_final (Lex_res_optimal_basis bas).

Definition basis_height bas :=
  #|[ set bas' : (lex_feasible_basis s) | (c^T *m (point_of_basis_pert s bas')) <lex (c^T *m (point_of_basis_pert s bas)) ]|.

Function lex_phase2 bas {measure basis_height bas} :=
  match basic_step bas with
  | Lex_final final_res => final_res
  | Lex_next_basis bas' => lex_phase2 bas'
  end.
Proof.
move => bas bas'.
move => Hbas.
apply/leP.
pose u := reduced_cost_of_basis c bas.
 
move: Hbas; rewrite /basic_step.
case: pickP => [i |]; last by done.
rewrite -/u; move => Hui.
case: {-}_ /idPn => [infeas_dir [] Hbas'|]; last by done.
 
move: (lex_rule_dec infeas_dir Hui) => Hc; rewrite Hbas' in Hc.
apply: proper_card.
set Sbas' := [set _ | _]; set Sbas := [set _ | _].
rewrite properEneq; apply/andP; split; last first.
- apply/subsetP; move => bas''.
  rewrite !inE; move/andP => [_ Hbas''].
  by apply:(lex_le_ltr_trans Hbas'' Hc).
- apply: contraT; rewrite negbK; move/eqP => Hcontra.
  have H1: bas' \notin (Sbas').
  + rewrite inE negb_and; apply/orP; left.
    by rewrite negbK eq_refl.
  have H2: bas' \in (Sbas) by rewrite inE.
  move/setP/(_ bas'): Hcontra.
  by move/negbTE: H1 ->; rewrite H2.
Qed.

CoInductive lex_phase2_spec : lex_final_result -> Type :=
| Lex_unbounded (p: (lex_feasible_basis s) * 'I_n) of (reduced_cost_of_basis c p.1) p.2 0 < 0 /\ feasible_dir A (direction p.1 p.2) : lex_phase2_spec (Lex_res_unbounded p)
| Lex_optimal_basis (bas: lex_feasible_basis s) of (reduced_cost_of_basis c bas) >=m 0 : lex_phase2_spec (Lex_res_optimal_basis bas).

Lemma lex_phase2P bas0 : lex_phase2_spec (lex_phase2 bas0).
Proof.
pose P bas' res := (lex_phase2_spec res).
suff /(_ bas0): (forall bas, P bas (lex_phase2 bas)) by done.
apply: lex_phase2_rect; last by done.
- move => bas1 res; rewrite /basic_step.
  case: pickP => [i Hi| Hu [] <-].
  + case: {-}_ /idPn => [? |/negP Hd [] /= <-]; try by done.
    * by rewrite negbK in Hd; constructor.
  + constructor; apply/forallP => i; rewrite mxE.
    move/(_ i)/negbT: Hu.
    by rewrite lerNgt.
Qed.

End LexPhase2.

Section Phase2.

Variable bas0 : feasible_basis.

Lemma n_leq_m : ((m - n) + n = m)%N.
Proof.
move: (max_card (pred_of_set bas0)).
rewrite (prebasis_card bas0) cardE size_enum_ord => ?.
rewrite subnK //.
Qed.

Definition C_bas0 := ~: bas0.

Lemma card_C_bas0 :  #|~: bas0| = (m-n)%N.
Proof.
move: (cardsC bas0).
rewrite (prebasis_card bas0) [RHS]cardE size_enum_ord -[RHS]n_leq_m.
by rewrite [RHS]addnC; move/addnI.
Qed.

Lemma in_setC' : forall i, ~ (i \in bas0) -> (i \in C_bas0).
Proof.
by move=> i; move/setCP; rewrite in_setC.
Qed.

Definition s0_fun i :=
  cast_ord n_leq_m
           (match (@idP (i \in bas0)) with
            | ReflectT Hi => rshift (m-n)%N (cast_ord (prebasis_card bas0) (enum_rank_in Hi i))
            | ReflectF Hi => lshift n (cast_ord card_C_bas0 (enum_rank_in (@in_setC' i Hi) i))
            end).

Definition s0_inj : injective s0_fun.
Proof.
move => i j /cast_ord_inj.
case: {-}_ /idP => [Hi /esym | Hi]; case: {-}_ /idP => [Hj | Hj].
- move/rshift_inj/cast_ord_inj/(congr1 enum_val).
  do 2![rewrite enum_rankK_in //].
- set k := (X in lshift _ X); set l := (X in rshift _ X).
  by move/eqP: (lrshift_distinct k l).
- set k := (X in lshift _ X); set l := (X in rshift _ X).
  by move/eqP: (lrshift_distinct k l).
- move/lshift_inj/cast_ord_inj/(congr1 enum_val).
    do 2![rewrite enum_rankK_in //; last by rewrite in_setC; apply/negP].
Qed.

Definition s0 := perm s0_inj.

Lemma ineq_in_basis_satisfied (i : 'I_m) (s : 'S_m) (bas : basis) :
let: u' := point_of_basis_pert s bas in
  i \in bas -> (row i (b_pert s)) <=lex ((row i A) *m u').
Proof.
move => Hi.
have /row_matrixP/(_ (cast_ord (prebasis_card bas) (enum_rank_in Hi i))): (matrix_of_prebasis A bas) *m point_of_basis_pert s bas = matrix_of_prebasis (b_pert s) bas.
  rewrite mulmxA mulmxV; last by apply: matrix_of_basis_in_unitmx.
  by rewrite mul1mx.
rewrite -[point_of_basis_pert _ _](castmx_id (erefl _, erefl _)) -castmx_mul;
do 2![rewrite row_castmx castmx_id cast_ordK].
rewrite -row_submx_mul 2!row_submx_row enum_rankK_in //.
by move <-; rewrite -row_mul; apply: lex_refl.
Qed.

Lemma feasible_to_lex_feasible :
  is_lex_feasible s0 bas0.
Proof.
pose b' := b_pert s0.
have Hb: forall j, col (rshift 1 (cast_ord n_leq_m (lshift n j))) (matrix_of_prebasis b' bas0) = 0.
- move => j.
  rewrite /matrix_of_prebasis.
  rewrite row_submx_row_mx castmx_row colKr.
  apply/colP => k; rewrite !mxE castmxE /= cast_ord_id row_submx_mxE !mxE.
  set l := cast_ord _ _; rewrite permE.
  suff /negbTE ->: (s0_fun (enum_val l) != cast_ord n_leq_m (lshift n j))
    by rewrite mulr0n oppr0.
  + rewrite /s0_fun (inj_eq (@cast_ord_inj _ _ n_leq_m)).
    move: (enum_valP l) => Hl; case: {-}_ /idP => [Hl' |]; last by done.
    rewrite eq_sym; exact: lrshift_distinct.
apply/forallP => i.
- set rowi := (_ *m _).
  have Hcol : forall j, col (rshift 1 (cast_ord n_leq_m (lshift n j))) rowi = 0.
  + by move => j; rewrite 2!col_mul (Hb j) 2!mulmx0.
  case: (boolP (i \in bas0)) => [Hi | Hi]; last first.
  + apply: lex_ltrW; apply: (@lex_lev_strict _ _ _ _ (rshift 1 (s0_fun i))).
    rewrite /s0_fun; case: {-}_ /idP => [ Hi' | Hi' ]; first by rewrite Hi' in Hi.
      set k := (cast_ord card_C_bas0 _).
    apply/andP; split; last first.
    * move/colP/(_ 0): (Hcol k); rewrite mxE [RHS]mxE; move ->.
      rewrite mxE row_mxEr !mxE.
      suff ->: s0 i == cast_ord n_leq_m (lshift n k).
      - by rewrite /= mulr1n; apply: ltrN10.
      - apply/eqP; rewrite permE /s0_fun.
        apply/(congr1 (cast_ord n_leq_m)); case: {-}_ /idP => [ Hi'' | Hi'' ]; first by done.
        apply/(congr1 (lshift _))/(congr1 (cast_ord _)); apply: enum_val_inj.
        by rewrite -in_setC in Hi; do 2![rewrite enum_rankK_in //].
    * apply/forallP => j.
      case: (splitP' j) => [l -> | l Hjl].
      - rewrite row_row_mx row_mxEl [X in X <= _]mxE.
        rewrite /rowi  /point_of_basis_pert -row_mul [X in _ <= X]mxE.
        rewrite mulmxA {2}/matrix_of_prebasis.
        rewrite row_submx_row_mx cast_row_mx mul_mx_row row_mxEl.
        rewrite -mulmxA.
        suff ->: (l = 0) by move/forallP/(_ i): (feasible_basis_is_feasible bas0).
        + by apply: ord_inj; move: (ltn_ord l); rewrite ltnS leqn0; move/eqP.
      - apply/implyP; rewrite {1}Hjl /=.
        rewrite ltn_add2l => Hl.
        move: (ltn_ord (enum_rank_in (in_setC' Hi') i)); rewrite {2}card_C_bas0.
        move/(ltn_trans Hl) => Hl0.
        pose l0 := Ordinal Hl0.
        have Hj: j = rshift 1 (cast_ord n_leq_m (lshift n l0)).
          by apply:ord_inj; rewrite Hjl /=.
        rewrite {Hjl Hl}.
        move/colP/(_ 0): (Hcol l0); rewrite mxE [RHS]mxE -Hj; move ->.
        rewrite row_row_mx Hj row_mxEr !mxE.
        by rewrite oppr_le0 ler0n.
  + by apply: (ineq_in_basis_satisfied s0 Hi).
Qed.

Variable c : 'cV[R]_n.

Inductive phase2_final_result :=
| Phase2_res_unbounded of feasible_basis * 'I_n
| Phase2_res_optimal_basis of feasible_basis.

Definition lex_to_phase2_final_result res :=
  match res with
  | Lex_res_unbounded (bas, i) => Phase2_res_unbounded (FeasibleBasis ((@lex_feasible_basis_is_feasible s0) bas), i)
  | Lex_res_optimal_basis bas => Phase2_res_optimal_basis (FeasibleBasis ((@lex_feasible_basis_is_feasible s0)  bas))
  end.

Definition phase2 :=
  let: lex_bas0 := LexFeasibleBasis (feasible_to_lex_feasible) in 
    lex_to_phase2_final_result ((@lex_phase2 s0) c lex_bas0).

(*Implicit Types bas : feasible_basis.*)

CoInductive phase2_spec : phase2_final_result -> Type :=
| Phase2_unbounded (p: feasible_basis * 'I_n) of (reduced_cost_of_basis c p.1) p.2 0 < 0 /\ feasible_dir A (direction p.1 p.2) : phase2_spec (Phase2_res_unbounded p)
| Phase2_optimal_basis (bas: feasible_basis) of (reduced_cost_of_basis c bas) >=m 0 : phase2_spec (Phase2_res_optimal_basis bas).

Lemma phase2P : phase2_spec phase2.
Proof.
rewrite /phase2 /lex_to_phase2_final_result.
case: lex_phase2P => [[bas d]|]; try by constructor.
Qed.

End Phase2.

End Simplex.

Section Feasibility.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Definition dual_set0 := [set (rshift (n+n) i) | i in [set: 'I_m] ].

Lemma dual_set0_card : (#| dual_set0 | == m)%N.
Proof.
rewrite card_imset; last exact: rshift_inj.
by rewrite cardsT card_ord eq_refl.
Qed.

Definition dual_pb0 := Prebasis dual_set0_card.

Lemma dual_pb0_is_basis : (is_basis (dualA A) dual_pb0).
Proof.
rewrite /is_basis -row_free_unit -row_leq_rank /matrix_of_prebasis.
rewrite row_submx_col_mx_rshift row_submxT !rank_castmx.
by rewrite row_leq_rank row_free_unit unitmx1.
Qed.

Definition dual_bas0 := Basis dual_pb0_is_basis.

Lemma dual_bas0_is_feasible : (is_feasible (dualb _ 0) dual_bas0).
Proof.
rewrite /is_feasible -dual_polyhedronE inE.
suff ->: point_of_basis (dualb m 0) dual_bas0 = 0
  by rewrite mulmx0 eq_refl lev_refl.
rewrite /point_of_basis {2}/matrix_of_prebasis /dualb row_submx_col_mx_rshift.
by rewrite row_submxT !castmx_const mulmx0.
Qed.

Definition dual_feasible_bas0 := FeasibleBasis dual_bas0_is_feasible.

Definition feasible :=
  if phase2 dual_feasible_bas0 (-b) is Phase2_res_optimal_basis _ then true else false.

Lemma feasibleP :
  reflect (exists x, x \in polyhedron A b) feasible.
Proof.
rewrite /feasible; case: phase2P => [[bas d] /= [Hd Hd']| bas Hbas]; constructor.
- move => [x Hx].
  move: (unbounded_cert_on_basis 0 Hd' Hd) => [u].
  rewrite -dual_polyhedronE inE vdotNl oppr_lt0.
  move => [/andP [/eqP Hu Hu'] Hu''].
  move/(vdot_lev Hu'): Hx; rewrite vdot_mulmx Hu vdot0l vdotC.
  by move/(ltr_le_trans Hu''); rewrite ltrr.
- pose v := ext_reduced_cost_of_basis (- b) bas.
  move: Hbas; rewrite ext_reduced_cost_dual_feasible -/v inE => /andP [/eqP].
  rewrite mul_tr_dualA gev0_vsubmx. 
  set x := (dsubmx (usubmx v) - usubmx (usubmx v)).
  move/(canRL (subrK _)) ->; rewrite addrC subv_ge0 => /andP [_ H].
  by exists x.
Qed.

Lemma infeasibleP :
  reflect (exists d, dual_feasible_dir A d /\ '[b,d] > 0) (~~ feasible). 
Proof.
rewrite /feasible.
case: phase2P => [[bas d] [/direction_improvement Hd Hd']| bas Hbas]; constructor.
- rewrite -dual_feasible_directionE in Hd'.
  exists (direction bas d); split; first by done.
  by rewrite vdotNl oppr_lt0 in Hd.
- move => [d [Hd Hd']].
  rewrite -oppr_lt0 -vdotNl in Hd'.
  pose x := point_of_basis (dualb m 0) bas.
  rewrite dual_feasible_directionE in Hd.
  move: (unbounded_certificate '[- b,x] (feasible_basis_is_feasible bas) Hd Hd') => [y [Hy Hy']].
  move/(_ _ Hy)/(ltr_le_trans Hy'): (optimal_cert_on_basis Hbas).
  by rewrite ltrr.
Qed.

End Feasibility.

Section DualFeasibility.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable c : 'cV[R]_n.

Definition dual_feasible := feasible (dualA A) (dualb _ c).

Lemma dual_feasibleP :
  reflect (exists u, u \in dual_polyhedron A c) dual_feasible.
Proof.
by apply: (iffP (feasibleP _ _)) => [[u]| [u]];
   do [ rewrite dual_polyhedronE | rewrite -dual_polyhedronE] => H; exists u.
Qed.

Lemma dual_infeasibleP :
  reflect (exists d, feasible_dir A d /\ '[c,d] < 0) (~~ dual_feasible).
Proof.
apply: (iffP (infeasibleP _ _)) => [[d]| [d] [Hd Hd']];
  last exists (col_mx (col_mx (neg_part d) (pos_part d)) (A *m d));
  rewrite dual_feasible_directionE inE;
  rewrite 2!mul_col_mx mul1mx mulNmx;
  rewrite 2!col_mx_gev0 oppv_ge0;
  rewrite mul_tr_dualA subv_ge0 subv_le0 -eqv_le;
  rewrite vdot_dualb oppr_gt0 gev0_vsubmx.
- move => [/and3P [/eqP <- _ Hd]].
  by set d' := dsubmx _ - usubmx _; exists d'.
- rewrite !col_mxKu !col_mxKd.
  rewrite add_pos_neg_part eq_refl /=.
  split; last by done.
  + by rewrite !col_mx_gev0 neg_part_gev0 pos_part_gev0 /=.
Qed.

End DualFeasibility.

Section Pointed_simplex.
(* a complete simplex method (phase 1 + 2) which applies to LP 
 * such that the feasible set is pointed *)

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis Hpointed: pointed A.

Lemma rank_row_submxT: (mxrank (row_submx A setT) >= n)%N.
Proof.
by rewrite row_submxT rank_castmx.
Qed.

Definition bas0_set := build_row_base A setT n.

Lemma bas0_card: #|bas0_set| == n.
Proof.
by move/row_base_correctness: rank_row_submxT => [_ /eqP ? _].
Qed.

Definition bas0_pbas := Prebasis bas0_card.

Lemma bas0_pbas_is_basis : is_basis A bas0_pbas.
Proof.
rewrite /is_basis -row_free_unit -row_leq_rank rank_castmx.
move/row_base_correctness: rank_row_submxT => [_ _ ->].
exact: leqnn.
Qed.

Definition bas0 := Basis bas0_pbas_is_basis.

Definition x0 := point_of_basis b bas0.

(*To implement phase 1 of schrijver book*)

Definition pos_idx := [ set i : 'I_m | (A *m x0) i 0 < b i 0 ].
Definition neg_idx := [ set i : 'I_m | (A *m x0) i 0 >= b i 0 ].

Notation p := #|pos_idx|.

Lemma bas0_subset_neg_idx : (bas0 \subset neg_idx).
Proof.
apply/subsetP => i Hi.
move/subsetP/(_ _ Hi): (basis_subset_of_active_ineq b bas0).
by rewrite 2!inE => /eqP ->; exact: lerr.
Qed.

Lemma pos_neg_idxU : pos_idx :|: neg_idx = setT.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; first exact: subsetT.
- by apply/subsetP => i _; rewrite in_setU !inE; case: lerP.
Qed.

Lemma pos_neg_idxI : [disjoint pos_idx & neg_idx].
Proof.
rewrite disjoints_subset.
by apply/subsetP => i; rewrite !inE ltrNge.
Qed.

Lemma pos_idxC : ~: pos_idx = neg_idx.
Proof.
rewrite -setTD -pos_neg_idxU setDUl.
rewrite setDv set0U.
by apply/setDidPl; rewrite disjoint_sym; exact: pos_neg_idxI.
Qed.

Lemma neg_idxC : ~: neg_idx = pos_idx.
Proof.
move/(congr1 (@setC _)): pos_idxC.
by rewrite setCK => ->.
Qed.

Lemma pos_neg_card : (#|pos_idx| + #|neg_idx| = m)%N.
Proof.
move/leqifP: (leq_card_setU pos_idx neg_idx).
rewrite ifT; last by apply:pos_neg_idxI.
by move: pos_neg_idxU ->; rewrite cardsT card_ord => /eqP <-.
Qed.

Definition A' :=
  \matrix_i (if (@idP (i \in pos_idx)) is (ReflectT Hi) then
               let: i' := enum_rank_in Hi i in
               row_mx (-(row i A)) (delta_mx 0 i')
             else
               row_mx (row i A) 0).

Definition b' :=
  \col_i (if i \in pos_idx then
            - (b i 0)
          else
            b i 0).

Definition s_idx_fun :=
  let: f := fun i =>   
              match split i with 
              | inl j => enum_val j
              | inr j => enum_val j
              end
  in (f \o (cast_ord (esym pos_neg_card))).

Lemma s_idx_inj : injective s_idx_fun.
Proof.
apply: inj_comp; last by apply: cast_ord_inj.
move => i i'.
case: splitP => [j H | j H]; case: splitP => [j' H' | j' H'] Hjj';
  try by move/enum_val_inj: Hjj' => Hjj'; rewrite Hjj' -H' in H; exact: ord_inj.
- move/andP: (conj (enum_valP j) (enum_valP j')); rewrite -Hjj'.
  by rewrite -in_setI; move/disjoint_setI0: pos_neg_idxI ->; rewrite in_set0.
- move/andP: (conj (enum_valP j) (enum_valP j')); rewrite -Hjj'.
  by rewrite -in_setI setIC; move/disjoint_setI0: pos_neg_idxI ->; rewrite in_set0.
Qed.

Definition s_idx := perm s_idx_inj.

Definition Apos := (row_submx A pos_idx).
Definition Aneg := (row_submx A neg_idx).

Definition bpos := (row_submx b pos_idx).
Definition bneg := (row_submx b neg_idx).

Lemma row_perm_pos_neg (q : nat) (M : 'M[R]_(m,q)) :
  let: Mpos := row_submx M pos_idx in
  let: Mneg := row_submx M neg_idx in
  row_perm s_idx M = castmx (pos_neg_card, erefl q) (col_mx Mpos Mneg).
Proof.
apply/matrixP => i j.
rewrite castmxE /= cast_ord_id !mxE permE /s_idx_fun /=.
by case: splitP => [ k _ | k _]; rewrite row_submx_mxE.
Qed.

Definition Aposext := row_submx A' pos_idx.
Definition Anegext := row_submx A' neg_idx.

Lemma Aposext_row_mx : Aposext = row_mx (-Apos) (1%:M).
Proof.
apply/row_matrixP => i.
rewrite row_submx_row.
rewrite row_row_mx linearN /= row_submx_row row1 rowK.
case: {-}_/idP => [H | H]; first by rewrite enum_valK_in.
by move: (enum_valP i).
Qed.

Lemma rel_A'_Aposneg :
  row_perm s_idx A' =
  castmx (pos_neg_card, erefl (n+p)%N) (block_mx (-Apos) (1%:M) Aneg 0).
Proof.
rewrite row_perm_pos_neg; apply: (congr1 (castmx _)).
rewrite block_mxEv; apply: (congr2 col_mx); 
apply/row_matrixP => i; rewrite row_submx_row rowK.
- case: {-} _/ idP => [H |]; last by move: (enum_valP i) ->.
  rewrite enum_valK_in.
  by rewrite row_row_mx linearN /= row_submx_row row1.
- case: {-} _/ idP => [H| H].
  + move: (enum_valP i); rewrite -{2}pos_idxC in_setC.
    by rewrite H.
  + by rewrite row_row_mx row_submx_row row0.
Qed.

Lemma rel_b'_bposneg :
  row_perm s_idx b' = castmx (pos_neg_card, erefl 1%N) (col_mx (-bpos) bneg).
Proof.
rewrite row_perm_pos_neg; apply: (congr1 (castmx _)).
apply: (congr2 col_mx); apply/colP => i; rewrite !mxE.
- by move: (enum_valP i) ->.
- by rewrite ifF; last by apply/negbTE; rewrite -in_setC pos_idxC; exact: enum_valP.
Qed.

Definition Aext := col_mx A' (row_mx 0 (1%:M)).
Definition bext := (col_mx b' 0):'cV_(m+p).

Lemma polyhedronext_inE x :
  let: (y,z) := (usubmx x, dsubmx x) in
  (x \in polyhedron Aext bext) = [&& (Aneg *m y) >=m bneg, (Apos *m y) <=m (bpos + z) & z >=m 0].
Proof.
rewrite inE -{1}[x]vsubmxK.
rewrite mul_col_mx mul_row_col.
rewrite mul1mx mul0mx add0r.
rewrite col_mx_lev.
rewrite [RHS]andbA; apply: congr2; last by done.
rewrite (row_perm_lev s_idx).
rewrite [X in _ <=m X]row_permE mulmxA -row_permE.
rewrite rel_A'_Aposneg rel_b'_bposneg cast_mulmx lev_castmx.
rewrite mul_block_col col_mx_lev.
rewrite mul0mx addr0 mul1mx andbC.
apply: congr1.
rewrite mulNmx -(lev_add2l (Apos *m usubmx x)) addrA addrN add0r.
by rewrite -(lev_add2r bpos) -addrA addNr addr0 addrC.
Qed.

Definition cext := (Aposext^T *m const_mx 1):'cV_(n+#|pos_idx|).
Definition Mext := '[const_mx 1, -bpos].

Lemma pos_neg_lev_decomp :
      polyhedron A b =i [predI (polyhedron Apos bpos) & (polyhedron Aneg bneg)].
Proof.
move => x; rewrite !inE.
by move: (lev_decomp b (A *m x) pos_idx); rewrite pos_idxC !row_submx_mul.
Qed.

Lemma cext_def x :
      '[cext, x] = '[const_mx 1, - (Apos *m usubmx x) + dsubmx x ].
Proof.
rewrite -vdot_mulmx Aposext_row_mx.
by rewrite -{1}[x]vsubmxK mul_row_col mul1mx mulNmx.
Qed.

Lemma cext_min_value x :
  (x \in polyhedron Aext bext) -> '[cext, x] >= Mext.
Proof.
rewrite polyhedronext_inE => /and3P [_ Hx _].
rewrite cext_def.
apply: vdot_lev.
- by apply/forallP => i; rewrite !mxE; apply: ler01.
- rewrite -(lev_add2r (-dsubmx x)) -addrA addrN addr0 -opprD.
  by rewrite lev_opp2.
Qed.

Lemma cext_min_value_attained x :
  (x \in polyhedron Aext bext) -> '[cext, x] = Mext ->
  Apos *m usubmx x = bpos + dsubmx x.
Proof.
rewrite polyhedronext_inE => /and3P [_ Hx _] Hx'.
symmetry; apply: subr0_eq.
have: '[const_mx 1, (bpos + dsubmx x) - (Apos *m usubmx x)] = 0.
- rewrite -addrA vdotDr.
  rewrite cext_def addrC in Hx'.
  by rewrite Hx' /Mext -vdotDr addrN vdot0r.
apply: vdot_lev_eq0; last by rewrite -subv_ge0 in Hx.
by apply/forallP => i; rewrite mxE; exact: ltr01.
Qed.

Lemma feasible_cext_eq_min_value x :
  x \in polyhedron A b ->
        let: z := col_mx x (Apos *m x - bpos) in
        (z \in polyhedron Aext bext) /\ ('[cext,z] = Mext).
Proof.
set z := Apos *m x - bpos.
rewrite (pos_neg_lev_decomp x) => /andP [Hx Hx'].
split.
- rewrite polyhedronext_inE col_mxKu col_mxKd.
  apply/and3P; split; try by [rewrite subv_ge0 | done].
  + by rewrite [X in bpos + X]addrC addrA addrN add0r lev_refl.
- rewrite cext_def col_mxKu col_mxKd.
  by rewrite addrA addNr add0r.
Qed.

Lemma feasible_cext_eq_min_active x :
  x \in polyhedron Aext bext -> '[cext,x] = Mext ->
  let: y := usubmx x in
  (y \in polyhedron A b).
Proof.
move => Hx.
move/(cext_min_value_attained Hx) => Hx'.
move: Hx; rewrite polyhedronext_inE => /and3P [Hxneg _].
rewrite -(lev_add2l bpos) addr0 -Hx' => Hxpos.
by rewrite pos_neg_lev_decomp inE; apply/andP; split.
Qed.

Lemma extremality_ext x :
  is_extreme x (polyhedron Aext bext: _ -> bool) -> ('[cext,x] = Mext) ->
    let: y := usubmx x in
    is_extreme y (polyhedron A b: _ -> bool).
Proof.
set y := usubmx x.
move => [Hx Hext] Hcext.
split; first by move: (feasible_cext_eq_min_active Hx Hcext).
move => y1 y2 lambda Hy1 Hy2 Hlambda Hy.
move: (feasible_cext_eq_min_value Hy1) => [Hx1 _].
set x1 := (col_mx y1 (Apos *m y1 - bpos)) in Hx1.
move: (feasible_cext_eq_min_value Hy2) => [Hx2 _].
set x2 := (col_mx y2 (Apos *m y2 - bpos)) in Hx2.
suff: x = x1 /\ x = x2.
- move => [/(congr1 usubmx) Hxx1 /(congr1 usubmx) Hxx2].
  rewrite 2!col_mxKu in Hxx1 Hxx2.
  by rewrite -Hxx1 -Hxx2.
- apply: (Hext _ _ lambda Hx1 Hx2 Hlambda).
  rewrite 2!scale_col_mx add_col_mx -Hy.
  rewrite 2!scalerDr addrACA 2!scalemxAr -mulmxDr -Hy.
  rewrite -scalerDl addrCA addrN addr0 scale1r.
  rewrite -[x]vsubmxK.
  suff ->: dsubmx x = Apos *m y - bpos by done.
  move: (cext_min_value_attained Hx Hcext).
  by move/(congr1 (fun z => z - bpos)); rewrite addrAC addrN add0r => ->.
Qed.

Definition dual_from_ext (u:'cV[R]_(m+p)) :=
  let u' := usubmx u in
  \col_i (if i \in pos_idx then 
           1 - u' i 0
         else
           u' i 0).

Lemma dual_from_ext_perm u :
  let: u' := usubmx u in
  let: upos := row_submx u' pos_idx in
  let: uneg := row_submx u' neg_idx in
  row_perm s_idx (dual_from_ext u) =
  (castmx (pos_neg_card, erefl 1%N) (col_mx (const_mx 1 - upos) uneg)).
Proof.
apply/colP => i.
rewrite castmxE /= cast_ord_id !mxE permE /s_idx_fun /=.
case: splitP => [ k _ | k _]; rewrite !mxE.
- by rewrite ifT; last exact: enum_valP.
- by rewrite ifF; last by apply:negbTE; rewrite -in_setC pos_idxC; exact: enum_valP.
Qed.

Lemma dual_polyhedron_from_ext u :
  (u \in dual_polyhedron Aext cext) ->
  dual_feasible_dir A (dual_from_ext u).
Proof.
rewrite inE tr_col_mx -{-3}[u]vsubmxK mul_row_col.
rewrite tr_row_mx trmx0 trmx1 mul_col_mx mul0mx mul1mx.
rewrite /cext Aposext_row_mx tr_row_mx trmx1 mul_col_mx mul1mx.
 
rewrite -(mulmx_tr_row_perm s_idx).
rewrite rel_A'_Aposneg trmx_cast /= tr_block_mx trmx1 trmx0.
rewrite -[pos_neg_card]esymK -[row_perm _ _](castmx_id (erefl _, erefl _))
        -mulmx_cast.
 
rewrite row_perm_pos_neg.
have {1}->: erefl 1%N = esym (erefl 1%N) by done.
rewrite castmxK.
set upos := row_submx (usubmx u) pos_idx.
set uneg := row_submx (usubmx u) neg_idx.
 
rewrite mul_block_col mul1mx mul0mx addr0.
rewrite add_col_mx addr0 col_mx_eq -andbA.
 
move/and3P => [Heq Heq' Hineq].
(* working with Heq *)
- move: Heq.
  rewrite -subr_eq0 linearN /= 2!mulNmx opprK -mulmxN.
  rewrite addrC addrA -mulmxDr => Heq.
(* working with Heq' *)
- move: Heq'; rewrite eq_sym addrC -subr_eq => /eqP Heq'.
(* with Hineq *)
- move: Hineq.
  rewrite col_mx_gev0 -{}Heq' => /andP [Hneg Hpos].
  move: Hneg; rewrite (row_perm_gev0 s_idx).
  rewrite row_perm_pos_neg castmx_gev0 col_mx_gev0 -/uneg => /andP [_ Hneg].
  
set v := dual_from_ext u.
apply/andP; split.
- rewrite -(mulmx_tr_row_perm s_idx).
  rewrite dual_from_ext_perm -/upos -/uneg.
  rewrite row_perm_pos_neg trmx_cast /= tr_col_mx mulmx_cast.
  have ->: erefl n = esym (erefl n) by done.
  by rewrite castmxK castmx_id mul_row_col.
 
- rewrite /v (row_perm_gev0 s_idx).
  rewrite dual_from_ext_perm castmx_gev0 col_mx_gev0.
  by apply/andP; split.
Qed.

Lemma dual_from_ext_obj u :
  '[bext, u] > Mext -> '[b, dual_from_ext u] > 0.
Proof.
rewrite -{1}[u]vsubmxK vdot_col_mx vdot0l addr0.
rewrite -(vdot_perm s_idx) rel_b'_bposneg.
rewrite row_perm_pos_neg vdot_castmx.
set u' := usubmx _; set upos := row_submx u' pos_idx; set uneg := row_submx u' neg_idx.
rewrite vdot_col_mx.
rewrite -subr_gt0 addrAC vdotNl -vdotNr.
rewrite [X in _ - X + _]vdotC [X in _ - X + _]vdotNl opprK.
rewrite [X in X + _]addrC -vdotDr => H.
rewrite -(vdot_perm s_idx) row_perm_pos_neg.
by rewrite dual_from_ext_perm vdot_castmx vdot_col_mx.
Qed.

Definition bas0_ext_set :=
  ((lshift p) @: bas0) :|: ((@rshift m _) @: [set: 'I_p]).

Lemma bas0_ext_card : (#|bas0_ext_set| == n+p)%N.
Proof.
rewrite lrshift_image_card.
by rewrite prebasis_card cardsT card_ord.
Qed.

Definition bas0_ext_pb := Prebasis bas0_ext_card.

Lemma A'_bas0 : row_submx A' bas0 = row_mx (row_submx A bas0) 0.
Proof.
apply/row_matrixP => i.
rewrite row_row_mx 2!row_submx_row row0.
rewrite rowK; case: {-}_/idP => [Hpos | _]; last by done.
move/subsetP/(_ _ (enum_valP i)): bas0_subset_neg_idx => Hneg.
move/setIP: (conj Hpos Hneg).
move/disjoint_setI0: pos_neg_idxI ->.
by rewrite in_set0.
Qed.

Lemma b'_bas0 : row_submx b' bas0 = (row_submx b bas0).
Proof.
apply/colP => i.
rewrite 2!row_submx_mxE mxE ifF; first by done.
apply/(introF idP) => Hpos.
move/subsetP/(_ _ (enum_valP i)): bas0_subset_neg_idx => Hneg.
move/setIP: (conj Hpos Hneg).
move/disjoint_setI0: pos_neg_idxI ->.
by rewrite in_set0.
Qed.

Lemma bas0_ext_pb_is_basis : is_basis Aext bas0_ext_pb.
Proof.
rewrite /is_basis -row_free_unit row_free_castmx.
rewrite row_submx_col_mx row_free_castmx.
rewrite A'_bas0 row_submxT cast_row_mx castmx_const.
set eq_pos_idx := esym _.
rewrite -kermx_eq0.
apply/rowV0P => v /sub_kermxP.
rewrite -[v]hsubmxK mul_row_col 2!mul_mx_row !mulmx0.
rewrite add_row_mx add0r addr0.
rewrite -[0]hsubmxK => /eq_row_mx.
rewrite 2!linear0.
rewrite mulmx_cast castmx_id mulmx1.
move => [/sub_kermxP H H'].
move: (matrix_of_basis_in_unitmx bas0).
rewrite -row_free_unit row_free_castmx -kermx_eq0.
move/rowV0P/(_ (lsubmx v) H) => ->.
move: H'; have ->: erefl 1%N = esym (erefl 1%N) by done.
move/(canRL (castmxKV _ _)).
by rewrite castmx_const => ->; exact: row_mx0.
Qed.

Definition bas0_ext:= Basis bas0_ext_pb_is_basis.

Lemma bas0_ext_is_feasible : is_feasible bext bas0_ext.
Proof.
apply: row_submx_is_feasible.
move => x.
rewrite 2!row_submx_col_mx.
rewrite cast_mulmx; move/castmx_inj.
rewrite A'_bas0 2!row_submxT cast_row_mx castmx_const.
set eq_pos_idx := esym _.
rewrite -{1}[x]vsubmxK mul_col_mx 2!mul_row_col.
rewrite 2!mul0mx addr0 add0r cast_mulmx.
set y := usubmx x.
set z := dsubmx x.
move/eq_col_mx => [Hy /castmx_inj Hz].
rewrite mul1mx /z in Hz.
have: y = point_of_basis b bas0.
- move/(congr1 (castmx (prebasis_card bas0, erefl 1%N))): Hy.
  rewrite castmx_mul castmx_id.
  move/(congr1 (mulmx (invmx (matrix_of_prebasis A bas0)))).
  rewrite mulmxA mulVmx; last exact: matrix_of_basis_in_unitmx.
  by rewrite mul1mx b'_bas0.
rewrite polyhedronext_inE.
rewrite /y Hz; move => ->; rewrite addr0 lev_refl andbT.
apply/andP; split; apply/forallP => i;
  rewrite -row_submx_mul 2!row_submx_mxE;
  move: (enum_valP i); rewrite inE.
- by done.
- exact: ltrW.
Qed.

Definition feasible_bas0_ext := FeasibleBasis bas0_ext_is_feasible.

Variable c : 'cV[R]_n.

Inductive pointed_final_result :=
| Pointed_res_infeasible of 'cV[R]_m
| Pointed_res_unbounded of (feasible_basis A b) * 'I_n
| Pointed_res_optimal_basis of (feasible_basis A b).

Definition pointed_simplex :=
  match phase2 feasible_bas0_ext cext with
  | Phase2_res_unbounded _ =>
    Pointed_res_infeasible 0 (* impossible, see Lemma cext_min_value *)
  | Phase2_res_optimal_basis bas =>
    let: x := point_of_basis bext bas in
    if ('[cext, x] =P Mext) is ReflectT Hext then
      (* LP(A,b,c) is feasible, we build a feasible basis *)
      let: bas' := extract_feasible_basis (extremality_ext (feasible_point_of_basis_is_extreme bas) Hext) in
      match phase2 bas' c with
      | Phase2_res_unbounded (bas'', i) => Pointed_res_unbounded (bas'', i)
      | Phase2_res_optimal_basis bas'' => Pointed_res_optimal_basis bas''
      end
    else
      Pointed_res_infeasible (dual_from_ext (ext_reduced_cost_of_basis cext bas))
  end.

CoInductive pointed_simplex_spec : pointed_final_result -> Type :=
| Pointed_infeasible (d : 'cV[R]_m) of dual_feasible_dir A d /\ '[b,d] > 0 : pointed_simplex_spec (Pointed_res_infeasible d)
| Pointed_unbounded (p : feasible_basis A b * 'I_n) of (reduced_cost_of_basis c p.1) p.2 0 < 0 /\ feasible_dir A (direction p.1 p.2) : pointed_simplex_spec (Pointed_res_unbounded p)
| Pointed_optimal_point (bas : feasible_basis A b) of (reduced_cost_of_basis c bas) >=m 0 : pointed_simplex_spec (Pointed_res_optimal_basis bas).

Lemma pointed_simplexP : pointed_simplex_spec pointed_simplex.
Proof.
rewrite /pointed_simplex.
case: phase2P => [[bas i] /= [Hd Hd']| bas Hbas].
- constructor.
  move: (unbounded_cert_on_basis Mext Hd' Hd) => [x [Hx]].
  by move/(conj (cext_min_value Hx))/andP; rewrite ler_lt_asym.
- pose x := point_of_basis bext bas.
  case: ('[cext, x] =P Mext) => [Hopt | Hopt].
  + case: phase2P => [[bas' d] /=|]; by constructor.
  + constructor; split.
    * apply: dual_polyhedron_from_ext.
      by rewrite -ext_reduced_cost_dual_feasible.
    * apply: dual_from_ext_obj.
      move: (eq_primal_dual_value bext cext bas) <-.
      rewrite ltr_def; apply/andP; split; first by apply/eqP.
      + by apply: (cext_min_value (feasible_basis_is_feasible bas)).
Qed.

End Pointed_simplex.

Section General_simplex.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Variable c : 'cV[R]_n.

Definition Apointed := col_mx (row_mx A (-A)) (1%:M).
Definition bpointed := col_mx b 0: 'cV[R]_(m+(n+n)).
Definition cpointed := col_mx c (-c).

Lemma feasibility_general_to_pointed x :
  x \in polyhedron A b ->
        col_mx (pos_part x) (neg_part x) \in polyhedron Apointed bpointed.
Proof.
rewrite !inE mul_col_mx mul1mx.
rewrite mul_row_col mulNmx -mulmxN -mulmxDr add_pos_neg_part.
by rewrite col_mx_lev -col_mx0 col_mx_lev pos_part_gev0 neg_part_gev0 /= andbT.
Qed.

Definition v2gen (z : 'cV[R]_(n+n)) := (usubmx z) - (dsubmx z).

Definition mulmxAv2gen (z : 'cV[R]_(n+n)):
  (row_mx A (-A)) *m z = A *m (v2gen z).
Proof.
by rewrite -{1}[z]vsubmxK mul_row_col mulNmx -mulmxN -mulmxDr.
Qed.

Definition cost2gen (z : 'cV[R]_(n+n)):
  '[cpointed, z] = '[c,v2gen z].
Proof.
by rewrite -{1}[z]vsubmxK vdot_col_mx vdotNl vdotBr.
Qed.

Definition ext_reduced_cost2gen (bas : basis Apointed) :=
  usubmx (ext_reduced_cost_of_basis cpointed bas).

Lemma ext_reduced_cost2gen_dual_feasible (bas : basis Apointed) :
  (reduced_cost_of_basis cpointed bas) >=m 0 -> (ext_reduced_cost2gen bas \in dual_polyhedron A c).
Proof.
rewrite /ext_reduced_cost2gen -non_neg_reduced_cost_equiv.
set u := ext_reduced_cost_of_basis _ _.
rewrite -{1}[u](vsubmxK) -[0](col_mx0) col_mx_lev => /andP [Hu Hu'].
rewrite inE; apply/andP; split; last by done.
- apply/eqP.
  move: (ext_reduced_cost_of_basis_def cpointed bas); rewrite -/u.
  rewrite /Apointed /A' -{1}[u](vsubmxK) tr_col_mx mul_row_col tr_row_mx mul_col_mx linearN /= mulNmx.
  rewrite trmx1 mul1mx.
  set t := col_mx _ _.
  move/(congr1 (fun z => -t + z)); rewrite addrA addNr add0r => Ht. (* DIRTY *)
  rewrite Ht addrC subv_ge0 in Hu'.
  move: Hu'; rewrite /t /cpointed col_mx_lev => /andP [H H'].
  rewrite lev_opp2 in H'.
  by apply: lev_antisym; apply/andP.
Qed.

Lemma feasibility_pointed_to_general z :
  z \in polyhedron Apointed bpointed -> v2gen z \in polyhedron A b.
Proof.
rewrite inE mul_col_mx col_mx_lev => /andP [? _].
by rewrite inE -mulmxAv2gen.
Qed.

Lemma infeasibility_pointed_to_general d :
  (dual_feasible_dir Apointed d /\ '[bpointed,d] > 0) ->
  dual_feasible_dir A (usubmx d) /\ '[b, usubmx d] > 0.
Proof.
set d_gen := usubmx d.
set d1 := usubmx (dsubmx d).
set d2 := dsubmx (dsubmx d).
have -> : d = col_mx d_gen (col_mx d1 d2) by rewrite !vsubmxK.
rewrite 2!inE tr_col_mx tr_row_mx trmx1.
rewrite mul_row_col mul1mx mul_col_mx add_col_mx col_mx_eq0.
rewrite 2!col_mx_gev0.
move => [/andP [/andP [/eqP Hd1 /eqP Hd2] /and3P [Hd_gen_pos Hd1_pos Hs2_pos]]].
move: (Hd1).
have [-> ->]: (d1 = 0) /\ (d2 = 0).
- move: Hd2 Hd1; rewrite linearN /= addrC mulNmx.
  move/(canRL (subrK _)); rewrite add0r => <-.
  move/eqP; rewrite paddv_eq0 // andbC.
  by move/andP => [/eqP -> /eqP ->].
rewrite addr0 => ->.
rewrite eq_refl Hd_gen_pos /=.
by rewrite vdot_col_mx vdot0l addr0.
Qed.

(*Definition set0_pointed := (@rshift m (n+n)%N) @: setT.

Lemma set0_pointed_card : (#|set0_pointed| == (n+n))%N.
Proof.
rewrite card_imset; last exact: rshift_inj.
by rewrite cardsT card_ord eq_refl.
Qed.

Definition pbas0_pointed := Prebasis set0_pointed_card.

Lemma pbas0_pointed_is_basis : is_basis Apointed pbas0_pointed.
Proof.
Admitted.

Definition bas0_pointed := Basis pbas0_pointed_is_basis.*)

Lemma Apointed_is_pointed: pointed Apointed.
Proof.
rewrite /pointed /Apointed.
move: (@mxrank1 R (n+n)%N) => {1}<-.
apply: mxrankS.
rewrite -addsmxE; exact: addsmxSr.
Qed.

Inductive simplex_final_result :=
| Simplex_infeasible of 'cV[R]_m
| Simplex_unbounded of 'cV[R]_n * 'cV[R]_n
| Simplex_optimal_point of 'cV[R]_n * 'cV[R]_m.

Definition simplex :=
  match pointed_simplex bpointed Apointed_is_pointed cpointed with
  | Pointed_res_infeasible d => Simplex_infeasible (usubmx d)
  | Pointed_res_unbounded (bas, i) =>
    let d := direction bas i in
    Simplex_unbounded (v2gen (point_of_basis bpointed bas), v2gen d)
  | Pointed_res_optimal_basis bas =>
    Simplex_optimal_point (v2gen (point_of_basis bpointed bas), ext_reduced_cost2gen bas)
  end.

CoInductive simplex_spec : simplex_final_result -> Type :=
| Infeasible d of (dual_feasible_dir A d /\ '[b, d] > 0): simplex_spec (Simplex_infeasible d)
| Unbounded p of [/\ (p.1 \in polyhedron A b), (feasible_dir A p.2) & ('[c,p.2] < 0)] : simplex_spec (Simplex_unbounded p)
| Optimal_point p of [/\ (p.1 \in polyhedron A b), (p.2 \in dual_polyhedron A c) & '[c,p.1] = '[b, p.2]] : simplex_spec (Simplex_optimal_point p).

Lemma simplexP: simplex_spec simplex.
Proof.
rewrite /simplex.
case: pointed_simplexP => [ d /infeasibility_pointed_to_general [Hd Hd'] | [bas i] /= [H H']| bas Hu]; constructor; try by done.
- split.
  + move: (feasible_basis_is_feasible bas); rewrite /is_feasible.
    by move/feasibility_pointed_to_general.
  + rewrite inE -mulmxAv2gen.
    rewrite /A' -[0]col_mx0 mul_col_mx col_mx_lev in H'.
    by move/andP: H' => [? _].
  + by rewrite -cost2gen /direction vdot_mulmx vdot_delta_mx trmx_inv.
- split.
  + move: (feasible_basis_is_feasible bas); rewrite /is_feasible.
    by move/feasibility_pointed_to_general.
  + by apply:ext_reduced_cost2gen_dual_feasible.
  + move: (eq_primal_dual_value bpointed cpointed bas).
    rewrite cost2gen => -> /=.
    by rewrite -[ext_reduced_cost_of_basis _ _]vsubmxK vdot_col_mx vdot0l addr0.
Qed.

Definition unbounded :=
  if simplex is (Simplex_unbounded _) then true else false.

Lemma unboundedP_cert :
  reflect (exists p, [/\ p.1 \in polyhedron A b, (feasible_dir A p.2) & '[c,p.2] < 0]) unbounded.
Proof.
rewrite /unbounded.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP H
                 | [x d] /= [Hx Hd Hd']
                 | [_ u] /= [_ /(intro_existsT (dual_feasibleP _ _)) Hu _]]; constructor.
- by move => [[x ?] /= [/(intro_existsT (feasibleP _ _))]].
- by exists (x, d); split.
- move => [[_ d] /= [_ Hd Hd']].
  by move/(intro_existsT (dual_infeasibleP A c))/negP: (conj Hd Hd').
Qed.

Lemma unboundedP : reflect (forall K, exists x, x \in polyhedron A b /\ '[c,x] < K) unbounded.
Proof.
rewrite /unbounded.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP H
                 | [x d] /= [Hx Hd Hd']
                 | [x u] /= [Hx Hu Hcsc]]; constructor.
- by move/(_ 0) => [x [/(intro_existsT (feasibleP _ _))]].
- by move => K ; apply: (unbounded_certificate K Hx Hd).
- move/(_ '[c,x]) => [y [Hy Hy']].
  move/eqP: Hcsc; rewrite -duality_gap_eq0_def; move/eqP => Hcsc.
  move/(_ _ Hy)/(conj Hy')/andP: (duality_gap_eq0_optimality Hx Hu Hcsc).
  by rewrite ltr_le_asym.
Qed.

Definition bounded :=
  if simplex is (Simplex_optimal_point _) then true else false.

Definition opt_value :=
  if simplex is (Simplex_optimal_point (x,_)) then
    '[c,x]
  else 0 (* not used *).

Lemma boundedP_cert :
  reflect (exists p, [/\ p.1 \in polyhedron A b, p.2 \in dual_polyhedron A c, '[c, p.1] = opt_value & '[b, p.2] = opt_value]) bounded.
Proof.
rewrite /bounded /opt_value.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP H
                 | [_ d] /= [_ Hd Hd']
                 | [x u] /= [Hx Hu Hcsc]]; constructor.
- by move => [[x ?] /= [/(intro_existsT (feasibleP _ _))]].
- move => [[_ d'] /= [_ /(intro_existsT (dual_feasibleP _ _)) H _]].
  by move/(intro_existsT (dual_infeasibleP A c))/negP: (conj Hd Hd').
- exists (x,u); split; try by done.
Qed.

Lemma boundedP :
  reflect ((exists x, x \in polyhedron A b /\ '[c,x] = opt_value) /\ (forall y, y \in polyhedron A b -> opt_value <= '[c,y])) bounded.
Proof. 
rewrite /bounded /opt_value.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP H
                 | [x d] /= [Hx Hd Hd']
                 | [x u] /= [Hx Hu Hcsc]]; constructor.
- by move => [[x [/(intro_existsT (feasibleP _ _))]]].
- move => [_ H].
  move: (unbounded_certificate 0 Hx Hd Hd') => [y [Hy Hy']].
  move/(conj Hy')/andP: (H _ Hy).
  by rewrite ltr_le_asym.
- split.
  + by exists x; split.
  + apply: (duality_gap_eq0_optimality Hx Hu).
    by apply/eqP; rewrite duality_gap_eq0_def; apply/eqP.
Qed.

Lemma bounded_is_not_unbounded :
  feasible A b -> bounded = ~~ unbounded.
Proof.
rewrite /bounded /unbounded.
by case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP | |].
Qed.

Lemma opt_value_is_optimal x :
  (x \in polyhedron A b) ->
  (forall y, y \in polyhedron A b -> '[c,x] <= '[c,y]) -> '[c,x] = opt_value.
Proof.
move => Hx Hopt; rewrite /opt_value.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP
                 | [_ d] /= [_ Hd Hd']
                 | [y u] /= [Hy Hu Hcsc]].
- by move/(intro_existsT (feasibleP _ _)): Hx.
- move: (unbounded_certificate '[c,x] Hx Hd Hd') => [y [Hy Hy']].
  move/(_ _ Hy): Hopt.
  by move/(ltr_le_trans Hy'); rewrite ltrr.
- move/eqP: Hcsc; rewrite -duality_gap_eq0_def.
  move/eqP/(duality_gap_eq0_optimality Hy Hu)/(_ _ Hx) => Hyx.
  move/(_ _  Hy): Hopt => Hxy.
  move/andP: (conj Hxy Hyx).
  by exact: ler_anti.
Qed.

Lemma bounded_is_dual_feasible :
  feasible A b -> bounded = (dual_feasible A c).
Proof.
rewrite /bounded.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP
                 | [_ d] /= [_ Hd Hd'] _
                 | [_ u] /= [_ /(intro_existsT (dual_feasibleP _ _)) -> _ ] ];
                   try by done.
- by move/(intro_existsT (dual_infeasibleP _ _))/negbTE: (conj Hd Hd').
Qed.

Lemma exists_feasible_basis :
  ([set: (feasible_basis A b)] != set0) = (feasible A b) && (pointed A).
Proof.
apply/set0Pn/andP => [[bas] _ | [Hfeas Hpointed]].
- split.
  + apply/feasibleP; exists (point_of_basis b bas); exact: feasible_basis_is_feasible.
  + move: (matrix_of_basis_in_unitmx bas).
    rewrite -row_free_unit -row_leq_rank rank_castmx /pointed => Hrk.
    move/mxrankS: (row_submx_submx A bas).
    exact: leq_trans.
- case: (phase2P (feasible_bas0_ext b Hpointed) (cext _ _)) => [[bas i] /= [Hd Hd']| bas Hbas].
  + move: (unbounded_cert_on_basis (Mext b Hpointed) Hd' Hd) => [x [Hx]].
    by move/(conj (cext_min_value Hx))/andP; rewrite ler_lt_asym.
  + pose x := point_of_basis (bext b Hpointed) bas.
    case: ('[cext _ _, x] =P (Mext b Hpointed)) => [Hopt | Hopt].
    * set bas' := extract_feasible_basis (extremality_ext (feasible_point_of_basis_is_extreme bas) Hopt).
      by exists bas'.
    * have: '[ cext b Hpointed, x] > Mext b Hpointed.
      - rewrite ltr_def.
        rewrite (cext_min_value (feasible_basis_is_feasible bas)).
        by move/eqP: Hopt ->.
      move: (eq_primal_dual_value (bext _ _) (cext _ _) bas) ->.
      move/dual_from_ext_obj => Hinfeas.
      suff /negP: (~~ feasible A b) by done.
      - apply/infeasibleP.
        set d := (dual_from_ext (ext_reduced_cost_of_basis (cext _ _) bas)).
        exists d; split; last by done.
        apply: dual_polyhedron_from_ext.
          by rewrite -ext_reduced_cost_dual_feasible.
Qed.

Hypothesis Hpointed : pointed A.

Definition bounded_pointed :=
  match pointed_simplex b Hpointed c with
  | Pointed_res_optimal_basis _ => true
  | _ => false 
  end.

Lemma bounded_pointed_equiv :
  bounded_pointed = bounded.
Proof.
rewrite /bounded_pointed.
case: pointed_simplexP =>
  [ d /(intro_existsT (infeasibleP _ _))/negP Hinfeas
  | [bas i] /= [Hd Hd']
  | bas Hu].
- symmetry; apply/(introF idP).
  move/boundedP.
  by move => [[x [/(intro_existsT (feasibleP _ _))]]].
- move/(intro_existsT (feasibleP _ _)): (feasible_basis_is_feasible bas) => Hfeas.
  suff: unbounded.
  + by move: (bounded_is_not_unbounded Hfeas) ->; move ->.
  + apply/unboundedP => K.
    exact: (unbounded_cert_on_basis K Hd' Hd).
- symmetry; apply/boundedP.
  move: (optimal_cert_on_basis Hu) => Hopt.
  suff <-: '[c, point_of_basis b bas] = opt_value.
  + split; last by done.
    * exists (point_of_basis b bas).
      by split; [exact: feasible_basis_is_feasible | done].
  + by apply: opt_value_is_optimal; [exact: feasible_basis_is_feasible | done].
Qed.

Lemma bounded_pointedP :
  reflect
    ((exists fbas: feasible_basis A b, '[c, point_of_basis b fbas] = opt_value)
     /\ (forall y, y \in polyhedron A b -> opt_value <= '[c,y]))
    bounded.
Proof.
rewrite -bounded_pointed_equiv /bounded_pointed.
case: pointed_simplexP =>
  [ d /(intro_existsT (infeasibleP _ _))/negP Hinfeas
  | [fbas i] /= [Hd Hd']
  | ]; constructor.
- move => [[fbas _] _].
  by move/(intro_existsT (feasibleP _ _)): (feasible_basis_is_feasible fbas).
- move => [_ Hopt].
  move: (unbounded_cert_on_basis opt_value Hd' Hd) => [x [Hx Hx']].
  by move/(ltr_le_trans Hx'): (Hopt _ Hx); rewrite ltrr.
- have Hval: '[ c, point_of_basis b bas] = opt_value.
  + apply: opt_value_is_optimal;
      [ exact: feasible_basis_is_feasible | exact: optimal_cert_on_basis].
  split; first by exists bas.
  + by rewrite -Hval; exact: optimal_cert_on_basis.
Qed.

End General_simplex.

Section BoundedPolyhedron.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Definition bounded_polyhedron := (~~ feasible A b) || ([forall i, bounded A b (delta_mx i 0)] && [forall i, bounded A b (-(delta_mx i 0))]).

Lemma bounded_polyhedronP_feasible : feasible A b -> reflect (forall c, bounded A b c) (bounded_polyhedron).
Proof.
move => Hfeas.
rewrite /bounded_polyhedron Hfeas /=.
apply: (iffP andP) => [[/forallP Hpos /forallP Hneg]| H]; last first.
- split; apply/forallP => i; exact: H.
- move => c.
  pose cpos := pos_part c.
  pose cneg := neg_part c.
  have Hc: c = \sum_i (cpos i 0) *: (delta_mx i 0) + \sum_i (cneg i 0) *: (-delta_mx i 0).
  + rewrite -[c]add_pos_neg_part.
    apply: congr2;
      rewrite -[LHS]mul1mx mulmx_sum_col;
      apply: eq_bigr => i _; do 1?[rewrite mxE scaleNr -scalerN];
      do 2?[apply: congr1]; apply: trmx_inj;
      by rewrite tr_col trmx1 trmx_delta row1.
  pose M := \sum_i (cpos i 0) * (opt_value A b (delta_mx i 0)) + \sum_i (cneg i 0) * (opt_value A b (-delta_mx i 0)).
  have Hbounded: forall x, x \in polyhedron A b -> '[c,x] >= M. 
  + move => x Hx.
    rewrite Hc vdotDl 2!vdot_sumDl.
    apply: ler_add; apply: ler_sum => i _; rewrite vdotZl; apply: ler_wpmul2l.
    * by move/forallP/(_ i): (pos_part_gev0 c); rewrite mxE.
    * move/(_ i)/boundedP: Hpos => [_ Hposi].
      exact: Hposi.
    * by move/forallP/(_ i): (neg_part_gev0 c); rewrite mxE.
    * move/(_ i)/boundedP: Hneg => [_ Hnegi].
      exact: Hnegi.
  rewrite bounded_is_not_unbounded //; apply/negP.
  move/unboundedP/(_ M) => [x [Hx Hx']].
  move/(_ _ Hx): Hbounded.
  by move/(ltr_le_trans Hx'); rewrite ltrr.
Qed.

Lemma feasible_bounded_polyhedron_is_pointed : feasible A b -> bounded_polyhedron -> pointed A.
Proof.
move => Hfeas.
move/(bounded_polyhedronP_feasible Hfeas) => Hbounded.
apply: contraT; move/pointedPn => [d [Hd Hd' _]].
move/(_ (-d)): Hbounded. 
apply: contraLR; rewrite (bounded_is_not_unbounded _ Hfeas) negbK.
move => _; apply/unboundedP_cert.
move/feasibleP: Hfeas => [x Hx].
exists (x,d); split; try by done.
- rewrite vdotNl /= oppr_lt0.
  by rewrite vnorm_gt0.
Qed.

End BoundedPolyhedron.
