(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum zmodp fingroup perm matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module Simplex.

Section Polyhedron.

Variable R : realFieldType.

Section Def.

Variable m n : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Implicit Types x : 'cV[R]_n.

Definition polyhedron := [pred x: 'cV_n | (A *m x) >=m b].

Definition active_ineq x :=
  [set i : 'I_m | (A *m x) i 0 == b i 0].

Definition feasible_dir := [pred d | (A *m d) >=m 0].

Lemma feasible_dirP d x :
  x \in polyhedron ->
  reflect (forall μ, μ >= 0 -> x + μ *: d \in polyhedron) (feasible_dir d). (* RK: lemma used in hpolyhedron *)
Proof.
move => x_in.
apply/(iffP idP) => [feasible_dir_d μ μ_ge0 | d_recession_dir].
- rewrite inE mulmxDr -scalemxAr -[b]addr0.
  apply/lev_add; first by done.
  have ->: 0 = μ *: (0 : 'cV[R]_m) by rewrite scaler0.
  by apply/lev_wpscalar.
- apply/contraT; rewrite negb_forall.
  move/existsP => [i A_d_i_neq].
  rewrite mxE in A_d_i_neq.
  set λ := ((A *m d) i 0 + b i 0 - (A *m x) i 0) * ((A *m d) i 0)^-1.
  have λ_ge_0: 0 <= λ.
    rewrite ler_ndivl_mulr; last by rewrite -ltNge in A_d_i_neq.
    rewrite mul0r ler_subl_addr.
    apply: ler_add; last exact: ((forallP x_in) i).
    apply: ltW.
    by rewrite -ltNge in A_d_i_neq.
  move: (forallP (d_recession_dir _  λ_ge_0) i) => b_i_ineq.
  rewrite mulmxDr -scalemxAr mxE [(λ *: (A *m d)) i 0]mxE -mulrA mulVf in b_i_ineq;
    last by apply: ltr0_neq0; rewrite -ltNge in A_d_i_neq.
  rewrite mulr1 [(A *m x) i 0 + _]addrC -3!ler_subl_addr opprK -addrA -opprB addNr in b_i_ineq.
  by rewrite b_i_ineq in A_d_i_neq.
Qed.

Definition pointed := (mxrank A >= n)%N.

Lemma pointedPn :
  reflect (exists d, [/\ d != 0, feasible_dir d & feasible_dir (-d)]) (~~pointed).
Proof.
have ->: ~~pointed = (kermx A^T != 0)%MS.
by rewrite /pointed -mxrank_tr row_leq_rank -kermx_eq0.
apply/(iffP rowV0Pn) => [[v] /sub_kermxP Hv Hv'| [d [Hd Hd' Hd'']]].
- move/(congr1 trmx): Hv; rewrite trmx0 trmx_mul trmxK => Hv.
  exists v^T; split; try by rewrite inE ?mulmxN Hv ?oppr0 lev_refl.
  + by rewrite -trmx0 inj_eq; last exact: trmx_inj.
- exists d^T; last by rewrite -trmx0 inj_eq; last exact: trmx_inj.
  + apply/sub_kermxP; rewrite -trmx_mul -trmx0.
    apply: congr1; apply: lev_antisym; apply/andP.
    by rewrite !inE mulmxN oppv_ge0 in Hd' Hd''.
Qed.

Hypothesis is_pointed: pointed.

Definition build_non_feasible_direction d :=
  if feasible_dir d then -d else d.

Lemma build_non_feasible_directionP d :
  d != 0 -> ~~ (feasible_dir (build_non_feasible_direction d)).
Proof.
move => d_neq0.
rewrite /build_non_feasible_direction.
case: ifP; last exact: negbT.
move => d_feas_dir.
move: is_pointed; apply: contraL => md_feas_dir.
by apply/pointedPn; exists d; split.
Qed.

End Def.

Section WeakDuality.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Variable c : 'cV[R]_n.

Implicit Types x : 'cV[R]_n.
Implicit Types u : 'cV[R]_m.

Definition dualA := col_mx (col_mx A^T (-A^T)) (1%:M).
Definition dualb := col_mx (col_mx c (-c)) (0:'cV_m).

Definition dual_polyhedron :=
  [pred u | A^T *m u == c & (u >=m 0)].

Lemma dual_polyhedronE u :
  (u \in dual_polyhedron) = (u \in polyhedron dualA dualb).
Proof.
rewrite 2!inE /dualA /dualb 2!mul_col_mx 2!col_mx_lev mul1mx mulNmx lev_opp2.
apply: (congr1 (andb^~ _)); apply/idP/idP.
- by move/eqP ->; rewrite lev_refl.
- by move/lev_antisym ->; apply: eq_refl.
Qed.

Definition dual_feasible_dir := [pred d | (A^T *m d == 0) && (d >=m 0)].

Lemma dual_feasible_directionE d :
  (dual_feasible_dir d) = (feasible_dir dualA d).
Proof.
rewrite 2!inE 2!mul_col_mx mul1mx.
rewrite -[0 in RHS]vsubmxK -[usubmx _]vsubmxK.
rewrite 2!col_mx_lev !linear0.
apply: (congr1 (andb^~ _)).
by rewrite mulNmx oppv_ge0 -eqv_le eq_sym.
Qed.

Lemma mul_tr_dualA (v : 'cV_(n+n+m)) :
  let: y := dsubmx (usubmx v) - usubmx (usubmx v) in
  let: z := dsubmx v in
    (dualA)^T *m v = z - A *m y.
Proof.
rewrite /dualA 2!tr_col_mx linearN /= !trmxK trmx1.
rewrite -{1}[v]vsubmxK mul_row_col mul1mx.
rewrite -{1}[usubmx v]vsubmxK mul_row_col.
rewrite addrC; apply/(congr1 (fun z => _ + z)).
by rewrite mulmxDr mulNmx mulmxN opprB.
Qed.

Lemma vdot_dualb (v : 'cV_(n+n+m)) :
  let: y := dsubmx (usubmx v) - usubmx (usubmx v) in
    '[dualb, v] = -'[c,y].
Proof.
rewrite /dualb -{1}[v]vsubmxK -{1}[usubmx v]vsubmxK.
rewrite 2!vdot_col_mx vdot0l addr0 vdotNl.
by rewrite -[in RHS]vdotNr opprB vdotDr vdotNr.
Qed.

Definition duality_gap x u := '[c,x] - '[b,u].

Fact duality_gap_def x u :
  (A^T *m u) = c -> duality_gap x u = '[u, A *m x - b].
Proof.
by rewrite /duality_gap; move <-; rewrite -vdot_mulmx [X in _ - X]vdotC vdotBr.
Qed.

Fact duality_gap_ge0_def x u :
  (duality_gap x u >= 0) = ('[c,x] >= '[b,u]).
Proof.
by rewrite /duality_gap subr_ge0.
Qed.

Fact duality_gap_eq0_def x u :
  (duality_gap x u == 0) = ('[c,x] == '[b,u]).
Proof.
by rewrite /duality_gap subr_eq0.
Qed.

Lemma weak_duality x u :
  x \in polyhedron A b -> u \in dual_polyhedron -> duality_gap x u >= 0.
Proof.
move => Hx; rewrite inE => /andP [/eqP/(duality_gap_def x) -> Hu'].
rewrite vdotBr subr_ge0.
by apply: vdot_lev; last by rewrite inE in Hx.
Qed.

Lemma dual_feasible_bounded u :
  u \in dual_polyhedron -> forall x, x \in polyhedron A b -> '[c,x] >= '[b,u].
Proof.
move => H x Hx; rewrite -duality_gap_ge0_def.
by apply: weak_duality.
Qed.

Definition compl_slack_cond (x : 'cV[R]_n) (u : 'cV[R]_m) :=
  [forall i, (u i 0 == 0) || (i \in active_ineq A b x)].

Lemma compl_slack_condP x u :
  reflect (forall i, u i 0 = 0 \/ ((A *m x) i 0 = b i 0)) (compl_slack_cond x u).
Proof.
apply: (iffP forallP) => [H i | H i].
- move/(_ i)/orP: H; case => [/eqP | ]; first by left.
  + by rewrite inE => /eqP; right.
- move/(_ i): H; rewrite inE; case => [-> | ->] ; by rewrite eq_refl ?orbT.
Qed.

Lemma duality_gap_eq0_compl_slack_cond x u :
  x \in polyhedron A b -> u \in dual_polyhedron ->
    (duality_gap x u = 0) -> compl_slack_cond x u.
Proof.
rewrite !inE.
move => Hx /andP [/eqP Hu Hu'] /eqP; rewrite (duality_gap_def x) // /vdot psumr_eq0.
- move/allP => H; apply/forallP => i.
  move/(_ i (mem_index_enum _))/implyP/(_ isT): H.
  by rewrite mulf_eq0 inE mxE [in X in _ + X]mxE subr_eq0.
- move => i _; apply: mulr_ge0.
  + by move/forallP/(_ i): Hu'; rewrite mxE.
  + by rewrite mxE [in X in _ + X]mxE subr_ge0; move/forallP: Hx.
Qed.

Lemma compl_slack_cond_duality_gap_eq0 x u :
  (A^T *m u) = c -> (compl_slack_cond x u) -> (duality_gap x u = 0).
Proof.
move => Hu /compl_slack_condP H; apply/eqP; rewrite (duality_gap_def _ Hu) /vdot.
apply/eqP; apply: big1 => i _.
move/(_ i): H.
case => [-> |]; first by rewrite mul0r.
- rewrite [in X in _ * X]mxE [in X in _ + X]mxE.
  by move ->; rewrite addrN mulr0.
Qed.

Lemma compl_slack_cond_duality_gap_equiv x u :
  x \in polyhedron A b -> u \in dual_polyhedron ->
  (duality_gap x u == 0) = (compl_slack_cond x u).
Proof.
move => Hx Hu.
move: (Hu); rewrite inE; move/andP => [/eqP Hu' _].
apply/idP/idP.
- by move/eqP; apply: duality_gap_eq0_compl_slack_cond.
- by move/(compl_slack_cond_duality_gap_eq0 Hu')/eqP.
Qed.

Lemma duality_gap_eq0_optimality x u :
  x \in polyhedron A b -> u \in dual_polyhedron -> duality_gap x u = 0 ->
  forall y, y \in polyhedron A b -> '[c,x] <= '[c,y].
Proof.
move => Hx Hu /eqP.
rewrite (duality_gap_eq0_def x u) => /eqP Hcx.
move => y Hy; rewrite Hcx -duality_gap_ge0_def.
by apply: weak_duality.
Qed.

Lemma unbounded_certificate x0 d K:
  x0 \in polyhedron A b -> feasible_dir A d -> '[c,d] < 0 ->
         exists x, x \in polyhedron A b /\ '[c,x] < K.
Proof.
move => /forallP Hx0 /forallP Hd Hcd.
set M := Order.max (0%R) ('[c,d]^-1 * (K - 1 - '[c, x0])).
set x := x0 + M *: d.
exists x; split.
+ apply/forallP => j.
  rewrite mulmxDr -scalemxAr mxE [X in _ + X]mxE.
  rewrite -[X in X <= _]addr0.
  apply: ler_add; first by apply: (Hx0 _).
  - apply: mulr_ge0; last by move/(_ j): Hd; rewrite mxE.
    by rewrite le_maxr lexx.
+ rewrite vdotDr vdotZr -ltr_subr_addl.
  rewrite -mulrC -ltr_ndivr_mull //.
  rewrite lt_maxr; apply/orP; right.
  rewrite -(ltr_nmul2l Hcd) 2!mulrA mulfV; last by apply: ltr0_neq0.
  by rewrite 2!mul1r ltr_add2r gtr_addl ltrN10.
Qed.

End WeakDuality.

End Polyhedron.

Section LexPolyhedron.
(* On unifying lex-polyhedra and polyhedra:
 * The idea would be to deal with polyhedra
 * { x \in 'cV[M]_n | A * x >= b }
 * where M is a left R-module, R is a ring, both are totally ordered
 * in a compatible way (making M an ordered left R-module)
 * BUT this requires major changes in MathComp:
   - show that 'M[M]_(p,q) is a left-module
   - extend matrix multiplication to A * B, where A: 'M[R]_(p,q) and
     B: 'M[M]_(q,r)
   - define ordered left modules
   - etc
 * The benefit in terms of maintainability is not so clear (unless these changes are done
   in a seperate library...)
 * Indeed, lex-polyhedra, or more generally, abstract polyhedra over modules, are only
 * used in this file *)

Variable R : realFieldType.

Variable m n : nat.

Section Def.

Variable p : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'M[R]_(m,p).

Definition lex_polyhedron :=
  [pred x : 'M[R]_(n,p) | [forall i, (row i (A *m x)) >=lex (row i b)]].

Definition active_lex_ineq (x : 'M[R]_(n,p)) :=
  [set i : 'I_m | (row i (A *m x)) == (row i b)].

Lemma lex_polyhedron_inP x :
  reflect (forall i, (row i (A *m x)) >=lex (row i b)) (x \in lex_polyhedron).
Proof.
exact: forallP.
Qed.

Lemma lex_polyhedron_gtP x i: x \in lex_polyhedron ->
  (row i (A *m x)) >lex (row i b) = (i \notin active_lex_ineq x).
Proof. by rewrite /ltrlex !inE=> /forallP/(_ i) ->; rewrite andbT eq_sym. Qed.

End Def.

Section UsualVsLexPolyhedron.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Lemma polyhedron_equiv_lex_polyhedron :
  polyhedron A b =i lex_polyhedron A b.
Proof.
move => x.
rewrite 2!inE.
apply: eq_forallb => i.
apply/idP/idP => [ineq |].
- apply: leqlex_seq_lev.
  apply/forall_inP => j _.
  rewrite 2!mxE.
  suff ->: j = 0 by done.
  + apply/ord_inj.
    by move: (ltn_ord j); rewrite ltnS leqn0 => /eqP.
- by move/lex_ord0; rewrite 2!mxE.
Qed.

Lemma active_ineq_equal_active_lex_ineq (x : 'cV[R]_n) :
  active_ineq A b x = (active_lex_ineq A b x).
Proof.
apply/setP => i.
rewrite 2!inE; apply/eqP/eqP => [ eq |].
- rewrite [row i (_ *m _)]mx11_scalar.
  by rewrite mxE eq [row i _]mx11_scalar mxE.
- by move/rowP/(_ 0); rewrite 2![(row _ _) _ _]mxE.
Qed.

End UsualVsLexPolyhedron.

End LexPolyhedron.

Section LexSimplex.

Variable R : realFieldType.
Variable m n : nat.
Variable A : 'M[R]_(m,n).

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

Definition prebasis_enum : seq prebasis := pmap insub (enum [set bas : {set 'I_m} | #|bas| == n]).

Fact prebasis_enum_uniq : uniq prebasis_enum.
Proof.
by apply: pmap_sub_uniq; apply: enum_uniq.
Qed.

Fact mem_prebasis_enum bas : bas \in prebasis_enum.
Proof.
rewrite mem_pmap_sub mem_enum in_set.
by move/eqP: (prebasis_card bas).
Qed.

Definition prebasis_finMixin :=
  Eval hnf in UniqFinMixin prebasis_enum_uniq mem_prebasis_enum.
Canonical prebasis_finType := Eval hnf in FinType prebasis prebasis_finMixin.
Canonical prebasis_subFinType := Eval hnf in [subFinType of prebasis].

Lemma prebasis_card_D1 (bas : prebasis) (i : 'I_m) :
  i \in bas -> (#|bas :\ i| = n-1)%N.
Proof.
move => i_in_bas.
move: (cardsD1 i bas) => basD1.
rewrite i_in_bas (prebasis_card bas) /= add1n in basD1.
by rewrite basD1 subn1.
Qed.

End Prebasis.

Section Basis.

Definition is_basis (bas : prebasis) := row_free (row_submx A bas).

Definition is_basisP_rank (bas : prebasis) :
  reflect (mxrank (row_submx A bas) = n) (is_basis bas).
Proof.
rewrite -[RHS](prebasis_card bas).
exact: eqP.
Qed.

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

Lemma basis_is_basis (bas : basis) : is_basis bas.
Proof.
by apply: (valP bas).
Qed.

Definition basis_enum : seq basis := pmap insub [seq bas <- prebasis_enum | is_basis bas].

Fact basis_enum_uniq : uniq basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: prebasis_enum_uniq.
Qed.

Fact mem_basis_enum bas : bas \in basis_enum.
Proof.
rewrite mem_pmap_sub mem_filter.
apply/andP; split; last by apply: mem_prebasis_enum.
by apply: basis_is_basis.
Qed.

Definition basis_finMixin :=
  Eval hnf in UniqFinMixin basis_enum_uniq mem_basis_enum.
Canonical basis_finType := Eval hnf in FinType basis basis_finMixin.
Canonical basis_subFinType := Eval hnf in [subFinType of basis].

Lemma mxrank_basis (bas : basis) : (mxrank (row_submx A bas) = n).
Proof.
apply/is_basisP_rank; exact: basis_is_basis.
Qed.

Lemma basis_trmx_row_free (bas : basis) : row_free (row_submx A bas)^T.
Proof.
rewrite /row_free mxrank_tr.
apply/eqP; exact: mxrank_basis.
Qed.

Lemma basis_pointedness (bas : basis) : pointed A.
Proof.
rewrite /pointed -{1}(mxrank_basis bas).
apply: mxrankS; exact: row_submx_submx.
Qed.

End Basis.

Section PointOfBasis.

Variable p : nat.
Variable b : 'M[R]_(m,p).

Definition point_of_basis (bas : basis) :=
  (qinvmx (prebasis_card bas) (row_submx A bas)) *m (row_submx b bas).

Lemma row_submx_point_of_basis (bas : basis) :
  (row_submx A bas) *m (point_of_basis bas) = row_submx b bas.
Proof.
by rewrite qmulKVmx; last exact: basis_is_basis.
Qed.

Lemma is_point_of_basis (bas : basis) x :
  (row_submx A bas) *m x = row_submx b bas -> x = point_of_basis bas.
Proof.
move/(congr1 (mulmx (qinvmx (prebasis_card bas) (row_submx A bas)))).
by rewrite qmulKmx; last exact: basis_is_basis.
Qed.

Lemma is_point_of_basis_active (bas : basis) x : (* TO BE IMPROVED ?
                                                  * handle the case p = 1 *)
  (forall i, i \in bas -> (A *m x) i =1 b i) -> x = point_of_basis bas.
Proof.
move/row_submx_matrixP; rewrite row_submx_mul => H.
exact: is_point_of_basis.
Qed.

(*RK: see if we keep this form of the previous lemma*)
Lemma is_point_of_basis_pert_active (bas : basis) x :
  (forall i, i \in bas -> row i (A *m x) = row i b) -> x = point_of_basis bas.
Proof.
move/row_submx_row_matrixP; rewrite row_submx_mul => H.
exact: is_point_of_basis.
Qed.

End PointOfBasis.

Section FeasibleBasis.

Variable p : nat.
Variable b : 'M[R]_(m,p).

Definition is_feasible (bas : basis) :=
  (point_of_basis b bas) \in (lex_polyhedron A b).

Lemma row_submx_is_feasible (bas : basis) :
  (forall x, (row_submx A bas) *m x = (row_submx b bas) -> x \in lex_polyhedron A b) ->
    is_feasible bas.
Proof.
apply.
by rewrite qmulKVmx; last exact: basis_is_basis bas.
Qed.

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

Fact feasible_basis_enum_uniq : uniq feasible_basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: basis_enum_uniq.
Qed.

Fact mem_feasible_basis_enum bas : bas \in feasible_basis_enum.
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
   (bas \subset (active_lex_ineq A b (point_of_basis b bas))).
Proof.
apply/subsetP => i Hi.
rewrite inE; apply/eqP.
move: (row_submx_point_of_basis b bas); rewrite -row_submx_mul.
by move/row_submx_row_matrixP/(_ _ Hi).
Qed.

Lemma basis_subset_active_ineq_eq (bas : basis) x :
  bas \subset (active_lex_ineq A b x) -> x = point_of_basis b bas.
Proof.
move => H.
apply: is_point_of_basis.
rewrite -row_submx_mul.
apply/row_submx_row_matrixP => i Hi.
move/subsetP/(_ _ Hi): H.
by rewrite inE; move/eqP.
Qed.

End FeasibleBasis.

Section PivotingLikeOperations.

Variable p : nat.
Variable b : 'M[R]_(m,p).

Section BuildBoundaryPoint.
(* AIM: from a feasible point x and an infeasible direction d,
 * follow d from x up to the boundary *)

Variable d : 'cV[R]_n.
Variable x : 'M[R]_(n,p).
Hypothesis d_infeas_dir : ~~ (feasible_dir A d).

Definition cand_idx := [pred j | (A *m d) j 0 < 0].

Lemma cand_idxP : (#|cand_idx| > 0)%N.
Proof.
apply/card_gt0P.
move/existsP : d_infeas_dir => [k].
rewrite mxE -ltNge => Ak_d_neg.
by exists k.
Qed.

Definition gap j :=
  ((A *m d) j 0)^-1 *: ((row j b) - (row j (A *m x))).

Let j0 := enum_val (Ordinal cand_idxP).

Let gap_seq := map gap (enum cand_idx).

Definition argmin_gap :=
  let min_gap := lex_min_seq gap_seq in
  match [pick j in cand_idx | min_gap == gap j] with
  | Some j => j
  | None => j0
  end.

Let min_gap := gap argmin_gap.

Definition point_along_dir := x + d *m min_gap.

Section Feasibility.

Hypothesis x_feas : x \in lex_polyhedron A b.

Fact gap_ge0 j : j \in cand_idx -> (gap j) >=lex 0.
Proof.
move => j_is_cand.
apply: lex_scalar_le0.
- rewrite invr_le0.
  exact: ltW.
- rewrite lex_subr_le0.
  by move/forallP/(_ j): x_feas.
Qed.

Fact gap_seqP : (gap_seq != [::]).
Proof.
rewrite -size_eq0 size_map -cardE.
apply: lt0n_neq0; exact: cand_idxP.
Qed.

Fact argmin_gapP :
  (argmin_gap \in cand_idx) *
    (forall j, j \in cand_idx -> (gap argmin_gap) <=lex (gap j)).
Proof.
rewrite /argmin_gap.
case: pickP => [j /andP [-> /eqP <-] /=|].
- split; first by done.
  move => k k_is_cand.
  apply: lex_min_seq_ler.
  by apply: map_f; rewrite mem_enum.
- move/hasP: (lex_min_seq_eq gap_seqP) => [? /mapP [k k_is_cand ->]] /= eq_min_gap.
  rewrite mem_enum in k_is_cand.
  by move/(_ k); rewrite k_is_cand eq_min_gap /=.
Qed.

Fact min_gap_ge0 : min_gap >=lex 0.
Proof.
apply: gap_ge0.
move: argmin_gapP.
exact: fst.
Qed.

Fact point_along_dir_feas :
  point_along_dir \in lex_polyhedron A b.
Proof.
apply/forallP => j.
rewrite /point_along_dir mulmxDr linearD /=.
rewrite mulmxA [X in _ + X]row_mul mulmx_row_cV_rV.
case: (boolP (cand_idx j)) => [j_is_cand | j_is_not_cand].
- have Hj: ((A *m d) j 0)^-1 < 0
    by rewrite inE -invr_lt0 in j_is_cand.
  rewrite lex_subr_addr (lex_negscalar _ _ Hj) scalerA mulVf; last by apply: ltr0_neq0; by rewrite -invr_lt0.
  rewrite scale1r.
  exact: (argmin_gapP.2 j j_is_cand).
- rewrite -[(row j b)]addr0.
  apply: lex_add; first by move/forallP: x_feas.
  apply: lex0_nnscalar; by [exact: min_gap_ge0 | rewrite leNgt].
Qed.

End Feasibility.

Section ActiveIneq.

Variable I : {set 'I_m}.

Hypothesis d_in_kerAI : (row_submx A I) *m d = 0.

Fact argmin_gap_not_in_I : argmin_gap \notin I.
Proof.
move: argmin_gapP => [argmin_is_cand _].
move: argmin_is_cand; apply: contraL => argmin_in_I.
rewrite inE.
move: d_in_kerAI; rewrite -row_submx_mul.
move/row_submx_col0P/(_ _ argmin_in_I) => ->.
by rewrite ltxx.
Qed.

Fact argmin_gap_rank :
  (\rank (row_submx A (argmin_gap |: I)) = (\rank (row_submx A I)).+1)%N.
Proof.
rewrite row_submx_spanU1; last exact: argmin_gap_not_in_I.
set j := argmin_gap.
set Aj := row j A.
set AI := row_submx A I.
have Ajd_neq0 : (Aj *m d) != 0.
  move: argmin_gapP => [j_is_cand _].
  move: j_is_cand; rewrite inE.
  apply: contraTneq.
  rewrite -row_mul; move/col0P/(_ 0); rewrite mxE => ->.
  by rewrite ltxx.
have Aj_inter_AI : (Aj :&: AI <= (0:'M_n))%MS.
  apply/rV_subP => ?; rewrite submx0 sub_capmx.
  move/andP => [/sub_rVP [a ->] /submxP [z]].
  move/(congr1 (mulmx^~ d)).
  rewrite -mulmxA -scalemxAl.
  move: d_in_kerAI ->; rewrite mulmx0.
  move/eqP; rewrite scalemx_eq0.
  move/negbTE: Ajd_neq0 ->; rewrite orbF.
  by move/eqP ->; rewrite scale0r.
move/leqifP: (mxrank_adds_leqif Aj AI).
rewrite ifT //; move/eqP ->;rewrite rank_rV.
suff ->: (Aj != 0) by done.
- apply/eqP.
  move/(congr1 (mulmx^~ d)); rewrite mul0mx.
  by move/eqP: Ajd_neq0.
Qed.

Hypothesis I_subset_active_ineq_x : I \subset (active_lex_ineq A b x).

Fact point_along_dir_active_ineq :
  argmin_gap |: I \subset active_lex_ineq A b (point_along_dir).
Proof.
apply/subsetP => i.
move/setU1P => [-> | i_in_I];
  rewrite inE /point_along_dir;
  rewrite mulmxDr linearD /=;
          rewrite mulmxA [X in _ + X]row_mul mulmx_row_cV_rV.
- move: (argmin_gapP.1) => Hargmin_gap.
  rewrite inE in Hargmin_gap.
  rewrite eq_sym addrC -subr_eq /min_gap /gap scalerA mulfV; last by apply: ltr0_neq0.
  by rewrite scale1r.
- suff ->: (A *m d) i 0 = 0.
    rewrite scale0r addr0.
    by move/subsetP/(_ _ i_in_I): I_subset_active_ineq_x; rewrite inE.
  move: d_in_kerAI; rewrite -row_submx_mul.
  move/row_submx_row_matrix0P/(_ _ i_in_I)/colP/(_ 0).
  by rewrite mxE [RHS]mxE.
Qed.

Fact point_along_dir_active_ineq_rank :
  let J := active_lex_ineq A b (point_along_dir) in
    (\rank (row_submx A J) > (\rank (row_submx A I)))%N.
Proof.
set J := active_lex_ineq _ _ _.
rewrite -argmin_gap_rank.
apply: mxrankS; apply: row_submx_subset_submx.
exact: point_along_dir_active_ineq.
Qed.

End ActiveIneq.

End BuildBoundaryPoint.

Section BuildFeasibleBasis. (* TODO: could be merge to Phase I?
                             * Except if this operation is interesting
                             * independently of Phase I (is it?)       *)

Hypothesis Hpointed : pointed A.

Definition build_basic_point_iter x :=
  let I := active_lex_ineq A b x in
  let d := pick_in_ker (row_submx A I) in
  if @idPn (d == 0) is ReflectT d_neq0 then
    let infeas_dir := (build_non_feasible_directionP Hpointed d_neq0) in
    (point_along_dir x infeas_dir)
  else x.

Fact build_basic_point_iter_feasible x :
  x \in lex_polyhedron A b -> build_basic_point_iter x \in lex_polyhedron A b.
Proof.
move => x_feas.
rewrite /build_basic_point_iter; case: {-}_/idPn => [d_neq0 | _]; last by done.
exact: point_along_dir_feas.
Qed.

Fact build_basic_point_iter_rank x :
  let I := active_lex_ineq A b x in
  let y := build_basic_point_iter x in
  let J := active_lex_ineq A b y in
    (\rank (row_submx A I) < n)%N -> (\rank (row_submx A I) < \rank (row_submx A J))%N.
Proof.
move => /= rk_AI.
rewrite /build_basic_point_iter.
case: {-}_/idPn => [d_neq0 | ]; last first.
- move/negP; rewrite negbK.
  by move/negbTE: (pick_in_ker_neq0 rk_AI) => ->.
- set I := active_lex_ineq A b x.
  set infeas_dir := build_non_feasible_directionP _ _.
  set y := point_along_dir _ _.
  set J := active_lex_ineq A b y.
  set d := build_non_feasible_direction A (pick_in_ker (row_submx A I)).
  have Ad_eq0 : (row_submx A I) *m d = 0.
    rewrite /d /build_non_feasible_direction.
    by case: ifP => [_ | _]; rewrite ?mulmxN;
       move: (pick_in_kerP (row_submx A I)) => ->; rewrite ?oppr0.
  apply: point_along_dir_active_ineq_rank; by [apply/eqP | done].
Qed.

Definition height x := (n - \rank (row_submx A (active_lex_ineq A b x)))%N.

Function build_basic_point x {measure height x} :=
  if (height x == 0)%N then x
  else build_basic_point (build_basic_point_iter x).
Proof.
move => x /negbT.
rewrite -lt0n subn_gt0 => rk_lt_n.
apply/ssrnat.leP.
move/build_basic_point_iter_rank: (rk_lt_n); exact: ltn_sub2l.
Qed.

Lemma build_basic_point_is_feas :
  forall x, x \in lex_polyhedron A b -> build_basic_point x \in lex_polyhedron A b.
Proof.
pose P := fun x y => x \in lex_polyhedron A b -> y \in lex_polyhedron A b.
apply: (build_basic_point_ind (P := P)).
- by move => x _; rewrite /=.
- move => x ? <- _ => ind_hyp.
  by move/build_basic_point_iter_feasible/ind_hyp.
Qed.

Lemma build_basic_point_rank :
  forall x, (\rank (row_submx A (active_lex_ineq A b (build_basic_point x))) >= n)%N.
Proof.
pose P := fun (x : 'M[R]_(n,p)) y => (\rank (row_submx A (active_lex_ineq A b y)) >= n)%N.
apply: (build_basic_point_ind (P := P)); last by done.
- by move => x; rewrite subn_eq0.
Qed.

Variable x : 'M[R]_(n,p).
Hypothesis x_is_feas : x \in lex_polyhedron A b.

Let y := build_basic_point x.

Let build_basis_set := build_row_base A (active_lex_ineq A b y) n.

Fact build_basis_setP : (#| build_basis_set | == n)%N.
Proof.
by move/build_basic_point_rank/row_base_correctness: x => [_ /eqP].
Qed.

Let build_basis_prebasis := Prebasis build_basis_setP.

Fact build_basis_prebasisP : is_basis build_basis_prebasis.
Proof.
apply/is_basisP_rank.
by move/build_basic_point_rank/row_base_correctness: x => [_ _].
Qed.

Definition build_basis_basis := Basis build_basis_prebasisP.

Fact build_basis_basisP : is_feasible b build_basis_basis.
Proof.
rewrite /is_feasible.
suff <-: (y = point_of_basis b build_basis_basis)
  by apply: build_basic_point_is_feas.
apply: basis_subset_active_ineq_eq.
by move/build_basic_point_rank/row_base_correctness: x => [].
Qed.

Definition build_feasible_basis := FeasibleBasis build_basis_basisP.

End BuildFeasibleBasis.

Section Pivoting.

Section IsBasis.

Variable bas : basis.
Variable i : 'I_#|bas|.

Fact n_is_pos : (n > 0)%N.
Proof.
rewrite -(prebasis_card bas); apply/card_gt0P.
exists (enum_val i); exact: enum_valP.
Qed.

Definition direction  :=
  let: ei := (delta_mx i 0):'cV_#|bas| in
    (qinvmx (prebasis_card bas) (row_submx A bas)) *m ei.

Local Notation d := direction.

Fact direction_neq0 : d != 0.
Proof.
apply/eqP.
move/(congr1 (mulmx (row_submx A bas))).
rewrite qmulKVmx; last exact: basis_is_basis.
rewrite mulmx0.
move/colP/(_ i); rewrite 2!mxE 2!eq_refl /=.
by move/eqP; rewrite pnatr_eq0.
Qed.

Fact mulmx_direction_entries_in_bas (j : 'I_m) :
  j \in bas -> (A *m d) j 0 = (j == enum_val i)%:R.
Proof.
move => Hj.
suff ->: (A *m d) j 0 = ((row_submx A bas) *m d) (enum_rank_in Hj j) 0.
- rewrite qmulKVmx; last exact: basis_is_basis.
  rewrite mxE andbT; do 2![apply: congr1].
  apply/eqP/eqP.
  + exact: (canRL_in (enum_rankK_in Hj)).
  + exact: (canLR (enum_valK_in Hj)).
- rewrite -row_submx_mul row_submx_mxE enum_rankK_in //.
Qed.

Fact mulmx_direction :
  (row_submx A (bas :\ enum_val i)) *m d = 0.
Proof.
rewrite -row_submx_mul.
apply/row_submx_col0P => j.
rewrite in_setD1 => /andP [Hj Hj'].
rewrite mulmx_direction_entries_in_bas //.
by move/negbTE: Hj ->.
Qed.

Fact row_direction : (row (enum_val i) A) *m d = 1%:M.
Proof. 
apply/matrixP=> x y; rewrite -row_mul (ord1_eq0 y) (ord1_eq0 x) mxE.
by rewrite mulmx_direction_entries_in_bas ?mxE ?eqxx ?enum_valP.
Qed.

Hypothesis d_infeas_dir : ~~ (feasible_dir A d).

Let x := point_of_basis b bas.
Let j := argmin_gap x d_infeas_dir.

Let lex_rule_set := j |: (bas :\ (enum_val i)).

Fact lex_rule_card : #|lex_rule_set| == n.
Proof.
rewrite cardsU1.
move: (argmin_gap_not_in_I x d_infeas_dir mulmx_direction) => -> /=.
rewrite prebasis_card_D1; last exact: enum_valP.
rewrite add1n subn1.
apply/eqP; apply: (prednK n_is_pos).
Qed.

Let lex_rule_pbasis := Prebasis lex_rule_card.

Fact lex_rule_is_basis : is_basis lex_rule_pbasis.
Proof.
apply/is_basisP_rank.
move: (argmin_gap_rank x d_infeas_dir mulmx_direction).
set i' := enum_val i.
set AIi := row_submx A (bas :\ i').
suff ->: \rank AIi = n.-1.
- by rewrite (prednK n_is_pos).
- apply/eqP.
  rewrite -subn1 eqn_leq.
  apply/andP; split.
  + rewrite -(prebasis_card_D1 (enum_valP i)).
    exact: (rank_leq_row AIi).
  + rewrite leq_subLR.
    move: (rank_leq_row (row i' A)); rewrite -(leq_add2r (\rank AIi)).
    apply: leq_trans.
    move: (mxrank_basis bas).
    rewrite (row_submx_spanD1 A (enum_valP i)) => {1}<-.
    exact: mxrank_adds_leqif.
Qed.

Definition lex_rule_basis := Basis lex_rule_is_basis.

Fact lex_rule_point_of_basis :
  point_of_basis b lex_rule_basis = point_along_dir x d_infeas_dir.
Proof.
symmetry; apply: basis_subset_active_ineq_eq.
apply: point_along_dir_active_ineq; first exact: mulmx_direction.
suff: bas \subset active_lex_ineq A b x.
- apply: subset_trans.
  exact: subD1set.
- exact: basis_subset_of_active_ineq.
Qed.

End IsBasis.

Section IsFeasible.

Variable bas : feasible_basis b.
Variable i : 'I_#|bas|.

Hypothesis d_infeas_dir : ~~ (feasible_dir A (direction i)).

Fact lex_rule_is_feasible :
  is_feasible b (lex_rule_basis d_infeas_dir).
Proof.
rewrite /is_feasible lex_rule_point_of_basis.
apply: point_along_dir_feas.
exact: feasible_basis_is_feasible.
Qed.

Definition lex_rule_fbasis := FeasibleBasis lex_rule_is_feasible.

End IsFeasible.

End Pivoting.

End PivotingLikeOperations.

Section Cost.

Variable c : 'cV[R]_n.
Variable bas : basis.

Implicit Types x : 'cV[R]_n.

(* Reduced cost of basis: u s.t.
   u = < A^{-1}_I, c >, where I is a basis *)
Definition reduced_cost_of_basis :=
  (qinvmx (prebasis_card bas) (row_submx A bas))^T *m c.

Definition reduced_cost_of_basis_def :
  (row_submx A bas)^T *m reduced_cost_of_basis = c.
Proof.
rewrite /reduced_cost_of_basis trmx_qinv; last exact: basis_is_basis.
by rewrite qmulKVmx; last exact: basis_trmx_row_free.
Qed.

Definition ext_reduced_cost_of_basis :=
  \col_i (if (@idP (i \in bas)) is ReflectT Hi then
            reduced_cost_of_basis (enum_rank_in Hi i) 0
          else 0).

Fact ext_reduced_cost_of_basis_in_bas i (Hi : (i \in bas)) :
  let: j := enum_rank_in Hi i in
    ext_reduced_cost_of_basis i 0 = reduced_cost_of_basis j 0.
Proof.
rewrite /ext_reduced_cost_of_basis mxE.
case: {-}_ /idP => [Hi' |]; last by done.
suff ->: enum_rank_in Hi i = enum_rank_in Hi' i by done.
- apply: enum_val_inj; by do 2![rewrite enum_rankK_in //].
Qed.

Fact ext_reduced_cost_of_basis_notin_bas i :
  (i \notin bas) -> ext_reduced_cost_of_basis i 0 = 0.
Proof.
move/negP => H; rewrite /ext_reduced_cost_of_basis mxE.
by case: {-}_ /idP => [ ? | _].
Qed.

Fact non_neg_reduced_cost_equiv :
  (ext_reduced_cost_of_basis >=m 0) = (reduced_cost_of_basis >=m 0).
Proof.
apply/idP/idP => [/gev0P H | /gev0P H].
- apply/gev0P => i.
  move: (ext_reduced_cost_of_basis_in_bas (enum_valP i)).
  rewrite enum_valK_in => <-.
  exact: H.
- apply/gev0P => i; case: (boolP (i \in bas)) => [Hi | Hi].
  + rewrite (ext_reduced_cost_of_basis_in_bas Hi).
    exact: H.
  + by rewrite (ext_reduced_cost_of_basis_notin_bas Hi).
Qed.

Fact ext_reduced_cost_of_basis_def :
  (* should be rewritten using an appropriate lemma to be written in row_submx.v,
   * stating that M = row_perm _ (col_mx (row_submx M bas) (row_submx M ~:bas))   *)
  A^T *m ext_reduced_cost_of_basis = c.
Proof.
apply/colP => i; rewrite !mxE.
rewrite (bigID (fun j => j \in bas)) /= [X in _ + X]big1;
  last by move => j /ext_reduced_cost_of_basis_notin_bas ->; rewrite mulr0.
rewrite addr0.
rewrite (reindex (@enum_val _ (mem bas))) /=;
  last by apply: (enum_val_bij_in (enum_valP (cast_ord (esym (prebasis_card bas)) i))).
rewrite (eq_bigl predT) /=; last by move => k /=; apply: (enum_valP k).
move/colP/(_ i): reduced_cost_of_basis_def; rewrite !mxE => <-.
apply: eq_bigr => j _.
rewrite (ext_reduced_cost_of_basis_in_bas (enum_valP j)) enum_valK_in.
by rewrite 2![_^T _ _]mxE row_submx_mxE.
Qed.

Fact ext_reduced_cost_dual_feasible :
  reduced_cost_of_basis >=m 0 = (ext_reduced_cost_of_basis \in dual_polyhedron A c).
Proof.
rewrite inE.
move/eqP: ext_reduced_cost_of_basis_def ->; rewrite /=.
by symmetry; apply: non_neg_reduced_cost_equiv.
Qed.

Lemma direction_improvement (i : 'I_#|bas|) :
  reduced_cost_of_basis i 0 < 0 -> '[c, direction i] < 0.
Proof.
by rewrite vdot_mulmx vdotr_delta_mx.
Qed.

Section Certificates.

Variable (b : 'cV[R]_m).

Lemma eq_primal_dual_value :
  '[c, point_of_basis b bas] = '[b, ext_reduced_cost_of_basis].
Proof.
apply/eqP; rewrite -duality_gap_eq0_def; apply/eqP.
apply: (compl_slack_cond_duality_gap_eq0 ext_reduced_cost_of_basis_def).
apply/compl_slack_condP => i.
case: (boolP (i \in bas)) => [Hi | Hi].
- right.
  move/subsetP/(_ i Hi): (basis_subset_of_active_ineq b bas).
  by rewrite inE; move/eqP/row_eq/(_ 0).
- by move: (ext_reduced_cost_of_basis_notin_bas Hi) => ->; left.
Qed.

Lemma optimal_cert_on_basis :
  let: x := point_of_basis b bas in
    x \in polyhedron A b -> reduced_cost_of_basis >=m 0 ->
      forall y, y \in polyhedron A b -> '[c,x] <= '[c,y].
Proof.
move => x_feas.
rewrite ext_reduced_cost_dual_feasible => Hu.
apply: (duality_gap_eq0_optimality x_feas Hu).
move: Hu; rewrite inE; move/andP => [/eqP Hu _].
by apply/eqP; rewrite subr_eq0 eq_primal_dual_value.
Qed.

Lemma unbounded_cert_on_basis (i : 'I_#|bas|) M :
  let: d := direction i in
  let: z := point_of_basis b bas in
    feasible_dir A d -> reduced_cost_of_basis i 0 < 0 -> z \in polyhedron A b ->
      exists x, (x \in polyhedron A b) /\ ('[c,x] < M).
Proof.
move => Hd Hui Hfeas.
exact: (unbounded_certificate M Hfeas Hd (direction_improvement Hui)).
Qed.

End Certificates.

End Cost.

Section ObjOfBasis. (* RK *)

Variable b : 'cV[R]_m.

Definition obj_of_basis (bas : feasible_basis b) :=
  let: e := (const_mx 1) : 'cV_#|bas| in
    (row_submx A bas)^T *m e.

Fact obj_of_basis_reduced_cost (bas : feasible_basis b) :
  let: c := obj_of_basis bas in
    (reduced_cost_of_basis c bas) >=m 0.
Proof.
rewrite /reduced_cost_of_basis /obj_of_basis.
rewrite trmx_qinv; last exact: basis_is_basis.
rewrite qmulKmx; last exact: basis_trmx_row_free.
apply/gev0P => i; by rewrite mxE ler01.
Qed.

Fact obj_of_basisP (bas: feasible_basis b) :
  let: c := obj_of_basis bas in
  let: x := point_of_basis b bas in
    forall y, y \in polyhedron A b -> '[c,y] <= '[c,x] -> y = x.
Proof.
set c := obj_of_basis bas.
set x := point_of_basis b bas.
move => y Hy Hc.
pose z := (row_submx A bas *m y) - row_submx b bas.
suff Hz: z = 0.
  apply: is_point_of_basis.
  exact: subr0_eq.
  apply: (vdot_lev_eq0 (x := const_mx 1)).
  - by apply/forallP => i; rewrite mxE ltr01.
  - rewrite subv_ge0 -row_submx_mul.
    exact: row_submx_lev.
  - rewrite vdotBr -[row_submx b bas]row_submx_point_of_basis 2!vdot_mulmx.
    apply/eqP; rewrite subr_eq0 eq_le.
    apply/andP; split; first by done.
    apply: (optimal_cert_on_basis (bas := bas)); last by done.
    + rewrite polyhedron_equiv_lex_polyhedron.
      exact: (feasible_basis_is_feasible bas).
    + exact: obj_of_basis_reduced_cost.
Qed.

End ObjOfBasis.

Variable b : 'cV[R]_m.

Definition b_pert := row_mx b (-(1%:M)).

Section LexFeasibleBasis.

Lemma rel_points_of_basis bas :
  point_of_basis b bas = col 0 (point_of_basis b_pert bas).
Proof.
rewrite col_mul row_submx_row_mx.
apply: (congr1 (mulmx _)).
by apply/colP => i; rewrite ![in RHS]mxE split1 unlift_none.
Qed.

Definition lex_feasible_basis := (feasible_basis b_pert). (* TODO: why not Inductive ? *)

Lemma lex_feasible_basis_is_feasible (bas : lex_feasible_basis) :
  point_of_basis b bas \in polyhedron A b.
Proof.
rewrite /is_feasible (rel_points_of_basis bas).
apply/forallP => i; rewrite -col_mul mxE.
move/forallP/(_ i)/lex_ord0: (feasible_basis_is_feasible bas).
by rewrite mxE [X in _ <= X]mxE mxE split1 unlift_none /=.
Qed.

Section BuildLexFeasibleBasis.

Hypothesis A_pointed : pointed A.
Variable x : 'cV[R]_n.
Hypothesis x_feas : x \in polyhedron A b.

Definition x_pert : 'M[R]_(n,1+m) := row_mx x (const_mx 0).

Fact x_pert_feasible :
  x_pert \in lex_polyhedron A b_pert.
Proof.
apply/lex_polyhedron_inP => i.
rewrite row_mul mul_mx_row mulmx0 row_row_mx linearN /= row1.
apply: lex_lev => j; rewrite 2!mxE.
case: (splitP j) => [j' _| j' _]; last first.
- rewrite !mxE eq_refl /=.
  by rewrite -mulNrn mulrn_wle0 // lerN10.
- rewrite [j']ord1_eq0 -row_mul 2!mxE.
  by move/forallP: x_feas.
Qed.

Definition build_lex_feasible_basis : lex_feasible_basis :=
  build_feasible_basis A_pointed x_pert_feasible.

End BuildLexFeasibleBasis.

Section NonDegenerate.

Variable bas : lex_feasible_basis.
Variable i : 'I_#|bas|.

Let d := direction i.
Let x := point_of_basis b_pert bas.

Hypothesis d_infeas_dir : ~~ (feasible_dir A d).

Let j := argmin_gap b_pert x d_infeas_dir.
Let lex_min_gap := (gap b_pert d x j).

Fact lex_ent_var_not_in_basis : j \notin bas.
Proof.
apply: contraT; rewrite negbK.
move => j_in_bas.
set k := enum_rank_in j_in_bas j.
have Hk: j = enum_val (A := mem bas) k
  by rewrite (enum_rankK_in j_in_bas).
have j_is_not_cand: (row_submx A bas *m d) k 0 >= 0.
  rewrite mulmxA qmulmxV; last exact: basis_is_basis; rewrite mul1mx mxE.
  by apply: ler0n.
rewrite -row_submx_mul row_submx_mxE -{}Hk in j_is_not_cand.
move: (argmin_gapP b_pert x d_infeas_dir) => [j_is_cand _].
move/andP: (conj j_is_not_cand j_is_cand).
by rewrite le_lt_asym.
Qed.

Fact col_b_pert (I : prebasis) k :
  (col (rshift 1 k) (row_submx b_pert I) != 0) = (k \in I).
Proof.
case: (boolP (k \in I)) => [k_in_I | k_not_in_I].
- pose k' := (enum_rank_in k_in_I k).
  apply/(contraTneq _ isT) => /=.
  move/colP/(_ k').
  rewrite mxE [RHS]mxE /= row_submx_mxE enum_rankK_in //.
  rewrite row_mxEr.
  rewrite !mxE eq_refl /= mulr1n.
  move/eqP; rewrite oppr_eq0.
  by move/lt0r_neq0/negP: (@ltr01 R).
- apply: negbTE; rewrite negbK.
  apply/eqP/colP => h.
  rewrite mxE /= row_submx_mxE row_mxEr !mxE.
  move/memPn/(_ _ (enum_valP h))/negbTE: k_not_in_I => -> /=.
  by rewrite mulr0n oppr0.
Qed.

Fact col_point_of_basis_pert (bas' : basis) k :
  (col (rshift 1 k) (point_of_basis b_pert bas') != 0) = (k \in bas').
Proof.
rewrite -col_b_pert col_mul.
set z:=  col (rshift 1 k) (row_submx b_pert bas').
case: (boolP (z == 0)) => [/eqP z_eq_0 | z_neq_0].
- by rewrite z_eq_0 mulmx0 eq_refl.
- move: z_neq_0; apply: contraNeq; rewrite eqb_id.
  move/negPn/eqP/(congr1 (mulmx (row_submx A bas')))/eqP.
  by rewrite qmulKVmx; last exact: basis_is_basis; rewrite mulmx0.
Qed.

Fact eq_pert_point_imp_eq_bas (bas' bas'' : basis) :
  (point_of_basis b_pert bas' = point_of_basis b_pert bas'') -> bas' == bas''.
Proof.
move => eq_point.
suff: bas' \subset bas''.
- move/subset_leqif_cards/geq_leqif.
  by rewrite 2!prebasis_card leqnn.
- apply/subsetP => k.
  by rewrite -2!col_point_of_basis_pert eq_point.
Qed.

Fact lex_min_gap_non_null : lex_min_gap != 0.
Proof.
move: (lex_feasible_basis_is_feasible bas) => Hfeas.
move: (argmin_gapP b_pert x d_infeas_dir).1 => Hj.
rewrite inE in Hj.
rewrite scalemx_eq0 negb_or; apply/andP; split.
- apply: invr_neq0; exact: ltr0_neq0.
- apply/eqP => /subr0_eq-/esym H.
  suff /eq_pert_point_imp_eq_bas/eqP Hbas:
    (point_of_basis b_pert bas) = (point_of_basis b_pert (lex_rule_fbasis d_infeas_dir)).
  + by move: lex_ent_var_not_in_basis; rewrite Hbas setU11 /=.
  + apply: is_point_of_basis_pert_active => k.
    rewrite in_setU1; move/orP; case.
    * by move/eqP ->.
    * rewrite in_setD1 => /andP [_ Hk].
      move: (row_submx_point_of_basis b_pert bas).
      by rewrite -row_submx_mul; move/row_submx_row_matrixP/(_ _ Hk).
Qed.

Fact lex_min_gap_lex_pos : lex_min_gap >lex 0.
Proof.
apply/andP; split.
- rewrite eq_sym; exact: lex_min_gap_non_null.
- exact: (min_gap_ge0 d_infeas_dir (feasible_basis_is_feasible bas)).
Qed.

End NonDegenerate.

Section LexicographicRuleCost.

Variable c : 'cV[R]_n.
Variable bas : lex_feasible_basis.
Variable i : 'I_#|bas|.

Hypothesis infeas_dir : ~~ (feasible_dir A (direction i)).

Lemma lex_rule_dec :
  let bas' := lex_rule_fbasis infeas_dir  in
  let u := reduced_cost_of_basis c bas in
  u i 0 < 0 ->
  (c^T *m point_of_basis b_pert bas') <lex (c^T *m point_of_basis b_pert bas).
Proof.
move => bas' u u_i_neg.
rewrite lex_rule_point_of_basis.
rewrite mulmxDr lex_gtr_addl mulmxA.
rewrite [c^T *m _]mx11_scalar -vdot_def mxE /= mulr1n mul_scalar_mx vdotC.
rewrite (lex_nmulr_rlt0 _ (direction_improvement u_i_neg)).
exact: lex_min_gap_lex_pos.
Qed.

End LexicographicRuleCost.

End LexFeasibleBasis.

Section Phase2.

Inductive phase2_final_result :=
| Phase2_res_unbounded (bas: lex_feasible_basis) of 'I_#|bas|
| Phase2_res_optimal_basis of lex_feasible_basis.

Inductive phase2_intermediate_result :=
| Phase2_final of phase2_final_result
| Phase2_next_basis of lex_feasible_basis.

Variable c : 'cV[R]_n.
Implicit Types bas : lex_feasible_basis.

Definition basic_step bas :=
  let u := reduced_cost_of_basis c bas in
  if [pick i | u i 0 < 0] is Some i then
    let d := direction i in
    if (@idPn (feasible_dir A d)) is ReflectT infeas_dir then
      Phase2_next_basis (lex_rule_fbasis infeas_dir)
    else Phase2_final (Phase2_res_unbounded i)
  else
    Phase2_final (Phase2_res_optimal_basis bas).

Definition basis_height bas :=
  #|[ set bas' : lex_feasible_basis | (c^T *m (point_of_basis b_pert bas')) <lex (c^T *m (point_of_basis b_pert bas)) ]|.

Lemma basis_height_desc bas bas' : basic_step bas = Phase2_next_basis bas' ->
  (basis_height bas' < basis_height bas)%coq_nat.
Proof.
move => Hbas.
apply/ssrnat.leP.
pose u := reduced_cost_of_basis c bas.
move: Hbas; rewrite /basic_step.
case: pickP => [i |]; last by done.
- rewrite -/u; move => Hui.
  case: {-}_ /idPn => [infeas_dir [] Hbas'|]; last by done.
  + move: (lex_rule_dec infeas_dir Hui) => Hc; rewrite Hbas' in Hc.
    apply: proper_card.
    set Sbas' := [set _ | _]; set Sbas := [set _ | _].
    rewrite properEneq; apply/andP; split.
    * apply: contraT; rewrite negbK; move/eqP => Hcontra.
      have H1: bas' \notin (Sbas').
        rewrite inE negb_and; apply/orP; left.
        by rewrite negbK eq_refl.
      have H2: bas' \in (Sbas) by rewrite inE.
      move/setP/(_ bas'): Hcontra.
      by move/negbTE: H1 ->; rewrite H2.
    * apply/subsetP; move => bas''.
      rewrite !inE; move/andP => [_ Hbas''].
      by apply:(lex_le_ltr_trans Hbas'' Hc).
Qed.

Function phase2 bas {measure basis_height bas} :=
  match basic_step bas with
  | Phase2_final final_res => final_res
  | Phase2_next_basis bas' => phase2 bas'
  end.
Proof. exact: basis_height_desc. Qed.

Variant phase2_spec : phase2_final_result -> Type :=
| Phase2_unbounded (bas: lex_feasible_basis) (i: 'I_#|bas|) of (reduced_cost_of_basis c bas) i 0 < 0 /\ feasible_dir A (direction i) : phase2_spec (Phase2_res_unbounded i)
| Phase2_optimal_basis (bas: lex_feasible_basis) of (reduced_cost_of_basis c bas) >=m 0 : phase2_spec (Phase2_res_optimal_basis bas).

Lemma phase2P bas0 : phase2_spec (phase2 bas0).
Proof.
pose P bas' res := (phase2_spec res).
suff /(_ bas0): (forall bas, P bas (phase2 bas)) by done.
apply: phase2_rect; last by done.
- move => bas1 res; rewrite /basic_step.
  case: pickP => [i Hi| Hu [] <-].
  + case: {-}_ /idPn => [? |/negP Hd [] /= <-]; try by done.
    * by rewrite negbK in Hd; constructor.
  + constructor; apply/forallP => i; rewrite mxE.
    move/(_ i)/negbT: Hu.
    by rewrite leNgt.
Qed.

Function phase2_exec bas {measure basis_height bas} :=
  match basic_step bas with
  | Phase2_final final_res => match final_res with
    | Phase2_res_unbounded bas' _ => [::]
    | Phase2_res_optimal_basis bas' => [::]
    end
  | Phase2_next_basis bas' => bas' :: (phase2_exec bas')
  end.
Proof. exact: basis_height_desc. Qed.

Lemma phase2_exec_adj bas0 : path (fun x y : lex_feasible_basis => #|x :&: y| == n.-1) bas0 (phase2_exec bas0).
Proof.
pose P bas exec : Type := (path (fun x y : lex_feasible_basis => #|x :&: y| == n.-1) bas exec).
suff: forall bas, P bas (phase2_exec bas) by move/(_ bas0).
apply: phase2_exec_rect=> // bas bas' basic_step_bas.
rewrite /P /= => ->; rewrite andbT.
move: basic_step_bas; rewrite /basic_step.
case: pickP=> // i; case: {-}_ /idPn=> // unfeas_dir_i red_cost_i.
case=> <-; rewrite /lex_rule_fbasis /=.
set j:= argmin_gap _ _ _.
rewrite setIUr setIDA setDIl setIid.
suff: j \notin bas.
- rewrite -disjoints1 disjoint_sym=> /disjoint_setI0 ->; rewrite set0U -subn1.
  exact/eqP/prebasis_card_D1/enum_valP.
exact: lex_ent_var_not_in_basis.
Qed.

Lemma phase2_exec_lexopt bas0 :
  path (fun x y : lex_feasible_basis => (c^T *m point_of_basis b_pert y) <lex (c^T *m point_of_basis b_pert x)) bas0 (phase2_exec bas0).
Proof.
pose P bas exec : Type :=
  (path (fun x y : lex_feasible_basis => (c^T *m point_of_basis b_pert y) <lex (c^T *m point_of_basis b_pert x)) bas exec).
suff: forall bas, P bas (phase2_exec bas) by move/(_ bas0).
apply: phase2_exec_rect=> // bas bas' basic_step_bas.
rewrite /P /= => ->; rewrite andbT.
move: basic_step_bas; rewrite /basic_step.
case: pickP=> // i red_cost_i; case: {-}_ /idPn=> // unfeas_dir_i.
case=> <-; exact: lex_rule_dec.
Qed.

Lemma phase2_exec_opt bas0:
path (fun x y : lex_feasible_basis => '[c, point_of_basis b y] <= '[c, point_of_basis b x]) bas0 (phase2_exec bas0).
Proof.
move: (phase2_exec_lexopt bas0); move: bas0 (phase2_exec bas0)=> a0 l.
elim: l a0=> //= a1 l' IH a0 /andP [+ /IH ->]; rewrite andbT.
move/lex_ltrW/lex_ord0.
by rewrite -!matrix_vdot !rel_points_of_basis row_id trmxK.
Qed.


Definition phase2_res bas0 := last bas0 (phase2_exec bas0).

Lemma basic_step_final bas0 : forall fin_res,
  let bas1 := match fin_res with
    |@Phase2_res_unbounded bas _ => bas |Phase2_res_optimal_basis bas => bas end in
  basic_step bas0 = Phase2_final fin_res -> bas0 = bas1.
Proof.
rewrite /basic_step; case.
- move=> bas ?.
  by case: pickP=> // ?; case: {-}_/idPn=> // _ _; case.
- move=> bas.
  case: pickP=> [?? | ?]; last by case.
  by case: {-}_/idPn.
Qed.

Lemma phase2_resP bas0 : forall fin_res, 
  let bas1 := match fin_res with
    |@Phase2_res_unbounded bas _ => bas |Phase2_res_optimal_basis bas => bas end in
  phase2 bas0 = fin_res -> phase2_res bas0 = bas1.
Proof.
move=> fin_res bas1; rewrite /phase2_res.
pose P bas s := phase2 bas = fin_res -> last bas s = bas1.
suff/(_ bas0): forall bas, P bas (phase2_exec bas) by [].
apply: phase2_exec_rect; rewrite /P /= /bas1.
- move=> bas f_res basic_eq _ _ _.
  rewrite phase2_equation basic_eq=> <-.
  by move: (basic_step_final basic_eq).
- move=> bas f_res basic_eq _ _.
  rewrite phase2_equation basic_eq=> <-.
  by move: (basic_step_final basic_eq).
- move=> bas bas' basic_eq IH.
  by rewrite phase2_equation basic_eq.
Qed.


End Phase2.

End LexSimplex.

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
apply/is_basisP_rank.
by rewrite row_submx_col_mx_rshift row_submxT !rank_castmx mxrank1.
Qed.

Definition dual_bas0 := Basis dual_pb0_is_basis.

Fact point_of_dual_bas0_is_feasible :
  point_of_basis 0 dual_bas0 \in polyhedron (dualA A) 0.
Proof.
set u0 := point_of_basis _ _.
suff ->: u0 = 0.
  rewrite inE mulmx0; exact: lev_refl.
by rewrite /u0 /point_of_basis row_submx0 mulmx0.
Qed.

(* WORKAROUND: instead of proving that dual_bas0 is (magically) lex-feasible,
 * we build a lex-feasible basis from the corresponding feasible basic point
 * This yields a much shorter proof *)
Definition dual_lex_feasible_bas0 :=
  let Apointed := basis_pointedness dual_bas0 in
  let u0_feas := point_of_dual_bas0_is_feasible in
  build_lex_feasible_basis Apointed u0_feas.

Inductive emptiness_proc_res :=
| FeasiblePoint of 'cV[R]_n
| InconsistencyCert of 'cV[R]_m.

Definition emptiness_proc :=
  match phase2 (-b) dual_lex_feasible_bas0 with
  | Phase2_res_optimal_basis bas =>
    let v := ext_reduced_cost_of_basis (- b) bas in
    FeasiblePoint (dsubmx (usubmx v) - usubmx (usubmx v))
  | Phase2_res_unbounded bas i => InconsistencyCert (direction i)
  end.

Definition feasible := if emptiness_proc is FeasiblePoint _ then true else false.

CoInductive emptiness_proc_spec : emptiness_proc_res -> bool -> Type :=
| Feasible x of (x \in polyhedron A b)  : emptiness_proc_spec (FeasiblePoint x) true
| Empty d of (dual_feasible_dir A d /\ '[b,d] > 0) : emptiness_proc_spec (InconsistencyCert d) false.

Lemma emptiness_procP :
  emptiness_proc_spec emptiness_proc feasible.
Proof.
rewrite /feasible /emptiness_proc.
case: phase2P => [bas i [/direction_improvement Hd Hd']| bas Hbas]; constructor.
- rewrite -dual_feasible_directionE in Hd'.
  split; first by done.
  by rewrite vdotNl oppr_lt0 in Hd.
- pose v := ext_reduced_cost_of_basis (- b) bas.
  move: Hbas; rewrite ext_reduced_cost_dual_feasible -/v inE => /andP [/eqP].
  rewrite mul_tr_dualA gev0_vsubmx.
  set x := (dsubmx (usubmx v) - usubmx (usubmx v)).
  by move/(canRL (subrK _)) ->; rewrite addrC subv_ge0 => /andP [_].
Qed.

Fact feasible_and_infeasible_is_false x d :
  x \in polyhedron A b -> (dual_feasible_dir A d /\ '[b,d] > 0) -> False.
Proof.
move => x_feas [/andP [/eqP Ad d_lt0] b_d_ltr0].
move/(vdot_lev d_lt0): x_feas.
rewrite vdot_mulmx Ad vdot0l vdotC.
by move/(lt_le_trans b_d_ltr0); rewrite ltxx.
Qed.

Lemma feasibleP :
  reflect (exists x, x \in polyhedron A b) feasible.
Proof.
case: emptiness_procP => [x x_feas | d d_inconsistent]; constructor.
- by exists x.
- move => [x x_feas].
  exact: (feasible_and_infeasible_is_false x_feas d_inconsistent).
Qed.

Lemma infeasibleP :
  reflect (exists d, dual_feasible_dir A d /\ '[b,d] > 0) (~~ feasible).
Proof.
case: emptiness_procP => [x x_feas | d d_inconsistent]; constructor.
- move => [d].
  exact: (feasible_and_infeasible_is_false x_feas).
- by exists d.
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

Section PointedSimplex.
(* a complete simplex method (phase 1 + 2) which applies to LP
 * such that the feasible set is pointed *)

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis Hpointed : pointed A.

Variable c : 'cV[R]_n.

Inductive pointed_final_result :=
| Pointed_res_infeasible of 'cV[R]_m
| Pointed_res_unbounded (bas: lex_feasible_basis A b) of 'I_#|bas|
| Pointed_res_optimal_basis of (lex_feasible_basis A b).

Definition pointed_simplex :=
  match emptiness_proc A b with
  | FeasiblePoint x =>
    if @idP (x \in polyhedron A b) is ReflectT x_feas then
      let bas0 := build_lex_feasible_basis Hpointed x_feas in
      match phase2 c bas0 with
      | Phase2_res_unbounded _ i => Pointed_res_unbounded i
      | Phase2_res_optimal_basis bas'' => Pointed_res_optimal_basis bas''
      end
    else
      Pointed_res_infeasible 0
  | InconsistencyCert d =>
    Pointed_res_infeasible d
  end.

CoInductive pointed_simplex_spec : pointed_final_result -> Type :=
| Pointed_infeasible (d : 'cV[R]_m) of dual_feasible_dir A d /\ '[b,d] > 0 : pointed_simplex_spec (Pointed_res_infeasible d)
| Pointed_unbounded (bas: lex_feasible_basis A b) (i: 'I_#|bas|) of (reduced_cost_of_basis c bas) i 0 < 0 /\ feasible_dir A (direction i) : pointed_simplex_spec (Pointed_res_unbounded i)
| Pointed_optimal_point (bas : lex_feasible_basis A b) of (reduced_cost_of_basis c bas) >=m 0 : pointed_simplex_spec (Pointed_res_optimal_basis bas).

Lemma pointed_simplexP : pointed_simplex_spec pointed_simplex.
Proof.
rewrite /pointed_simplex.
case: emptiness_procP => [x x_feas | d d_inconsistent]; last first.
- by constructor.
- case: {-}_/idP => [?|]; last by done.
  case: phase2P => [[bas' d] /=|]; by constructor.
Qed.

End PointedSimplex.

Section GeneralSimplex.

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

Definition mulmxAv2gen (z : 'cV[R]_(n+n)) :
  (row_mx A (-A)) *m z = A *m (v2gen z).
Proof.
by rewrite -{1}[z]vsubmxK mul_row_col mulNmx -mulmxN -mulmxDr.
Qed.

Definition cost2gen (z : 'cV[R]_(n+n)) :
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
  rewrite /Apointed -{1}[u](vsubmxK) tr_col_mx mul_row_col tr_row_mx mul_col_mx linearN /= mulNmx.
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
  | Pointed_res_unbounded bas i =>
    let d := direction i in
    Simplex_unbounded (v2gen (point_of_basis bpointed bas), v2gen d)
  | Pointed_res_optimal_basis bas =>
    Simplex_optimal_point (v2gen (point_of_basis bpointed bas), ext_reduced_cost2gen bas)
  end.

Definition unbounded :=
  if simplex is (Simplex_unbounded _) then true else false.

Definition bounded :=
  if simplex is (Simplex_optimal_point _) then true else false.

Definition opt_point :=
  if simplex is (Simplex_optimal_point (x, _)) then
    x
  else 0 (* not used *).

Definition dual_opt_point :=
  if simplex is (Simplex_optimal_point (_, u)) then
    u
  else 0 (* not used *).

Definition opt_value := '[c, opt_point].
(*  if simplex is (Simplex_optimal_point (x, _)) then
    '[c, x]
  else 0. *)

CoInductive simplex_spec : simplex_final_result (*-> bool -> bool -> bool*) -> Type :=
| Infeasible d of (dual_feasible_dir A d /\ '[b, d] > 0): simplex_spec (Simplex_infeasible d)(*false false false*)
| Unbounded p of [/\ (p.1 \in polyhedron A b), (feasible_dir A p.2) & ('[c,p.2] < 0)] : simplex_spec (Simplex_unbounded p) (*true true false*)
| Optimal_point p of [/\ (p.1 \in polyhedron A b), (p.2 \in dual_polyhedron A c) & '[c,p.1] = '[b, p.2]] : simplex_spec (Simplex_optimal_point p) (*true false true*).

Lemma simplexP: simplex_spec simplex (*(feasible A b) unbounded bounded*).
Proof.
rewrite /simplex.
case: pointed_simplexP => [ d /infeasibility_pointed_to_general [Hd Hd'] | bas i [H H']| bas Hu]; constructor; rewrite //=.
- split.
  + apply: feasibility_pointed_to_general.
    exact: lex_feasible_basis_is_feasible.
  + rewrite -mulmxAv2gen.
    rewrite inE /Apointed mul_col_mx col_mx_gev0 in H'.
    by move/andP: H' => [? _].
  + by rewrite -cost2gen /direction vdot_mulmx vdotr_delta_mx.
- split.
  + apply: feasibility_pointed_to_general.
    exact: lex_feasible_basis_is_feasible.
  + by apply: ext_reduced_cost2gen_dual_feasible.
  + move: (eq_primal_dual_value cpointed bas bpointed).
    rewrite cost2gen => -> /=.
    by rewrite -[ext_reduced_cost_of_basis _ _]vsubmxK vdot_col_mx vdot0l addr0.
Qed.

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

Lemma unboundedP :
  reflect (forall K, exists x, x \in polyhedron A b /\ '[c,x] < K) unbounded.
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
  by rewrite lt_le_asym.
Qed.

Lemma opt_point_is_feasible :
  bounded -> opt_point \in polyhedron A b.
Proof.
rewrite /opt_point /bounded.
case: simplexP => //.
by move => [x d] /= [? _ _].
Qed.

(* A certificate of boundedness in terms of duality *)
Lemma boundedP_cert :
  ([&& opt_point \in polyhedron A b,
    dual_opt_point \in dual_polyhedron A c &
    '[c, opt_point] == '[b, dual_opt_point]]) = bounded.
Proof.
rewrite /opt_point /dual_opt_point /bounded //=.
case: simplexP.
- move => d /(intro_existsT (infeasibleP _ _))/feasibleP H.
  apply Bool.andb_false_iff. constructor.
  apply /idP => Q. destruct H. by exists 0.
- move => //= [_ p] //= [_ _ Q]. apply /and3P. move => [_ P _].
  move: P. rewrite /dual_polyhedron !inE => /andP [/eqP P _].
  move: P. rewrite mulmx0 => Qn. move: Q. by rewrite -Qn vdot0l ltxx.
- move => [p1 p2] //= [Q1 Q2 Q3]. apply /and3P. by rewrite Q1 Q2 Q3.
Qed.

Lemma boundedP :
  reflect ((exists x, x \in polyhedron A b /\ '[c,x] = opt_value) /\ (forall y, y \in polyhedron A b -> opt_value <= '[c,y])) bounded.
Proof.
rewrite /bounded /opt_value /opt_point.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP H
                 | [x d] /= [Hx Hd Hd']
                 | [x u] /= [Hx Hu Hcsc]]; constructor.
- by move => [[x [/(intro_existsT (feasibleP _ _))]]].
- move => [_ H].
  move: (unbounded_certificate 0 Hx Hd Hd') => [y [Hy Hy']].
  move/(conj Hy')/andP: (H _ Hy).
  by rewrite vdot0r lt_le_asym.
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

Lemma unbounded_is_not_bounded :
  feasible A b -> unbounded = ~~ bounded.
Proof.
rewrite /bounded /unbounded.
by case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP | |].
Qed.

Lemma infeasible_or_boundedP :
  reflect (exists K, (forall x, x \in polyhedron A b -> '[c,x] >= K)) (~~ feasible A b || bounded).
Proof.
case: (boolP (feasible A b)) => /= [Hfeas | /negP Hinfeas]; last first.
- constructor; exists 0; move => x.
  by move/(intro_existsT (feasibleP _ _)).
- apply: (iffP idP) => [/boundedP [ _ H ]| [K H]].
  + by exists opt_value.
  + rewrite bounded_is_not_unbounded //.
    apply/negP; move/unboundedP/(_ K) => [x [Hx Hlt]].
    by move/(_ _ Hx): H; move/(lt_le_trans Hlt); rewrite ltxx.
Qed.

Lemma boundedP_lower_bound : (feasible A b) ->
  reflect (exists K, (forall x, x \in polyhedron A b -> '[c,x] >= K)) bounded.
Proof.
move => Hfeas.
apply: (iffP idP).
+ by move => /boundedP [_ H]; exists opt_value.
+ move => [K H]. rewrite bounded_is_not_unbounded //.
  apply /negP. move/unboundedP/(_ K) => [x [Hx Hlt]].
  move/(_ _ Hx): H. by rewrite lt_geF.
Qed.

Lemma opt_value_is_optimal x :
  (x \in polyhedron A b) -> (forall y, y \in polyhedron A b ->
    '[c,x] <= '[c,y]) -> '[c,x] = opt_value.
Proof.
move => Hx Hopt; rewrite /opt_value /opt_point.
case: simplexP => [ d /(intro_existsT (infeasibleP _ _))/negP
                 | [_ d] /= [_ Hd Hd']
                 | [y u] /= [Hy Hu Hcsc]].
- by move/(intro_existsT (feasibleP _ _)): Hx.
- move: (unbounded_certificate '[c,x] Hx Hd Hd') => [y [Hy Hy']].
  move/(_ _ Hy): Hopt.
  by move/(lt_le_trans Hy'); rewrite ltxx.
- move/eqP: Hcsc; rewrite -duality_gap_eq0_def.
  move/eqP/(duality_gap_eq0_optimality Hy Hu)/(_ _ Hx) => Hyx.
  move/(_ _  Hy): Hopt => Hxy.
  move/andP: (conj Hxy Hyx).
  by exact: le_anti.
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

(* RK: I needed this result in the slightly different form below
Lemma exists_feasible_basis :
  ([set: (feasible_basis A b)] != set0) = (feasible A b) && (pointed A).
Proof.
apply/set0Pn/andP => [[bas] _ | [/feasibleP [x x_feas] Hpointed]].
- split.
  + apply/feasibleP; exists (point_of_basis b bas).
    rewrite (polyhedron_equiv_lex_polyhedron A b (point_of_basis b bas)).
    exact: feasible_basis_is_feasible.
  + move/is_basisP_rank: (basis_is_basis bas).
    rewrite /pointed => {1}<-.
    apply: mxrankS; exact: row_submx_submx.
- rewrite (polyhedron_equiv_lex_polyhedron A b x) in x_feas.
  by exists (build_feasible_basis Hpointed x_feas).
Qed.*)
Lemma exists_feasible_basis :
  ([set bas : basis A | is_feasible b bas] != set0) = (feasible A b) && (pointed A).
Proof.
apply/set0Pn/andP => [[bas] bas_is_feasible | [/feasibleP [x x_feas] Hpointed]].
- split.
  + apply/feasibleP; exists (point_of_basis b bas).
    rewrite (polyhedron_equiv_lex_polyhedron A b (point_of_basis b bas)).
    by rewrite in_set in bas_is_feasible.
  + move/is_basisP_rank: (basis_is_basis bas).
    rewrite /pointed => {1}<-.
    apply: mxrankS; exact: row_submx_submx.
- rewrite (polyhedron_equiv_lex_polyhedron A b x) in x_feas.
  exists (build_basis_basis b Hpointed x).
  rewrite in_set.
  exact: build_basis_basisP.
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
  | bas i [Hd Hd']
  | bas Hu].
- symmetry; apply/(introF idP).
  move/boundedP.
  by move => [[x [/(intro_existsT (feasibleP _ _))]]].
- move/(intro_existsT (feasibleP _ _)): (lex_feasible_basis_is_feasible bas) => Hfeas.
  suff: unbounded.
  + by move: (bounded_is_not_unbounded Hfeas) ->; move ->.
  + apply/unboundedP => K.
    exact: (unbounded_cert_on_basis K Hd' Hd (lex_feasible_basis_is_feasible bas)).
- symmetry; apply/boundedP.
  move: (optimal_cert_on_basis (lex_feasible_basis_is_feasible bas) Hu) => Hopt.
  suff <-: '[c, point_of_basis b bas] = opt_value.
  + split; last by done.
    * exists (point_of_basis b bas).
      by split; [exact: (lex_feasible_basis_is_feasible bas) | done].
  + by apply: opt_value_is_optimal; [exact: (lex_feasible_basis_is_feasible bas) | done].
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
  | fbas i [Hd Hd']
  | ]; constructor.
- move => [[fbas _] _]. move: (feasible_basis_is_feasible fbas) => Hfeas.
  rewrite /is_feasible -(polyhedron_equiv_lex_polyhedron A b _) in Hfeas.
  by move/(intro_existsT (feasibleP _ _)): Hfeas.
- move => [_ Hopt].
  move: (unbounded_cert_on_basis opt_value Hd' Hd (lex_feasible_basis_is_feasible fbas)) => [x [Hx Hx']].
  by move/(lt_le_trans Hx'): (Hopt _ Hx); rewrite ltxx.
- have Hval: '[ c, point_of_basis b bas] = opt_value.
    apply: opt_value_is_optimal;
      [ exact: (lex_feasible_basis_is_feasible bas) | exact: (optimal_cert_on_basis (lex_feasible_basis_is_feasible bas) i)].
  split; last first.
  + by rewrite -Hval; exact: (optimal_cert_on_basis (lex_feasible_basis_is_feasible bas) i).
  + have bas_is_feasible: is_feasible b bas.
      rewrite /is_feasible -(polyhedron_equiv_lex_polyhedron A b _).
      exact: (lex_feasible_basis_is_feasible bas).
    by exists (FeasibleBasis bas_is_feasible).
Qed.

End GeneralSimplex.

Section ExtraIneqPert.
Context {R : realFieldType} {m n' : nat}.
Notation n := (n'.+1).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).
Context (I : lex_feasible_basis A b).
Let b' := b_pert b.

Lemma active_ineq_pert_exact :
  I =i active_lex_ineq A b' (point_of_basis b' I).
Proof.
move=> i; apply/idP/idP;
  first (move: i; exact/subsetP/basis_subset_of_active_ineq).
rewrite /active_lex_ineq inE row_mul=> /eqP row_i_act.
apply: contraT; rewrite -(col_point_of_basis_pert b) negbK=> /eqP col_i_0.
have: (row i A <= row_submx A I)%MS.
- apply:submx_full; move: (basis_is_basis I).
  by rewrite /is_basis -row_leq_rank {1}prebasis_card col_leq_rank.
move/(submxMr (point_of_basis b' I)); rewrite row_i_act.
(* TODO : why is typing mandatory ?*)
move/(submxMr ((delta_mx (rshift 1 i) 0): 'cV__)).
rewrite -!colE col_mul col_i_0 mulmx0.
move/submx0null/matrixP/(_ ord0 ord0).
rewrite !mxE; case: splitP=> j; rewrite ?(ord1_eq0 j) //= !add1n.
move/succn_inj/val_inj=> -> /eqP.
by rewrite !mxE eqxx mulr1n oppr_eq0 oner_eq0.
Qed.

End ExtraIneqPert.

Section ExtraEdge.
Context {R : realFieldType} {m n' : nat}.
Notation n := (n'.+1).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).
Context (I : lex_feasible_basis A b) (i : 'I_#|I|).
Let b' := b_pert b.
Context (J : lex_feasible_basis A b) (j : 'I_m).
Hypothesis j_n_I : j \notin I.
Hypothesis J_eq : J = j |: (I :\ (enum_val i)) :> {set _}.
Hypothesis infeas_dir : ~~ (feasible_dir A (direction i)).

Lemma j_dir: (A *m (direction i)) j 0 != 0.
Proof.
apply/contraT; rewrite negbK=> A_dir_j.
move: (basis_trmx_row_free J)=> A_J_free.
suff: (direction i)^T *m (row_submx A J)^T = 0 by move/eqP; rewrite mulmx_free_eq0 // trmx_eq0 (negPf (direction_neq0 i)).
rewrite -trmx_mul; apply/eqP; rewrite trmx_eq0.
apply/eqP; rewrite J_eq; apply/row_matrixP=> k.
rewrite row_mul row_submx_row; move: (enum_valP k).
rewrite row0 inE; case/orP.
- rewrite inE=> /eqP ->.
  apply/matrixP=> p q; rewrite [RHS]mxE -(eqP A_dir_j).
  by rewrite -row_vdot -matrix_vdot tr_row !col_id.
- move=> kIi; move: (mulmx_direction i).
  set k' := enum_rank_in kIi (enum_val k).
  move/row_matrixP=> /(_ k'); rewrite row_mul row_submx_row.
  by rewrite enum_rankK_in // row0.
Qed.

Lemma adj_same_point_of_basis:
  point_of_basis b' J = 
  point_of_basis b' I + (direction i) *m (gap A b' (direction i) (point_of_basis b' I) j).
Proof.
apply/esym/basis_subset_active_ineq_eq.
apply/subsetP=> k; rewrite J_eq inE.
case/orP.
- rewrite !inE; move/eqP=> ->.
  rewrite row_mul mulmxDr [X in _ + X]mulmxA -[in X in _ + X]row_mul.
  rewrite /gap -scalemxAr mulmx_row_cV_rV scalerA mulVf; last exact/j_dir.
  by rewrite row_mul scale1r addrCA subrr addr0.
- move=> /[dup] kIi; rewrite !inE; case/andP=> k_i kI; rewrite row_mul mulmxDr.
  move: (kI); rewrite (active_ineq_pert_exact I) inE row_mul=> /eqP ->.
  apply/eqP/subr0_eq; rewrite addrAC subrr add0r mulmxA.
  set k' := enum_rank_in kIi k.
  move/(congr1 (row k')): (mulmx_direction i). 
  rewrite row_mul row_submx_row enum_rankK_in // => ->.
  by rewrite row0 mul0mx.
Qed.

Lemma xI_gtlex_j : ((row j A) *m (point_of_basis b' I)) >lex (row j b').
Proof.
rewrite -row_mul lex_polyhedron_gtP -?active_ineq_pert_exact //.
exact: feasible_basis_is_feasible.
Qed.

Lemma xJ_gtlex_i:
  ((row (enum_val i) A) *m (point_of_basis b' J)) >lex (row (enum_val i) b').
Proof.
rewrite -row_mul lex_polyhedron_gtP; last exact: feasible_basis_is_feasible.
rewrite -active_ineq_pert_exact ?J_eq ?K_eq !inE ?enum_valP ?eqxx /= orbF.
apply/contraT; rewrite negbK=> /eqP.
by move: j_n_I=> /[swap] <-; rewrite enum_valP.
Qed.

Lemma Ajd_lt0: (A *m (direction i)) j 0 < 0.
Proof.
have: j \in J by rewrite J_eq !inE eqxx.
rewrite active_ineq_pert_exact inE adj_same_point_of_basis.
rewrite row_mul mulmxDr [X in _ + X]mulmxA=> /eqP b'_j_eq.
move: xI_gtlex_j.
rewrite -b'_j_eq lex_gtr_addl [row j A *m _]mx11_scalar -row_mul mxE.
rewrite mul_scalar_mx. apply/contraTT.
rewrite -leNgt lex_ltrNge negbK=> ?.
apply/lex0_nnscalar=> //; apply:lex_ltrW.
move: xJ_gtlex_i; rewrite adj_same_point_of_basis mulmxDr.
move/row_matrixP: (row_submx_point_of_basis b' I)=> /(_ i).
rewrite row_mul !row_submx_row=> ->.
by rewrite lex_ltr_addl mulmxA row_direction mul1mx.
Qed.

Lemma edge_lex_ruleE : J = (lex_rule_fbasis infeas_dir).
Proof.
apply/eqP/(eq_pert_point_imp_eq_bas (b:=b)).
rewrite adj_same_point_of_basis lex_rule_point_of_basis.
congr (_ + _); congr (_ *m _).
apply/lex_antisym; rewrite argmin_gapP ?inE ?Ajd_lt0 // andbT.
set k := argmin_gap _ _ _.
case/boolP: (k == j); first by (move/eqP=> ->; exact/lex_refl).
move=> k_n_j.
have: k \notin J. 
- rewrite J_eq !inE (negPf k_n_j).
  by rewrite (negPf (lex_ent_var_not_in_basis infeas_dir)) andbF.
rewrite active_ineq_pert_exact -lex_polyhedron_gtP;
  last exact:feasible_basis_is_feasible.
rewrite adj_same_point_of_basis row_mul mulmxDr; move/lex_ltrW.
rewrite lex_subr_addr [X in _ <=lex X]mulmxA.
rewrite [_ *m direction _]mx11_scalar -!row_mul mxE mul_scalar_mx.
set l := (A *m direction _) _ _.
have l_lt0 : l < 0 by
  case: (argmin_gapP b' (point_of_basis b' I) infeas_dir); rewrite inE.
rewrite (lex_negscalar (a:=l^-1)) ?invr_lt0 // scalerA mulVr ?scale1r ?lambda_J_eq //.
exact/unitf_lt0/l_lt0.
Qed.

End ExtraEdge.

Module Exports.

Canonical prebasis_subType.
Canonical prebasis_eqType.
Canonical prebasis_choiceType.
Canonical prebasis_countType.
Canonical prebasis_subCountType.
Canonical prebasis_finType.
Canonical prebasis_subFinType.
Canonical basis_subType.
Canonical basis_eqType.
Canonical basis_choiceType.
Canonical basis_countType.
Canonical basis_subCountType.
Canonical basis_finType.
Canonical basis_subFinType.
Canonical feasible_basis_subType.
Canonical feasible_basis_eqType.
Canonical feasible_basis_choiceType.
Canonical feasible_basis_countType.
Canonical feasible_basis_subCountType.
Canonical feasible_basis_finType.
Canonical feasible_basis_subFinType.
End Exports.

End Simplex.
Export Simplex.Exports.
Coercion set_of_prebasis := Simplex.set_of_prebasis.
Coercion prebasis_of_basis := Simplex.prebasis_of_basis.
Coercion basis_of_feasible_basis := Simplex.basis_of_feasible_basis.
