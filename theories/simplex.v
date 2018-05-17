(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com    *)
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

Variable m n : nat.

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

Variable A : 'M[R]_(m,n).

Definition is_basis (bas : prebasis) := row_free (row_submx A bas).

Definition is_basisP_rank (bas : prebasis) : reflect (mxrank (row_submx A bas) = n) (is_basis bas).
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

Lemma basis_enum_uniq : uniq basis_enum.
Proof.
by apply: pmap_sub_uniq; apply: filter_uniq; apply: prebasis_enum_uniq.
Qed.

Lemma mem_basis_enum bas : bas \in basis_enum.
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

End PointOfBasis.

(*
Section FeasibleBasis.

Definition is_feasible (bas : basis) :=
  (point_of_basis bas) \in (polyhedron A b).

Lemma row_submx_is_feasible (bas : basis) :
  (forall x, (row_submx A bas) *m x = (row_submx b bas) -> x \in polyhedron A b) -> is_feasible bas.
Proof.
apply; by rewrite qmulKVmx; last exact: basis_is_basis bas.
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
apply/subsetP => i Hi.
rewrite inE; apply/eqP.
move: (row_submx_point_of_basis bas); rewrite -row_submx_mul.
by move/row_submx_colP/(_ _ Hi).
Qed.

Lemma active_ineq_in_point_of_basis (bas : basis) :
  (row_submx A bas <= active_ineq_mx A b (point_of_basis bas))%MS.
Proof.
apply/row_subP => i; rewrite row_submx_row.
move/subsetP/(_ _ (enum_valP i)): (basis_subset_of_active_ineq bas) => Hbas_i.
suff ->: row (enum_val i) A = row (enum_rank_in Hbas_i (enum_val i)) (active_ineq_mx A b (point_of_basis bas)) by apply: row_sub.
by rewrite row_submx_row enum_rankK_in //.
Qed.

Lemma feasible_point_of_basis_is_extreme (bas : feasible_basis) :
    is_extreme (point_of_basis bas) (polyhedron A b: _ -> bool).
Proof.
apply/extremality_active_ineq/andP; split; first exact: feasible_basis_is_feasible.
set M := active_ineq_mx _ _ _.
move/mxrankS: (active_ineq_in_point_of_basis bas).
move: (mxrank_basis bas) -> => H.
by move/andP/anti_leq: (conj H (rank_leq_col M)) => <-.
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
apply/eqP.
move: (leqnn n);
move/extremality_active_ineq: (Hextr) => /andP [_ /eqP {2} <-].
move/row_base_correctness => [_ _ ->].
symmetry; exact: prebasis_card.
Qed.

Definition extract_basis (x : 'cV[R]_n) (Hextr: is_extreme x (polyhedron A b: _ -> bool)) :=
    Basis (extract_prebasis_is_basis Hextr).

Lemma basis_subset_active_ineq_eq (bas : basis) (x : 'cV[R]_n) :
  bas \subset (active_ineq A b x) -> x = point_of_basis bas.
Proof.
move => H.
apply: is_point_of_basis.
rewrite -row_submx_mul.
apply/row_submx_colP => i Hi.
move/subsetP/(_ _ Hi): H.
by rewrite inE; move/eqP.
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
by move/extremality_active_ineq/andP: (Hextr) => [? _].
Qed.

Definition extract_feasible_basis (x : 'cV[R]_n) (Hextr : is_extreme x (polyhedron A b: _ -> bool)) :=
  FeasibleBasis (extract_basis_is_feasible Hextr).

Lemma extract_feasible_basis_point_of_basis (x : 'cV[R]_n) (Hextr: is_extreme x (polyhedron A b: _ -> bool)) :
  x = point_of_basis (extract_feasible_basis Hextr).
Proof.
by apply: extract_basis_point_of_basis.
Qed.*)

Section LexFeasibleBasis.

Variable p : nat.
Variable b : 'M[R]_(m,p).

Definition is_feasible (bas : basis) :=
  (point_of_basis b bas) \in (lex_polyhedron A b).

Lemma row_submx_is_feasible (bas : basis) :
  (forall x, (row_submx A bas) *m x = (row_submx b bas) -> x \in lex_polyhedron A b) -> is_feasible bas.
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

End LexFeasibleBasis.

Section BuildFeasibleBasis.

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
rewrite mxE -ltrNge => Ak_d_neg.
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

Lemma gap_ge0 j : j \in cand_idx -> (gap j) >=lex 0.
Proof.
move => j_is_cand.
apply: lex_scalar_le0.
- rewrite invr_le0.
  exact: ltrW.
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

Fact point_along_dir_feas : point_along_dir \in lex_polyhedron A b. (* RK *)
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
  apply: lex0_nnscalar; by [exact: min_gap_ge0 | rewrite lerNgt].
Qed.

End Feasibility.

Section ActiveIneq.

Variable I : {set 'I_m}.

Hypothesis d_in_kerAI : (row_submx A I) *m d == 0.

Fact argmin_gap_not_in_I : argmin_gap \notin I.
Proof.
move: argmin_gapP => [argmin_is_cand _].
move: argmin_is_cand; apply: contraL => argmin_in_I.
rewrite inE.
move/eqP: d_in_kerAI; rewrite -row_submx_mul.
move/row_submx_col0P/(_ _ argmin_in_I) => ->.
by rewrite ltrr.
Qed.

Fact argmin_gap_rank : (\rank (row_submx A (argmin_gap |: I)) = (\rank (row_submx A I)).+1)%N.
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
  by rewrite ltrr.
have Aj_inter_AI : (Aj :&: AI <= (0:'M_n))%MS.
  apply/rV_subP => ?; rewrite submx0 sub_capmx.
  move/andP => [/sub_rVP [a ->] /submxP [z]].
  move/(congr1 (mulmx^~ d)).
  rewrite -mulmxA -scalemxAl.
  move/eqP: d_in_kerAI ->; rewrite mulmx0.
  move/eqP; rewrite scalemx_eq0.
  move/negbTE: Ajd_neq0 ->; rewrite orbF.
  by move/eqP ->; rewrite scale0r.
move/leqifP: (mxrank_adds_leqif Aj AI).
rewrite ifT //. move/eqP ->.
rewrite rank_rV.
suff ->: (Aj != 0) by done.
- apply/eqP.
  move/(congr1 (mulmx^~ d)); rewrite mul0mx.
  by move/eqP: Ajd_neq0.
Qed. 

Hypothesis I_subset_active_ineq_x : I \subset (active_lex_ineq A b x).

Fact point_along_dir_active_ineq : (* RK *)
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
  move/eqP: d_in_kerAI; rewrite -row_submx_mul.
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

Hypothesis Hpointed : pointed A.

Definition build_basic_point_iter x :=
  let I := active_lex_ineq A b x in
  let d := pick_in_ker (row_submx A I) in
  if @idPn (d == 0) is ReflectT d_neq0 then
    let infeas_dir := (build_non_feasible_directionP Hpointed d_neq0) in
    (point_along_dir x infeas_dir)
  else x.

Fact build_basic_point_iter_feasible x : x \in lex_polyhedron A b -> build_basic_point_iter x \in lex_polyhedron A b.
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
  - rewrite /d /build_non_feasible_direction.
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
apply/leP.
move/build_basic_point_iter_rank: (rk_lt_n); exact: ltn_sub2l.
Qed.

Lemma build_basic_point_is_feas : forall x, x \in lex_polyhedron A b -> build_basic_point x \in lex_polyhedron A b.
Proof.
pose P := fun x y => x \in lex_polyhedron A b -> y \in lex_polyhedron A b.
apply: (build_basic_point_ind (P := P)).
- by move => x _; rewrite /=.
- move => x ? <- _ => ind_hyp.
  by move/build_basic_point_iter_feasible/ind_hyp.
Qed.

Lemma build_basic_point_rank : forall x, (\rank (row_submx A (active_lex_ineq A b (build_basic_point x))) >= n)%N.
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

Let build_basis_basis := Basis build_basis_prebasisP.

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

Section Cost.

Implicit Types c : 'cV[R]_n.
Implicit Types bas : basis.
Implicit Types x : 'cV[R]_n.
Implicit Types u : 'cV[R]_m.

(* Reduced cost of basis: u s.t.
   u = < A^{-1}_I, c >, where I is a basis *)
Definition reduced_cost_of_basis c bas :=
  (qinvmx (prebasis_card bas) (row_submx A bas))^T *m c.

Definition reduced_cost_of_basis_def c bas :
  (row_submx A bas)^T *m (reduced_cost_of_basis c bas) = c.
Proof.
rewrite /reduced_cost_of_basis trmx_qinv; last exact: basis_is_basis.
by rewrite qmulKVmx; last exact: basis_trmx_row_free.
Qed.

Definition ext_reduced_cost_of_basis c bas :=
  let: u := reduced_cost_of_basis c bas in
  \col_i (if (@idP (i \in bas)) is ReflectT Hi then
            u (enum_rank_in Hi i) 0
          else 0).

Lemma ext_reduced_cost_of_basis_in_bas c bas i (Hi : (i \in bas)) :
  let: j := enum_rank_in Hi i in
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
apply/idP/idP => [/gev0P H | /gev0P H].
- apply/gev0P => i.
  move: (ext_reduced_cost_of_basis_in_bas c (enum_valP i)).
  rewrite enum_valK_in => <-.
  exact: H.
- apply/gev0P => i; case: (boolP (i \in bas)) => [Hi | Hi].
  + rewrite (ext_reduced_cost_of_basis_in_bas c Hi).
    exact: H.
  + by rewrite (ext_reduced_cost_of_basis_notin_bas c Hi).
Qed.

Lemma ext_reduced_cost_of_basis_def c bas :
  (* should be rewritten using an appropriate lemma to be written in row_submx.v,
   * stating that M = row_perm _ (col_mx (row_submx M bas) (row_submx M ~:bas))   *)
  A^T *m (ext_reduced_cost_of_basis c bas) = c.
Proof.
apply/colP => i; rewrite !mxE.
rewrite (bigID (fun j => j \in bas)) /= [X in _ + X]big1;
  last by move => j /ext_reduced_cost_of_basis_notin_bas ->; rewrite mulr0.
rewrite addr0.
rewrite (reindex (@enum_val _ (mem bas))) /=;
  last by apply: (enum_val_bij_in (enum_valP (cast_ord (esym (prebasis_card bas)) i))).
rewrite (eq_bigl predT) /=; last by move => k /=; apply: (enum_valP k).

move/colP/(_ i): (reduced_cost_of_basis_def c bas); rewrite !mxE => <-.
apply: eq_bigr => j _.
rewrite (ext_reduced_cost_of_basis_in_bas c (enum_valP j)) enum_valK_in.
by rewrite 2![_^T _ _]mxE row_submx_mxE.
Qed.

Lemma ext_reduced_cost_dual_feasible c bas :
  let: u := ext_reduced_cost_of_basis c bas in
  (reduced_cost_of_basis c bas) >=m 0 = (u \in dual_polyhedron A c).
Proof.
rewrite inE.
move/eqP: (ext_reduced_cost_of_basis_def c bas) ->; rewrite /=.
by symmetry; apply: non_neg_reduced_cost_equiv.
Qed.

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

Definition direction bas (i:'I_#|bas|) :=
  let: ei := (delta_mx i 0):'cV_#|bas| in
  (qinvmx (prebasis_card bas) (row_submx A bas)) *m ei.

Lemma direction_neq0 bas (i:'I_#|bas|) : direction i != 0.
Proof.
apply/eqP.
move/(congr1 (mulmx (row_submx A bas))).
rewrite qmulKVmx; last exact: basis_is_basis.
rewrite mulmx0.
move/colP/(_ i); rewrite 2!mxE 2!eq_refl /=.
by move/eqP; rewrite pnatr_eq0.
Qed.

Lemma direction_improvement c bas (i:'I_#|bas|):
  let: u := reduced_cost_of_basis c bas in
  u i 0 < 0 -> '[c, direction i] < 0.
Proof.
by rewrite vdot_mulmx vdotr_delta_mx.
Qed.

Lemma unbounded_cert_on_basis c (bas : feasible_basis) (i:'I_#|bas|) M:
  let: u := reduced_cost_of_basis c bas in
  let: d := direction i in
  feasible_dir A d -> u i 0 < 0 ->
  exists x, (x \in polyhedron A b) /\ ('[c,x] < M).
Proof.
move => Hd Hui.
apply: (unbounded_certificate (x0 := point_of_basis bas) (d:=direction i));
  try by [exact: feasible_basis_is_feasible | done].
by rewrite vdot_mulmx vdotr_delta_mx.
Qed.

Lemma direction_prop (bas : basis) (i : 'I_#|bas|) (j : 'I_m) :
  let: d := direction i in
  j \in bas -> (A *m d) j 0 = (j == enum_val i)%:R.
Proof.
set d := direction i.
move => Hj.
suff ->: (A *m d) j 0 = ((row_submx A bas) *m d) (enum_rank_in Hj j) 0.
- rewrite qmulKVmx; last exact: basis_is_basis.
  rewrite mxE andbT; do 2![apply: congr1].
  apply/eqP/eqP.
  + exact: (canRL_in (enum_rankK_in Hj)).
  + exact: (canLR (enum_valK_in Hj)).
- rewrite -row_submx_mul row_submx_mxE enum_rankK_in //.
Qed.

Lemma mulmx_direction (bas : basis) (i : 'I_#|bas|):
  let: d := direction i in
  (row_submx A (bas :\ enum_val i)) *m d = 0.
Proof.
rewrite -row_submx_mul.
apply/row_submx_col0P => j.
rewrite in_setD1 => /andP [Hj Hj'].
rewrite direction_prop //.
by move/negbTE: Hj ->.
Qed.

End Cost.

Section Lexicographic_rule.

Variable s : 'S_m.

Variable c : 'cV[R]_n.

Implicit Types bas : lex_feasible_basis.

Definition lex_gap bas (d : 'cV_n) j :=
  let: x := point_of_basis_pert bas in
  ((A *m d) j 0)^-1 *: ((row j b_pert) - ((row j A) *m x)).

Definition lex_ent_var_nat bas (i: 'I_#|bas|) :=
  let: d := direction i in
  let: J := [ seq j <- (enum 'I_m) | (A *m d) j 0 < 0 ] in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- J] in
  find (fun j => (j \in J) && (lex_min_gap == lex_gap bas d j)) (enum 'I_m).

Lemma lex_ent_var_bound bas (i: 'I_#|bas|) :
  let: d := direction i in
  ~~ (feasible_dir A d) -> (lex_ent_var_nat i < m)%N.
Proof.
move => /existsP [k Hk].
rewrite mxE in Hk.
rewrite -[X in (_ < X)%N]size_enum_ord -has_find.
set d := direction i.
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
Variable i : 'I_#|bas|.
Hypothesis infeas_dir : ~~(feasible_dir A (direction i)).

Definition lex_ent_var := Ordinal (lex_ent_var_bound infeas_dir).

Lemma lex_ent_var_properties :
  let: d := direction i in
  let: J := [ seq j <- (enum 'I_m) | (A *m d) j 0 < 0 ] in
  let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- J] in
  let: j := lex_ent_var in
  (j \in J) && (lex_min_gap == lex_gap bas d j).
Proof.
set d := direction i.
set J := filter (fun j => (A *m d) j 0 < 0) (enum 'I_m).
set lex_gaps := [seq lex_gap bas d j | j <- J].
set j_nat := lex_ent_var_nat i.
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
  j |: (bas :\ (enum_val i)).

Lemma lex_ent_var_not_in_basis:
  lex_ent_var \notin bas.
Proof.
set d := direction i.
set J := [ seq j <- (enum 'I_m) | (A *m d) j 0 < 0 ].
set j := lex_ent_var.
apply/negP; move/(direction_prop i) => Hj.
have Hpos: (A *m d) j 0 >= 0 by rewrite Hj; exact: ler0n.
suff: j \in J.
- rewrite mem_filter => /andP [Hneg _].
  by move: (ler_lt_trans Hpos Hneg); rewrite ltrr.
- by move/andP: lex_ent_var_properties => [? _].
Qed.

Lemma lex_rule_card : #|lex_rule_set| == n.
Proof.
rewrite cardsU1 in_setD1 negb_and lex_ent_var_not_in_basis orbT /=.
rewrite cardsD.
move: (enum_valP i); rewrite -sub1set => Hibas.
move/subset_leq_card: (Hibas).
move/setIidPr: Hibas ->; rewrite cards1 => Hbas.
by rewrite subn1 addnC addn1 prednK // (prebasis_card bas).
Qed.

Definition lex_rule_pbasis := Prebasis lex_rule_card.

Lemma lex_rule_is_basis : is_basis lex_rule_pbasis.
Proof.
set d := direction i.
set j := lex_ent_var.
set J := lex_rule_set.
 
move: (mxrank_basis bas).
rewrite (row_submx_spanD1 A (enum_valP i)).
set AIi := row_submx A (bas :\ enum_val i).
set Ai := row (enum_val i) A.
set Aj := row j A.
 
have HAjd: (Aj *m d) != 0.
- apply/eqP; move/col0P/(_ 0).
  rewrite -row_mul mxE => Hj.
  move/andP: lex_ent_var_properties => [Hj' _].
  move: Hj'; rewrite mem_filter.
  by rewrite Hj ltrr.
 
move => HrkI.
rewrite /is_basis -row_leq_rank {1}(prebasis_card lex_rule_pbasis).
rewrite row_submx_spanU1 -/AIi -/j -/Aj; last first.
- move: lex_ent_var_not_in_basis;
  by apply: contra; rewrite in_setD1; move/andP => [_].
 
have HrkIi: (n <= 1+\rank AIi)%N.
- rewrite -{1}HrkI.
  move: (rank_leq_row Ai); rewrite -(leq_add2r (\rank AIi)).
  apply: leq_trans.
  exact: mxrank_adds_leqif.
 
have Hw_inter_AIi : (Aj :&: AIi <= (0:'M_n))%MS.
- apply/rV_subP => ?; rewrite submx0 sub_capmx.
  move/andP => [/sub_rVP [a ->] /submxP [z]].
  move/(congr1 (mulmx^~ d)).
  rewrite -mulmxA -scalemxAl mulmx_direction // mulmx0.
  move/eqP; rewrite scalemx_eq0.
  move/negbTE: HAjd ->; rewrite orbF.
  by move/eqP ->; rewrite scale0r.
 
move/leqifP: (mxrank_adds_leqif Aj AIi).
rewrite ifT //; move/eqP ->.
rewrite rank_rV.
suff ->: (Aj != 0) by done.
- apply/eqP.
  move/(congr1 (mulmx^~ d)); rewrite mul0mx.
  by move/eqP: HAjd.
Qed.

Definition lex_rule_bas := Basis lex_rule_is_basis.

Lemma lex_rule_rel_succ_points :
let: d := direction i in
let: v := point_of_basis_pert bas in
let: next_bas := lex_rule_bas in
let: next_v := point_of_basis_pert next_bas in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
  next_v = v + d *m lex_min_gap.
Proof.
set d := direction i.
set j := lex_ent_var.
set next_bas := lex_rule_bas.
set v := point_of_basis_pert bas.
set next_v := point_of_basis_pert next_bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
set u := v + d *m lex_min_gap.
 
move: (basis_is_basis bas) => Hbas.
move: (basis_is_basis next_bas) => Hnext_bas.
move/andP: lex_ent_var_properties => [Hj /eqP Hj'].
move: Hj; rewrite mem_filter; move/andP => [Hj _].
 
move: (row_submx_point_of_basis_pert bas) => Hv.
rewrite -/j -/d -/v -row_submx_mul in Hj, Hj', Hv.
 
symmetry; apply: is_point_of_basis_pert_active => k Hk;
  rewrite row_mul mulmxDr.
 
case: (altP (k =P j)) => [-> | H].
- rewrite -[X in _ + X]row_mul.
  rewrite [X in _ + row _ X]mulmxA row_mul.
  rewrite [X in _ + X *m _]mx11_scalar mul_scalar_mx mxE.
  rewrite /lex_min_gap Hj' scalerA mulfV; last by apply: ltr0_neq0.
  by rewrite scale1r addrC -addrA addNr addr0.
 
- have HkI: (k \in bas :\ enum_val i)
    by move: Hk; rewrite in_setU1; move/negbTE: H ->.
  have HkI': (k \in bas)
    by move: HkI; rewrite in_setD1; move/andP => [_].
  move/row_submx_row_matrixP/(_ _ HkI'): Hv; rewrite row_mul => ->.
  rewrite mulmxA.
  suff ->: row k A *m d = 0 by rewrite mul0mx addr0.
  + rewrite -row_mul.
    move: (mulmx_direction i); rewrite -row_submx_mul.
    by move/row_submx_row_matrix0P/(_ _ HkI).
Qed.

Lemma lex_min_gap_lex_pos :
let: d := direction i in
let: j := lex_ent_var in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
   0 <=lex lex_min_gap.
Proof.
set d := direction i.
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

Lemma lex_min_gap_lex_prop (k : 'I_m) :
let: d := direction i in
let: v := point_of_basis_pert bas in
let: lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0] in
   (A *m d) k 0 < 0 -> (row k b_pert) <=lex (row k A *m v + (A *m d) k 0 *: lex_min_gap).
Proof.
set d := direction i.
set v := point_of_basis_pert bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
move => H.
move: (H); rewrite -invr_lt0 => H'.
rewrite lex_subr_addr (lex_negscalar (row k b_pert - row k A *m v) ((A *m d) k 0 *: lex_min_gap) H') scalerA mulVr;
  last by rewrite unitfE; apply: (ltr0_neq0 H).
rewrite scale1r.
apply: lex_min_seq_ler; apply: map_f.
rewrite mem_filter; apply/andP; split; by rewrite ?mem_enum.
Qed.

Lemma lex_rule_lex_feasibility : is_lex_feasible lex_rule_bas.
Proof.
set d := direction i.
set j := lex_ent_var.
set bas' := lex_rule_bas.
set v := point_of_basis_pert bas.
set lex_min_gap := lex_min_seq [ seq lex_gap bas d j | j <- enum 'I_m & (A *m d) j 0 < 0].
set u := v + d *m lex_min_gap.
move: (lex_feasible_basis_is_lex_feasible bas) => Hfeas.
move: lex_min_gap_lex_pos => Hmin_gap.
move: lex_rule_rel_succ_points => Hvu.
rewrite -/u in Hvu.
have Hu: [forall j, ((row j A) *m u) >=lex (row j b_pert)].
- apply/forallP => k.
  rewrite mulmxDr [X in _ + X]mulmxA -[X in _ + X *m _]row_mul.
  rewrite [X in _ + X *m _]mx11_scalar mul_scalar_mx mxE.
  case: (ltrgt0P ((A *m d) k 0)) => [H | H | ->].
  + rewrite -[X in X <=lex _]addr0.
    apply: (@lex_trans _ _ (row k A *m v + 0)).
    - rewrite lex_add2r; by move/forallP: Hfeas.
    - rewrite lex_add2l -[0](scaler0 _ ((A *m d) k 0)) lex_pscalar //.
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
set d := direction i.
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
rewrite lex_ltrNge -[X in X *: _]opprK scaleNr -scalerN -[0](scaler0 _ (-'[c,d])).
rewrite lex_pscalar;
  last by rewrite oppr_gt0; apply: (direction_improvement Hui).
rewrite -lex_ltrNge.
apply/andP; split; last first.
- rewrite -oppv_gelex0 opprK.
  exact: lex_min_gap_lex_pos.
- move/andP: lex_ent_var_properties => [Hj /eqP Hj'].
  move: Hj; rewrite mem_filter; move/andP => [Hj _].
  rewrite -/j -/d in Hj, Hj'.
  rewrite /lex_min_gap Hj' /lex_gap -/d -/j oppr_eq0 scaler_eq0.
  move/ltr0_neq0/invr_neq0/negbTE: (Hj) => -> /=.
  apply/eqP; move/rowP/(_ (rshift 1 (s j))).
 
  rewrite [RHS]mxE mxE [X in _ + X]mxE => /subr0_eq.
  rewrite row_row_mx row_mxEr ![in LHS]mxE eq_refl /= mulr1n.
 
  suff: col (rshift 1 (s j)) (row_submx b_pert bas) = 0.
  + move/(congr1 (mulmx (qinvmx (prebasis_card bas) (row_submx A bas)))).
    rewrite mulmx0 -col_mul.
    move/(congr1 (mulmx (row j A))); rewrite mulmx0.
    rewrite -col_mul -row_mul.
    move/matrixP/(_ 0 0); rewrite 2!mxE [RHS]mxE => ->.
    move/(congr1 (fun x => x+1)); rewrite add0r addNr.
    apply/eqP; rewrite eq_sym; exact: oner_neq0.
  + rewrite row_submx_row_mx colKr.
    rewrite row_submx_col.
    apply/row_submx_col0P => k Hk.
    rewrite !mxE (inj_eq (@perm_inj _ s)).
    move/memPn/(_ _ Hk)/negbTE: lex_ent_var_not_in_basis => -> /=.
    by rewrite mulr0n oppr0.
Qed.

End Lexicographic_rule.

Section LexPhase2.

Variable s : 'S_m.

Inductive lex_final_result :=
| Lex_res_unbounded (bas: lex_feasible_basis s) of 'I_#|bas|
| Lex_res_optimal_basis of (lex_feasible_basis s).

Inductive lex_intermediate_result :=
| Lex_final of lex_final_result
| Lex_next_basis of (lex_feasible_basis s).

Variable c : 'cV[R]_n.
Implicit Types bas : (lex_feasible_basis s).

Definition basic_step bas :=
  let u := reduced_cost_of_basis c bas in
  if [pick i | u i 0 < 0] is Some i then
    let d := direction i in
    if (@idPn (feasible_dir A d)) is ReflectT infeas_dir then
      Lex_next_basis (lex_rule_lex_bas infeas_dir)
    else Lex_final (Lex_res_unbounded i)
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
| Lex_unbounded (bas: (lex_feasible_basis s)) (i: 'I_#|bas|) of (reduced_cost_of_basis c bas) i 0 < 0 /\ feasible_dir A (direction i) : lex_phase2_spec (Lex_res_unbounded i)
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
move: (row_submx_point_of_basis_pert s bas); rewrite -row_submx_mul.
move/row_submx_row_matrixP/(_ _ Hi) => <-.
rewrite row_mul; exact: lex_refl.
Qed.

Lemma feasible_to_lex_feasible :
  is_lex_feasible s0 bas0.
Proof.
pose b' := b_pert s0.
have Hb: forall j, col (rshift 1 (cast_ord n_leq_m (lshift n j))) (row_submx b' bas0) = 0.
- move => j.
  rewrite row_submx_row_mx colKr.
  apply/colP => k; rewrite mxE row_submx_mxE [RHS]mxE.
  set l := cast_ord _ _. rewrite !mxE permE.
  suff /negbTE ->: (s0_fun (enum_val k) != l)
    by rewrite mulr0n oppr0.
  + rewrite /s0_fun (inj_eq (@cast_ord_inj _ _ n_leq_m)).
    move: (enum_valP k) => Hk; case: {-}_ /idP => [Hk' |]; last by done.
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
        rewrite mulmxA row_submx_row_mx mul_mx_row row_mxEl.
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
| Phase2_res_unbounded (bas: feasible_basis) of 'I_#|bas|
| Phase2_res_optimal_basis of feasible_basis.

Definition lex_to_phase2_final_result (res: lex_final_result s0) :=
  match res with
  | Lex_res_unbounded bas i => Phase2_res_unbounded (bas := bas) i (* need due to the corecion *)
  | Lex_res_optimal_basis bas => Phase2_res_optimal_basis bas
  end.

Definition phase2 :=
  let: lex_bas0 := LexFeasibleBasis (feasible_to_lex_feasible) in
    lex_to_phase2_final_result ((@lex_phase2 s0) c lex_bas0).

CoInductive phase2_spec : phase2_final_result -> Type :=
| Phase2_unbounded (bas: feasible_basis) (i: 'I_#|bas|) of (reduced_cost_of_basis c bas) i 0 < 0 /\ feasible_dir A (direction i) : phase2_spec (Phase2_res_unbounded i)
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
apply/is_basisP_rank.
by rewrite row_submx_col_mx_rshift row_submxT !rank_castmx mxrank1.
Qed.

Definition dual_bas0 := Basis dual_pb0_is_basis.

Lemma dual_bas0_is_feasible : (is_feasible (dualb _ 0) dual_bas0).
Proof.
apply: row_submx_is_feasible => x.
rewrite 2!row_submx_col_mx_rshift 2!row_submxT /=.
rewrite 2!cast_mulmx mul1mx.
do 2![move/castmx_inj] => ->.
rewrite -dual_polyhedronE inE.
by rewrite mulmx0 eq_refl lev_refl.
Qed.

Definition dual_feasible_bas0 := FeasibleBasis dual_bas0_is_feasible.

Inductive emptiness_proc_res :=
| FeasiblePoint of 'cV[R]_n
| InconsistencyCert of 'cV[R]_m.

Definition emptiness_proc :=
  match phase2 dual_feasible_bas0 (-b) with
  | Phase2_res_optimal_basis bas =>
    let v := ext_reduced_cost_of_basis (- b) bas in
    FeasiblePoint (dsubmx (usubmx v) - usubmx (usubmx v))
  | Phase2_res_unbounded bas i => InconsistencyCert (direction i)
  end.

Definition feasible := if emptiness_proc is FeasiblePoint _ then true else false.

CoInductive emptiness_proc_spec : emptiness_proc_res -> bool -> Type :=
| Feasible x of (x \in polyhedron A b)  : emptiness_proc_spec (FeasiblePoint x) true
| Empty d of (dual_feasible_dir A d /\ '[b,d] > 0) : emptiness_proc_spec (InconsistencyCert d) false.

Lemma emptiness_procP : emptiness_proc_spec emptiness_proc feasible.
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
(*RK: the next line was changed to remove a "Nothing to inject" message
move => x_feas [[/andP [/eqP Ad d_lt0]] b_d_ltr0].*)
move => x_feas [/andP [/eqP Ad d_lt0] b_d_ltr0].
move/(vdot_lev d_lt0): x_feas.
rewrite vdot_mulmx Ad vdot0l vdotC.
by move/(ltr_le_trans b_d_ltr0); rewrite ltrr.
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


Section Pointed_simplex.
(* a complete simplex method (phase 1 + 2) which applies to LP
 * such that the feasible set is pointed *)

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Hypothesis Hpointed: pointed A.

Variable c : 'cV[R]_n.

Inductive pointed_final_result :=
| Pointed_res_infeasible of 'cV[R]_m
| Pointed_res_unbounded (bas: feasible_basis A b) of 'I_#|bas|
| Pointed_res_optimal_basis of (feasible_basis A b).

Definition pointed_simplex :=
  match emptiness_proc A b with
  | FeasiblePoint x =>
    if @idP (x \in polyhedron A b) is ReflectT x_feas then
      let bas0 := build_feasible_basis Hpointed x_feas in
      match phase2 bas0 c with
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
| Pointed_unbounded (bas: feasible_basis A b) (i: 'I_#|bas|) of (reduced_cost_of_basis c bas) i 0 < 0 /\ feasible_dir A (direction i) : pointed_simplex_spec (Pointed_res_unbounded i)
| Pointed_optimal_point (bas : feasible_basis A b) of (reduced_cost_of_basis c bas) >=m 0 : pointed_simplex_spec (Pointed_res_optimal_basis bas).

Lemma pointed_simplexP : pointed_simplex_spec pointed_simplex.
Proof.
rewrite /pointed_simplex.
case: emptiness_procP => [x x_feas | d d_inconsistent]; last first.
- by constructor.
- case: {-}_/idP => [?|]; last by done.
  case: phase2P => [[bas' d] /=|]; by constructor.
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

CoInductive simplex_spec : simplex_final_result -> Type :=
| Infeasible d of (dual_feasible_dir A d /\ '[b, d] > 0): simplex_spec (Simplex_infeasible d)
| Unbounded p of [/\ (p.1 \in polyhedron A b), (feasible_dir A p.2) & ('[c,p.2] < 0)] : simplex_spec (Simplex_unbounded p)
| Optimal_point p of [/\ (p.1 \in polyhedron A b), (p.2 \in dual_polyhedron A c) & '[c,p.1] = '[b, p.2]] : simplex_spec (Simplex_optimal_point p).

Lemma simplexP: simplex_spec simplex.
Proof.
rewrite /simplex.
case: pointed_simplexP => [ d /infeasibility_pointed_to_general [Hd Hd'] | bas i [H H']| bas Hu]; constructor; rewrite //=.
- split.
  + apply: feasibility_pointed_to_general.
    exact: feasible_basis_is_feasible.
  + rewrite -mulmxAv2gen.
    rewrite inE /Apointed mul_col_mx col_mx_gev0 in H'.
    by move/andP: H' => [? _].
  + by rewrite -cost2gen /direction vdot_mulmx vdotr_delta_mx.
- split.
  + apply: feasibility_pointed_to_general.
    exact: feasible_basis_is_feasible.
  + by apply: ext_reduced_cost2gen_dual_feasible.
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
  rewrite /opt_point /dual_opt_point /bounded  //=.
  case: simplexP.
  - move => d /(intro_existsT (infeasibleP _ _))/feasibleP H.
    apply Bool.andb_false_iff. constructor.
    apply /idP => Q. destruct H. by exists 0.
  - move => //= [_ p] //= [_ _ Q]. apply /and3P. move => [_ P _].
    move: P. rewrite /dual_polyhedron !inE => /andP [/eqP P _].
    move: P. rewrite mulmx0 => Qn. move: Q. by rewrite -Qn vdot0l ltrr.
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
  by rewrite vdot0r ltr_le_asym.
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
    by move/(_ _ Hx): H; move/(ltr_le_trans Hlt); rewrite ltrr.
Qed.

Lemma boundedP_lower_bound : (feasible A b) ->
  reflect (exists K, (forall x, x \in polyhedron A b -> '[c,x] >= K)) bounded.
Proof.
  move => Hfeas.
  apply: (iffP idP).
  + move => /boundedP [_ H]. by exists opt_value.
  + move => [K H]. rewrite bounded_is_not_unbounded //.
    apply /negP. move/unboundedP/(_ K) => [x [Hx Hlt]].
    move/(_ _ Hx): H. by rewrite ltr_geF.
Qed.

Lemma opt_value_is_optimal x :
  (x \in polyhedron A b) ->
  (forall y, y \in polyhedron A b -> '[c,x] <= '[c,y]) -> '[c,x] = opt_value.
Proof.
move => Hx Hopt; rewrite /opt_value /opt_point.
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
apply/set0Pn/andP => [[bas] _ | [/feasibleP [x x_feas] Hpointed]].
- split.
  + apply/feasibleP; exists (point_of_basis b bas); exact: feasible_basis_is_feasible.
  + move/is_basisP_rank: (basis_is_basis bas).
    rewrite /pointed => {1}<-.
    apply: mxrankS; exact: row_submx_submx.
- by exists (build_feasible_basis Hpointed x_feas).
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
  | fbas i [Hd Hd']
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

Lemma bounded_polyhedronP_Linfty : reflect (exists K, forall x, x \in polyhedron A b -> forall i, `|x i 0| <= K) bounded_polyhedron.
Proof.
rewrite /bounded_polyhedron.
case: (boolP (feasible A b)) => /= [Hfeas | /negP Hinfeas]; last first.
- constructor; exists 0; move => x.
  by move/(intro_existsT (feasibleP _ _)).
- apply: (iffP andP) => [[/forallP Hpos /forallP Hneg]| [K H]]; last first.
  + split; apply/forallP => i; [pose v := (delta_mx i 0):'cV[R]_n | pose v := -(delta_mx i 0):'cV[R]_n];
      suff Hi: forall x, x \in polyhedron A b -> '[v, x] >= -K;
      by [ move/(intro_existsT (infeasible_or_boundedP _ _ _)): Hi;
           rewrite Hfeas
         | move => x Hx; rewrite ?vdotNl vdotl_delta_mx ?ler_opp2;
           move/(_ _ Hx i): H; rewrite ler_norml; move/andP => [? ?]].
  + set K := -(min_seq [
      seq Num.min (opt_value A b (delta_mx i 0))
      (opt_value A b (-(delta_mx i 0))) | i :'I_n] 0).
    exists K; move => x Hx i.
    suff: '[delta_mx i 0, x] >= -K /\ '[-(delta_mx i 0), x] >= -K.
    * rewrite vdotNl vdotl_delta_mx ler_opp2 => /andP.
      by rewrite ler_norml.
    * split; rewrite opprK;
      [ move/(_ i)/(boundedP _ _ _): Hpos => [_] | move/(_ i)/(boundedP _ _ _): Hneg => [_]];
      [ pose v := opt_value A b (delta_mx i 0) | pose v := opt_value A b (-(delta_mx i 0))];
      move/(_ _ Hx); apply: ler_trans;
      suff: Num.min (opt_value A b (delta_mx i 0)) (opt_value A b (-(delta_mx i 0))) <= v;
      by [ apply: ler_trans; apply: min_seq_ler; apply: map_f; rewrite mem_enum
         | rewrite ler_minl lerr ?orbT].
Qed.

Hypothesis Hfeas: feasible A b.

Lemma bounded_polyhedronP_obj : reflect (forall c, bounded A b c) bounded_polyhedron.
Proof.
apply: (iffP idP) => [/bounded_polyhedronP_Linfty [K H] c | H]; last first.
- rewrite /bounded_polyhedron Hfeas /=.
  apply/andP; split; apply/forallP => i; exact: H.
- suff: forall x, x \in polyhedron A b -> '[c, x] >= - \sum_i `|c i 0| * K
    by move/(intro_existsT (infeasible_or_boundedP _ _ _)); rewrite Hfeas.
  + move => x Hx.
    have: `|'[c,x]| <= \sum_i `|c i 0| * K.
    * suff: \sum_i `|c i 0 * x i 0| <= \sum_i `|c i 0| * K.
      - apply: ler_trans.
        + rewrite /vdot; exact: ler_norm_sum.
        + apply: ler_sum => i _; rewrite normrM.
          apply: ler_wpmul2l; [ exact: normr_ge0 | exact: H ].
    by rewrite ler_norml => /andP [? _].
Qed.

Lemma bounded_polyhedronP_feasible_dir : reflect (forall d, feasible_dir A d -> d = 0) bounded_polyhedron.
Proof.
apply: (iffP bounded_polyhedronP_obj) => [ Hbounded | H].
- move => d Hd.
  move/feasibleP: (Hfeas) => [x Hx].
  move/(_ (-d)): Hbounded.
  rewrite bounded_is_not_unbounded //.
  apply: contraNeq => [Hd']; apply/unboundedP_cert.
  exists (x, d); split; try by done.
  by rewrite vdotNl /= oppr_lt0 vnorm_gt0.
- move => c; rewrite bounded_is_not_unbounded //.
  apply/negP; move/unboundedP_cert => [[? d] [_ Hd]].
  move/(_ _ (Hd)): H; rewrite /= => ->.
  by rewrite vdot0r ltrr.
Qed.

Lemma feasible_bounded_polyhedron_is_pointed : bounded_polyhedron -> pointed A.
Proof.
move/bounded_polyhedronP_obj => Hbounded.
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
