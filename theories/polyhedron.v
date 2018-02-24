(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section BasicNotion.

Section Defs.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Implicit Types x : 'cV[R]_n.

Definition polyhedron := [pred x: 'cV_n | (A *m x) >=m b].

Lemma polyhedron_rowinE x:
  (x \in polyhedron) = [forall i, ((row i A) *m x) 0 0 >= b i 0].
Proof.
rewrite inE; apply: eq_forallb => i.
by rewrite -row_mul [in RHS]mxE.
Qed.

Definition active_ineq x :=
  [set i : 'I_m | (A *m x) i 0 == b i 0].

Definition feasible_dir := [pred d | (A *m d) >=m 0].

Definition pointed := (mxrank A >= n)%N.

Lemma pointedPn : reflect (exists d, [/\ d != 0, feasible_dir d & feasible_dir (-d)]) (~~pointed).
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
    
End Defs.

Section WeakDuality.

Variable R : realFieldType.
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

Definition duality_gap x u := '[c,x] - '[b,u].

Lemma duality_gap_def x u :
  (A^T *m u) = c -> duality_gap x u = '[u, A *m x - b].
Proof.
by rewrite /duality_gap; move <-; rewrite -vdot_mulmx [X in _ - X]vdotC vdotBr.
Qed.

Lemma duality_gap_ge0_def x u : (duality_gap x u >= 0) = ('[c,x] >= '[b,u]).
Proof.
by rewrite /duality_gap subr_ge0.
Qed.

Lemma duality_gap_eq0_def x u : (duality_gap x u == 0) = ('[c,x] == '[b,u]).
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
set M := Num.max (0%R) ('[c,d]^-1 * (K - 1 - '[c, x0])).
set x := x0 + M *: d.
exists x; split.
+ apply/forallP => j.
  rewrite mulmxDr -scalemxAr mxE [X in _ + X]mxE.
  rewrite -[X in X <= _]addr0.
  apply: ler_add; first by apply: (Hx0 _).
  - apply: mulr_ge0; last by move/(_ j): Hd; rewrite mxE.
    by rewrite lter_maxr lerr.
+ rewrite vdotDr vdotZr -ltr_subr_addl.
  rewrite -mulrC -ltr_ndivr_mull //.
  rewrite lter_maxr; apply/orP; right.
  rewrite -(ltr_nmul2l Hcd) 2!mulrA mulfV; last by apply: ltr0_neq0.
  by rewrite 2!mul1r ltr_add2r gtr_addl ltrN10. 
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

End WeakDuality.

End BasicNotion.

Section Extremality.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Implicit Types x : 'cV[R]_n.

Definition is_extreme x (P: pred 'cV[R]_n)  :=
  x \in P /\ forall y z, forall lambda,
           y \in P -> z \in P -> (0 < lambda < 1) -> x = lambda *: y + (1 - lambda) *: z
           -> x = y /\ x = z.

Lemma active_ineq_eq x ( i : 'I_m) :
  i \in active_ineq A b x -> row i (A *m x) = row i b.
Proof.
rewrite inE.
move/eqP => H.
by rewrite [RHS]mx11_scalar mxE [LHS]mx11_scalar mxE H.
Qed.

Lemma inactive_ineq x :
  x \in (polyhedron A b) ->
       forall i, (i \notin (active_ineq A b x)) = ((A *m x) i 0 > (b i 0)).
Proof.
move/forallP => Hx i; move/(_ i): Hx.
rewrite inE !mxE ltr_def => H.
by rewrite andb_idr; last by move => _; apply: H.
Qed.

Definition active_ineq_mx x :=
  row_submx A (active_ineq A b x).

Definition active_ineq_col x :=
  row_submx b (active_ineq A b x).

Lemma active_ineq_mx_col_eq x : (active_ineq_mx x) *m x = active_ineq_col x.
Proof.
apply/colP => i.
rewrite -row_submx_mul 2!row_submx_mxE.
by apply/eqP; move: (enum_valP i); rewrite inE.
Qed.

Lemma polyhedron_submx x :
  x \in (polyhedron A b) -> forall (s: {set 'I_m}), x \in (polyhedron (row_submx A s) (row_submx b s)).
Proof.
move => /forallP Hx s.
apply/forallP => i; by rewrite -row_submx_mul 2!row_submx_mxE.
Qed.

Definition gap_in_direc_seq x (v : 'cV_n) :=
  [seq (if (A *m v) i 0 == 0 then 1 else ( ((A *m x) i 0 - b i 0 )) * ( `|(A *m v) i 0 |)^-1 ) |
   i <- enum 'I_m & i \notin (active_ineq A b x)].

Lemma extremality_active_ineq_part1 x :
  is_extreme x (polyhedron A b) -> (\rank (active_ineq_mx x) = n).
Proof.
move => [Hpoly Hextreme].
move/negP: notF; apply: contraNeq => Hrk.
 
set AI := active_ineq_mx x.
 
(* extract a vector v in the (right) kernel of AI *) 
have: (kermx AI^T != 0).
- rewrite kermx_eq0 -row_leq_rank -ltnNge ltn_neqAle.
  apply/andP; split; by [rewrite mxrank_tr | apply:rank_leq_row].
 
move/rowV0Pn => [v /sub_kermxP/(congr1 trmx) Hv Hv'].
rewrite trmx0 trmx_mul trmxK in Hv.
rewrite {Hrk}.
 
pose gap_seq := gap_in_direc_seq x v^T.
pose epsilon := if nilp gap_seq then 1 else min_seq gap_seq.
 
have Hepsilon : epsilon > 0.
- rewrite /epsilon; case: ifP => [ _ | /nilP H]; first by apply: ltr01.
  + rewrite min_seq_positive; last by apply/eqP.
    apply/allP => epsilon'.
    rewrite /gap_seq; move/mapP => [i]; rewrite mem_filter; move/andP => [Hi Hi'].
    case: ifP => [_ -> | /negbT H' ->]; first by apply: ltr01. 
    * apply: divr_gt0; 
      by [rewrite subr_gt0 -(inactive_ineq Hpoly) | rewrite normr_gt0]. 
 
have Hintermediate:
  (forall i, i \notin (active_ineq A b x) -> (A *m x) i 0 - epsilon *  `| (A *m v^T) i 0 | >= b i 0).
- move => i Hi.
  have Hgap_seq: (~~ nilp gap_seq).
  rewrite /gap_seq /gap_in_direc_seq /nilp size_map; apply/nilP/eqP.
  rewrite -has_filter. by apply/hasP; exists i; first by rewrite mem_enum.
  case Hvi: ((A *m v^T) i 0 == 0); first by move/eqP: Hvi => ->; rewrite normr0 mulr0 subr0; move/forallP/(_ i): Hpoly. 
  + rewrite ler_subr_addr addrC -ler_subr_addr.
    rewrite -ler_pdivl_mulr; last by rewrite normr_gt0 //; apply: negbT.
    rewrite /epsilon ifF; last by apply: negbTE.
    apply: min_seq_ler.
    rewrite /gap_seq /gap_in_direc_seq.
    apply/mapP; exists i.
    * rewrite mem_filter; apply/andP; split; by [done | rewrite mem_enum].
      by rewrite Hvi.
 
set y := x + epsilon *: v^T.
set z := x - epsilon *: v^T.
pose lambda := (1 / (2%:R)): R.
 
move/(_ y z lambda): Hextreme; case. 
- (* y \in polyhedron A b *)
  apply/forallP => i; rewrite /y mulmxDr -scalemxAr mxE [X in _ + X]mxE.
  case: (boolP (i \in (active_ineq A b x))) => [Hi | Hi].
  + move/colP/(_ (enum_rank_in Hi i)): Hv; rewrite [RHS]mxE -row_submx_mul row_submx_mxE enum_rankK_in //; move ->.
    by rewrite mulr0 addr0; move/forallP: Hpoly.
  + have H'': (A *m x) i 0 + epsilon * (A *m v^T) i 0 >= (A *m x) i 0 - epsilon * `|(A *m v^T) i 0|.
    * by rewrite (ler_add2l ((A *m x) i 0)) -[X in X * `|_|]gtr0_norm // -normrM ler_oppl -normrN; apply: ler_norm.
    move: (Hintermediate i Hi) H''; apply: ler_trans.
 
- (* z \in polyhedron A b *)
  apply/forallP => i; rewrite /z mulmxDr -scaleNr -scalemxAr scaleNr mxE [X in _ + X]mxE [X in _ - X]mxE.
  case: (boolP (i \in (active_ineq A b x))) => [Hi | Hi].
  + move/colP/(_ (enum_rank_in Hi i)): Hv; rewrite [RHS]mxE -row_submx_mul row_submx_mxE enum_rankK_in //; move ->.
    by rewrite mulr0 subr0; move/forallP: Hpoly.
  + have H'': (A *m x) i 0 - epsilon * (A *m v^T) i 0 >= (A *m x) i 0 - epsilon * `|(A *m v^T) i 0|.
    * by rewrite (ler_add2l ((A *m x) i 0)) -[X in X * `|_|]gtr0_norm // -normrM ler_opp2; apply: ler_norm.
    move: (Hintermediate i Hi) H''; apply: ler_trans.
 
- (* 0 < lambda < 1 *)
  apply/andP; split; rewrite /lambda.
  + apply: divr_gt0; by [apply: ltr01 | apply: ltr0n].
  + rewrite ltr_pdivr_mulr; last by apply: ltr0n.
    * by rewrite mul1r ltr1n.
 
- (* x = lambda *: y + (1 - lambda) *: z *)
  rewrite /y /z 2!scalerDr scalerN [X in _ + _ + X]addrC addrA -[X in X + _]addrA.
  rewrite -scaleNr -scalerDl [X in (_ - X)*: _]addrC opprD opprK addrA -mulr2n /lambda -mulrnAl divff;
    last by apply: lt0r_neq0; rewrite ltr0n.
  by rewrite addrN scale0r addr0 scalerDl addrCA scaleNr addrN scale1r addr0.
 
(* now we prove the contradiction *)
- move => /eqP Hcontra _; move: Hcontra. 
  rewrite /y eq_sym addrC -subr_eq0 -addrA addrN addr0 scalemx_eq0.
  move/orP; case => /eqP; first by move/lt0r_neq0/eqP: Hepsilon.
  move/(congr1 trmx); rewrite trmxK trmx0; by move/eqP: Hv'.
Qed.

Lemma extremality_active_ineq_part2 x :
  x \in polyhedron A b -> (\rank (active_ineq_mx x) = n) %N -> is_extreme x (polyhedron A b).
Proof.
set AI := active_ineq_mx x.
set bI := active_ineq_col x.
move => Hpoly /eqP Hrank.
rewrite /is_extreme; split; first by done.
move => y z lambda.
move/polyhedron_submx/(_ (active_ineq A b x)); rewrite inE; move => Hy.
move/polyhedron_submx/(_ (active_ineq A b x)); rewrite inE; move => Hz.
move/andP => [Hlambda Hlambda']; move/(congr1 (fun v => AI *m v)).
rewrite -subr_gt0 in Hlambda'.
 
rewrite active_ineq_mx_col_eq -/bI mulmxDr -2!scalemxAr.
have HbI : bI = lambda *: bI + (1 - lambda) *: bI.
- by rewrite scalerDl addrC -addrA scaleNr addNr addr0 scale1r.
rewrite {}HbI.
move/eqP; rewrite eq_sym -subr_eq0; move/eqP;
rewrite opprD [X in X + _]addrC addrA -[X in X + _]addrA -scalerN -scalerDr
                                [X in X - _]addrC -addrA -scalerN -scalerDr.
move/eqP; rewrite paddv_eq0; last 2 first.
- by rewrite -(scaler0 _ (lambda)) lev_pscalar // subv_ge0.
- by rewrite -(scaler0 _ (1 - lambda)) lev_pscalar // subv_ge0. 
 
rewrite 2!scaler_eq0.
move/lt0r_neq0/negbTE: Hlambda => ->; rewrite orFb.
move/lt0r_neq0/negbTE: Hlambda' => ->; rewrite orFb.
rewrite 2!subr_eq0 2!/bI -active_ineq_mx_col_eq -/AI.
move/andP; case.
- move/eqP/(row_full_inj Hrank) => ->.
- move/eqP/(row_full_inj Hrank) => ->.
by done.
Qed.

Theorem extremality_active_ineq x :
  is_extreme x (polyhedron A b) <-> (x \in (polyhedron A b)) && (\rank (active_ineq_mx x) == n) %N.
Proof.
split.
- move => H; apply/andP; split; last by apply/eqP; apply: extremality_active_ineq_part1.
  by move: H; rewrite /is_extreme; move => [H _].
- by move/andP => [? /eqP ?]; apply: extremality_active_ineq_part2.
Qed.

End Extremality.


