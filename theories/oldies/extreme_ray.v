From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc extra_big inner_product vector_order extra_matrix polyhedral_cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section ExtremeRay.

Variable R: realFieldType.
Variable n m : nat.

Implicit Types A : 'M[R]_(m,n).

Definition ray_eq (v w: 'cV[R]_n) := (scale1 v == scale1 w).

Lemma ray_eq_refl (v: 'cV[R]_n) : (ray_eq v v).
Proof.
by rewrite /ray_eq.
Qed.

Lemma ray_eq_sym (v w: 'cV[R]_n) : (ray_eq v w) = (ray_eq w v).
Proof.
by rewrite /ray_eq eq_sym.
Qed.

Lemma ray_eq_trans (u v w: 'cV[R]_n) : (ray_eq u v) -> (ray_eq v w) -> (ray_eq u w).
Proof.
by rewrite /ray_eq; move => /eqP ? /eqP ?; apply/eqP; apply:(eq_trans (y :=(scale1 v))).
Qed.

Lemma ray_eq_scale (u v: 'cV[R]_n) (a: R) : a > 0 -> (ray_eq u v = ray_eq u (a *: v)).
Proof.
by rewrite /ray_eq => ?; rewrite scale1_homo //.
Qed.

Lemma ray_eqP (v w: 'cV[R]_n) : reflect (exists lambda, lambda > 0 /\ v = lambda *: w) (ray_eq v w).
Proof.
apply: (iffP idP) => [/eqP H | [? [?] ->]]; rewrite /ray_eq; last by rewrite scale1_homo.
- rewrite [v]scale1_eq [w]scale1_eq H.
  case Hw: (w == 0).
  + exists 1; split; first by apply: ltr01.
      by move/eqP: Hw => ->; rewrite scale10 !scaler0.
  + move/negbT: Hw => Hw. exists ((norm1 v)/(norm1 w)).
    rewrite scalerA -mulrA mulVf; last by rewrite norm1_eq0.
    rewrite mulr1; split; last by done.
    apply: divr_gt0; last by rewrite norm1_gt0.
      by rewrite norm1_gt0 -scale1_eq0 H scale1_eq0.
Qed.

Lemma eq_rVP (u v : 'rV[R]_n) : (u != 0) -> reflect (exists a, a != 0 /\ u = a *: v) (u == v)%MS.
Proof.
move => Hu.
apply: (iffP idP).
- move/andP => [H _]; move/sub_rVP: H => [a H].
  exists a; split; last by done.
  by move/eqP: H; apply: contraTneq; move ->; rewrite scale0r.
- move => [a [H H']].
  apply/andP; split; first by apply/sub_rVP; exists a.
  apply/sub_rVP; exists a^-1.
  by rewrite H' scalerA mulVf // scale1r.
Qed.

Lemma eq_cVP (u v : 'cV[R]_n) : (u != 0) -> reflect (exists a, a != 0 /\ u = a *: v) (u^T == v^T)%MS.
Proof.
rewrite -(raddf_eq0 _ (@trmx_inj _ _ _)) /= => Hu.
apply: (iffP (eq_rVP _ Hu)); move => [a [H]];
rewrite -?linearZ /= => H'; exists a; split; rewrite // -?linearZ /=.
- by move/trmx_inj: H'.
- by apply/(congr1 trmx).
Qed.

Lemma pointed_coneP A :
  reflect (exists v, [/\ v != 0, v \in cone A & -v \in cone A]) (\rank A != n)%N.
Proof.
apply: (iffP idP).
- move => H. move: (rank_leq_col A) => H'.
  have HrkA: (\rank A < n)%N by rewrite ltn_neqAle; apply/andP; split.
  rewrite {H H'}.
  have: (kermx A^T != 0)%MS
    by rewrite -mxrank_eq0 mxrank_ker mxrank_tr subn_eq0 -ltnNge.
  move/rowV0Pn => [v]. move/sub_kermxP/(congr1 trmx); rewrite trmx_mul trmxK trmx0 => Hv Hv'.
  exists v^T; split.
  + rewrite -trmx0 inj_eq //; apply: trmx_inj.
    by rewrite inE Hv lev_refl.
  + by rewrite inE mulmxN oppv_ge0 Hv lev_refl.
- move => [v [Hv]]; rewrite !inE mulmxN oppv_ge0 => H H'.
  have: (A *m v = 0) by apply: lev_antisym; apply/andP; split.
  rewrite {H H'}. move/(congr1 trmx); rewrite trmx_mul trmx0.
  move/sub_kermxP/mxrankS; rewrite rank_rV -trmx0 (inj_eq (@trmx_inj _ _ _)) Hv /= mxrank_ker mxrank_tr.
  by rewrite lt0n; apply: contraNneq; move ->; rewrite subnn eq_refl.
Qed.

Lemma colinear_rays_in_cone_eq A (u v: 'cV[R]_n) :
  \rank A = n ->
  (u != 0) -> (u \in cone A) -> (v \in cone A) ->
  (u^T == v^T)%MS -> ray_eq u v.
Proof.
move => HrkA HuN0 Hu Hv.
move/(eq_cVP _ HuN0) => [a [_ Huv]].
apply/ray_eqP; exists a; split; last by done.
apply: contraT; rewrite -lerNgt.
rewrite -oppr_ge0 => Ha.
rewrite -[a]opprK scaleNr in Huv.
move/(congr1 (-%R)) : Huv; rewrite opprK => Huv.
have Hmv: -u \in cone A by rewrite Huv; apply: cone_is_closed_by_scaling.
move/eqP: HrkA; apply: contraLR; move => _.
by apply/pointed_coneP;  exists u; split.
Qed.

(*Lemma active_to_ray_eq A (I: {set 'I_m}) (u v: 'cV_n) :
  let: A' := row_submx A I in
  \rank A = n -> \rank A' = n.-1 ->
  (u != 0) -> (v != 0) ->
  (u \in cone A) -> (v \in cone A) ->
  A' *m u = 0 -> A' *m v = 0 -> ray_eq u v.
Proof.
set A' := row_submx A I.
move => HrkA HrkA' Hu Hv Hu' Hv' Hu'' Hv''.

move/eqmxP/eqmx_sym: (corank1_kermx_eq HrkA HrkA' Hv Hv'') => H.
move/eqmxP: (eqmx_trans (eqmxP (corank1_kermx_eq HrkA HrkA' Hu Hu'')) H).

move/(eq_cVP _ Hu) => [a [_ Huv]].
apply/ray_eqP; exists a; split; last by done.
apply: contraT; rewrite -lerNgt.
rewrite -oppr_ge0 => Ha.
rewrite -[a]opprK scaleNr in Huv.
move/(congr1 (-%R)) : Huv; rewrite opprK => Huv.
have Hmv: -u \in cone A by rewrite Huv; apply: cone_is_closed_by_scaling.
move/eqP: HrkA; apply: contraLR; move => _.
by apply/pointed_coneP;  exists u; split.
Qed.*)

Definition is_extreme_ray u (C: 'cV[R]_n -> Prop) :=
  [/\ u != 0, C u & forall v w, v != 0 -> w != 0 -> C v -> C w -> u = v + w
           -> ray_eq u v /\ ray_eq u w].

Lemma is_extreme_ray_closed_under_eq (u v: 'cV[R]_n) A : (* this can be generalized to more abstract class of cones *)
  ray_eq u v -> is_extreme_ray v (cone A: _ -> bool) -> is_extreme_ray u (cone A: _ -> bool).
Proof.
move/ray_eqP => [a [Ha ->]].
move => [Hv Hv' Hv''].
split.
- rewrite scalemx_eq0 negb_or Hv andbT.
  by apply: lt0r_neq0.
- by apply: cone_is_closed_by_scaling; last by apply: ltrW.
- move => y z Hy Hz Hy' Hz'.
  move/(canRL (scalerK (lt0r_neq0 Ha))); rewrite scalerDr => Hyz.
  suff: (ray_eq v (a^-1 *: y)) /\ (ray_eq v (a^-1 *: z)).
  + move => [ Hvy Hvz ].
    move: (Ha); rewrite -invr_gt0 => Ha'.
    rewrite -(ray_eq_scale _ _ Ha') in Hvy.
    rewrite -(ray_eq_scale _ _ Ha') in Hvz.
    by split; rewrite ray_eq_sym -(ray_eq_scale _ _ Ha) ray_eq_sym.
  + apply: Hv''; last by done.
    - by rewrite scalemx_eq0 negb_or Hy andbT invr_neq0 //; apply: lt0r_neq0.
    - by rewrite scalemx_eq0 negb_or Hz andbT invr_neq0 //; apply: lt0r_neq0.
    - by apply: cone_is_closed_by_scaling; last by apply: ltrW; rewrite invr_gt0.
    - by apply: cone_is_closed_by_scaling; last by apply: ltrW; rewrite invr_gt0.
Qed.

Definition active_ineq_cone (x: 'cV[R]_n) (A: 'M[R]_(m,n)) :=
  [set i : 'I_m | (A *m x) i 0 == 0 ].

Lemma active_ineq_cone_eq (A: 'M[R]_(m,n)) (u v: 'cV[R]_n) : ray_eq u v -> (active_ineq_cone u A = active_ineq_cone v A).
Proof.
move/ray_eqP => [lambda [Hlambda ->]].
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => i.
- by rewrite !inE -scalemxAr mxE mulrI_eq0; last by apply: mulfI; apply:lt0r_neq0.
- by rewrite !inE -scalemxAr [(_ *: (_ *m _)) _ _]mxE; move/eqP ->; rewrite mulr0 eq_refl.
Qed.

Lemma active_ineq_cone_sum A (x u v: 'cV[R]_n) :
  (x \in cone A) -> (u \in cone A) -> (v \in cone A) -> (x = u + v) ->
  ((active_ineq_cone x A) \subset (active_ineq_cone u A))
  /\ ((active_ineq_cone x A) \subset (active_ineq_cone v A)).
Proof.
move => Hx /forallP Hu /forallP Hv Huv.
split; apply/subsetP => i; rewrite !inE Huv mulmxDr mxE;
                           rewrite addr_ss_eq0.
- by move/andP => [? ?].
  apply/orP; left; apply/andP; split; by [ move/(_ i): Hu; rewrite mxE
                                         | move/(_ i): Hv; rewrite mxE ].
- by move/andP => [? ?].
  apply/orP; left; apply/andP; split; by [ move/(_ i): Hu; rewrite mxE
                                         | move/(_ i): Hv; rewrite mxE ].
Qed.

Lemma active_ineq_cone0 A : active_ineq_cone 0 A = [set: 'I_m].
Proof.
apply/eqP; rewrite -subTset; apply/subsetP => i.
by rewrite !inE mulmx0 mxE eq_refl.
Qed.

Section ExtRowSubmx.

Definition ext_row_submx (R : comRingType) (n m : nat) (A : 'M[R]_(m,n)) (I : {set 'I_m}) :=
  \matrix_(i,j) (if i \in I then A i j else 0).

Lemma full_ext_row_submx (R : realFieldType) (n m : nat) (A : 'M[R]_(m,n)) : ext_row_submx A [set: 'I_m] = A.
Proof.
by apply/matrixP => ? ?; rewrite /ext_row_submx mxE ifT; last by apply: in_setT.
Qed.

Lemma row_ext_row_submx (R : realFieldType) (n m : nat) (i : 'I_m) (A : 'M[R]_(m,n)) (I : {set 'I_m}) :
  row i (ext_row_submx A I) = (if i \in I then row i A else 0).
Proof.
case: ifP => [? | ?]; rewrite /row_submx; apply/rowP => ?; rewrite !mxE.
- by rewrite ifT.
- by rewrite ifF.
Qed.

Lemma ext_row_submx_submx (R : realFieldType) (m n : nat) (A : 'M[R]_(m,n)) (I I' : {set 'I_m}) : 
          (I \subset I') -> (ext_row_submx A I <= ext_row_submx A I')%MS.
Proof.
move => H.
apply/row_subP => i; rewrite row_row_submx.
case: ifP => [Hi | _]; last by apply: sub0mx.
- move/subsetP/(_ _ Hi): H => Hi'.
  apply: (submx_trans (B:=(row i (ext_row_submx A I')))); last by apply:row_sub.
  by rewrite row_ext_row_submx Hi'.
Qed.

Lemma ext_row_submx_submx_full (R : realFieldType) (m n : nat) (A : 'M[R]_(m,n)) (I : {set 'I_m}) :
  (ext_row_submx A I <= A)%MS.
Proof.
apply/row_subP => i; rewrite row_row_submx.
case: ifP => [_ | _]; by [apply: row_sub | apply: sub0mx].
Qed.

Lemma ext_row_submx_mul_eq (R : comRingType) (p q : nat) (x : 'cV[R]_q) (A : 'M[R]_(p,q)) (b : 'cV[R]_p) (I : {set 'I_p}):
A *m x = b -> (ext_row_submx A I) *m x  = (ext_row_submx b I).
Proof.
move/colP => H.
apply/colP => i.
rewrite /ext_row_submx !mxE.
case H': (i \in I).
+ rewrite (eq_bigr (fun j => (A i j) * (x j 0))) ; last by move => j _; rewrite !mxE ifT //.
  by move: (H i); rewrite mxE.
+ rewrite (eq_bigr (fun j => 0)); last by move => j _; rewrite !mxE ifF // mul0r.
  by apply: big1_eq.
Qed.

Lemma row_ext_row_submx_eq (R : comRingType) (p q : nat) (A : 'M[R]_(p,q)) (I J : {set 'I_p}):
J \subset I -> (ext_row_submx (ext_row_submx A I) J) = (ext_row_submx A J).
Proof.
move/subsetP => H.
apply/matrixP => i j.
rewrite !mxE.
case H': (i \in J).
  - apply: ifT.
    by apply: (H i H').
by done.
Qed.


Lemma corank1_kermx_eq (R : realFieldType) (m n : nat) (A : 'M[R]_(m,n)) (I : {set 'I_m}) (u : 'cV_n) :
  let: A' := ext_row_submx A I in
  \rank A = n -> \rank A' = n.-1 ->
  (u != 0) -> A' *m u = 0 -> (u^T == row_base (kermx A'^T))%MS.
Proof.
set A' := ext_row_submx A I.
move => HrkA HrkA' Hu Hu'.
apply/eqmxP; move/eqmx_sym: (eq_row_base (kermx A'^T)).
apply: eqmx_trans; apply/eqmxP.
have: (u^T <= (kermx A'^T))%MS
  by apply/sub_kermxP; rewrite -trmx_mul -trmx0; move/(congr1 trmx): Hu'.
move/mxrank_leqif_eq/geq_leqif <-.
rewrite mxrank_ker mxrank_tr HrkA' rank_rV -trmx0 (inj_eq (@trmx_inj _ _ _)) Hu /=.
by rewrite leq_subLR [X in (_ <= X)%N]addn1; apply: leqSpred.
Qed.


End ExtRowSubmx.

Definition active_ineq_cone_mx (x: 'cV_n) (A: 'M[R]_(m,n)) := row_submx A (active_ineq_cone x A).

Lemma active_ineq_cone_mx_eq A (u v: 'cV[R]_n) : ray_eq u v -> (active_ineq_cone_mx u A = active_ineq_cone_mx v A).
Proof.
by move => H; rewrite /active_ineq_cone_mx (active_ineq_cone_eq _ H).
Qed.

Lemma active_ineq_cone_mx_mul (x:  'cV_n) (A: 'M[R]_(m,n)) :
  ((active_ineq_cone_mx x A) *m x) = 0.
Proof.
apply/colP => i; rewrite !mxE /active_ineq_cone_mx.
case H: (i \in (active_ineq_cone x A)).
- rewrite (eq_bigr (fun j => (A i j) * (x j 0))); last by move => j _; rewrite /active_ineq_cone_mx !mxE ifT.
  by move: H; rewrite inE mxE; move/eqP.
- rewrite (eq_bigr (fun j => 0)); last by move => j _; rewrite /active_ineq_cone_mx mxE ifF // mul0r.
  by apply: big1_eq.
Qed.

Lemma active_ineq_cone_mx_mul_subset (x y:  'cV_n) (A: 'M[R]_(m,n)) :
  ((active_ineq_cone x A) \subset (active_ineq_cone y A)) = (((active_ineq_cone_mx x A) *m y) == 0).
Proof.
apply/idP/idP.
- move => /subsetP Hsubset; apply/eqP/colP => i. rewrite /active_ineq_cone_mx.
  case: (boolP (i \in (active_ineq_cone x A))) => [H | H].
  + rewrite mxE (eq_bigr (fun j => (A i j) * (y j 0))); last by move => ? _; rewrite /active_ineq_cone_mx !mxE ifT.
    * move/colP/(_ i): (active_ineq_cone_mx_mul y A); rewrite /active_ineq_cone_mx.
      rewrite mxE
            [\sum_j (row_submx A (active_ineq_cone y A)) i j * y j 0](eq_bigr (fun j => (A i j) * (y j 0))) //.
      - by move => ? _; rewrite mxE ifT //=; last by move/(_ i)/(_ H): Hsubset.
  + rewrite !mxE (eq_bigr (fun j => 0)); last by move => j _; rewrite !mxE ifN // mul0r.
    by apply: big1_eq.
- move/eqP => H.
  apply/subsetP => i.
  rewrite !inE => H'.
  apply/eqP; rewrite mxE (eq_bigr (fun j => (active_ineq_cone_mx x A) i j * y j 0)).
  + by move/colP/(_ i): H; rewrite !mxE.
  + by move => j _; rewrite /active_ineq_cone_mx mxE inE H'.
Qed.

Lemma inactive_ineq_cone (x: 'cV_n) A i :
  x \in cone A ->
        (i \notin (active_ineq_cone x A)) = ((A *m x) i 0 > 0).
Proof.
move/forallP/(_ i). rewrite inE !mxE ltr_def; move => H.
by rewrite andb_idr; last by move => _; apply: H.
Qed.

Lemma active_ineq_cone_mx_row i A (x v: 'cV_n) : 
    i \in (active_ineq_cone x A) -> (active_ineq_cone_mx x A *m v) i 0 = (A *m v) i 0.
Proof.
move => Hi.
rewrite mxE /active_ineq_cone_mx.
rewrite (eq_bigr (fun j => A i j * v j 0)); first by rewrite mxE.
- by move => ? _; rewrite mxE ifT.
Qed.

Lemma inactive_ineq_open_set A i (x: 'cV_n) (v: 'cV_n) :
  x \in cone A -> i \notin (active_ineq_cone x A) ->
  holds_for_small_enough (fun eps => (A *m (x + eps *: v)) i 0 > 0).
Proof.
move => Hx Hi.
rewrite /holds_for_small_enough.
pose epsilon := if (A *m v) i 0 >= 0 then 1 else (A *m x) i 0 /(- (A *m v) i 0 +1).
exists epsilon; split.
- rewrite /epsilon.
  case: ifP => H; first by apply: ltr01.
  apply negbT in H.
  rewrite -ltrNge -oppr_gt0 in H.
  move: (addr_gt0 H ltr01) => H'.
  rewrite (inactive_ineq_cone i) in Hi; last by done.
  by apply: divr_gt0.
- move => eps' Heps'.
  move/andP: Heps' => [Heps' Hee].
  rewrite mulmxDr -scalemxAr mxE [(eps' *: (A *m v)) i 0]mxE.
  case Hvi: (0 <= (A *m v) i 0).
   + rewrite (inactive_ineq_cone i) in Hi; last by done.
     rewrite addrC.
     apply ltr_paddl; last by done.
     apply mulr_ge0; last by done.
     by apply gt0_cp.
   + rewrite /epsilon ifF in Hee; last by done.
     rewrite ler_pdivl_mulr in Hee.
     rewrite mulrDr mulr1 mulrN addrC ler_sub_addr in Hee.
     by apply: (ltr_le_trans Heps' Hee).
     apply negbT in Hvi.
     rewrite -ltrNge -oppr_gt0 in Hvi.
     by apply: (addr_gt0 Hvi ltr01).
Qed.

Lemma mem_perturbation A (x: 'cV_n) (v: 'cV_n) :
  x \in cone A -> (active_ineq_cone_mx x A) *m v == 0 ->
  holds_for_small_enough (fun eps => (x + eps *: v) \in cone A).
Proof.
move => Hx Hv.
apply: small_enough_ordinal.
move => i.
case: (boolP (i \in active_ineq_cone x A)) => [H | H].
- apply/(@small_enough_eq R xpredT); last by apply:small_enough_cons.
  move => eps; rewrite mulmxDr -scalemxAr [X in _ <= X] mxE [X in _ + X]mxE.
  move/(active_ineq_cone_mx_row v): H => <-.
  move/eqP/matrixP/(_ i 0): Hv => ->; rewrite [X in _ * X]mxE mulr0 addr0.
  by move/forallP/(_ i): Hx.
- move: (inactive_ineq_open_set v Hx H).
  by apply: small_enough_imply; last by move => eps ?; apply: ltrW; rewrite mxE.
Qed.

Lemma exists_transversal_vector (p q: nat) (A : 'M[R]_(p,n)) (B : 'M[R]_(q,n)) :
  ~~(B <= A)%MS ->  exists (x: 'cV[R]_n), ((A *m x == 0) && (B *m x != 0)).
Proof.
rewrite submx_kermx; move/row_subPn => [i Hi].
exists (row i (kermx A^T))^T.
apply/andP; split.
- rewrite -[X in X *m _]trmxK -trmx_mul -trmx0.
  apply/eqP/trmx_inj.
  by rewrite -row_mul mulmx_ker row0.
- rewrite -[X in X *m _]trmxK -trmx_mul -trmx0.
  by apply/eqP; move/trmx_inj/sub_kermxP; apply/negP.
Qed.

Lemma partial_completion (p q: nat) (A: 'M[R]_(p,n)) (B: 'M[R]_(q,n)) :
  (A <= B)%MS -> (\rank A < (\rank B).-1)%N ->
    exists (i j: 'I_q), ~~(row i B <= (col_mx A (row j B)))%MS && ~~(row j B <= (col_mx A (row i B)))%MS.
Proof.
move => HAB HrArB.
 
have HAB': ~~(B <= A)%MS.
- apply/negP; move/mxrankS.
  move/(leq_trans (leq_trans HrArB (leq_pred (\rank B)))).
  by rewrite ltnn.
move/row_subPn: (HAB') => [i HrowiB].
 
have HrB: (\rank B > 0)%N.
- move: HAB'; rewrite lt0n; apply: contraNneq.
  move/eqP; rewrite mxrank_eq0; move/eqP ->.
  by apply: sub0mx.
 
set AiB := col_mx A (row i B).
have: ~~(B <= AiB)%MS.
- apply/negP; move/mxrankS; move/eqmxP/eqmx_rank: (addsmxE A (row i B)) <- => Hcontra.
  move: (fst (mxrank_adds_leqif A (row i B))) => H.
  move: (rank_leq_row (row i B)); rewrite -(leq_add2l (\rank A)).
  move/(leq_trans H); rewrite {H} addn1 => H.
  move/(leq_trans H): HrArB; rewrite {H}.
  move/(leq_trans Hcontra).
  by rewrite -[X in (X <= _)%N]prednK; first by rewrite ltnn.
move/row_subPn => [j HrowjB].
 
exists i; exists j; apply/andP; split; last by done.
apply/negP; move/submxP => [x].
rewrite -[x]hsubmxK mul_row_col.
rewrite [rsubmx x]mx11_scalar -scalemx1 -scalemxAl mul1mx. 
set z := (rsubmx x) 0 0.
 
case: (altP (z =P 0)) => [-> | Hz].
- rewrite scale0r addr0 => H.
  move: HrowiB; apply/negP; rewrite negbK.
  by apply/submxP; exists (lsubmx x). 
- move/(congr1 (+%R (-(lsubmx x *m A)))); rewrite addrA addNr add0r.
  move/(congr1 ( *:%R (z^-1))).
  rewrite [in RHS]scalerA mulVf // scale1r.
  rewrite scalerDr -scaleN1r scalerA mulrN1.
  rewrite -[row i B]mul1mx 2!scalemxAl scalemx1 => H; symmetry in H.
  move: HrowjB; apply/negP; rewrite negbK.
  apply/submxP; exists (row_mx (- z^-1 *: lsubmx x) (z^-1%:M)).
  by rewrite mul_row_col.
Qed.

Lemma exists_transversal_vector_cone (p q: nat) (A : 'M[R]_(p,n)) (B : 'M[R]_(q,n)) :
  (A <= B)%MS -> (\rank A < (\rank B).-1)%N ->
  exists v, [&& (v \notin (cone B)), (-v \notin (cone B)) & (A *m v == 0)].
Proof.
move => H H'.
move: (partial_completion H H') => [i [j /andP [Hi Hj]]].
move: (exists_transversal_vector Hi) => [vi /andP [Hvi]].
- move: Hvi; rewrite mul_col_mx -col_mx0 -row_mul; move/eqP/eq_col_mx => [HviA].
  move/colP/(_ 0); rewrite mxE [in RHS]mxE => HviB.
rewrite scalar_mx_eq0 -row_mul mxE => Hvi'.
move: (exists_transversal_vector Hj) => [vj /andP [Hvj]].
- move: Hvj; rewrite mul_col_mx -col_mx0 -row_mul; move/eqP/eq_col_mx => [HvjA].
  move/colP/(_ 0). rewrite mxE [in RHS]mxE => HvjB.
rewrite scalar_mx_eq0 -row_mul mxE => Hvj'.
set Bi_vi := (B *m vi) i 0 in Hvi'.
set Bj_vj := (B *m vj) j 0 in Hvj'.
 
exists ((Num.sg Bi_vi) *: vi - (Num.sg Bj_vj) *: vj).
apply/and3P; split.
- rewrite negb_forall; apply/existsP; exists j.
  rewrite mxE mulmxDr mulmxN -2!scalemxAr 2!mxE [X in _ + X]mxE [X in _ - X]mxE.
  by rewrite HviB mulr0 add0r oppr_ge0 -ltrNge -normrEsg normr_gt0.
- rewrite negb_forall; apply/existsP; exists i.
  rewrite mxE mulmxN mxE mulmxDr mulmxN -2!scalemxAr 2!mxE [X in _ + X]mxE [X in _ - X]mxE.
  by rewrite HvjB mulr0 subr0 oppr_ge0 -ltrNge -normrEsg normr_gt0.  
- by rewrite mulmxDr mulmxN -2!scalemxAr HviA HvjA 2!scaler0 subr0 eq_refl.
Qed.

Lemma active_inequality_transversal_vector A (x v: 'cV_n) :
  let: AIx := active_ineq_cone_mx x A in
  x \in (cone A) -> v \notin (cone A) -> AIx *m v = 0 ->
    exists lambda: R, [&& lambda > 0, ((x + lambda *: v) \in (cone A)) & (\rank (active_ineq_cone_mx x A) < \rank (active_ineq_cone_mx (x + lambda *: v) A))%N].
Proof.
move => Hx Hv Hv'.
 
set S := [seq i <- enum 'I_m | (A *m v) i 0 < 0].
have HS': all (predC (mem (active_ineq_cone x A))) S.
- apply/allP => i; rewrite mem_filter => /andP [Hi Hi'].
  apply/negP; move => H.
  move/matrixP/(_ i 0): Hv'; rewrite /active_ineq_cone_mx mxE.
  rewrite (eq_bigr (fun j => (A i j) * (v j 0))); last by move => ? _; rewrite mxE /= ifT.
  by move => H'; move: Hi; rewrite mxE H' mxE ltrr.
 
have HS: (S != [::]).
- move/existsP: Hv; move => [i Hi].
  rewrite -ltrNge [X in _ < X]mxE in Hi.
  by rewrite -has_filter; apply/hasP; exists i; first by apply:mem_enum. 
 
set Sgap := [seq ((A *m x) i 0)/(- (A *m v) i 0) | i <- S].
have HSgap: (Sgap != [::]).
  by apply/eqP/nilP; rewrite /S /nilp size_map; apply/nilP/eqP.
 
pose lambda := min_seq Sgap.
have Hlambda: lambda > 0.
- rewrite min_seq_positive //.
  apply/allP => ?; move/mapP => [i Hi].
  move: (Hi); rewrite mem_filter; move/andP => [Hi' _] -> /=.
  apply: divr_gt0; last by rewrite oppr_cp0.
  by move/allP/(_ i Hi): HS'; rewrite -inactive_ineq_cone //.
 
exists lambda; apply/and3P; split; first by done.
 
- apply/forallP => i; rewrite mxE mulmxDr mxE -scalemxAr [X in _+X]mxE. 
  case: (boolP (i \in S)) => [Hi |].
  + move: (Hi); rewrite mem_filter; move => /andP [Hi' _].
    rewrite -[X in _ + X]opprK -mulrN subr_ge0 -ler_pdivl_mulr; last by rewrite oppr_cp0.
    by apply: min_seq_ler; apply: map_f.
  + rewrite mem_filter.
    have ->: (i \in enum 'I_m) by apply:mem_enum. 
    rewrite andbT -lerNgt => Hi.
    apply: addr_ge0; first by move/forallP/(_ i): Hx; rewrite mxE.
    by apply: mulr_ge0; first by apply:ltrW.
 
- move/hasP: (min_seq_eq HSgap) => [? /=]; move/mapP => [j Hj ->].
  rewrite -/lambda; move/eqP => Hlambda'. 
  have Hj': (A *m (x + lambda *: v)) j 0 = 0.
  + rewrite mulmxDr mxE -scalemxAr [X in _+X]mxE.
    rewrite Hlambda' -mulrA invrN mulNr mulVf; first by rewrite mulrN mulr1 addrN.
    by apply: ltr0_neq0; move: Hj; rewrite mem_filter; move/andP => [? _].
  have Hsubset : {subset (active_ineq_cone x A) <= (active_ineq_cone (x + lambda *: v) A)}.
  + move => i Hi.
    move: (Hi); rewrite !inE => /eqP Hi'. rewrite mulmxDr mxE -scalemxAr [X in _+X]mxE {}Hi' add0r.
    move/colP/(_ i): Hv'; rewrite active_ineq_cone_mx_row //.
    by move ->; rewrite mxE mulr0 eq_refl.
  have H: (active_ineq_cone_mx x A <= active_ineq_cone_mx (x + lambda *: v) A)%MS.
  + apply/row_subP => i.
    rewrite row_row_submx.
    case: ifP; last by move => _; apply: sub0mx.
    * move/(Hsubset _) => H.
      apply: (submx_trans _ (row_sub i (active_ineq_cone_mx (x + lambda *: v) A))).
      by rewrite row_row_submx ifT.
  move/ltn_leqif: (mxrank_leqif_sup H) ->.
  apply/row_subPn; exists j; rewrite row_row_submx ifT; last by rewrite inE Hj' eq_refl.
  apply/negP; move/submxP => [y].
  move/(congr1 (mulmx^~ x)); rewrite -mulmxA (active_ineq_cone_mx_mul x A) mulmx0.
  move/rowP/(_ 0); rewrite [in RHS]mxE -row_mul mxE => H'.
  by move/allP/(_ j Hj): HS'; rewrite /= inactive_ineq_cone // H' ltrr. 
Qed.

(* Lemma inc_rank_active_ineq  (x: 'cV_n) (A: 'M[R]_(m,n)) : (* Proposition 4 (a) of Fukuda and Prodon *)
  forall k , k \notin active_ineq_cone x A -> 
    \rank (((active_ineq_cone_mx x A) + (row k A))%MS ) == ((\rank (active_ineq_cone_mx x A)) + 1)%N.
Proof.
set AI := active_ineq_cone_mx x A.
move => k.
set Ak := row k A.
apply: contraLR. 
rewrite neq_ltn; move/orP; case.
- rewrite [(_ + 1)%N]addn1 ltnS.
  move/(conj (mxrankS (addsmxSl AI (row k A))))/andP.
  rewrite -eqn_leq; move/eqP => H.
  move: (mxrank_leqif_sup (addsmxSl (AI) Ak)). rewrite -{}H; move/leqif_refl.
  rewrite addsmx_sub; move/andP => [_].
  move/submxP => [D]; move/(congr1 (mulmx^~ x)); rewrite -mulmxA.
  rewrite (active_ineq_cone_mx_mul x A) mulmx0 /Ak.
  by rewrite -row_mul; move/rowP/(_ 0)/eqP; rewrite ![_ 0 0]mxE inE negbK. 
- have H: (\rank (AI + Ak) <= ((\rank AI) +1))%N.
  + move: (rank_leq_row Ak); rewrite -(leq_add2l (\rank AI) (\rank Ak) 1). 
    move/leq_of_leqif: (mxrank_adds_leqif AI Ak).
    by apply: leq_trans.  
  by move/(leq_ltn_trans H); rewrite ltnn.
Qed. *)

Lemma rank_in_active_cone A (x: 'cV_n) : (* Proposition 4 (b) of Fukuda and Prodon *)
  let: AIx := active_ineq_cone_mx x A in
  let: k := (n - \rank AIx)%N in
  x \in cone A -> x != 0 ->
        exists S:'M[R]_(k,n), [/\ \rank S = k, (S <= kermx (AIx^T))%MS & [forall i, (row i S)^T \in cone A]].
Proof.
move => Hx Hneq0.
set AI := active_ineq_cone_mx x A.
pose kerAI := kermx AI^T.
set k := (n - \rank AI)%N.
 
have Hrk_kerAI : \rank kerAI = k.
- by rewrite mxrank_ker mxrank_tr.
have Hrkx : \rank x^T = 1%N.
- by rewrite rank_rV; apply/eqP; rewrite eqb1 -trmx0 inj_eq //; apply: trmx_inj.
 
have Hx_in_kerAI : (x^T <= kerAI)%MS.
- apply/sub_kermxP; rewrite -trmx_mul.
  apply/(canLR (@trmxK _ _ _)); rewrite trmx0.
  by apply: (active_ineq_cone_mx_mul x A).
 
have Hkpos: (k > 0)%N.
  by move/mxrankS: Hx_in_kerAI; rewrite Hrkx Hrk_kerAI.
 
set M := (kerAI :\: x^T)%MS.
have HrkM : (\rank M = k-1)%N.
- apply/(canRL (addnK _)).
  + have <- : (\rank (kerAI :&: x^T) = 1)%N by move/capmx_idPr: Hx_in_kerAI ->.
    by rewrite addnC mxrank_cap_compl.
 
have Hcast_mx : (\rank M + 1 = (k-1)+1)%N.
- by rewrite HrkM subnK //.
 
set S' := (castmx (Hcast_mx, erefl n) (col_mx (row_base M) x^T)).
- have Hrk_S' : \rank S' = k.
  suff: \rank ((row_base M + x^T)%MS) = k
    by rewrite rank_castmx; move/eqmxP/eqmx_rank: (addsmxE (row_base M) x^T) ->.
  rewrite mxrank_disjoint_sum.
  move/eqmxP/eqmx_rank: (eq_row_base M) ->; rewrite HrkM Hrkx subnK //.
  apply/eqP; move/eqmx_eq0: (cap_eqmx (eq_row_base M) (eqmx_refl x^T)) ->.
  by apply/eqP; apply: capmx_diff.
 
have HMkerAI : (row_base M <= kerAI)%MS.
- suff: (M <= kerAI)%MS
    by move/eqmxP/andP: (eq_row_base M) => [? _]; apply: submx_trans.
  by apply: diffmxSl.
 
have [eps [Heps Heps']]:
  holds_for_small_enough (fun eps => [forall i, x + eps *: col i (castmx (erefl n, HrkM) (row_base M)^T) \in cone A]).
- apply: small_enough_fintype.
  move => ?; apply: mem_perturbation; first by done.
  rewrite -col_mul mulmx_cast -castmx_mul -[active_ineq_cone_mx x A](trmxK) -trmx_mul.
  by move/sub_kermxP: HMkerAI ->; rewrite trmx0 castmx_const col0 eq_refl.
move/(_ eps): Heps'; rewrite Heps lerr /=; move/(_ is_true_true) => Heps'.
 
pose P:'M[R]_((k-1)+1) := block_mx (eps%:M) (const_mx 1) 0 1. 
pose S := P *m S'.
have HrkS : \rank S = k.
- rewrite -mxrank_tr trmx_mul mxrankMfree; first by rewrite mxrank_tr.
  apply/eqP; rewrite mxrank_tr; apply: mxrank_unit.
  rewrite unitmxE; rewrite det_ublock det_scalar det1 mulr1.
  by apply: unitrX; apply: unitf_gt0.
 
suff: exists S: 'M[R]_((k-1)+1,n), [/\ \rank S = k, (S <= kermx (AI^T))%MS & [forall i, (row i S)^T \in cone A]].
- move => [S0 [? ? H0]]; exists (castmx (subnK Hkpos, erefl n) S0); split.
  + by rewrite rank_castmx.
  + by rewrite submx_castmx.
  + apply/forallP => i; rewrite row_castmx castmx_id.
    by move/forallP/(_ (cast_ord (esym (subnK Hkpos)) i)): H0.
 
exists S; split; first by done.
- apply: mulmx_sub.
  by rewrite submx_castmx col_mx_sub; apply/andP; split.
- apply/forallP => j.
  rewrite tr_row /S mulmx_cast (@castmx_block _ _ _ _ _ _ _ _ _ _ (esym HrkM)).
  rewrite castmx_col mul_block_col -!castmx_mul /= !mul1mx !castmx_const
    !castmx_id mul0mx add0r tr_col_mx trmxK.
  rewrite -[j]splitK; case: splitP => j' Hj; last by rewrite colKr col_id.
  + rewrite colKl !raddfD /=.
    rewrite [X in _ + col _ X]trmx_mul trmxK trmx_const col_mul col_const [const_mx _]mx11_scalar mxE mulmx1.
    rewrite trmx_mul trmx_cast mulmx_cast castmx_id tr_scalar_mx -scalemx1 -scalemxAr mulmx1 addrC linearZ /= esymK.
    by move/forallP/(_ j'): Heps'.
Qed.

Lemma rank_active_leq_dim_minus_two (x: 'cV[R]_n) (A: 'M[R]_(m,n)) : (* Proposition 4 (c) of Fukuda and Prodon *)
  let: AIx := active_ineq_cone_mx x A in
  (x \in cone A) -> (\rank AIx < (\rank A).-1)%N ->
  exists (y z: 'cV_n), [/\ (\rank (active_ineq_cone_mx y A) > \rank AIx)%N, 
                           (\rank (active_ineq_cone_mx z A) > \rank AIx)%N,
                           x = y + z, y \in cone A & z \in cone A].
Proof.
move => Hx.
rewrite /active_ineq_cone_mx => HrkAI.
move: (exists_transversal_vector_cone (row_submx_submx_full A (active_ineq_cone x A)) HrkAI) => [v /and3P [Hv Hv' /eqP Hv'']].
move: (active_inequality_transversal_vector Hx Hv Hv'') => [lambda /and3P [Hlambda Hxv Hxv']].
move/(congr1 -%R): Hv''; rewrite oppr0 -mulmxN => Hv''.
move: (active_inequality_transversal_vector Hx Hv' Hv'') => [mu /and3P [Hmu Hxmv Hxmv']].
rewrite scalerN in Hxmv Hxmv'.
 
pose a := mu / (lambda + mu).
have Ha : a > 0 by apply: divr_gt0; last by apply: addr_gt0.
pose b := lambda / (lambda + mu).
have Hb : b > 0 by apply: divr_gt0; last by apply: addr_gt0.
have Hab : a + b = 1
  by rewrite /a /b -mulrDl addrC mulfV; last by  apply/lt0r_neq0; apply: addr_gt0.
have Hab' : a * lambda - b * mu = 0.
- by rewrite /a /b mulrC mulrA [X in _ -X]mulrC [X in _ -X]mulrA -mulNr -mulrDl [X in (_ - X)/_]mulrC addrN mul0r.
 
exists (a *: (x + lambda *: v)); exists (b *: (x - mu *: v)); split.
- by rewrite (@active_ineq_cone_eq _ (a *: (x + lambda *: v)) (x + lambda *: v));
    last by apply/ray_eqP; exists a; split.
- by rewrite (@active_ineq_cone_eq _ (b *: (x - mu *: v)) (x - mu *: v));
    last by apply/ray_eqP; exists b; split.
- rewrite 2!scalerDr [X in X + _]addrC -addrA [X in _ + X]addrA -scalerDl.
  rewrite Hab scale1r.
  rewrite [X in _ + X]addrC scalerN addrA 2!scalerA -scaleNr -scalerDl.
  by rewrite Hab' scale0r add0r.
- by apply: cone_is_closed_by_scaling; last by apply: ltrW.
- by apply: cone_is_closed_by_scaling; last by apply: ltrW.
Qed.

Lemma extreme_rayP A (x: 'cV_n) : (* Only if part of Proposition 5 (a) of Fukuda and Prodon *)
  (\rank A = n)%N -> 
  reflect (is_extreme_ray x (cone A: _ -> bool))
          [&& (x != 0), (x \in cone A) & (\rank (active_ineq_cone_mx x A) == n.-1)].
Proof.
move => HrkA.
set AI := active_ineq_cone_mx x A.
apply: (iffP idP) => [/and3P [Hx Hx' /eqP Hx'']| [Hx Hx' Hx'']].
- split; try by done.
  + move => v w Hv Hw Hv' Hw' Hvw.
    move: (active_ineq_cone_sum Hx' Hv' Hw' Hvw).
    rewrite 2!active_ineq_cone_mx_mul_subset /active_ineq_cone_mx; move => [/eqP Hv'' /eqP Hw''].
    split.
    * apply: (colinear_rays_in_cone_eq HrkA); try by done.
      apply/eqmxP. apply: (eqmx_trans (B := (row_base (kermx AI^T)))).
      - apply/eqmxP; apply: corank1_kermx_eq; try by done.
          by apply: active_ineq_cone_mx_mul.
      - apply/eqmx_sym/eqmxP; apply: corank1_kermx_eq; try by done.
    * apply: (colinear_rays_in_cone_eq HrkA); try by done.
      apply/eqmxP. apply: (eqmx_trans (B := (row_base (kermx AI^T)))).
      - apply/eqmxP; apply: corank1_kermx_eq; try by done.
          by apply: active_ineq_cone_mx_mul.
      - apply/eqmx_sym/eqmxP; apply: corank1_kermx_eq; try by done.
- apply/and3P; split; try by done.
  have HrkAI: (\rank AI <= n.-1)%N.
    move: Hx; rewrite -ltnS; apply: contraLR.
    rewrite -ltnNge negbK; move => Haux.
    move:(leq_ltn_trans (leqSpred n) Haux) => Haux'.
    move:(rank_leq_col AI) => Haux''.
    rewrite ltnS in Haux'.
    have: (n ==(\rank AI))%N by rewrite eqn_leq; apply/andP; split.
    move/eqP; rewrite {Haux Haux' Haux''}.
    move => HrkAI.
    move/eq_leq in HrkAI; rewrite col_leq_rank in HrkAI; move/row_fullP in HrkAI.
    move: HrkAI.
    case => B.
    move/(congr1 (fun C => C *m x)).
    move:(active_ineq_cone_mx_mul x A) => Haux.
    rewrite mul1mx /AI -mulmxA Haux mulmx0; move => H; symmetry in H. 
    by move/eqP: H.
  apply: contraT.
  move => HrkAI'.
  have HrkAI'': (\rank AI < n.-1)%N.
    by rewrite ltn_neqAle; apply/andP; split. rewrite {HrkAI HrkAI'}.
  rewrite -[X in X.-1]HrkA in HrkAI''.
  move:(rank_active_leq_dim_minus_two Hx' HrkAI'').
  case => y [z].
  move => [Hrky Hrkz Hxyz Hy' Hz'].
  have Hy: y != 0.
    move: Hrkz; apply: contraTneq; move => Haux.
    rewrite Haux add0r in Hxyz.
    by rewrite Hxyz ltnn.
  have Hz: z != 0.
    move: Hrky; apply: contraTneq; move => Haux.
    rewrite Haux addr0 in Hxyz.
    by rewrite Hxyz ltnn.
  move: (Hx'' y z Hy Hz Hy' Hz' Hxyz).
  move => [Hxy Hxz].
  move: (active_ineq_cone_mx_eq A Hxy) => HxyActive.
  move: Hrky.
  by rewrite HxyActive ltnn.
Qed.

Definition set_of_bases A := [set I : {set 'I_m} | \rank (row_submx A I) == n.-1].

Definition basis_to_ray A (I: {set 'I_m}) :=
  let: v := conform_mx (0: 'cV[R]_n) (row_base (kermx (row_submx A I)^T))^T in
  if (v \notin (cone A)) && (-v \notin (cone A)) then 0
  else
    if v \in cone A then v
    else -v.

(*Lemma basis_to_ray_is_extreme A (I: {set 'I_m}) :
  (n > 0)%N -> \rank A = n -> \rank (row_submx A I) = n.-1 -> (basis_to_ray A I != 0) ->
  (is_extreme_ray (basis_to_ray A I) (cone A: 'cV_n -> bool)).
Proof.
set v := basis_to_ray A I.
move => Hn HrkA HrkAI Hv.

have Hdim_kerAI: (\rank (kermx (row_submx A I)^T) = 1)%N.
- rewrite mxrank_ker mxrank_tr HrkAI -subn1 subKn //.

apply/(extreme_rayP _ HrkA)/and3P; split; try by done.
  
  
set v' := castmx (erefl n, Hdim_kerAI) (row_base (kermx (row_submx A I)^T))^T.
have Hv : v' = conform_mx (0: 'cV[R]_n) (row_base (kermx (row_submx A I)^T))^T.
- rewrite -[v'](conform_mx_id (0: 'cV[R]_n)) /v'.
  apply: conform_castmx.
*)

Definition set_of_extreme_rays A :=
  undup (filter (fun v => (v != 0)) (map (basis_to_ray A) (enum (set_of_bases A)))).

Lemma set_of_extreme_rays_is_extreme A (u: 'cV_n) : 
  (n > 0)%N -> (\rank A = n) -> u \in (set_of_extreme_rays A) -> is_extreme_ray u (cone A: 'cV_n -> bool).
Proof.
move => Hn HrkA.
rewrite mem_undup mem_filter => [/andP [Hu /mapP [I Hu']] Hu''].
rewrite Hu'' in Hu.
  move: Hu'; rewrite mem_enum inE => /eqP Hu'.
  apply/(extreme_rayP _ HrkA).
  apply/and3P. split. 
  + by rewrite Hu''.
  + rewrite  Hu'' /basis_to_ray.
    case: ifP => [_ | ]; first by apply: cone_mem0.
    case: ifP => [| _]; first by done.
      by rewrite /=; move/negbFE.
  + rewrite /active_ineq_cone_mx eqn_leq.
    set I' := active_ineq_cone (basis_to_ray A I) A.
    apply/andP; split.
    * apply: (non_trivial_ker Hu).
      rewrite Hu''.
      by apply: active_ineq_cone_mx_mul.
    * rewrite -Hu'; apply/mxrankS; apply: row_submx_submx.
      apply/subsetP => i Hi; rewrite inE; apply/eqP.
      suff: (row_submx A I) *m (basis_to_ray A I) = 0.
      - move => H; rewrite mxE; rewrite (eq_bigr (fun j => (row_submx A I) i j * (basis_to_ray A I) j 0)).
        + by move/colP/(_ i): H; rewrite !mxE.
          rewrite Hu''.
        + by move => j _; rewrite /row_submx mxE Hi.
      rewrite /basis_to_ray.
      case: ifP => [_ | _]; first by rewrite mulmx0.
      case: ifP => [_ | _];
        rewrite /= -(conform_castmx (erefl n, corank1_kermx Hn Hu')) conform_mx_id ?mulmxN;
        do ?[apply/(canLR (@opprK _)); rewrite oppr0]; 
        apply/(trmx_inj); rewrite trmx_mul trmx_cast /= trmx0 trmxK; apply/sub_kermxP;
        by rewrite submx_castmx; move/eqmxP/andP: (eq_row_base (kermx (row_submx A I)^T)) => [? _].
Qed.

Lemma set_of_extreme_raysE A (x: 'cV_n) : (* essentially Proposition 5 (a) of Fukuda and Prodon *)
  (n > 0)%N -> (\rank A = n) ->
  (is_extreme_ray x (cone A: 'cV_n -> bool) <-> exists u, (u \in (set_of_extreme_rays A)) && (ray_eq x u)).
Proof.
move => Hn HrkA; split. 
- move/(extreme_rayP _ HrkA)/and3P => [Hx Hx'].
  rewrite /active_ineq_cone_mx => /eqP Hx''.
  set I := active_ineq_cone x A.
  move/eqmxP: (corank1_kermx_eq HrkA Hx'' Hx (active_ineq_cone_mx_mul x A)) => HxI'.
  move/eqmx_sym: (eqmx_cast (row_base (kermx (row_submx A I)^T)) (corank1_kermx Hn Hx'', erefl n)) => HxI''.
  move/eqmxP: (eqmx_trans HxI' HxI''); rewrite {HxI' HxI''}.
  rewrite -[(castmx _ _)]trmxK trmx_cast /=.
  move/(eq_cVP _ Hx) => [a [Ha HxI]].
  suff: (basis_to_ray A I = (Num.sg(a) * a^-1) *: x).
  + have Ha' : Num.sg(a) * a^-1 > 0 by rewrite -sgrV -normrEsg normr_gt0 invr_eq0 //. 
  + move => H.
    exists (basis_to_ray A I); apply/andP; split.
    * rewrite mem_undup mem_filter; apply/andP;  split; last first.
      - rewrite map_f // mem_enum inE /I.
        by apply/eqP.
      - rewrite H scalemx_eq0 negb_or Hx andbT.
        by apply: lt0r_neq0.
    * rewrite ray_eq_sym; rewrite H; apply/ray_eqP.
      by exists (Num.sg a / a); split.
  + rewrite /basis_to_ray.
    rewrite -(conform_castmx (erefl n, corank1_kermx Hn Hx'')) conform_mx_id.
    move/(canLR (scalerK Ha)): HxI <-.
    rewrite [a^-1]numEsg sgrV -!scalerA.
    have Hxa : (`|a^-1| *: x \in cone A) by apply: cone_is_closed_by_scaling.
    case: (sgrP a) => [?|_|_]; first by move/eqP in Ha.
    - by rewrite !scale1r Hxa /=.
    - rewrite !scaleNr !scale1r opprK.
      rewrite Hxa /= andbF; apply: ifF.
      apply:negbTE. apply: contraT. rewrite negbK => Hxa'.
      move/eqP: HrkA.
      apply: contraLR => _; apply/pointed_coneP; exists (`|a^-1| *: x); split; try by done.
      * rewrite scalemx_eq0 negb_or Hx andbT.
        by rewrite normr_eq0 invr_eq0 //.
- move => [u].
  move => /andP [Hu Hux].
  apply: (is_extreme_ray_closed_under_eq Hux).
  by apply: (set_of_extreme_rays_is_extreme Hn HrkA Hu).
Qed.

Theorem Minkowski' A :
  (n > 0)%N -> (\rank A = n) ->
  forall x : 'cV[R]_n, x \in cone A <-> is_in_conic_hull (set_of_extreme_rays A) x.
Proof.
move => Hn HrkA x.
split; last first.
- apply: conic_hull_incl_cone.
  + move => v Hv.
    suff: (is_extreme_ray v (cone A: _ -> bool)) by move/(extreme_rayP _ HrkA)/and3P => [_ ? _].
    by apply/(set_of_extreme_raysE _ Hn HrkA); exists v; apply/andP; split; last by apply:ray_eq_refl.
 
- move: x.
  suff: forall x, x != 0 -> x \in cone A -> is_in_conic_hull (set_of_extreme_rays A) x.
  + move => H x.
    case: (altP (x =P 0%R)) => [-> _| ]; by [apply: zero_is_in_conic_hull| apply: H x].
  suff: forall k, (k <= n.-1)%N -> (forall x, \rank (active_ineq_cone_mx x A) = k -> x != 0 -> x \in cone A -> is_in_conic_hull (set_of_extreme_rays A) x).
  + move => H x Hx; move: H.
    by move/(_ (\rank (active_ineq_cone_mx x A)) (non_trivial_ker Hx (active_ineq_cone_mx_mul x A)) x (erefl _) Hx).
 
  apply: decr_strong_ind.
  (* base case, rk = n.-1 *)
  * move => x /eqP Hrk HxN0 Hx.
    suff: exists u, (u \in (set_of_extreme_rays A)) && (ray_eq x u).
    - move => [u /andP [Hu /ray_eqP [a [Ha ->]]]].
      apply: conic_hull_is_closed_by_scaling; last by apply: ltrW.
      by apply: conic_hull_incl_self; first by apply: undup_uniq.
    rewrite -set_of_extreme_raysE //.
    by apply/(extreme_rayP _ HrkA)/and3P; split.
  * move => k /andP [Hk Hk'] IH x Hrk HxN0 Hx.
    have: (\rank (active_ineq_cone_mx x A) < (\rank A).-1)%N.
    - rewrite HrkA Hrk prednK //.
    move/(rank_active_leq_dim_minus_two Hx) => [y [z [Hrky Hrkz Hxyz Hy Hz]]].
    have HyN0: y != 0.
    - move: Hrkz; apply: contraTneq; move => Hy0.
      move: Hxyz; rewrite Hy0 add0r; move ->.
      by rewrite ltnn.
    have HzN0: z != 0.
    - move: Hrky; apply: contraTneq; move => Hz0.
      move: Hxyz; rewrite Hz0 addr0; move ->. 
      by rewrite ltnn.
 (*   have: (y != z).
    - move: Hrky; apply: contraTneq; move => Hyz.
      move: Hxyz; rewrite Hyz; move ->.
      rewrite -mulr2n -scaler_nat.
      rewrite /active_ineq_cone_mx (active_ineq_cone_eq _ (v:=z)); first by rewrite ltnn. 
      rewrite ray_eq_sym -ray_eq_scale; by [rewrite ray_eq_refl | apply: ltr0Sn].*)
    suff: is_in_conic_hull ([:: y; z]) x; last first.
    - pose lx := fun (v:'cV[R]_n) => 1:R.
      exists lx; split.
      + by move => ? _; rewrite /lx; apply: ler01.
      + by rewrite big_cons big_seq1 /lx !scale1r.
    - apply: conic_hull_incl.
      move => v; rewrite mem_seq2.
      move/orP; case; move/eqP ->.
      + apply: (IH (\rank (active_ineq_cone_mx y A))); rewrite //.
        apply/andP; split; first by rewrite -[k]prednK // -Hrk.
        apply: (non_trivial_ker HyN0 (active_ineq_cone_mx_mul y A)).
      + apply: (IH (\rank (active_ineq_cone_mx z A))); rewrite //.
        apply/andP; split; first by rewrite -[k]prednK // -Hrk.
        apply: (non_trivial_ker HzN0 (active_ineq_cone_mx_mul z A)).
Qed.

Lemma generating_set_contains_extreme_rays (S: seq 'cV[R]_n) (u: 'cV[R]_n) : (uniq S) ->
  is_extreme_ray u (is_in_conic_hull S) -> exists v, v \in S /\ ray_eq u v.
Proof.
move => Huniq.
rewrite /is_extreme_ray.
move => [Hu0 [lu [Hlu]]].
rewrite (big_rem_idx (fun v => ((lu v > 0) && (v != 0)))) /=; last first.
  - move => i Hi; move/nandP.
    case.
    + by rewrite -lerNgt; move => H; move/pair_andP/andP: (H, (Hlu _ Hi)); 
      move/ler_asym => ->; apply: scale0r.
    + by move/negbNE/eqP => Hi'; rewrite Hi' scaler0.
rewrite {Hlu} -big_filter.
set Sp := [seq i <- S | 0 < lu i & i != 0].
have HSp : subseq Sp S.
  - by rewrite /Sp; apply: filter_subseq.
have HSp': all [pred i | 0 < lu i & i != 0] Sp.
  - by rewrite /Sp; apply: filter_all.
move: HSp HSp'; case: Sp => [|v Sp']; first by rewrite big_nil; move/eqP: Hu0.
rewrite big_cons; move => /mem_subseq_nnil [Hv HSp] /andP [/= /andP [Hlv Hv'] /allP /= HSp'].
set w := \sum_(j <- Sp') lu j *: j.
move => Hu; move/(_ (lu v *: v) w) => H.
exists v; split; first by done.
suff: ray_eq u (lu v *: v).
  - rewrite /ray_eq; rewrite scale1_homo //.
case: (altP (w =P 0)).
  - by move => Hw; rewrite Hw addr0 in Hu; rewrite Hu; apply: ray_eq_refl.
  - move => Hw.
    suff: ray_eq u (lu v *: v) /\ ray_eq u w.
      by case.
    apply: H; last by done.
      + rewrite scaler_eq0; apply/norP. split; last by done. by apply: lt0r_neq0. 
      + by done.
      + apply: conic_hull_is_closed_by_scaling; last by apply: ltrW.
        by apply: conic_hull_incl_self.
      + apply: (conic_hull_monotone Huniq HSp). 
        rewrite /is_in_conic_hull; exists lu; split; last by done.
        move => i Hi. move/andP: (HSp' i Hi) => [Hi' Hli]. by apply: ltrW.
Qed.

(*Corollary non_extreme_elim A (S: seq 'cV_n) :
  (n > 0)%N -> (\rank A = n) ->
  (forall x : 'cV[R]_n, x \in cone A <-> is_in_conic_hull S x) ->
  forall y, (y \in S) -> ~ (is_extreme_ray y (cone A: _ -> bool)) ->
            (forall x : 'cV[R]_n, x \in cone A <-> is_in_conic_hull (rem y S) x).
Proof.
move => Hn HrkA Hhull y Hy.
move/(introN (extreme_rayP _ HrkA)).

Hy'.
*)

End ExtremeRay.