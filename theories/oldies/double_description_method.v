(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix polyhedral_cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Basic_implementation.

Variable R : realFieldType.
Variable m n : nat.

Definition DDM_elementary_step (S : seq 'cV[R]_n) (c : 'cV_n) :=
  let: Splus := filter (fun v => '[c, v] > 0) S in
  let: S0 := filter (fun v => '[c, v] == 0) S in
  let: Sminus := filter (fun v => '[c, v] < 0) S in
  let: Scomb := [ seq ('[c, v] *: w + (- '[c, w]) *: v) | v <- Splus, w <- Sminus ] in
                    undup (Splus ++ S0 ++ Scomb).

Lemma conic_hull_incl_in_halfspace (S : seq 'cV[R]_n) (c : 'cV_n) :
    (forall v, v \in S -> '[c, v] >= 0) -> (forall x, is_in_conic_hull S x ->  '[c, x] >= 0).
Proof.
move => H x [lx [Hlx ->]].
rewrite (((big_morph (fun v => '[c, v])) 0%R) +%R); last 2 [by apply:vdotDr]; last by apply: vdot0r.
rewrite (eq_bigr (fun v => (lx v) * '[c, v])); last by [move => i _; rewrite vdotZr].
rewrite big_seq; apply: sumr_ge0 => w Hw.
- apply: mulr_ge0; first 2 [by apply: (H _ Hw)]; first by apply: (Hlx _ Hw). 
Qed.

Lemma combination_in_halfspace (c : 'cV[R]_n) (v w : 'cV_n):
  '[c, '[c, v] *: w +  (- '[c, w]) *: v] = 0.
Proof.
by rewrite vdotDr !vdotZr mulrC mulNr addrN.
Qed.

Lemma DDM_elementary_step_proof_part1 (S : seq 'cV_n) (c : 'cV_n) : (uniq S) -> 
  forall x : 'cV_n, is_in_conic_hull (DDM_elementary_step S c) x -> is_in_conic_hull S x /\ '[c, x] >= 0.
Proof.
move => Huniq; split.
- move: x H.
  apply: conic_hull_incl => v.
  rewrite /DDM_elementary_step mem_undup !mem_cat.
  move/or3P; case;
    try by rewrite mem_filter; move/andP => [_ H]; apply: conic_hull_incl_self.
  + move/allpairsP => [p]; rewrite !mem_filter.
    move => [/andP [/ltrW Hp1 Hp1'] /andP [/ltrW Hp2 Hp2'] ->].
    rewrite -oppr_ge0 in Hp2.
    apply: conic_hull_is_closed_by_sum;
      by apply: conic_hull_is_closed_by_scaling;
        first by apply: (conic_hull_incl_self Huniq).
- move: x H.
  apply: conic_hull_incl_in_halfspace => v.
  rewrite /DDM_elementary_step mem_undup !mem_cat.
  move/orP; case; last move/orP; case.
  + by rewrite mem_filter; move/andP => [/ltrW -> _ ].
  + by rewrite mem_filter; move/andP => [/eqP -> _].
  + by move/allpairsP => [p [_ _ ->]]; rewrite combination_in_halfspace.
Qed.

Lemma vdotsumr (c : 'cV_n) (S : seq 'cV_n) (l : 'cV_n -> R) :
  '[c, \sum_(v <- S) (l v) *: v] = \sum_(v <- S) (l v) * '[c, v].
Proof.
rewrite (((big_morph (fun v => '[c, v])) 0%R) +%R).
- by apply: eq_bigr => v _; rewrite vdotZr.
- by apply: vdotDr.
- by apply: vdot0r.
Qed.

Lemma vdotsumr_cond (c : 'cV_n) (S : seq 'cV_n) (P : pred 'cV_n) (l : 'cV_n -> R) :
  '[c, \sum_(v <- S | P v) (l v) *: v] = \sum_(v <- S | P v) (l v) * '[c, v].
Proof.
rewrite (((big_morph (fun v => '[c, v])) 0%R) +%R).
- by apply: eq_bigr => v _; rewrite vdotZr.
- by apply: vdotDr.
- by apply: vdot0r.
Qed.

Lemma DDM_elementary_step_proof_part2_ind (c : 'cV_n) (S : seq 'cV_n) :
  (uniq S) ->
  forall Sminus: seq 'cV_n,
    subseq Sminus S ->
    forall Splus: seq 'cV_n,
      subseq Splus S ->
      forall lx: 'cV_n -> R,
        ((forall v, v \in Splus -> lx v > 0) ->
         (forall v, v \in Splus -> '[c, v] > 0) ->
         (forall v, v \in Sminus -> lx v > 0) ->
         (forall v, v \in Sminus -> '[c, v] < 0) ->
         (\sum_(v <- Sminus) (lx v) * '[c, v]) + (\sum_(v <- Splus) (lx v) * '[c, v]) >= 0 ->
         is_in_conic_hull (DDM_elementary_step S c) ((\sum_(v <- Sminus) (lx v) *: v) + (\sum_(v <- Splus) (lx v) *: v))).
Proof.
move => Huniq Sminus.
elim: Sminus => [ | v Sminus IHSminus].
  
  (* base case when Sminus is empty *)
- move => _ Splus Hsubseq_Splus lx HSplus HSplus' _ _ _.
  rewrite big_nil add0r.
  apply: (@conic_hull_monotone _ _ Splus); first by rewrite undup_uniq.
  + move => w Hw.
    rewrite /DDM_elementary_step mem_undup mem_cat.
    apply/orP; left.
    rewrite mem_filter; apply/andP; split;
      by [apply: HSplus' | apply: (mem_subseq Hsubseq_Splus)].
  
  + exists lx; split; last by done.
    * move => w Hw; apply: ltrW; apply: (HSplus _ Hw).
  
- move => Hsubseq_Sminus Splus.
  elim: Splus => [ | w Splus IHSplus].
  
  (* the base case is handled by getting a contradiction *)
  + move => _ lx.
    (* for the base case, no need of the induction hypothesis on Sminus *)
    rewrite {IHSminus} !big_nil !addr0 !big_cons.
    move => _ _ /allP /andP [Hv /allP HSminus] /allP /andP [Hv' /allP HSminus'].
    have Hcontradiction: lx v * '[ c, v] + \sum_(j <- Sminus) lx j * '[ c, j] < 0.
    rewrite big_seq.
    * apply: addr_ltr_le0; last first.
      - apply: sumr_le0 => i Hi.
        + apply: ltrW; rewrite (pmulr_rlt0 _ (HSminus _ Hi)).
        + apply: HSminus' _ Hi.
      - by rewrite (pmulr_rlt0 _ Hv).
    move => Hcontradiction'.
    move: (ltr_le_add Hcontradiction Hcontradiction').
    by rewrite add0r addr0 ltrr.
  
  (* we now assume that Splus = w::Splus' *)
- move => Hsubseq_Splus lx
          /allP /andP [Hw /allP HSplus]
          /allP /andP [Hw' /allP HSplus']
          /allP /andP [Hv /allP HSminus]
          /allP /andP [Hv' /allP HSminus'].
  rewrite !big_cons.
  rewrite 2![(_ (lx v) _) + _]addrC -2!addrA 2![(_ (lx v) _) + (_ + _)]addrA
          2![_ + (_ + _)]addrC -2![(_ +  _) + _ + _]addrA.
  pose vw := '[c, w] *: v + (- '[c, v]) *: w.
  have Hvwc := combination_in_halfspace c w v.
  
  have Hvw_in_conic_hull: is_in_conic_hull (DDM_elementary_step S c) vw.
  + apply: conic_hull_incl_self; first by apply: undup_uniq.
    rewrite mem_undup mem_cat; apply/orP; right; rewrite mem_cat; apply/orP; right.
    apply/allpairsP; exists (w, v); rewrite //=; split; last by done.
    * rewrite mem_filter; apply/andP; split; first by done.
      - apply:(subseq_head Hsubseq_Splus).
    * rewrite mem_filter; apply/andP; split; first by done.
      - apply:(subseq_head Hsubseq_Sminus).
  
  have HvSminus : v \notin Sminus.
  + by move: (subseq_uniq Hsubseq_Sminus Huniq); rewrite cons_uniq; move/andP => [H0 _].
  have HwSplus : w \notin Splus.
  + by move: (subseq_uniq Hsubseq_Splus Huniq); rewrite cons_uniq; move/andP => [H0 _].
  
  have HvSplus : v \notin Splus.
  + apply: (@discr_seq _ _ _ (fun v => '[c,v] > 0)); last by apply/allP.
    * by rewrite -lerNgt ltrW.
  have HwSminus : w \notin Sminus.
  + apply: (@discr_seq _ _ _ (fun v => '[c,v] < 0)); last by apply/allP.
    * by rewrite -lerNgt ltrW.
  
  case: (ltrgtP (- ((lx v) * '[c,v])) ((lx w) * '[c, w])) => [H | H | H].
  
    (* 1st case: v is eliminated *)
  + pose lx' x :=
    if x == w then lx w + lx v * '[ c, v] / '[ c, w]
    else lx x.
    
    pose lx'_vw := lx v / '[c,w].
    
    (* rewriting the goal in terms of vw and w only *)
    have Hvw: (lx v *: v + lx w *: w) = (lx'_vw) *: vw  + (lx' w) *: w.
    * rewrite scalerDr /lx' eq_refl /lx'_vw scalerDl !scalerA.
      rewrite mulfVK; last by apply: lt0r_neq0.
      rewrite -mulrA [_^-1 * _]mulrC mulrA mulrN mulNr scaleNr.
      by rewrite -addrA [lx w *: _ + _]addrC [-(_) + (_ + _)]addrA addNr add0r.
    rewrite Hvw.
    move/(congr1 (fun x => '[c, x])): Hvw; rewrite 2!vdotDr 4!vdotZr Hvwc mulr0 add0r; move => ->.
    
    (* rewriting the occurences of lx into lx' *)
    rewrite (eq_big_seq_congr2 lx lx' id) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HwSplus => ->.
    rewrite (eq_big_seq_congr2 lx lx' id) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HwSminus => ->.
    rewrite (eq_big_seq_congr2 lx lx' (fun x => '[c,x])) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HwSplus => ->.
    rewrite (eq_big_seq_congr2 lx lx' (fun x => '[c,x])) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HwSminus => ->.
    
    (* grouping w and Splus *)
    rewrite -[_ + _ + (_ + _)]addrA 2![(_ (lx' w) _) + (_ + _)]addrA.
    have H1: lx' w * '[ c, w] + \sum_(i <- Splus) lx' i * '[ c, i] = \sum_(i <- w::Splus) lx' i * '[ c, i].
    * by rewrite big_cons.
    have H2: lx' w *: w + \sum_(i <- Splus) lx' i *: i = \sum_(i <- w::Splus) lx' i *: i.
    * by rewrite big_cons.
    
    rewrite H1 H2 addrC; move => Hc; rewrite [\sum_(i <- _ ) _ + \sum_(i <- _ ) _]addrC.
    apply: conic_hull_is_closed_by_sum.
    * apply: conic_hull_is_closed_by_scaling; first by done.
      - by apply: ltrW; rewrite /lx'_vw; apply: divr_gt0.
    * apply: IHSminus; rewrite //.
      - by apply: (subseq_trans (subseq_cons Sminus v)).
      - move => i; rewrite in_cons; move/orP; case => [/eqP -> | Hi].
        + rewrite /lx' eq_refl -(@pmulr_lgt0 _ '[c,w]); last by done.
          rewrite mulrDl mulfVK; last by apply: lt0r_neq0.
          by rewrite -(ltr_add2r (- (lx v * '[c,v]))) add0r -addrA addrN addr0.
        + rewrite /lx' ifN; last by move/memPn: HwSplus => ->.
          by apply: HSplus.
      - move => i; rewrite in_cons; move/orP; case => [/eqP -> | Hi]; first by done.
        + by apply: HSplus'.
      - move => i Hi; rewrite /lx' ifN; last by move/memPn: HwSminus => ->.
        by apply: HSminus.
    
    (* 2nd case: w is eliminated *)
  + pose lx' x :=
    if x == v then lx v + lx w * '[ c, w] / '[ c, v]
    else lx x.
    
    pose lx'_vw := (lx w / -'[c,v]).
    
    (* rewriting the goal in terms of vw and w only *)
    have Hvw: (lx v *: v + lx w *: w) = (lx'_vw) *: vw  + (lx' v) *: v.
    * rewrite scalerDr /lx' eq_refl /lx'_vw scalerDl !scalerA.
      rewrite mulfVK; last  by apply: lt0r_neq0; rewrite oppr_gt0.
      rewrite -mulrA [_^-1 * _]mulrC mulrA invrN mulrN scaleNr.
      by rewrite -addrA [lx w *: _ + _ in RHS]addrC addrA [lx v *: _ + _ in RHS]addrC !addrA addNr add0r.
    rewrite Hvw.
    move/(congr1 (fun x => '[c, x])): Hvw; rewrite 2!vdotDr 4!vdotZr Hvwc mulr0 add0r; move => ->.
    (* done *)
    
    (* rewriting the occurences of lx into lx' *)
    rewrite (eq_big_seq_congr2 lx lx' id) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HvSplus => ->.
    rewrite (eq_big_seq_congr2 lx lx' id) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HvSminus => ->.
    rewrite (eq_big_seq_congr2 lx lx' (fun x => '[c,x])) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HvSplus => ->.
    rewrite (eq_big_seq_congr2 lx lx' (fun x => '[c,x])) /=;
            last by move => x Hx; by rewrite /lx' ifN; last by move/memPn: HvSminus => ->.
    
    (* grouping w and Splus *)
    rewrite -[_ + _ + (_ + _)]addrA 2![(_ (lx' v) _) + (_ + _)]addrCA.
    have H1: lx' v * '[ c, v] + \sum_(i <- Sminus) lx' i * '[ c, i] = \sum_(i <- v::Sminus) lx' i * '[ c, i].
    * by rewrite big_cons.
    have H2: lx' v *: v + \sum_(i <- Sminus) lx' i *: i = \sum_(i <- v::Sminus) lx' i *: i.
    * by rewrite big_cons.
    
    rewrite H1 H2 addrC; move => Hc; rewrite [\sum_(i <- _ ) _ + \sum_(i <- _ ) _]addrC.
    apply: conic_hull_is_closed_by_sum.
    * apply: conic_hull_is_closed_by_scaling; first by done.
      - by apply: ltrW; rewrite /lx'_vw; apply: divr_gt0; last by rewrite oppr_gt0.
    * apply: IHSplus; rewrite //.
      - by apply: (subseq_trans (subseq_cons Splus w)).
      - move => i Hi; rewrite /lx' ifN; last by move/memPn: HvSplus => ->.
        by apply: HSplus.
      - move => i; rewrite in_cons; move/orP; case => [/eqP -> | Hi].
        + rewrite /lx' eq_refl.
          rewrite -(@pmulr_lgt0 _ (-'[c,v])); last by rewrite oppr_gt0.
          rewrite mulrN mulrDl mulfVK; last by apply: ltr0_neq0.
          by rewrite opprD subr_gt0.
        + rewrite /lx' ifN; last by move/memPn: HvSminus => ->.
          by apply: HSminus.
      - move => i; rewrite in_cons; move/orP; case => [/eqP -> | Hi]; first by done.
        + by apply: HSminus'.
   
    (* 3rd case, both v and w are eliminated *)
  + rewrite -H addrN add0r.
   
    pose lx'_w := lx w + lx v * '[ c, v] / '[ c, w].
    pose lx'_vw := lx v / '[c,w].
    
    (* rewriting the goal in terms of vw only *)
    have Hvw: (lx v *: v + lx w *: w) = lx'_vw *: vw  + lx'_w *: w.
    * rewrite scalerDr /lx'_w /lx'_vw scalerDl !scalerA.
      rewrite mulfVK; last by apply: lt0r_neq0.
      rewrite -mulrA [_^-1 * _]mulrC mulrA mulrN mulNr scaleNr.
      by rewrite -addrA [lx w *: _ + _]addrC [-(_) + (_ + _)]addrA addNr add0r.
    
    have Hlx'_w : lx'_w = 0.
    * rewrite /lx'_w. rewrite -[_ / _]opprK -[- (_ / _)]mulNr H -mulrA mulfV; last by apply:lt0r_neq0.
      by rewrite mulr1 addrN.
    
    rewrite Hvw Hlx'_w scale0r addr0.
    
    rewrite addrC; move => Hc; rewrite [\sum_(i <- _ ) _ + \sum_(i <- _ ) _]addrC.
    apply: conic_hull_is_closed_by_sum.
    + apply: conic_hull_is_closed_by_scaling; first by done.
      - by apply: ltrW; rewrite /lx'_vw; apply: divr_gt0.
    
    + by apply: IHSminus; [ apply: (subseq_trans (subseq_cons Sminus v))
                          | apply: (subseq_trans (subseq_cons Splus w))
                          | apply: HSplus | apply: HSplus'
                          | apply: HSminus | apply: HSminus' | done].
Qed.

Lemma DDM_elementary_step_proof_part2 (S : seq 'cV_n) (c : 'cV_n) : (uniq S) -> 
  forall x : 'cV_n,  is_in_conic_hull S x -> '[c, x] >= 0 -> is_in_conic_hull (DDM_elementary_step S c) x.
Proof.
(* first we rewrite x into the sum of three terms, depending on the sign of '[c,v], and enforcing lx v > 0 *)
move => Huniq x.
move => [lx [Hlx]].
rewrite (bigID (fun v => ('[c, v] >= 0))) (bigID (fun v => ('[c, v] == 0))) /=.
rewrite (eq_bigl_seq (fun v => '[c,v] == 0)) /=; last by move => i _;
  rewrite andb_idl; last by rewrite le0r; move => H; by apply/orP; left.
rewrite [X in _ + X + _](eq_bigl_seq (fun v => '[c,v] > 0)) /=;
  last by move => i _; rewrite andbC lt0r.
rewrite [X in _ + _ + X](eq_bigl_seq (fun v => '[c,v] < 0)) /=;
  last by move => i Hi; rewrite ltrNge.
rewrite (big_rem_idx (fun v => (lx v > 0))) /=; last by
  move => i Hi /andP [_]; rewrite -lerNgt; move => H;
  move/pair_andP/andP: (H, (Hlx _ Hi)); move/ler_asym => ->; apply:scale0r.
rewrite [X in _ + X + _](big_rem_idx (fun v => (lx v > 0))) /=; last by
  move => i Hi /andP [_]; rewrite -lerNgt; move => H;
  move/pair_andP/andP: (H, (Hlx _ Hi)); move/ler_asym => ->; apply:scale0r.
rewrite [X in _ + _ + X](big_rem_idx (fun v => (lx v > 0))) /=; last by
  move => i Hi /andP [_]; rewrite -lerNgt; move => H;
  move/pair_andP/andP: (H, (Hlx _ Hi)); move/ler_asym => ->; apply:scale0r.
move => {Hlx} ->.
 
(* now we work on the expression of '[c,x] *)
rewrite 2!vdotDr 3!vdotsumr_cond.
rewrite big1; last by move => i /andP [/eqP -> _]; rewrite mulr0.
rewrite add0r.
 
(* we get rid of the vectors such that '[c,v] == 0 *)
move => Hc; rewrite -addrA.
apply: conic_hull_is_closed_by_sum.
- rewrite -big_filter.
  set S0 := [seq i <- S | '[ c, i] == 0 & 0 < lx i].
  apply: (@conic_hull_monotone _ _ S0); first by rewrite undup_uniq.
  + move => v; rewrite mem_filter; move => /andP [/andP [Hv _] Hv'].
    rewrite /DDM_elementary_step mem_undup 2!mem_cat.
    apply/orP; right; apply/orP; left.
    by rewrite mem_filter; move/pair_andP/andP: (Hv, Hv').
  + exists lx; split; last by done.
    * by move => v; rewrite mem_filter; move => /andP [/andP [_ Hv] _]; by apply: ltrW.
(* and finally we apply the previous intermediate lemma *)
- rewrite -2!(big_filter S) addrC in Hc;  rewrite -2!(big_filter S) addrC.
  apply: DDM_elementary_step_proof_part2_ind; rewrite //;
    by [ apply: filter_subseq | apply: filter_subseq |
         move => i; rewrite mem_filter => /andP [/andP [_ Hi]] |
         move => i; rewrite mem_filter => /andP [/andP [Hi _]] |
         move => i; rewrite mem_filter => /andP [/andP [_ Hi]] |
         move => i; rewrite mem_filter => /andP [/andP [Hi _]] ].
Qed.

Theorem DDM_elementary_step_proof (S : seq 'cV_n) (c : 'cV_n) :
  (uniq S) -> 
  forall x : 'cV_n, (is_in_conic_hull S x /\ '[c, x] >= 0) <-> is_in_conic_hull (DDM_elementary_step S c) x.
Proof.
move => HSuniq x; split.
- by case; apply: DDM_elementary_step_proof_part2.
- by apply: DDM_elementary_step_proof_part1.
Qed.

End Basic_implementation.

