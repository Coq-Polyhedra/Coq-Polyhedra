(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import polyhedral_cone double_description_method polyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Section Homogenization.

Definition vectorH (x : 'cV[R]_n) :=
  \col_(i < n.+1) (match unlift 0 i with
                     | None => 1
                     | Some j => x j 0
                   end).

Definition add_first_coord_0 (x : 'cV[R]_n) :=
  \col_(i < n.+1) (match unlift 0 i with
                     | None => 0
                     | Some j => x j 0
                   end).

Lemma add_first_coord_0K (x : 'cV[R]_(n.+1)) :
        x 0 0 = 0 -> (add_first_coord_0 (row' 0 x)) = x.
Proof.
move => H.
rewrite /add_first_coord_0.
apply/colP => i.
rewrite !mxE.
case: (unliftP 0 i).
- by move => j Hj; rewrite !mxE Hj.
- by move => Hi; rewrite Hi H.
Qed.

Lemma vectorHK (x : 'cV[R]_(n.+1)) :
        x 0 0 = 1 -> (vectorH (row' 0 x)) = x.
Proof.
move => H.
rewrite /vectorH.
apply/colP => i.
rewrite !mxE.
case: (unliftP 0 i).
- by move => j Hj; rewrite !mxE Hj.
- by move => Hi; rewrite Hi H.
Qed.

Lemma vectorH0 (x : 'cV_n) : (vectorH x) 0 0 = 1.
Proof.
by rewrite mxE unlift_none.
Qed.

Lemma vectorHn (x : 'cV_n) : row' 0 (vectorH x) = x.
Proof.
apply/colP => i.
by rewrite !mxE liftK.
Qed.

Lemma eq_vectorH (x : 'cV[R]_n) (y : 'cV[R]_(n.+1) ) :
        (y = vectorH x) <-> (y 0 0 = 1) /\ (row' 0 y = x).
Proof.
split.
- move => -> {y}.
  split; by [apply:vectorH0 | apply:vectorHn].
- move => [H1 H2].
  by rewrite -H2 (vectorHK H1).
Qed.

Lemma le_row' (v w : 'cV[R]_m.+1) (i : 'I_m.+1) :
        (v <=m w) = (v i 0 <= w i 0) && ((row' i v) <=m (row' i w)).
Proof.
apply/idP/idP.
- move/forallP => H.
  apply/andP; split; first by apply: (H i).
  by apply/forallP => j; rewrite !mxE; apply (H (lift i j)).
- move/andP => [H /forallP H'].
  apply/forallP => j.
  case: (unliftP i j) => [k -> | ->] //.
  + by move: (H' k); rewrite !mxE.
Qed.

Lemma eq_row' (p : nat) (v w : 'cV[R]_(p.+1)) (i : 'I_(p.+1)) :
        (v == w) = (v i 0 == w i 0) && (row' i v == row' i w).
Proof.
apply/idP/idP.
- move/eqP/colP => H. apply/andP; split.
  + by rewrite (H _).
  + by apply/eqP/colP => j; rewrite !mxE; rewrite (H _).
- move/andP => [/eqP H1 /eqP/colP H2]; apply/eqP/colP => j.
  case: (unliftP i j) => [k -> | ->] //.
  + by move: (H2 k); rewrite !mxE.
Qed.

Lemma mul_row (p q r : nat) (M : 'M[R]_(p.+1, q)) (N : 'M[R]_(q,r)) (i : 'I_p.+1) :
        row' i (M *m N) = (row' i M) *m N.
Proof.
apply/matrixP => j k; rewrite !mxE.
by apply: eq_bigr => l _; rewrite mxE.
Qed.

Lemma zero_row' (i : 'I_m.+1) : row' i 0 = (0:'cV[R]_m).
Proof.
by apply/colP => j; rewrite !mxE.
Qed.

Definition matrixH :=
  \matrix_(i < m.+1, j < n.+1) (match unlift 0 i with
                                  | None =>
                                    match unlift 0 j with
                                      | None => 1
                                      | Some _ => 0
                                    end
                                  | Some i' =>
                                    match unlift 0 j with
                                      | None => -(b i' 0)
                                      | Some j' => A i' j'
                                    end
                                end).

Lemma matrixH_vectorH (x : 'cV_n) :
        -b + A *m x = row' 0 (matrixH *m (vectorH x)).
Proof.
apply/colP => i.
rewrite !mxE big_ord_recl !mxE liftK unlift_none mulr1. (* utiliser big_nat_recl !!! *)
by rewrite [in RHS](eq_bigr (fun j => A i j * x j 0)) /=; last by move => j _; rewrite !mxE !liftK.
Qed.

Lemma matrixH_coord0 (z : 'cV_n.+1) :
        (matrixH *m z) 0 0 = z 0 0.
Proof.
rewrite /matrixH mxE big_ord_recl !mxE !unlift_none mul1r.
rewrite big1; first by apply: addr0.
- move => i _; by rewrite !mxE liftK unlift_none mul0r.
Qed.

Lemma polyhedronH :
        (polyhedron A b) =1 [pred x | ((vectorH x) \in cone (matrixH))].
Proof.
move => x /=.
rewrite inE [in RHS](le_row' _ _ 0) -matrixH_vectorH matrixH_coord0 vectorH0 !mxE zero_row'.
by rewrite ler01 andTb -(lev_add2l (-b)) addNr.
Qed.

Definition is_in_convex_hull (S : seq 'cV_n) (x : 'cV_n) :=
  exists (l : 'cV[R]_n -> R),
    (forall v, v \in S -> l v >= 0) /\ (\sum_(v <- S) l v = 1) /\
    x = \sum_(v <- S) (l v) *: v.

Definition normalize (x : 'cV[R]_(n.+1)) :=
  if x 0 0 != 0 then (`|x 0 0|)^-1 *: x else x.

Lemma normalize_coord0 (x : 'cV[R]_(n.+1)) :
        (normalize x) 0 0 = Num.sg (x 0 0).
Proof.
rewrite /normalize.
case: ifP => [/normr0P/eqP H | /eqP H].
- rewrite mxE.
  rewrite {2}[(x 0 0)]realEsg; last by apply: num_real.
  rewrite [Num.sg _ * _]mulrC mulrA mulVf; last by done.
  by rewrite mul1r.
- by rewrite H sgr0.
Qed.

Lemma normalize_coord0' (x : 'cV[R]_(n.+1)) :
        Num.sg ((normalize x) 0 0) = Num.sg (x 0 0).
Proof.
by rewrite normalize_coord0; apply: sgr_id.
Qed.

Lemma conic_hull_normalize (S : seq 'cV[R]_(n.+1)) :
(uniq S) ->
    (forall x : 'cV[R]_(n.+1),
        is_in_conic_hull S x <-> is_in_conic_hull (undup [seq normalize i | i <- S]) x).
Proof.
move => Huniq x.
split.
- apply: conic_hull_incl.
  move => v HvS.
  case H: (v 0 0 == 0).
  + apply: conic_hull_incl_self; [apply: undup_uniq | rewrite mem_undup].
    apply/mapP.
    exists v; first by done.
    rewrite /normalize ifF; first by done.
    move/eqP in H.
    by apply/eqP.
  + have H': ((`|v 0 0|)^-1 *: v \in (map normalize S)).
      apply/mapP.
      exists v; first by done.
      rewrite /normalize ifT; first by done.
      move/eqP in H.
      by apply/eqP.
    rewrite -mem_undup in H'.
    have H'' :  is_in_conic_hull (undup [seq normalize i | i <- S]) (`|v 0 0|^-1 *: v)
      by apply: conic_hull_incl_self; [apply: undup_uniq | done].
    have Hscale : v = `|v 0 0| *: (`|v 0 0|^-1 *: v).
      rewrite scalerA mulrV; last by rewrite unitfE; move/normr0P/eqP: H.
      by rewrite scale1r.
    rewrite Hscale.
    by apply: conic_hull_is_closed_by_scaling; [done | apply: normr_ge0].
- apply: conic_hull_incl.
  move => v HvS.
  rewrite mem_undup in HvS.
  move/mapP: HvS => [ w HwS H ].
  case H': (w 0 0 == 0).
  + by rewrite H /normalize ifF; [apply: conic_hull_incl_self | apply/eqP; move/eqP: H'].
  + by rewrite H /normalize ifT; [apply: conic_hull_is_closed_by_scaling; [apply: conic_hull_incl_self | rewrite invr_ge0 normr_ge0] | apply/eqP; move/eqP: H'].
Qed.

Lemma conic_hullHI (S : seq 'cV[R]_(n.+1)) :
  (uniq S) -> 
    let: S' := undup (map normalize S) in
    let: S1 := map (row' 0) [seq v : 'cV[R]_n.+1 <- S' | v 0 0 != 0] in
    let: S2 := map (row' 0) [seq v : 'cV[R]_n.+1 <- S' | v 0 0 == 0] in
      (forall v, v \in S -> v 0 0 >= 0) -> 
        forall x, (is_in_conic_hull S' (vectorH x) <-> (exists y z : 'cV[R]_n, x = y + z /\ is_in_convex_hull S1 y /\ is_in_conic_hull S2 z)).
Proof.
set S' := undup (map normalize S).
set S1 := [seq v : 'cV[R]_n.+1 <- S' | v 0 0 != 0].
set S2 := [seq v : 'cV[R]_n.+1 <- S' | v 0 0 == 0].
move => Huniq Hcoord0 x.
have HS1 : forall v, v \in S1 -> v 0 0 = 1.
  move => v.
  rewrite mem_filter mem_undup.
  move/andP => [Hv /mapP [w Hw Hvw]].
  have Hv': (v 0 0 > 0).
    rewrite lt0r; apply/andP.
    by split; [done | rewrite Hvw normalize_coord0 sgr_ge0; apply Hcoord0].
  by move: Hv'; rewrite Hvw normalize_coord0 sgr_gt0; apply: gtr0_sg.
have HS2 : forall v, v \in S2 -> v 0 0 = 0.
  move => v.
  rewrite mem_filter.
  by move/andP => [/eqP Hv _].
split.
- move => [lx [Hlx Hx]].
  symmetry in Hx.
  move/eq_vectorH: Hx => [Hlx' Hx].
  rewrite raddf_sum (eq_bigr (fun v => (lx v) *: (row' 0 v))) in Hx;
    last by move => i _ /=; rewrite linearZ.
  exists (\sum_(v <- S1) (lx v) *: (row' 0 v)), (\sum_(v <- S2) (lx v) *: (row' 0 v)).
  split.
  + by rewrite 2!big_filter -Hx (bigID (fun (v:'cV[R]_(n.+1)) => v 0 0 == 0)) /= addrC.
  + split.
    * rewrite big_seq summxE (eq_bigr (fun v => (lx v) * (v 0 0))) in Hlx';
        last by move => i _; rewrite mxE.
      rewrite (big_rem_idx (fun (v:'cV[R]_(n.+1)) => v 0 0 != 0)) /= in Hlx';
        last by move => i _ /andP [_ /negbNE/eqP ->]; rewrite mulr0.
      rewrite (eq_bigr (fun v => lx v)) in Hlx';
        last by move => i Hi; rewrite HS1; [rewrite mulr1 | rewrite mem_filter andbC].
      rewrite -big_seq_cond -big_filter in Hlx'.
      have H': forall w, w \in S1 -> w = vectorH (row' 0 w)
        by move => w Hw; rewrite vectorHK; [done | apply: HS1].
      rewrite /is_in_convex_hull.
      set lxp := (fun v => lx (vectorH v)).
      exists lxp.
      split.
      - move => v /mapP [w Hw Hvw].
        have H'': subseq S1 (undup [seq normalize i | i <- S])
          by apply: filter_subseq.
        rewrite Hvw /lxp -H'; last by done.
        apply: Hlx.
        by apply: (mem_subseq H'').
      - split.
        + rewrite big_seq_cond (eq_bigl (fun i =>  vectorH i \in S1)) /lxp;
            last by move => i /=; rewrite Bool.andb_true_r; apply/idP/idP;
              [move/mapP => [j Hj Hij]; rewrite Hij -(H' j Hj) | move => Hi; apply/mapP; exists (vectorH i); [done | symmetry; apply: vectorHn]].
          rewrite big_map big_seq_cond (eq_bigr (fun i => lx i));
            last by move => i /andP [x0 Hx0]; rewrite -H'.
          rewrite (eq_bigl (fun i => (i \in S1) && true));
            last by move =>i /=; rewrite Bool.andb_true_r;
              apply/idP/idP; [move/andP => [Hi _] | move => Hi; apply /andP; split; [done | rewrite -(H' i Hi)]].
          rewrite -big_seq_cond.
          by apply: Hlx'.
        + rewrite [\sum_(v <- [seq row' 0 i | i <- S1]) lxp v *: v]big_map.
          rewrite big_seq_cond [\sum_(j <- S1) lxp (row' 0 j) *: row' 0 j]big_seq_cond.
          apply: eq_bigr.
          move => x0.
          rewrite Bool.andb_true_r.
          move => Hx0.
          by rewrite /lxp -H'.
    * rewrite /is_in_conic_hull /=.
      set lxp := (fun v => lx (add_first_coord_0 v)).
      exists lxp.
      split.
      - move => v /mapP [x0 [Hx0 Hvx0]].
        have H': subseq S2 S'
          by apply: filter_subseq.
        rewrite /lxp Hvx0 (add_first_coord_0K (HS2 x0 Hx0)).
        apply: Hlx.
        by apply: (mem_subseq H').
      - symmetry.
        rewrite big_map /lxp big_seq [\sum_(v <- S2) lx v *: row' 0 v]big_seq.
        apply: eq_bigr.
        move => i Hi.
        by rewrite (add_first_coord_0K (HS2 i Hi)).
- case => y [z] [Hx] [Hy] [lz] [Hlz] Hz.
  move: Hy.
  rewrite /is_in_convex_hull.
  move  => [ly [Hly [Hly1 Hy]]].
  rewrite /is_in_conic_hull.
  set lx := (fun v: 'cV_n.+1 =>  if v 0 0 != 0 then ly (row' 0 v) else lz (row' 0 v)).
  exists lx.
  split.
  + move => v Hv.
    rewrite /lx.
    case H: (v 0 0 != 0).
    * apply: Hly.
      apply: map_f.
      rewrite /S1 mem_filter.
      by apply/andP.
    * apply: Hlz.
      apply: map_f.
     rewrite /S2 mem_filter.
     apply/andP.
     by split; [apply/eqP; move/eqP: H | done].
  + rewrite Hy in Hx.
    rewrite Hz in Hx.
    rewrite (bigID (fun (v:'cV[R]_(n.+1)) => v 0 0 == 0)) /=.
    symmetry.
    rewrite eq_vectorH.
    split.
    * have H1: \sum_(k <- S' | k 0 0 == 0) (lx k *: k) 0 0 = 0.
        apply: big1_seq.
        move => i /andP [/eqP Hi Hi'].
        by rewrite mxE Hi mulr0.
      have H2: \sum_(k <- S' | k 0 0 != 0) (lx k *: k) 0 0 = 1.
        rewrite big_seq_cond (eq_bigr (fun i => (ly (row' 0 i))));
          last by move => i /andP [Hi Hi']; rewrite /lx !mxE;
            rewrite ifT; [rewrite HS1; [apply: mulr1 | rewrite /S1 mem_filter; apply/andP] | done].
        rewrite big_map /S1 in Hly1.
        rewrite -big_seq_cond.
        by rewrite -big_filter.
      rewrite mxE !summxE H1 H2.
      by apply: add0r.
    * have H1: \sum_(v <- [seq row' 0 i | i <- S2]) lz v *: v = \sum_(i <- S' | (i \in S') && (i 0 0 == 0)) row' 0 (lx i *: i).
        rewrite big_map /S2.
        symmetry.
        rewrite [\sum_(i <- S' | (i \in S') && (i 0 0 == 0)) row' 0 (lx i *: i)](eq_bigr (fun i => (lz (row' 0 i) *: (row' 0 i)))).
          - by rewrite -big_seq_cond -big_filter.
          - move => i /andP [Hi Hi'].
            rewrite -linearZ /lx.
            have H: (if i 0 0 != 0 then ly (row' 0 i) else lz (row' 0 i)) =lz (row' 0 i)
              by apply: ifF; rewrite /eqP Hi'.
            by rewrite H.
      have H2: \sum_(v <- [seq row' 0 i | i <- S1]) ly v *: v = \sum_(i <- S' | (i \in S') && (i 0 0 != 0)) row' 0 (lx i *: i).
        rewrite big_map /S1.
        symmetry.
        rewrite [\sum_(i <- S' | (i \in S') && (i 0 0 != 0)) row' 0 (lx i *: i)](eq_bigr (fun i => (ly (row' 0 i) *: (row' 0 i)))).
          - by rewrite -big_seq_cond -big_filter.
          - move => i /andP [Hi Hi'].
            rewrite -linearZ /lx.
            have H: (if i 0 0 != 0 then ly (row' 0 i) else lz (row' 0 i)) =ly (row' 0 i)
                by apply ifT.
        by rewrite H.
      rewrite big_seq_cond [\sum_(i <- S' | i 0 0 != 0) lx i *: i]big_seq_cond -bigID /= raddf_sum.
      by rewrite (bigID (fun (v:'cV[R]_(n.+1)) => v 0 0 == 0)) /= -H1 -H2 addrC.
Qed.

End Homogenization.

Section Minkowski_Theorem_for_cones.

Variable R : realFieldType.
Variable m n : nat.

Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.

Definition id_mx := (pid_mx n) : ('M[R]_n).

Definition canonical_basis :=
  [seq (col i id_mx) | i in 'I_n].

Lemma canonical_basis_uniq :
        uniq canonical_basis.
Proof.
rewrite map_inj_in_uniq.
by apply: enum_uniq.
- move => i j Hi Hj.
  move/colP/(_ i); rewrite /id_mx /pid_mx !mxE eq_refl !ltn_ord /=.
  move/eqP; rewrite eqr_nat andbT eq_sym eqb1; move/eqP.
  by apply: ord_inj.
Qed.

Definition minus_canonical_basis :=
  [seq -v | v <- canonical_basis].

Lemma minus_canonical_basis_uniq :
        uniq minus_canonical_basis.
Proof.
rewrite map_inj_in_uniq.
by apply: canonical_basis_uniq.
- move => i j Hi Hj.
  by apply: oppr_inj.
Qed.

Lemma canonical_bases v :
        (v \in minus_canonical_basis) = (-v \in canonical_basis).
Proof.
rewrite -[v in v \in _]opprK.
rewrite mem_map; first by done.
- by apply: oppr_inj.
Qed.

Lemma canonical_bases_uniq :
        uniq (canonical_basis ++ minus_canonical_basis).
Proof.
rewrite cat_uniq.
apply/andP; split; first by apply: canonical_basis_uniq.
apply/andP; split; last by apply: minus_canonical_basis_uniq.
- apply/hasPn => v /mapP [w Hw].
  move/mapP: Hw => [i Hi Hi'].
  move => ->.
  apply/negP => /mapP [j Hj Hj'].
  rewrite Hi' in Hj'.
  move/colP in Hj'.
  move: (Hj' i) => H.
  rewrite !mxE in H.
  rewrite eq_refl !ltn_ord !andbT mulr1n /= in H.
  have H'' : (i == j)%:R >= 0 :> R.
  apply ler0n.
  rewrite -H in H''.
  by rewrite ler0N1 in H''.
Qed.

Lemma Minkowski_Theorem_for_Rplusn :
  forall x : 'cV_n, (forall i: 'I_n, x i 0 >= 0) -> is_in_conic_hull (canonical_basis) x.
Proof.
  move => x.
  exists (fun v => '[v, x]).
  split.
  + move => v /mapP [i Hi Hi'].
    rewrite /vdot Hi' /id_mx /col.
    apply: sumr_ge0 => j _.
    rewrite !mxE.
    apply: mulr_ge0; by [ apply:ler0n |apply: H].
  
  + apply/colP => i.
    rewrite summxE big_map.
    rewrite (eq_big_perm (i::(rem i (enum 'I_n)))) /=.
    rewrite big_cons.
    have H': ('[ col i id_mx, x] *: col i id_mx) i 0 = x i 0.
    + rewrite !mxE eq_refl ltn_ord /= mulr1.
      rewrite /vdot /id_mx /col.
      rewrite (bigD1 i) //=.
      rewrite !mxE eq_refl ltn_ord /= mul1r.
      have H'':  \sum_(i0 < n | i0 != i) (\col_i1 (pid_mx n) i1 i) i0 0 * x i0 0 = 0.
      + apply: big1_seq => k /andP [/eqP Hk _].
        rewrite !mxE.
        have H''': ~~((k == i) && (k < n)%N).
        apply/andP. by move => [ /eqP H1 _].
        by rewrite (negbTE H''') mul0r.
      by rewrite H'' addr0.
    
    rewrite H'.
    have H'': (\sum_(j <- rem i (enum 'I_n)) ('[ col j id_mx, x] *: col j id_mx) i 0)=0.
    + rewrite big1_seq //.
      + move => j /andP [_ Hj].
        rewrite !mxE.
        have H''' : ((i == j) && (i < n)%N)= false.
        + rewrite mem_rem_uniq in Hj.
          + case/predD1P: Hj => [Hineqj _].
            by apply/andP; move => [ H1 _ ]; rewrite eq_sym in H1; move/eqP in H1.
          + by apply: enum_uniq.
        by rewrite H''' mulr0.
    by rewrite H'' addr0.
    
    by apply: perm_to_rem; rewrite mem_enum.
Qed.

Lemma Minkowski_Theorem_for_Rminusn :
  forall x : 'cV_n, (forall i: 'I_n, x i 0 <= 0) -> is_in_conic_hull (minus_canonical_basis) x.
Proof.
move => x H.
 
have H' : is_in_conic_hull canonical_basis (-x).
apply: Minkowski_Theorem_for_Rplusn.
+ move => i.
  by rewrite mxE oppr_ge0.
case: H' => lx [Hlx Hx].
exists (fun v => lx (-v)).
split.
+ move => v Hv.
  have H'': -v \in canonical_basis.
  by rewrite canonical_bases in Hv.
  by apply: Hlx.
  rewrite big_map.
  move/eqP in Hx; rewrite eqr_oppLR in Hx; move/eqP in Hx.
  rewrite Hx -sumrN.
  by apply: eq_bigr => v _; rewrite opprK scalerN.
Qed.

Lemma Minkowski_Theorem_for_Rn :
  forall x : 'cV[R]_n, is_in_conic_hull (canonical_basis ++ minus_canonical_basis) x.
Proof.
  move => x.
  have H : x = map_mx (Num.max^~ 0) x + map_mx (Num.min^~ 0) x.
  apply/colP => i.
  by rewrite !mxE addr_max_min addr0.
  
  have H1: is_in_conic_hull canonical_basis (map_mx (Num.max^~ 0) x).
  + apply: Minkowski_Theorem_for_Rplusn => i.
    rewrite !mxE.
    case: (lerP (x i 0) 0) => [H' | H'].
    + by rewrite maxr_r.
    + by move/ltrW in H'; rewrite maxr_l.
  
  have H2: is_in_conic_hull minus_canonical_basis (map_mx (Num.min^~ 0) x).
  + apply: Minkowski_Theorem_for_Rminusn => i.
    rewrite !mxE.
    case: (lerP (x i 0) 0) => [H' | H'].
    + by rewrite minr_l.
    + by move/ltrW in H'; rewrite minr_r.
  
  have H1': is_in_conic_hull (canonical_basis ++ minus_canonical_basis) (map_mx (Num.max^~ 0) x).
  + apply: (@conic_hull_monotone _ _ canonical_basis); last by done.
    + by apply: canonical_bases_uniq.
    + by apply: mem_subseq; apply: prefix_subseq.
  
  have H2': is_in_conic_hull (canonical_basis ++ minus_canonical_basis) (map_mx (Num.min^~ 0) x).
  + apply: (@conic_hull_monotone _ _ minus_canonical_basis); last by done.
    + by apply: canonical_bases_uniq.
    + by apply: mem_subseq; apply: suffix_subseq.
  
  rewrite H.
  by apply: conic_hull_is_closed_by_sum.
Qed.

Theorem Minkowski_Theorem_for_Polyhedral_Cones (C : seq 'cV[R]_n) :
exists S : seq 'cV_n,
  (uniq S) /\
  forall x : 'cV_n, all (fun c => '[c, x] >= 0) C <-> (is_in_conic_hull S x).
Proof.
elim C => [ | c C' [S'  [IH IH']]].
 
(* base case *)
+ exists (canonical_basis ++ minus_canonical_basis).
  split.
  + by apply: canonical_bases_uniq.
  + move => x.
    split.
    + move => _.
      apply: Minkowski_Theorem_for_Rn.
      by rewrite all_nil.
 
+ exists (DDM_elementary_step S' c).
  split.
  + by apply: undup_uniq.
  + move => x.
    split.
    + case/andP => Hc HC'.
      apply: DDM_elementary_step_proof_part2; by [done | apply/IH' | done].
    + move => H.
      apply/andP.
      move/DDM_elementary_step_proof_part1: H => H.
      case: (H IH) => Hx Hx'.
      split; by [done | apply/IH'].
Qed.

Theorem Minkowski_Theorem_for_Polyhedral_Cones' :
exists S : seq 'cV_n,
  (uniq S) /\
  forall x : 'cV_n, x \in (cone A) <-> is_in_conic_hull S x.
Proof.
move: (Minkowski_Theorem_for_Polyhedral_Cones [seq (row i A)^T, i]) => [S [Huniq H]].
exists S.
split; first by done.
+ move => x; rewrite inE.
  have H' := (cone_ineq_seq A x).
  rewrite /= in H'.
  by rewrite H'.
Qed.

End Minkowski_Theorem_for_cones.


Theorem Minkowski_Theorem_for_Polyhedra :
  exists S1 S2 : seq 'cV_n,
    (uniq S1) /\ (uniq S2) /\
    forall x : 'cV_n, (x \in polyhedron A b) <->
                          (exists y z : 'cV_n, x = y + z /\ is_in_convex_hull S1 y /\ is_in_conic_hull S2 z).
Proof.
have [S [Huniq Hequiv]] := (Minkowski_Theorem_for_Polyhedral_Cones' matrixH).
pose S' := undup (map normalize S).
pose S1 := map (row' 0) [seq v : 'cV[R]_n.+1 <- S' | v 0 0 != 0].
pose S2 := map (row' 0) [seq v : 'cV[R]_n.+1 <- S' | v 0 0 == 0].
 
have HS_coord0: forall v, (v \in S) -> v 0 0 >= 0.
- move => v Hv;  move/Hequiv/forallP: (@conic_hull_incl_self _ _ _ Huniq _ Hv).
  by move/(_ 0); rewrite matrixH_coord0 mxE.
have HS1_coord0: forall v, (v \in S') && (v 0 0 != 0) -> v 0 0 = 1.
- move => v; rewrite mem_undup; move => /andP [/mapP [w Hw]] ->.
  move: (HS_coord0 w Hw); rewrite normalize_coord0 sgr_cp0; move => Hw' Hw''.
  by apply/eqP; rewrite sgr_cp0; move/pair_andP/andP: (Hw'', Hw'); rewrite ltr_def.
  
exists S1; exists S2; split. (*do ?[split].*)
- rewrite map_inj_in_uniq //; last first.
  + move => v w; rewrite !mem_filter; move => /andP [Hv Hv'] /andP [Hw Hw'] H.
    apply/eqP; rewrite (@eq_row' _ _ _ 0); apply/andP; split; apply/eqP; last by done.
    * rewrite HS1_coord0; last by apply/andP; split.
      - by symmetry; apply HS1_coord0; last by apply/andP; split.
  + by apply:filter_uniq; apply: undup_uniq.
split.
- rewrite map_inj_in_uniq //; last first.
  + move => v w; rewrite !mem_filter; move => /andP [/eqP Hv Hv'] /andP [/eqP Hw Hw'] H.
    apply/eqP; rewrite (@eq_row' _ _ _ 0); apply/andP; split; apply/eqP; last by done.
    * by rewrite Hv Hw.
  + by apply:filter_uniq; apply: undup_uniq.
- move => x. move: (polyhedronH x); rewrite !inE => ->.
  rewrite Hequiv; rewrite conic_hull_normalize //.
  by apply: conic_hullHI.
Qed.
