(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra.
Require Import extra_misc inner_product vector_order extra_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section RowSubmx.

Definition row_submx (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) :=
  \matrix_(i < #|I|, j < p) M (enum_val i) j.

Lemma row_submx_mul (R : realFieldType) (m p q : nat) (M : 'M[R]_(m,p)) (N : 'M[R]_(p,q)) (I : {set 'I_m}) :
  row_submx (M *m N) I = (row_submx M I) *m N.
Proof.
apply/matrixP => ? ?; rewrite !mxE; apply: eq_bigr => ? _.
by rewrite !mxE.
Qed.

Lemma row_submx_row (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (k : 'I_#|I|) :
  row k (row_submx M I) = row (enum_val k) M.
Proof.
by apply/matrixP => ? ?; rewrite !mxE.
Qed.

Lemma row_submx_row_mx (R : realFieldType) (m p q : nat) (M : 'M[R]_(m,p)) (N : 'M[R]_(m,q)) (I : {set 'I_m}) :
  row_submx (row_mx M N) I = row_mx (row_submx M I) (row_submx N I).
Proof.
by apply/row_matrixP => ?; rewrite row_submx_row !row_row_mx !row_submx_row.
Qed.

Lemma row_submx_mxE (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (k : 'I_#|I|) (l : 'I_p) :
  (row_submx M I) k l = M (enum_val k) l.
Proof.
by rewrite !mxE.
Qed.

Lemma row_submx_lev (R : realFieldType) (m : nat) (x y : 'cV[R]_m) (I : {set 'I_m}) : 
      (x <=m y) -> ((row_submx x I) <=m (row_submx y I)).
Proof.
by move/forallP => ?; apply/forallP => ?; rewrite !mxE.
Qed.

Lemma lev_decomp (R : realFieldType) (m : nat) (x y : 'cV[R]_m) (I : {set 'I_m}) :
    (x <=m y) = (((row_submx x I) <=m (row_submx y I)) && ((row_submx x (~:I)) <=m (row_submx y (~:I)))).
Proof.
apply/idP/idP.
- move => H.
  by apply/andP; split; apply: (row_submx_lev _ H).
- move/andP => [/forallP HI /forallP HcI].
  apply/forallP => i.
  case: (boolP (i \in I)) => [Hi | Hi].
  + by move: (HI (enum_rank_in Hi i)); rewrite !row_submx_mxE enum_rankK_in.
  + by rewrite -in_setC in Hi; move: (HcI (enum_rank_in Hi i)); rewrite !row_submx_mxE enum_rankK_in.
Qed.

Lemma row_submx_span (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) :
  (row_submx M I :=: \sum_(i in I) <<row i M>>)%MS.
Proof.
apply/eqmxP/andP; split.
- apply/row_subP => i.
  rewrite row_submx_row.
  apply: (submx_trans (B:= <<row (enum_val i) M>>%MS)); first by move/eqmxP: (genmxE (row (enum_val i) M)) => /andP [_].
  by apply: (sumsmx_sup (enum_val i)); first by apply: enum_valP.
- apply/sumsmx_subP => i Hi.
  apply: (submx_trans (B:= (row i M))); first by move/eqmxP: (genmxE (row i M)) => /andP [? _].
  + move: (enum_rankK_in Hi Hi) <-; rewrite -row_submx_row.
    apply: row_sub.
Qed.

Lemma row_submx_spanU1 (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (i : 'I_m) :
  (i \notin I) -> (row_submx M  (i |: I) :=: row i M + (row_submx M I)) %MS.
Proof.
move => Hi; apply/eqmx_sym.
move/eqmx_sym: (row_submx_span M (i |: I)).
apply: eqmx_trans. apply/eqmx_sym.
move/(adds_eqmx (genmxE (row i M))): (eqmx_sym (row_submx_span M I)).
apply: eqmx_trans.
by rewrite big_setU1 //=.
Qed.

Lemma row_submx_spanD1 (R : realFieldType) (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (i : 'I_m) :
  (i \in I) -> (row_submx M I :=: row i M + (row_submx M (I :\ i))) %MS.
Proof.
move => Hi; apply/eqmx_sym.
move/eqmx_sym: (row_submx_span M I).
apply: eqmx_trans. apply/eqmx_sym.
move/(adds_eqmx (genmxE (row i M))): (eqmx_sym (row_submx_span M (I :\ i))).
apply: eqmx_trans.
by rewrite (big_setD1 i) //=.
Qed.

Lemma lshift_inj (m n : nat): injective (@lshift m n).
Proof.
move => i j /(congr1 (@nat_of_ord (m+n)%N))/eqP.
rewrite /=; by move/eqP/ord_inj.
Qed.

Lemma lshift_card (m n : nat): #|[set lshift n i | i : 'I_m]| = m.
Proof.
move/(card_imset predT): (@lshift_inj m n) ->.
by rewrite cardT size_enum_ord.
Qed.

Lemma rshift_inj (m n : nat): injective (@rshift m n).
Proof.
move => i j /(congr1 (@nat_of_ord (m+n)%N))/eqP.
by rewrite eqn_add2l; move/eqP/ord_inj.
Qed.

Lemma rshift_card (m n : nat): #|[set rshift m i | i : 'I_n]| = n.
Proof.
move/(card_imset predT): (@rshift_inj m n) ->.
by rewrite cardT size_enum_ord.
Qed.

Lemma rshift_iota (m n : nat): (mem [set rshift m i | i : 'I_n]) =1 (fun i => (nat_of_ord i \in iota m n)).
Proof.
move => i; rewrite mem_iota inE; apply/idP/idP.
- move/imsetP => [l _ /(congr1 (@nat_of_ord (m+n)%N)) ->].
  rewrite /=; apply/andP; split; last by apply: rshift_subproof.
  + by rewrite -{1}[m]addn0 leq_add2l; apply: leq0n.
- move/andP => [Hi Hi'].
  apply/imsetP; exists (Ordinal (split_subproof Hi)); first by done.
  by apply: ord_inj; rewrite /= subnKC //.
Qed.

Lemma lrshift_distinct (m n : nat) (i:'I_m) (j: 'I_n): lshift n i != rshift m j. 
Proof.
apply/eqP; move/(congr1 (@nat_of_ord (m+n)%N)).
rewrite /= => Hij.
move: (leq_addr (nat_of_ord j) m); rewrite -Hij.
by move/(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Lemma rshift_compl (m n : nat): ~: [set rshift m i | i : 'I_n] = [set lshift n i | i : 'I_m].
Proof.
have H: [set lshift n i | i : 'I_m] \subset ~: [set rshift m i | i : 'I_n].
- apply/subsetP => i /imsetP [j _ ->].
  apply/setCP/negP; apply: contraT; rewrite negbK.
  move/imsetP => [j' _].
  by move/eqP: (lrshift_distinct j j').
apply/eqP; rewrite eq_sym.
rewrite eqEcard; apply/andP; split; first by done.
move: (cardsC  [set rshift m i | i : 'I_n]).
rewrite [RHS]cardE size_enum_ord rshift_card lshift_card addnC.
move/addIn ->; by apply:leqnn.
Qed.

Lemma row_submx_col_mx (R : realFieldType) (m n p : nat) (M : 'M[R]_(m,p)) (N : 'M[R]_(n,p)) :
  let I := [set rshift m i | i : 'I_n] in
  row_submx (col_mx M N) I = castmx (esym (rshift_card m n), erefl p) N.
Proof.
move => I.
apply/row_matrixP => i.
rewrite row_submx_row row_castmx esymK castmx_id.
move/imsetP: (enum_valP i) => [j _ Hj].
rewrite Hj rowKd.
suff ->: (j = cast_ord (rshift_card m n) i) by done.
apply: ord_inj; move/(congr1 (@nat_of_ord (m+n)%N)): Hj.
rewrite /=.
suff ->: nat_of_ord (enum_val i) = (m+i)%N.
  by move/eqP; rewrite eqn_add2l; move/eqP ->.
- rewrite /enum_val /enum_mem -(@nth_map _ _ _ 0%N); last by rewrite -cardE.
  move/eq_filter: (@rshift_iota m n) ->.
  rewrite -filter_map -enumT val_enum_ord.
  have /(subseq_uniqP (iota_uniq 0 (m+n)%N)) <-: subseq (iota m n) (iota 0 (m+n)%N).
  + move: (iota_add 0 m n) ->; rewrite add0n.
    by apply:suffix_subseq.
  by rewrite nth_iota; last by move: (ltn_ord i); rewrite {2}(rshift_card m n).
Qed.

Variable R: realFieldType.
Variable p q: nat.
Variable M: 'M[R]_(p,q).

Variable bas0: {set 'I_p}.

Fixpoint build_row_base k :=
  match k with
  | 0 => set0
  | k'.+1 =>
    let bas := build_row_base k' in
    if [pick i in bas0 | ~~ (row i M <= row_submx M bas)%MS] is Some i then (i |: bas)
    else set0
  end.

Lemma row_base_correctness k :
  (k <= \rank (row_submx M bas0))%N ->
  let: bas := build_row_base k in
  [/\ bas \subset bas0, #|bas| = k & (\rank (row_submx M bas) = k)].
Proof.
elim: k => [Hrk | k IH Hrk].
- split; try by [ apply sub0set | rewrite cards0].
  apply/eqP; rewrite -leqn0 -(rank_castmx (cards0 _) (row_submx M _)).
  apply: rank_leq_row.
- move/(_ (ltnW Hrk)): IH => [IH IH' IH''].
  set bas := build_row_base k.
  set bas' := build_row_base k.+1.
  have [i0 Hi0]: exists i, (i \in bas0) /\ (~~ ((row i M) <= (row_submx M bas))%MS).
  + suff: (~~ (row_submx M bas0 <= row_submx M bas)%MS).
    * move/row_subPn => [i]; rewrite row_submx_row => H.
      by exists (enum_val i); split; first by apply: enum_valP.
    * move: Hrk; apply: contraL.
      by move/mxrankS; rewrite leqNgt IH'' /=.
  rewrite /bas' /=.
  case: (pickP _) => [i |]; last by move/(_ i0)/andP. 
  + rewrite {Hi0 i0} => /andP [Hi Hi'].
    have Hi'': (i \notin bas).
    * move: Hi'; apply: contraNN => Hi'.
      by rewrite -[i](enum_rankK_in Hi') // -row_submx_row; apply: row_sub.
    split.
    * apply/subsetP => j; rewrite in_setU1; move/orP.
      by case => [/eqP ->|]; last by move/subsetP/(_ j): IH.
    * by rewrite cardsU1 Hi'' IH' add1n.
    * move: (row_submx_spanU1 M Hi'') ->.
      rewrite -[RHS]add1n -IH''.
      move: (rank_rV (row i M)).
      have -> /=: (row i M != 0).
      - move: Hi'; apply: contraNneq; move ->.
        by apply: sub0mx.
      move => Hrk_row; rewrite -{}[in RHS]Hrk_row.
      apply/eqP; rewrite mxrank_adds_leqif; apply/rV_subP => ?.
      rewrite sub_capmx; move/andP => [/sub_rVP [lambda ->]].
      case: (lambda =P 0) => [-> _ | /eqP Hlambda]; first by rewrite scale0r; apply: sub0mx.
      - move/(scalemx_sub (lambda^-1)); rewrite scalerA mulVf // scale1r.
        by move/negbTE: Hi' ->.
Qed.

Lemma row_free_col_mx (r : nat) (M1 : 'M[R]_(p,r)) (M2 : 'M[R]_(q,r)) : row_free (col_mx M1 M2) -> row_free M1.
Proof.
pose P := row_mx 1%:M 0: 'M[R]_(p,p+q).
move/row_freeP => [B /(congr1 (mulmx P))].
rewrite mulmxA mul_row_col mul1mx mul0mx addr0 mulmx1.
rewrite -[B]hsubmxK mul_mx_row.
move/eq_row_mx => [? _].
by apply/row_freeP; exists (lsubmx B).
Qed.

End RowSubmx.