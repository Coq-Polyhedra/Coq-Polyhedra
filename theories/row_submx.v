(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra.
From mathcomp Require Import fingroup perm.
Require Import extra_misc inner_product vector_order extra_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section RowSubmx.

Variable R : realFieldType.
  
Definition row_submx (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) :=
  \matrix_(i < #|I|, j < p) M (enum_val i) j.

Lemma row_submx_mul (m p q : nat) (M : 'M[R]_(m,p)) (N : 'M[R]_(p,q)) (I : {set 'I_m}) :
  row_submx (M *m N) I = (row_submx M I) *m N.
Proof.
apply/matrixP => ? ?; rewrite !mxE; apply: eq_bigr => ? _.
by rewrite !mxE.
Qed.

Lemma row_submx_row (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (k : 'I_#|I|) :
  row k (row_submx M I) = row (enum_val k) M.
Proof.
by apply/matrixP => ? ?; rewrite !mxE.
Qed.

Lemma row_submx_row_mx (m p q : nat) (M : 'M[R]_(m,p)) (N : 'M[R]_(m,q)) (I : {set 'I_m}) :
  row_submx (row_mx M N) I = row_mx (row_submx M I) (row_submx N I).
Proof.
by apply/row_matrixP => ?; rewrite row_submx_row !row_row_mx !row_submx_row.
Qed.

Lemma row_submx_mxE (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (k : 'I_#|I|) (l : 'I_p) :
  (row_submx M I) k l = M (enum_val k) l.
Proof.
by rewrite !mxE.
Qed.

Lemma row_submx_lev (m : nat) (x y : 'cV[R]_m) (I : {set 'I_m}) : 
      (x <=m y) -> ((row_submx x I) <=m (row_submx y I)).
Proof.
by move/forallP => ?; apply/forallP => ?; rewrite !mxE.
Qed.

Lemma lev_decomp (m : nat) (x y : 'cV[R]_m) (I : {set 'I_m}) :
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

Lemma row_submx_span (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) :
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

Lemma row_submx_spanU1 (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (i : 'I_m) :
  (i \notin I) -> (row_submx M  (i |: I) :=: row i M + (row_submx M I)) %MS.
Proof.
move => Hi; apply/eqmx_sym.
move/eqmx_sym: (row_submx_span M (i |: I)).
apply: eqmx_trans. apply/eqmx_sym.
move/(adds_eqmx (genmxE (row i M))): (eqmx_sym (row_submx_span M I)).
apply: eqmx_trans.
by rewrite big_setU1 //=.
Qed.

Lemma row_submx_spanD1 (m p : nat) (M : 'M[R]_(m,p)) (I : {set 'I_m}) (i : 'I_m) :
  (i \in I) -> (row_submx M I :=: row i M + (row_submx M (I :\ i))) %MS.
Proof.
move => Hi; apply/eqmx_sym.
move/eqmx_sym: (row_submx_span M I).
apply: eqmx_trans. apply/eqmx_sym.
move/(adds_eqmx (genmxE (row i M))): (eqmx_sym (row_submx_span M (I :\ i))).
apply: eqmx_trans.
by rewrite (big_setD1 i) //=.
Qed.

End RowSubmx.

Section ExtraFinType.

Variable T T': finType.

Variable A: {set T}.

Variable f: T -> T'.
Hypothesis injf: injective f.

Definition liftf (i: 'I_#|A|) :=
  (enum_rank_in (mem_imset f (enum_valP i)) (f (enum_val i))): 'I_#|f @: A|.

Lemma liftf_inj : injective liftf.
Proof.
move => i i'.
move/(congr1 enum_val).
do 2![rewrite enum_rankK_in; last exact: (mem_imset _ (enum_valP _))].
move/injf; exact: enum_val_inj.
Qed.

Definition liftf_perm_fun := (cast_ord (card_imset (mem A) injf)) \o liftf.

Lemma liftf_perm_inj : injective liftf_perm_fun.
Proof.
apply: inj_comp; [exact: cast_ord_inj | exact liftf_inj].
Qed.

Definition liftf_perm := perm liftf_perm_inj: 'S_#|A|.

End ExtraFinType.

Section RowSubmxPerm.

Variable R: realFieldType.
  
Variable m n: nat.
Variable M: 'M[R]_(m,n). 
Variable I: {set 'I_m}.

Variable perm_idx : 'S_m.

Lemma row_submx_perm :
  let: perm_idx_inj := @perm_inj _ perm_idx in
  row_submx (row_perm perm_idx M) I =
  row_perm (liftf_perm I perm_idx_inj)
           (castmx (card_imset (mem I) perm_idx_inj, erefl n)
                   (row_submx M (perm_idx @: I))).
Proof.
apply/matrixP => i j.
rewrite row_submx_mxE mxE.
rewrite mxE castmxE /= cast_ord_id row_submx_mxE.
by rewrite permE cast_ordK enum_rankK_in; last exact: (mem_imset _ (enum_valP _)).
Qed.

End RowSubmxPerm.

Section SplitExtra.

Variable m n: nat.

Lemma lshift_inj: injective (@lshift m n).
Proof.
move => i j /(congr1 (@nat_of_ord (m+n)%N))/eqP.
rewrite /=; by move/eqP/ord_inj.
Qed.

Lemma rshift_inj: injective (@rshift m n).
Proof.
move => i j /(congr1 (@nat_of_ord (m+n)%N))/eqP.
by rewrite eqn_add2l; move/eqP/ord_inj.
Qed.

Lemma enum_lrshift :
  (enum 'I_(m+n)) = 
  [seq (lshift n i) | i <- enum 'I_m]
    ++ [seq (rshift m i) | i <- enum 'I_n].
Proof.
apply: (inj_map (@ord_inj (m+n)%N)).
rewrite val_enum_ord.
rewrite map_cat -!map_comp -2!enumT.
set s1 := (X in X ++ _).
set s2 := (X in _ ++ X).
have ->: (s1 = [seq (nat_of_ord i) | i <- enum 'I_m])
  by exact: eq_map.
have ->: (s2 = map (addn m) [seq (nat_of_ord i)%N | i <- enum 'I_n])
  by rewrite -map_comp; exact: eq_map.
by rewrite 2!val_enum_ord -iota_addl [in RHS]addnC -iota_add.
Qed.   

CoInductive split_spec' (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | SplitLo' (j : 'I_m) of i = lshift n j : split_spec' i (inl _ j) true
  | SplitHi' (k : 'I_n) of i = rshift m k : split_spec' i (inr _ k) false.

Lemma splitP' (i : 'I_(m + n)) : split_spec' i (split i) (i < m)%N.
Proof.
case: (splitP i) => [j | k].
- have <-: (nat_of_ord (lshift n j) = j)%N by done.
  by move/ord_inj ->; constructor.
- have <-: (nat_of_ord (rshift m k) = (m+k))%N by done.
  by move/ord_inj ->; constructor.
Qed.

Lemma lrshift_distinct i j: lshift n i != rshift m j. 
Proof.
apply/eqP; move/(congr1 (@nat_of_ord (m+n)%N)).
rewrite /= => Hij.
move: (leq_addr (nat_of_ord j) m); rewrite -Hij.
by move/(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Lemma lrshift_disjoint (I: {set 'I_m}) (J: {set 'I_n}):
  [disjoint ((@lshift m n) @: I) & ((@rshift m n) @: J)].
Proof.
rewrite disjoint_subset.
apply/subsetP => i; rewrite inE.
move/imsetP => [i' _ ->].
apply/negP; move/imsetP => [j _].
move/eqP; apply/negP.
exact: lrshift_distinct.
Qed.


End SplitExtra.

Section RowSubmxSplit.

Variable R: realFieldType.

Variable m n: nat.
Variable p: nat.
Variable M: 'M[R]_(m,p).
Variable N: 'M[R]_(n,p).

Variable I: {set 'I_m}.
Variable J: {set 'I_n}.

Lemma lshift_enum_val (i: 'I_#|I|):
  lshift n (enum_val i) =
  enum_val (cast_ord (esym (card_imset (mem I) (@lshift_inj m n))) i).
Proof.
rewrite (enum_val_nth (enum_default ((cast_ord (esym (card_imset (mem I) (@lshift_inj m n))) i)))).
rewrite /enum_mem -enumT.
rewrite enum_lrshift filter_cat.
set s1 := (X in X ++ _).
set s2 := (X in _ ++ X).
have ->: s1 = [seq (lshift n i) | i <- enum I].
- rewrite /s1 filter_map {2}/enum_mem -enumT.
  apply/(congr1 (map _)); apply: eq_filter => j.
  rewrite !inE; apply/idP/idP.
  + by move/imsetP => [j' Hj' /lshift_inj ->].
  + exact: mem_imset.
rewrite {s1}; set s1 := (X in X ++ _).
rewrite nth_cat size_map /= -cardE ltn_ord.
rewrite (nth_map (enum_default i)) //=.
  by rewrite -cardE ltn_ord.
Qed.

Lemma row_submx_col_mx_lshift :
  let: I' := (@lshift m n) @: I in
  row_submx (col_mx M N) I' =
  castmx (esym (card_imset (mem I) (@lshift_inj m n)), erefl p)
          (row_submx M I).
Proof.
set I' := (@lshift m n) @: I.
apply/matrixP => i j.
rewrite row_submx_mxE.
move/imsetP: (enum_valP i) => [i' Hi' Hi].
rewrite Hi col_mxEu.
rewrite castmxE esymK cast_ord_id row_submx_mxE.
suff: (enum_val i = lshift n (enum_val (cast_ord (card_imset (mem I) (@lshift_inj m n)) i))).
  by rewrite Hi; move/lshift_inj => ->.
by rewrite lshift_enum_val cast_ordK.
Qed.

Lemma rshift_enum_val (i: 'I_#|J|):
  rshift m (enum_val i) =
  enum_val (cast_ord (esym (card_imset (mem J) (@rshift_inj m n))) i).
Proof.
rewrite (enum_val_nth (enum_default ((cast_ord (esym (card_imset (mem J) (@rshift_inj m n))) i)))).
rewrite /enum_mem -enumT.
rewrite enum_lrshift filter_cat.
set s1 := (X in X ++ _).
set s2 := (X in _ ++ X).
have ->: s1 = [::]. 
- rewrite /s1 filter_map.
  rewrite (@eq_filter _ _ pred0).
  + by rewrite filter_pred0 /=.
  + move => j; rewrite !inE.
    apply: (introF imsetP); move => [j' _].
    apply: (elimN eqP); exact: lrshift_distinct.
rewrite cat0s.
have ->: s2 = [seq (rshift m i) | i <- enum J].
- rewrite /s2 filter_map {2}/enum_mem -enumT.
  apply/(congr1 (map _)); apply: eq_filter => j.
  rewrite !inE; apply/idP/idP.
  + by move/imsetP => [j' Hj' /rshift_inj ->].
  + exact: mem_imset.
rewrite (nth_map (enum_default i)) //=.
  by rewrite -cardE ltn_ord.
Qed.

Lemma row_submx_col_mx_rshift :
  let: J' := (@rshift m n) @: J in
  row_submx (col_mx M N) J' =
  castmx (esym (card_imset (mem J) (@rshift_inj m n)), erefl p)
          (row_submx N J).
Proof.
set J' := (@rshift m n) @: J.
apply/matrixP => i j.
rewrite row_submx_mxE.
move/imsetP: (enum_valP i) => [i' Hi' Hi].
rewrite Hi col_mxEd.
rewrite castmxE esymK cast_ord_id row_submx_mxE.
suff: (enum_val i = rshift m (enum_val (cast_ord (card_imset (mem J) (@rshift_inj m n)) i))).
  by rewrite Hi; move/rshift_inj => ->.
by rewrite rshift_enum_val cast_ordK.
Qed.

Lemma lrshift_image_card :
  (#| ((@lshift m n) @: I) :|: ((@rshift m n) @: J) | = #|I| + #|J|)%N.
Proof.
set I' := (@lshift m n) @: I.
set J' := (@rshift m n) @: J.
move/leqifP: (leq_card_setU I' J').
rewrite lrshift_disjoint => /eqP ->.
rewrite card_imset; last exact (@lshift_inj m n).
by rewrite card_imset; last exact (@rshift_inj m n).
Qed.

Lemma lshift_enum_valC (i: 'I_#|I|):
  lshift n (enum_val i) =
  enum_val (cast_ord (esym lrshift_image_card) (lshift #|J| i)).
Proof.
rewrite (enum_val_nth (enum_default (cast_ord (esym lrshift_image_card) (lshift #|J| i)))).
rewrite /enum_mem -enumT.
rewrite enum_lrshift filter_cat.
set s1 := (X in X ++ _).
set s2 := (X in _ ++ X).
have ->: s1 = [seq x <- [seq lshift n i | i <- enum 'I_m] | (mem [set lshift n x | x in I]) x].
- apply: eq_in_filter => j /mapP [j' Hj' ->].
  rewrite !inE.
  have /negbTE ->: ((lshift n j') \notin [set rshift m x | x in J]).
  + apply: (introN idP) => /imsetP [k _].
    apply: (elimN eqP); exact: lrshift_distinct.
  by rewrite orbF.  
rewrite {s1}; set s1 := (X in X ++ _).
have ->: s1 = [seq (lshift n i) | i <- enum I].
- rewrite /s1 filter_map {2}/enum_mem -enumT.
  apply/(congr1 (map _)); apply: eq_filter => j.
  rewrite !inE; apply/idP/idP.
  + by move/imsetP => [j' Hj' /lshift_inj ->].
  + exact: mem_imset.
rewrite {s1}; set s1 := (X in X ++ _).
rewrite nth_cat size_map /= -cardE ltn_ord.
rewrite (nth_map (enum_default i)) //.
by rewrite -cardE ltn_ord.
Qed.

Lemma rshift_enum_valC (i: 'I_#|J|):
  rshift m (enum_val i) =
  enum_val (cast_ord (esym lrshift_image_card) (rshift #|I| i)).
Proof.
rewrite (enum_val_nth (enum_default (cast_ord (esym lrshift_image_card) (rshift #|I| i)))).
rewrite /enum_mem -enumT.
rewrite enum_lrshift filter_cat.
set s1 := (X in X ++ _).
set s2 := (X in _ ++ X).
have ->: s1 = [seq x <- [seq lshift n i | i <- enum 'I_m] | (mem [set lshift n x | x in I]) x].
- apply: eq_in_filter => j /mapP [j' Hj' ->].
  rewrite !inE.
  have /negbTE ->: ((lshift n j') \notin [set rshift m x | x in J]).
  + apply: (introN idP) => /imsetP [k _].
    apply: (elimN eqP); exact: lrshift_distinct.
  by rewrite orbF.  
rewrite {s1}; set s1 := (X in X ++ _).
have ->: s1 = [seq (lshift n i) | i <- enum I].
- rewrite /s1 filter_map {2}/enum_mem -enumT.
  apply/(congr1 (map _)); apply: eq_filter => j.
  rewrite !inE; apply/idP/idP.
  + by move/imsetP => [j' Hj' /lshift_inj ->].
  + exact: mem_imset.
rewrite {s1}; set s1 := (X in X ++ _).
have ->: s2 = [seq x <- [seq rshift m i | i <- enum 'I_n] | (mem [set rshift m x | x in J]) x].
- apply: eq_in_filter => j /mapP [j' Hj' ->].
  rewrite !inE.
  have /negbTE ->: ((rshift m j') \notin [set lshift n x | x in I]).
  + apply: (introN idP) => /imsetP [k _] /esym.
    apply: (elimN eqP); exact: lrshift_distinct.
  done.
rewrite {s2}; set s2 := (X in _ ++ X).
have ->: s2 = [seq (rshift m i) | i <- enum J].
- rewrite /s2 filter_map {2}/enum_mem -enumT.
  apply/(congr1 (map _)); apply: eq_filter => j.
  rewrite !inE; apply/idP/idP.
  + by move/imsetP => [j' Hj' /rshift_inj ->].
  + exact: mem_imset.
rewrite {s2}; set s2 := (X in _ ++ X).
rewrite nth_cat size_map /= -cardE.
rewrite -[X in (_ < X)%N]addn0 ltn_add2l ltn0.
rewrite (nth_map (enum_default i)); rewrite addKn //.
by rewrite -cardE ltn_ord.
Qed.

Lemma row_submx_col_mx :
  let: I' := (@lshift m n) @: I in
  let: J' := (@rshift m n) @: J in
  castmx (lrshift_image_card, erefl p) (row_submx (col_mx M N) (I' :|: J')) =
  col_mx (row_submx M I) (row_submx N J).
Proof.
set I' := (@lshift m n) @: I.
set J' := (@rshift m n) @: J.
apply/matrixP => i l.
rewrite castmxE /= cast_ord_id row_submx_mxE.
set i' := enum_val (_ _ i).
case: (splitP' i') => [j Hij | j Hij].
- rewrite Hij col_mxEu.
  case: (splitP' i) => [k Hik | k Hik];
    move: Hij; rewrite /i' Hik => /esym.
  + rewrite -lshift_enum_valC => /lshift_inj ->.
    by rewrite col_mxEu row_submx_mxE.
  + rewrite -rshift_enum_valC.
    by move/eqP: (lrshift_distinct j (enum_val k)).
- rewrite Hij col_mxEd.
  case: (splitP' i) => [k Hik | k Hik];
    move: Hij; rewrite /i' Hik.
  + rewrite -lshift_enum_valC. 
    by move/eqP: (lrshift_distinct (enum_val k) j).
  + rewrite -rshift_enum_valC => /rshift_inj <-.
    by rewrite col_mxEd row_submx_mxE.
Qed.

End RowSubmxSplit.

Section RowSubmxRowBase.

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

End RowSubmxRowBase.