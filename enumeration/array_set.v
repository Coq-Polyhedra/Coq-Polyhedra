(* -------------------------------------------------------------------- *)
From Coq      Require Import PArray Uint63.
From mathcomp Require Import all_ssreflect finmap.

From Polyhedra Require Import extra_misc.
Require Import refinement.

Require Import extra_int extra_array.
Require Import NArith.BinNat NArith.BinNatDef.
Require Import PArith.BinPos PArith.BinPosDef.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

(* -------------------------------------------------------------------- *)
Module ArrayInterComputation.

Definition array_inter_step {t : Type} (lt_t : rel t) (a b : array t):=
  fun '(i,j,c)=> 
    if (i <? length a)%uint63 then
      if (j <? length b)%uint63 then
        if (lt_t a.[i] b.[j]) then (Uint63.succ i,j,c) else
        if (lt_t b.[j] a.[i]) then (i,Uint63.succ j, c) else
        (Uint63.succ i, Uint63.succ j, Uint63.succ c) 
      else (i,j,c)
    else (i,j,c).

Definition array_inter {t : Type} (lt_t : rel t) (a b : array t):= 
  (IFold.ifold (fun _ ijc => array_inter_step lt_t a b ijc) (length a + length b)%uint63 (0%uint63, 0%uint63, 0%uint63)).2.

End ArrayInterComputation.

Module AIC := ArrayInterComputation.

Section ArrayInterEquiv.

Definition array_inter_step {t : Type} (lt_t : rel t) (a b : array t):=
  fun '(i,j,c)=> 
    if (i < length a)%O then
      if (j < length b)%O then
        if (lt_t a.[i] b.[j]) then (succ i,j,c) else
        if (lt_t b.[j] a.[i]) then (i,succ j, c) else
        (succ i, succ j, succ c) 
      else (i,j,c)
    else (i,j,c).

Definition array_inter {t : Type} (lt_t : rel t) (a b : array t):= 
  (ifold (fun _ ijc => array_inter_step lt_t a b ijc) (length a + length b)%uint63 (0%uint63, 0%uint63, 0%uint63)).2.

Lemma array_interE {t : Type} (lt_t : rel t) (a b : array t):
  AIC.array_inter lt_t a b = array_inter lt_t a b.
Proof.
rewrite /AIC.array_inter /array_inter ifoldE /ifold. 
by elim: (irange0 _).
Qed.

End ArrayInterEquiv.

Section ArrayInter.
(* Hypothesis (r ==> r ==> eq) lt_t lt_T *)

Definition eq_3uple {T : Type} (x y : T * T * T) := [/\ x.1.1 = y.1.1, x.1.2 = y.1.2 & x.2 = y.2].

Lemma rel_array_inter_step {t T : Type}
  (r : t -> T -> Prop)
  (lt_t : rel t) (lt_T : rel T) (i j c: Uint63.int):
  (r =~> r =~> eq) lt_t lt_T ->
  (rel_array r =~> rel_array r =~> eq_3uple) 
    (fun a b=> array_inter_step lt_t a b (i,j,c)) (fun a b=> array_inter_step lt_T a b (i,j,c)). 
Proof.
move=> lt_tT a A aA b B bB /=.
rewrite -(rel_array_length aA) -(rel_array_length bB).
case/boolP: (i < length a)%O=> [i_a|]; last by split.
case/boolP: (j < length b)%O=> [j_b|]; last by split.
under lt_tT; [exact/(rel_array_r aA)|exact/(rel_array_r bB)| ].
case: (lt_T A.[i] B.[j]); first by split.
under lt_tT; [exact/(rel_array_r bB)|exact/(rel_array_r aA)| ].
by case: (lt_T B.[j] A.[i]); split.
Qed.

Lemma rel_array_inter
  {t T : Type} (r : t -> T -> Prop)
  (lt_t : rel t) (lt_T : rel T) :
  (r =~> r =~> eq) lt_t lt_T ->
  (rel_array r =~> rel_array r =~> eq) (array_inter lt_t) (array_inter lt_T).
Proof.
move=> lt_tT a A aA b B bB.
rewrite /array_inter (rel_array_length aA) (rel_array_length bB) !ifold_iter.
set e := iter _ _ _; set E := iter _ _ _.
suff: eq_3uple e E by case.
rewrite {}/e {}/E; elim: (int_to_nat (length A + length B)%uint63); first by split.
move=> k [] /=; set e := iter k _ _; set E := iter k _ _.
case: e=> -[i j] c; case: E=> -[I J] C /= -> -> ->.
apply/rel_array_inter_step; [exact:lt_tT|exact:aA|exact:bB].
Qed. 

End ArrayInter.

Section ArraySetInter.

Context {T : finType} (lt_T : rel T).
Hypothesis irr_lt_T : irreflexive lt_T.
Hypothesis tra_lt_T : transitive lt_T.
Hypothesis eq_lt_T : forall x y, ~~ lt_T x y -> ~~lt_T y x -> x = y. 

(* Definition rel_array_set_ord (a : array T) (A : {set T}) i := 
  rel_sorted lt_T a /\ A = [set a.[k] | k in irange0 i].

Lemma rel_array_set_ord_len a A: rel_array_set_ord a A (length a)= rel_array_set lt_T a A.
Proof. by []. Qed. *)

Definition inter_step_inv a b i j (c : int) := 
  [/\ 
    ((j < length b)%O -> forall k, (k < i)%O -> lt_T a.[k] b.[j]),
    ((i < length a)%O -> forall k, (k < j)%O -> lt_T b.[k] a.[i]),
    (c <= i)%O, (c <= j)%O &
    #|[set a.[k]| k in irange0 i] :&: [set b.[k]| k in irange0 j]| = c
  ].

Lemma array_inter_stepP a b i j c:
  rel_sorted lt_T a -> rel_sorted lt_T b->
  inter_step_inv a b i j c -> let: (i',j',c'):= array_inter_step lt_T a b (i,j,c) in
  inter_step_inv a b i' j' c'.
Proof.
move=> st_a st_b [bj_max ai_max c_i c_j c_inter]; rewrite /array_inter_step.
case: ifP=> // i_a; case:ifP=> // j_b; case: ifP; try case: ifP.
- move=> ai_bj; split=> //.
  + move=> _ k /ltiS_ltVeqS; move/(_ (lt_length_lt_max i_a))=> [k_i|-> //]; exact/bj_max.
  + move=> Si_a k /(ai_max i_a); move/tra_lt_T; apply.
    rewrite sorted_rel_eq //; exact/ltiSi/lt_length_lt_max/i_a.
  + apply/(le_trans c_i)/ltW/ltiSi/lt_length_lt_max/i_a.
  + rewrite -{}c_inter; apply/eq_card=> z; rewrite !inE; apply/idP/idP.
    * case/andP=> /imsetP [ki + z_aki] /imsetP [kj + z_bkj].
      rewrite !mem_irangeE !le0x /=; move/(ltiS_ltVeqS (lt_length_lt_max i_a)).
      case; [by move=> ??; rewrite {1}z_aki z_bkj !imset_f // !mem_irangeE !le0x|].
      move=> ki_i kj_j; move: z_aki; rewrite z_bkj ki_i=> abs.
      by move: (ai_max i_a)=> /(_ kj kj_j); rewrite abs irr_lt_T.
    * case/andP=> /imsetP [ki + z_aki] /imsetP [kj + z_bkj].
      rewrite !mem_irangeE !le0x /= => ki_i kj_j.
      rewrite {1}z_aki z_bkj !imset_f ?mem_irangeE ?le0x //=.
      exact/(lt_trans ki_i)/ltiSi/lt_length_lt_max/i_a.
- move=> bj_ai; split=> //.
  + move=> Sj_b k /(bj_max j_b); move/tra_lt_T; apply.
    rewrite sorted_rel_eq //; exact/ltiSi/lt_length_lt_max/j_b.
  + move=> _ k /ltiS_ltVeqS; move/(_ (lt_length_lt_max j_b))=> [k_i|-> //]; exact/ai_max.
  + apply/(le_trans c_j)/ltW/ltiSi/lt_length_lt_max/j_b.
  + rewrite -{}c_inter; apply/eq_card=> z; rewrite !inE; apply/idP/idP.
    * case/andP=> /imsetP [ki + z_aki] /imsetP [kj + z_bkj].
      rewrite !mem_irangeE !le0x /=; move=> ki_i /(ltiS_ltVeqS (lt_length_lt_max j_b)).
      case; [by move=> ?; rewrite {1}z_aki z_bkj !imset_f // !mem_irangeE !le0x|].
      move=> kj_j; move: z_bkj; rewrite z_aki kj_j=> abs.
      by move: (bj_max j_b)=> /(_ ki ki_i); rewrite abs irr_lt_T.
    * case/andP=> /imsetP [ki + z_aki] /imsetP [kj + z_bkj].
      rewrite !mem_irangeE !le0x /= => ki_i kj_j.
      rewrite {1}z_aki z_bkj !imset_f ?mem_irangeE ?le0x //=.
      exact/(lt_trans kj_j)/ltiSi/lt_length_lt_max/j_b.
- move=> bj_ai ai_bj; move: (@eq_lt_T a.[i] b.[j]); rewrite {}ai_bj {}bj_ai=> /(_ isT isT) ai_bj.
  split.
  + move=> Sj_b k /(ltiS_ltVeqS (lt_length_lt_max i_a)).
    case=> [k_i|->]; [apply/(@tra_lt_T a.[i])|] ; try (rewrite ai_bj sorted_rel_eq ?ltiSi //; exact: (lt_length_lt_max j_b)).
    rewrite sorted_rel_eq //; exact/(lt_trans k_i).
  + move=> Si_a k /(ltiS_ltVeqS (lt_length_lt_max j_b)).
    case=> [k_j|->]; [apply/(@tra_lt_T b.[j])|] ; try (rewrite -ai_bj sorted_rel_eq ?ltiSi //; exact: (lt_length_lt_max i_a)).
    rewrite sorted_rel_eq //; exact/(lt_trans k_j).
  + rewrite -succ_int_mono //; [apply/(le_lt_trans c_i)|]; exact:(lt_length_lt_max i_a).
  + rewrite -succ_int_mono //; [apply:(le_lt_trans c_j)|]; exact:(lt_length_lt_max j_b).
  + set S := _ :&: _; suff ->: S = [set a.[k] | k in irange0 i] :&: [set b.[k] | k in irange0 j] :|: [set a.[i]].
      * rewrite (eqTleqif (leq_card_setU _ _)) ?cards1 ?c_inter ?addn1 ?succ_intE //;
          last exact/(le_lt_trans c_i)/lt_length_lt_max/i_a.
        rewrite disjoint_sym disjoints1 !inE negb_and; apply/orP; left.
        apply/negP=> /imsetP [k]; rewrite mem_irangeE le0x /= => /[dup] k_i + ai_ak.
        rewrite -(sorted_rel_eq irr_lt_T tra_lt_T st_a) // ?ai_ak ?irr_lt_T //.
        exact/(lt_trans k_i).
    apply/setP=> z; rewrite !inE; apply/idP/idP.
      * case/andP=> /imsetP [ki + z_aki] /imsetP [kj + z_bkj].
        rewrite !irange0_succ; try apply/lt_length_lt_max; [exact:i_a|exact:j_b|].
        rewrite !mem_rcons !inE; case/orP=> [/eqP <-|ki_i]; [rewrite z_aki eqxx orbT //|].
        case/orP; [rewrite ai_bj z_bkj=> /eqP <-; rewrite eqxx orbT //|move=> kj_j].
        by rewrite {1}z_aki z_bkj !imset_f.
      * case/orP=> [|/eqP ->]; 
          [|rewrite {2}ai_bj !imset_f ?mem_irangeE ?le0x ?ltiSi //; apply/lt_length_lt_max; [exact:i_a|exact:j_b]].
        case/andP=> /imsetP [ki ki_i z_aki] /imsetP [kj kj_j z_bkj].
        rewrite {1}z_aki z_bkj !imset_f ?irange0_succ ?mem_rcons ?in_cons ?ki_i ?kj_j ?orbT //; 
          apply/lt_length_lt_max; [exact:i_a|exact:j_b].
Qed.

Lemma array_inter_foldP a b n:
  rel_sorted lt_T a -> rel_sorted lt_T b ->
  let: (i,j,c) := (ifold (fun _ ijc => array_inter_step lt_T a b ijc) n (0%uint63, 0%uint63, 0%uint63)) in
  inter_step_inv a b i j c.
Proof.
move=> st_a st_b.
rewrite /ifold; elim/last_ind: (irange0 n)=> [|h t]; last first.
  rewrite foldl_rcons; set F := foldl _ _ _; case: F=> -[i j] c; exact:array_inter_stepP.
rewrite /=; split; rewrite ?lexx /irange0 ?irangee //=; try (by move=> _ k; rewrite ltx0).
by apply/eqP; rewrite cards_eq0 -subset0; apply/subsetP=> x; rewrite inE=> /andP [/imsetP []].
Qed.

Definition stop_inv (a b : array T) i j (n : int):= 
  [/\ (i <= length a)%O, (j <= length b)%O &
  (i < length a)%O -> (j < length b)%O -> (n <= i + j)%nat 
  ].

Lemma array_inter_fold_stop a b n:
  rel_sorted lt_T a -> rel_sorted lt_T b ->
  let: (i,j,c) := (ifold (fun _ ijc => array_inter_step lt_T a b ijc) n (0%uint63, 0%uint63, 0%uint63)) in
  stop_inv a b i j n.
Proof.
move=> st_a st_b;
set F := ifold _ _ _; case F_eq: F=> [[i j] c].
suff: inter_step_inv a b i j c /\ stop_inv a b i j n by case.
move: F_eq.
rewrite {}/F /ifold irange0_iota /stop_inv.
elim: (int_to_nat n) i j c=> [|n' IHn] i' j' c'.
- move: (array_inter_foldP 0%uint63 st_a st_b)=> /=; rewrite /ifold /irange0 irangee /=.
  by move=> ? [<- <- <-]; split=> //; split=> //; rewrite le0x.
- rewrite iotaS_rcons add0n map_rcons foldl_rcons.
  case F_eq: (foldl _ _ _)=> [[i j] c]; case: (IHn _ _ _ F_eq).
  move=> /[dup] ijc_inv [bj_max ai_max c_i c_j c_eq] [i_a j_a n_le] step_ijc'.
  split; first by (move:(array_inter_stepP st_a st_b ijc_inv); rewrite step_ijc').
  move: step_ijc'=> /=; case: ifP=> i_len; last by (case=> [<- <- _]; split=> //; rewrite i_len).
  case: ifP=> j_len; last by (case=> [<- <- _]; split=> //; rewrite j_len).
  case: ifP; try case:ifP.
  + move=> _ [<- <- _]; split=> //; rewrite ?leEint_nat ?succ_intE -?ltEint_nat //; try apply/lt_length_lt_max/i_len.
    by move=> Si_a _; apply/(leq_ltn_trans (n_le i_len j_len)); rewrite addSnnS addnS.
  + move=> _ _ [<- <- _]; split=> //; rewrite ?leEint_nat ?succ_intE -?ltEint_nat //; try apply/lt_length_lt_max/j_len.
    by move=> _ _; apply/(leq_ltn_trans (n_le i_len j_len)); rewrite addnS.
  + move=> _ _ [<- <- _]; split; rewrite ?leEint_nat ?succ_intE -?ltEint_nat //;
      try apply/lt_length_lt_max/i_len; try apply/lt_length_lt_max/j_len.
    by move=> _ _; apply/(leq_ltn_trans (n_le i_len j_len)); rewrite addSnnS !addnS.
Qed.

Lemma rel_array_set_inter: (rel_array_set lt_T =~> rel_array_set lt_T =~> rel_int)
  (array_inter lt_T) (fun A B=> #|A :&:B|).
Proof.
move=> a A [st_a ->] b B [st_b ->]; rewrite /rel_int /= /array_inter.
move: (array_inter_foldP (length a + length b)%uint63 st_a st_b).
move: (array_inter_fold_stop (length a + length b)%uint63 st_a st_b).
case: (ifold _ _ _)=> -[i j] c /= [i_a j_b Slen_ij] [bj_max ai_max _ _ <-].
apply/eq_card=> z; rewrite !inE.
move: i_a j_b; rewrite !le_eqVlt; case/orP=> + /orP [].
- by move=> /eqP -> /eqP ->.
- move=> /eqP + /[dup] j_b /bj_max; move=> -> lt_bj.
  apply/idP/idP; last (case/andP=> /imsetP [ka ka_a z_aka] /imsetP [kb kb_j z_bkb]; 
    rewrite {1}z_aka z_bkb !imset_f //; move: kb_j; rewrite !mem_irangeE !le0x /=; move/lt_trans; exact).
  case/andP=> /imsetP [ka ka_a z_aka] /imsetP [kb kb_b z_bkb]; rewrite {1}z_aka z_bkb !imset_f //=.
  move: ka_a; rewrite !mem_irangeE !le0x /= => /lt_bj; rewrite -z_aka z_bkb.
  by rewrite sorted_rel_eq //; move: kb_b; rewrite mem_irangeE le0x.
- move=> /[dup] /ai_max + i_a /eqP; move=> /[swap] -> bk_ai.
  apply/idP/idP; last by (case/andP=> /imsetP [ki + z_aki] /imsetP [kj kj_j z_bkj];
    rewrite mem_irangeE le0x /= => ki_i; rewrite {1}z_aki z_bkj !imset_f // mem_irangeE le0x (lt_trans ki_i i_a)).
  case/andP=> /imsetP [ki ki_a z_aki] /imsetP [kj kj_b z_bkj].
  apply/andP; split; last rewrite z_bkj imset_f //.
  rewrite z_aki imset_f //; move: kj_b; rewrite !mem_irangeE !le0x /=.
  move/bk_ai; rewrite -z_bkj z_aki sorted_rel_eq //.
  by move: ki_a; rewrite mem_irangeE le0x.
- move=> i_a j_b; move: (Slen_ij i_a j_b); rewrite -sum_length.
  move: i_a j_b; rewrite !ltEint_nat=> /leq_add /[apply].
  move/leq_trans=> /[apply]; rewrite addSnnS !addnS.
  elim: (i + j)=> //.
Qed.

End ArraySetInter.

Section BasisInter.

Context {t : Type} (T : finType) (r : t -> T -> Prop).
Context {lt_t : rel t} {lt_T : rel T}.

Hypothesis lt_tT : (r =~> r =~> eq) lt_t lt_T.
Hypothesis irr_lt_T : irreflexive lt_T.
Hypothesis tr_lt_T : transitive lt_T.
Hypothesis eq_lt_T : forall x y, ~~ lt_T x y -> ~~lt_T y x -> x = y. 

Lemma rel_arr_set_r_inter :
  (@rel_arr_set_r _ _ r lt_T =~> @rel_arr_set_r _ _ r lt_T =~> rel_int) 
    (array_inter lt_t) (fun A B=> #|A :&: B|).
Proof.
apply/rel_equiv_func2; [exact:rel_equiv_refl|exact: rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func2; 
  [exact:(rel_array_inter lt_tT)|exact:rel_array_set_inter].
Qed.

End BasisInter.





(* Section ArraySet.
Definition array_set_i (a : array int) (i : int) (S : {set int}) :=
  S =i [seq a.[k] | k <- irange i (length a)].

Definition array_set (a : array int) (S : {set int}):= array_set_i a 0%uint63 S.

Lemma array_set0 (a : array int) (i : int) (S : {set int}):
  length a = 0%uint63 -> array_set_i a i S -> S = set0.
Proof.
move=> len_a array_seta; apply/setP=> x; rewrite array_seta inE.
move: isT; apply/contraTF=> /mapP [y].
by rewrite mem_irangeE len_a ltx0 andbF.
Qed.

Lemma array_set_length (a : array int) (S : {set int}):
  array_set_i a (length a) S -> S = set0.
Proof.
move=> array_setS; apply/setP=> x; rewrite array_setS !inE.
move: isT; apply/contraTF=> /mapP [y].
rewrite mem_irangeE=> /andP [].
by move/le_lt_trans=> /[apply]; rewrite ltxx.
Qed.

Lemma array_set_mono (a : array int) (i j : int) (I J : {set int}):
  lti_sorted a -> (j <= length a)%O -> (i <= length a)%O ->
  array_set_i a i I -> array_set_i a j J ->
  (i <= j)%O = (J \subset I).
Proof.
move=> stta j_len i_len as_iI as_jJ; apply/idP/idP.
- move=> i_le_j; apply/subsetP=> x.
  rewrite as_jJ=> /mapP [k]; rewrite mem_irangeE=> /andP [j_le_k k_len] ->.
  rewrite as_iI; apply/mapP; exists k=> //; rewrite mem_irangeE k_len andbT.
  exact/(le_trans i_le_j).
- move: j_len; rewrite le_eqVlt; case/orP; first by move/eqP=> ->.
  move=> j_len /subsetP /(_ a.[j]).
  have aj_J: a.[j] \in J by rewrite as_jJ map_f // mem_irangeE j_len lexx.
  move/(_ aj_J); rewrite as_iI=> /mapP [j']; rewrite mem_irangeE.
  by case/andP=> i_le_j' j'_len /(lti_sorted_inj stta j_len j'_len) ->.
Qed. 

Lemma array_set_succ (a : array int) (i : int) (A : {set int}):
  (i < succ i)%O -> lti_sorted a -> array_set_i a i A -> array_set_i a (succ i) (A :\ a.[i]).
Proof.
move=> i_Si stta array_seta x; apply/idP/idP.
- rewrite !inE=> /andP [x_n_ai]; rewrite array_seta.
  case/mapP=> k; rewrite mem_irangeE=> /andP [ik k_len] x_eq.
  apply/mapP; exists k=> //; rewrite mem_irangeE; apply/andP; split=> //.
  move: ik; rewrite le_eqVlt; case/orP.
  + by move/eqP=> ki; move: x_n_ai; rewrite x_eq ki eqxx.
  + by rewrite ltEint_nat leEint_nat (succ_int_ltE i_Si).
- case/mapP=> k; rewrite mem_irangeE=> /andP [Si_k k_len] ->.
  rewrite !inE array_seta; apply/andP; split.
  + apply/contraT; rewrite negbK=> /eqP.
    move/(@lti_sorted_inj _ stta k i k_len).
    move: (lt_le_trans i_Si Si_k)=> i_k; move/(_ (lt_trans i_k k_len)).
    by move/eqP; rewrite eq_sym; move/lt_eqF: i_k=> ->.
  + apply/mapP; exists k=> //; rewrite mem_irangeE k_len andbT.
    exact/ltW/(lt_le_trans i_Si).
Qed.

Lemma array_set_stt_notin (a : array int) (i : int) (A : {set int}) x:
  lti_sorted a -> array_set_i a i A -> (i < length a)%O -> (x < a.[i])%O ->
  x \notin A.
Proof.
move=> stta array_seta i_len x_ai; rewrite array_seta.
apply/contraT; rewrite negbK; case/mapP=> k.
rewrite mem_irangeE=> /andP [ik k_len] x_eq.
by move: x_ai; rewrite x_eq (lti_sorted_eq stta k_len i_len) ltNge ik.
Qed.

Definition arr_to_set (a : array int):=
  [set i | i in arr_to_seq a].

Lemma arr_to_setP a: array_set a (arr_to_set a).
Proof. by move=> x; rewrite /arr_to_set mem_imset_eq. Qed.

Lemma card_arr_to_set a: lti_sorted a -> #|arr_to_set a| = length a.
Proof.
move=> stta; rewrite cardE -size_arr_to_seq.
apply/perm_size/uniq_perm; rewrite ?enum_uniq //; first exact/lti_sorted_uniq.
by move=> x; rewrite mem_enum /arr_to_set mem_imset_eq.
Qed.

End ArraySet.
(* -------------------------------------------------------------------- *)

Module PArrayIUtils.
Definition parrayI (I J : array int):=
  fun '(i, j, c)=>
    if (i <? length I)%uint63 then
      if (j <? length J)%uint63 then
        if (I.[i] <? J.[j])%uint63 then
          ((succ i)%uint63, j, c)
        else if (J.[j] <? I.[i])%uint63 then
          (i, (succ j)%uint63, c)
        else
          ((succ i)%uint63, (succ j)%uint63, (succ c)%uint63)
      else (i, j, c)
    else (i, j, c).

Definition parrayI_iter (I J : array int) (n : int) d :=
  IFold.ifold 
    (fun _ acc=> (parrayI I J) acc) n d.

Definition parrayI_final (I J : array int) :=
  let res := (parrayI_iter I J (length I) (0%uint63, 0%uint63, 0%uint63)) in
  (parrayI_iter I J (length J) res).2.

End PArrayIUtils.

Section PArrayI.
Definition parrayI_iter (I J : array int) (n : int) d:=
  ifold 
    (fun _ acc=> (PArrayIUtils.parrayI I J) acc) 
    n d.

Definition parrayI_final (I J : array int):=
  let res := (parrayI_iter I J (length I) (0%uint63, 0%uint63, 0%uint63)) in
  (parrayI_iter I J (length J) res).2.

Section Equiv.

Lemma parrayI_iterE (I J : array int) (n : int) d:
  PArrayIUtils.parrayI_iter I J n d= parrayI_iter I J n d.
Proof. exact: ifoldE. Qed.

Lemma parrayI_finalE (I J : array int):
  PArrayIUtils.parrayI_final I J = parrayI_final I J.
Proof. by congr snd; rewrite /PArrayIUtils.parrayI_iter !ifoldE. Qed.

End Equiv.

(* -------------------------------------------------------------------- *)
Definition pair_map1 {T T' U : Type} (f : T -> T') (x : T * U) :=
  (f x.1, x.2).

Definition pair_map2 {T U U' : Type} (g : U -> U') (x : T * U) :=
  (x.1, g x.2).

Definition pswap {T U : Type} (x : T * U) := (x.2, x.1).

Lemma parrayI_sym (a b : array int) (ia ib c : int) :
  PArrayIUtils.parrayI a b (ia, ib, c) = 
  pair_map1 pswap (PArrayIUtils.parrayI b a (ib, ia, c)).
Proof.
rewrite /PArrayIUtils.parrayI.
do 4 case: ifP=> //=; rewrite -ltEint; move/lt_trans=> /[apply].
by rewrite ltxx.
Qed.

(* -------------------------------------------------------------------- *)
Lemma parrayI_done (a b : array int) (ia ib c : int) :
  (ia >= length a)%O || (ib >= length b)%O ->
    PArrayIUtils.parrayI a b (ia, ib, c) = ((ia, ib), c).
Proof.
rewrite /PArrayIUtils.parrayI -!lteEint 2!ltNge.
by do 2! case: (leP (length _)) => //= _.
Qed.

(* -------------------------------------------------------------------- *)
Lemma parrayIP (a b : array int) (A B : {set int}) (ia ib c : int) :
     (c <= Order.max ia ib)%O
  -> (ia <= length a)%O
  -> (ib <= length b)%O
  -> array_set_i a ia A
  -> array_set_i b ib B
  -> lti_sorted a
  -> lti_sorted b
  -> let: (ia', ib', c') := PArrayIUtils.parrayI a b (ia, ib, c) in [/\
         [/\ (ia <= ia')%O & (ib <= ib')%O]
       , [/\ (ia' <= length a)%O & (ib' <= length b)%O]
       , [&& ia <? length a & ib <? length b]%uint63 -> ((ia <? ia') || (ib <? ib'))%uint63
       , (c' <= Order.max ia' ib')%O
       & exists A' B', [/\
             array_set_i a ia' A'
           , array_set_i b ib' B'
           , (B' :&: (A :\: A') = set0)
           , (A' :&: (B :\: B') = set0)
           & c' = c + #|(A :\: A') :&: (B :\: B')| :> nat]
     ].
Proof.
move=> le_c; rewrite -!lteEint.
case/boolP: ((ia < length a) && (ib < length b))%O; last first.
- rewrite negb_and -!leNgt=> /(@parrayI_done a b) -> /= -> -> ????.
  do !split=> //; exists A, B; split=> //.
  - by rewrite setDv setI0.
  - by rewrite setDv setI0.
  - by rewrite !setDv setI0 cards0 addn0.
move=> + _ _ => /andP[].
wlog: A B a b ia ib le_c / (a.[ia] <= b.[ib])%O => [wlog|].
- case: (leP a.[ia] b.[ib]); first by apply: wlog.
  move/ltW=> le_bib_aia lt_ia_a lt_ib_b array_seta array_setb stt_a stt_b.
  have := wlog B A b a ib ia; rewrite maxC => /(_ le_c).
  move/(_ le_bib_aia lt_ib_b lt_ia_a array_setb array_seta stt_b stt_a).
  rewrite parrayI_sym; case: PArrayIUtils.parrayI => [[ia' ib'] c'] /=.
  case=> -[-> ->] -[-> ->] /(_ isT); rewrite orbC => -> le_c'.
  case=> [B'] [A'] h; do! split=> //; first by rewrite maxC.
  exists A', B'; case: h => *; split=> //.
  by rewrite setIC.
move=> le_aia_bib lt_ia_a lt_ib_b array_seta array_setb stt_a stt_b.
have lt_iaS: (ia < Uint63.succ ia)%O by
  rewrite ltEint_nat (succ_int_ltE lt_ia_a) ltnSn.
have lt_ibS: (ib < Uint63.succ ib)%O by
  rewrite ltEint_nat (succ_int_ltE lt_ib_b) ltnSn.
rewrite /PArrayIUtils.parrayI -!lteEint !(lt_ia_a, lt_ib_b).
rewrite [(b.[ib] < _)%O]ltNge le_aia_bib /=.
move: le_aia_bib; rewrite le_eqVlt orbC.
case: ltP => /= [lt_aia_bib _|_ /eqP eq_aia_bib].
- do! split=> //; try (by apply: ltW || by move=> _; rewrite !(lt_iaS, lt_ibS)).
  - rewrite leEint_nat (succ_int_ltE lt_ia_a) // -ltEint_nat //.
  - by apply/(le_trans le_c); rewrite le_maxl !le_maxr lexx (ltW lt_iaS) /= orbT.
  exists (A :\ a.[ia]), B; split => //.
  - exact: array_set_succ.
  - rewrite setDDr setDv set0U; apply: disjoint_setI0.
    rewrite disjoint_sym disjoint_subset; apply/subsetP=> x.
    rewrite !inE=> /andP [_ /eqP ->]; exact: (array_set_stt_notin stt_b array_setb).
  - by rewrite setDv setI0.
  - by rewrite setDv setI0 cards0 addn0.
- do! split=> //; try (by apply: ltW || by move=> _; rewrite !(lt_iaS, lt_ibS)).
  - rewrite leEint_nat (succ_int_ltE lt_ia_a) // -ltEint_nat //.
  - rewrite leEint_nat (succ_int_ltE lt_ib_b) // -ltEint_nat //.
  - rewrite (succ_int_lt_max lt_ia_a lt_ib_b).
    set M := (Order.max (length a) (length b)).
    suff ? : (Order.max ia ib < M)%O by 
      rewrite -(@succ_int_lt_mono _ _ M M) //; exact/(le_lt_trans le_c).
    by rewrite lt_maxl !lt_maxr lt_ia_a lt_ib_b /= orbT.
  exists (A :\ a.[ia]), (B :\ b.[ib]); split.
  - exact: array_set_succ. (* OK: a is uniq and we remove the first element *)
  - exact: array_set_succ. (* OK: b is uniq and we remove the first element *)
  - rewrite setDDr setDv set0U; apply: disjoint_setI0.
    rewrite disjoint_sym disjoint_subset; apply/subsetP=> x.
    by rewrite !inE=> /andP [_ /eqP ->]; rewrite eq_aia_bib eqxx.
  - rewrite setDDr setDv set0U; apply: disjoint_setI0.
    rewrite disjoint_sym disjoint_subset; apply/subsetP=> x.
    by rewrite !inE=> /andP [_ /eqP ->]; rewrite eq_aia_bib eqxx.
  - set M := (Order.max (length a) (length b)).
    rewrite (@succ_int_ltE _ M); first apply/(le_lt_trans le_c). 
    - by rewrite lt_maxl !lt_maxr lt_ia_a lt_ib_b /= orbT.
    rewrite -addn1; congr (_ + _).
    rewrite [X in (X :&: _)](_ : _ = [set a.[ia]]).
    - rewrite setDDr setDv set0U; apply/setIidPr/subsetP=> x.
      rewrite inE=> /eqP ->; rewrite array_seta.
      by apply/mapP; exists ia=> //; rewrite mem_irangeE lexx lt_ia_a.
    rewrite [X in (_ :&: X)](_ : _ = [set b.[ib]]).
    - rewrite setDDr setDv set0U; apply/setIidPr/subsetP=> x.
      rewrite inE=> /eqP ->; rewrite array_setb.
      by apply/mapP; exists ib=> //; rewrite mem_irangeE lexx lt_ib_b.
    by rewrite eq_aia_bib setIid cards1.
Qed.

Lemma set_cond {T : finType} {A B A' B' A'' B'': {set T}}:
  (A'' :&: (B' :\: B'')) = set0 -> (A' :&: (B :\: B')) = set0 ->
  (B' \subset B) -> (A'' \subset A') ->
  (A'' :&: (B :\: B'')) = set0.
Proof.
move=> A''_eq A'_eq B'_sub A''_sub.
apply/setP=> x; rewrite !inE; move: isT; apply/contraTF=> /=.
case/and3P=> xA'' xnB''; rewrite -(setID B B') (setIidPr B'_sub) inE.
case/orP.
- by move=> xB'; move/setP: A''_eq=> /(_ x); rewrite !inE xA'' xnB'' xB'.
- move=> xBnB'; move/subsetP: A''_sub=> /(_ _ xA'') xA'.
  by move/setP: A'_eq=> /(_ x); rewrite inE xA' xBnB' inE.
Qed.

Lemma set_cond2 {T : finType} {A B A' B' A'' B'' : {set T}}:
  A' \subset A -> A'' \subset A' -> 
  B' \subset B -> B'' \subset B' ->
  B' :&: (A :\: A') = set0 ->
  A' :&: (B :\: B') = set0 ->
  B'' :&: (A' :\: A'') = set0 ->
  A'' :&: (B' :\: B'') = set0 ->
  (A :\: A') :&: (B :\: B') :|: (A' :\: A'') :&: (B' :\: B'') =
  (A :\: A'') :&: (B :\: B'').
Proof.
move=> subA subA' subB subB' B'_IA A'_IB B''_IA A''_IB.
apply/setP=> x; rewrite !inE.
move: B'_IA A'_IB B''_IA A''_IB=> /setP/(_ x) + /setP/(_ x) + /setP/(_ x) + /setP/(_ x).
rewrite !inE.
case/boolP: (x \in A'')=> /=; first by move/subsetP: subA'=> /[apply] ->.
case/boolP: (x \in B'')=> /=; rewrite ?andbF.
  by move/subsetP: subB'=> /[apply] ->; rewrite !andbF /=.
case/boolP: (x \in A')=> /=; case/boolP: (x \in B')=> //=; rewrite ?andbF ?orbF //.
- by move/subsetP: subB=> /[apply] ->; move/subsetP: subA=> /[apply] ->.
- by move=> _ _ _ _ _ ->; rewrite andbF.
- by move=> _ _ _ _ ->.
Qed.

Lemma parrayI_iter_n (a b : array int) (n n': int) d:
  let res := parrayI_iter a b n d in
  parrayI_iter a b n' res =
  iter (int_to_nat n + int_to_nat n')%nat (PArrayIUtils.parrayI a b) d.
Proof. by rewrite /parrayI_iter !ifold_iter addnC iterD. Qed.


Lemma parrayI_iterP (a b : array int) (A B : {set int}) (n : nat):
  lti_sorted a -> lti_sorted b ->
  array_set_i a 0%uint63 A -> array_set_i b 0%uint63 B ->
  let: (ia', ib', c') := 
    iter n (PArrayIUtils.parrayI a b) (0%uint63, 0%uint63, 0%uint63) in
  [/\ (ia' <= length a)%O, (ib' <= length b)%O,
    (c' <= Order.max ia' ib')%O &
    ((ia' < length a)%O && (ib' < length b)%O -> (n <= (ia' + ib'))%nat) /\
    exists A' B', [/\
    array_set_i a ia' A'
  , array_set_i b ib' B'
  , (B' :&: (A :\: A') = set0)
  , (A' :&: (B :\: B') = set0)
  & c' = #|(A :\: A') :&: (B :\: B')| :> nat]].
Proof.
move=> stta sttb array_seta array_setb.
elim: n=> /= [|n].
- split; rewrite ?le0x //; split=> //.
  by exists A, B; rewrite !setDv !setI0 ?cards0; split.
- case: (iter n _ _)=> -[i j] c.
  case=> i_len_a j_len_b c_max [n_h] /[dup] AB'_ex [A'] [B'].
  case=> arr_setA' arr_setB' B'_IA A'_IB c_eq.
  move: (parrayIP c_max i_len_a j_len_b arr_setA' arr_setB' stta sttb).
  case: (PArrayIUtils.parrayI _ _ _)=> -[i' j' c'].
  case=> -[ii' jj'] [i'_len_a j'_len_b] len_ltb c'_max.
  case=> A'' [B''] [arr_setA'' arr_setB'' B''_AI A''_BI c'_eq].
  split=> //; split.
  + case/andP=> i'_len_ltb j'_len_ltb.
    move: (le_lt_trans ii' i'_len_ltb) (le_lt_trans jj' j'_len_ltb)=> i_len_ltb j_len_ltb.
    apply/(leq_ltn_trans (n_h _)); rewrite ?i_len_ltb ?j_len_ltb //.
    move: len_ltb; rewrite -ltEint i_len_ltb j_len_ltb /=.
    case/(_ isT)/orP; rewrite ltEint_nat.
    * rewrite addnC [X in _ -> (_ < X)%nat]addnC.
      by apply/leq_ltn_addn; rewrite -leEint_nat.
    * by apply/leq_ltn_addn; rewrite -leEint_nat.
  + exists A'', B''; split=> //.
    * apply:(set_cond B''_AI B'_IA)=> //.
      - rewrite -(array_set_mono stta _ _ array_seta arr_setA') ?le0x //.
      - rewrite -(array_set_mono sttb _ _ arr_setB' arr_setB'') //.
    * apply:(set_cond A''_BI A'_IB)=> //.
      - rewrite -(array_set_mono sttb _ _ array_setb arr_setB') ?le0x //.
      - rewrite -(array_set_mono stta _ _ arr_setA' arr_setA'') //.
      * rewrite c'_eq c_eq -(eqTleqif (leq_card_setU _ _)).
        - rewrite disjoint_subset; apply/subsetP=> x. 
          rewrite !inE !negb_and !negbK.
          by case/and3P=> /andP [-> _ -> _]; rewrite orbT.
        - congr card; congr mem; congr pred_of_set.
          rewrite set_cond2 //.
          + by rewrite -(array_set_mono stta _ _ array_seta arr_setA') ?le0x.
          + by rewrite -(array_set_mono stta _ _ arr_setA' arr_setA'').
          + by rewrite -(array_set_mono sttb _ _ array_setb arr_setB') ?le0x.
          + by rewrite -(array_set_mono sttb _ _ arr_setB' arr_setB'').
Qed.

Lemma parrayI_finalP a b A B:
  lti_sorted a -> lti_sorted b ->
  array_set a A -> array_set b B ->
  parrayI_final a b = #| A :&: B| :> nat.
Proof.
move=> stta sttb array_seta array_setb.
rewrite /parrayI_final parrayI_iter_n.
have:= (parrayI_iterP _ stta sttb array_seta array_setb).
move/(_ (length a + length b)%nat).
case: (iter _ _ _) => -[ia ib] c [ia_len ib_len c_max] [n_max].
case=> A' [B'] [array_set_ia array_set_ib A'_eq B'_eq] /= ->.
have: ia = length a \/ ib = length b.
- move: ia_len; rewrite le_eqVlt=> /orP [/eqP ->|ia_len]; first by left.
  move: ib_len; rewrite le_eqVlt=> /orP [/eqP ->|ib_len]; first by right.
  move: n_max; rewrite ia_len ib_len /= => /(_ isT).
  move: ia_len ib_len; rewrite !ltEint_nat=> /ltnW/leq_add /[apply].
  by rewrite addnS ltnNge => /negPf ->.
wlog : A B A' B' ia ib a b stta sttb array_seta array_setb n_max ia_len ib_len array_set_ia array_set_ib c_max A'_eq B'_eq/
  ia = length a => [wlog|].
- move/[dup]; case; [apply: (wlog _ _ _ _ _ _ _ _ _ _ _ _)=> // |].
  move=> + /or_comm; rewrite setIC [(A :&: B)]setIC.
  have:= (wlog B A B' A' ib ia b a _ _ _ _).
  apply=> //; rewrite 1?andbC 1?add_comm 1?[(ib + ia)%uint63]add_comm 1?maxC //.
  by rewrite addnC [ib + ia]addnC.
- move=> ia_eq _; move: array_set_ia; rewrite ia_eq=> /array_set_length A'_0.
  move: A'_eq; rewrite A'_0 setD0 setIDA=> B'A.
  congr card; congr mem; congr pred_of_set.
  apply/setP=> x; move/setP: B'A=> /(_ x).
  by rewrite !inE; case: (x \in B')=> //= ->.
Qed.

End PArrayI.
Section ArraySetOrd.

Context {m : nat}.
Definition set_int_ord (A : {set int}) (B : {set 'I_m}):=
  [forall i : 'I_m, val i \in [seq int_to_nat i | i in A] == (i \in B)] &&
  [forall i : int, i \in A == (int_to_nat i \in [seq val i | i in B])].

Lemma set_int_ordP (A : {set int}) (B : {set 'I_m}):
  reflect
    ([seq int_to_nat i | i in A] =i [seq val i | i in B])
    (set_int_ord A B).
Proof.
apply/(iffP idP).
- case/andP=> /forallP hA /forallP hB x.
  apply/idP/idP.
  + case/mapP=> x'; rewrite mem_enum.
    by move/eqP: (hB x')=> -> + ->.
  + case/mapP=> x'; rewrite mem_enum.
    by move/eqP: (hA x')=> <- + ->.
- move=> h; apply/andP; split.
  + apply/forallP=> x; rewrite h mem_map ?mem_enum //.
    exact/val_inj.
  + apply/forallP=> x; rewrite -h mem_map ?mem_enum //.
    exact/int_to_nat_inj.
Qed.

Lemma set_int_ord_card A B: set_int_ord A B -> #|A| = #|B|.
Proof.
move/set_int_ordP/uniq_perm; rewrite !map_inj_uniq;
  [exact: int_to_nat_inj|exact: val_inj | ].
move/(_ (enum_uniq _) (enum_uniq _))/perm_size.
by rewrite !cardE !size_map.
Qed.

Definition array_set_ord (a : array int) (A : {set 'I_m}) : bool :=
  set_int_ord (arr_to_set a) A.

Lemma array_set_ord_card a A: lti_sorted a -> array_set_ord a A -> #|A| = length a.
Proof. by move=> stta /set_int_ord_card <-; rewrite card_arr_to_set. Qed.

Lemma array_set_ord_inj (a b : array int) (A B : {set 'I_m}):
  lti_sorted a -> lti_sorted b ->
  array_set_ord a A -> array_set_ord b B ->
  reflect (A = B) (eq_array_int a b).
Proof.
move=> stta sttb as_aA as_bB; apply/(iffP idP).
- case/eq_array_intP=> eq_len nth_eq; apply/setP=> x.
  move/set_int_ordP: as_aA=> /(_ (val x)); rewrite mem_map ?mem_enum; first exact: val_inj.
  move/set_int_ordP: as_bB=> /(_ (val x)); rewrite mem_map ?mem_enum; first exact: val_inj.
  move=> <- <-; congr in_mem; congr mem.
  apply/eq_image=> // y; rewrite !arr_to_setP -eq_len.
  congr in_mem; congr mem; apply/eq_in_map=> k.
  rewrite mem_irangeE le0x /=; exact: nth_eq.
- move=> eq_AB; apply/eq_array_intP.
  suff: arr_to_seq a = arr_to_seq b.
  + move=> a2s_ab.
    split; move/(congr1 size): (a2s_ab); rewrite !size_arr_to_seq.
      by move/int_to_nat_inj.
    move=> len_ab i; rewrite ltEint_nat => /[dup] i_len_a.
    rewrite len_ab => i_len_b.
    move: (nth_arr_to_seq i_len_a) (nth_arr_to_seq i_len_b).
    rewrite int_to_natK => <- <-; rewrite a2s_ab.
    by apply/nth_eq_dflt; rewrite size_arr_to_seq.
  apply/lt_sorted_eq=> // x.
  move/set_int_ordP: as_aA=> /(_ (int_to_nat x)). 
  move/set_int_ordP: as_bB=> /(_ (int_to_nat x)).
  rewrite !mem_image; try exact: int_to_nat_inj.
  by rewrite !mem_imset_eq // => -> ->; rewrite eq_AB.
Qed.

Lemma array_set_ord_mem (a : array int) (A : {set 'I_m}) (i : 'I_m):
  array_set_ord a A -> i \in A ->
  exists2 j : int, (j < length a)%O & int_to_nat a.[j] = val i.
Proof.
case/andP=> /forallP /(_ i) /eqP <- _.
case/mapP=> ?; rewrite mem_enum=> /imsetP [?].
case/mapP=> j; rewrite mem_irangeE le0x /=.
by move=> ? -> -> ->; exists j.
Qed.

Lemma parrayI_final_ord a b A B:
  lti_sorted a -> lti_sorted b ->
  array_set_ord a A -> array_set_ord b B ->
  #|A :&: B| = parrayI_final a b.
Proof.
move=> stta sttb as_aA as_bB.
move: (arr_to_setP a) (arr_to_setP b)=> a2s_a a2s_b.
rewrite (parrayI_finalP stta sttb a2s_a a2s_b).
rewrite -(size_image int_to_nat) -(size_image (@nat_of_ord m)).
apply/perm_size/uniq_perm; rewrite ?map_inj_uniq ?enum_uniq //.
  exact: val_inj. exact: int_to_nat_inj.
move=> x; apply/idP/idP.
- case/imageP=> x'; rewrite inE=> /andP [].
  move/(image_f val)=> + /(image_f val). 
  move:as_aA as_bB=> /set_int_ordP <- /set_int_ordP <-.
  case/imageP=> i i_a i_eq /imageP [j j_b].
  rewrite i_eq=> /int_to_nat_inj ij ->.
  by apply/imageP; exists i=> //; rewrite inE i_a ij j_b.
- case/imageP=> i; rewrite inE=> /andP [].
  move/(image_f int_to_nat)=> + /(image_f int_to_nat).
  move: as_aA as_bB=> /set_int_ordP -> /set_int_ordP ->.
  case/imageP=> p pA p_eq /imageP [q qB]; rewrite p_eq=> /val_inj pq ->.
  by apply/imageP; exists p=> //; rewrite inE pA pq qB.
Qed.

Section ArrToSetOrd.

Definition arr_to_set_ord (a : array int) : {set 'I_m} := [set j : 'I_m | nat_to_int j \in arr_to_set a].

Lemma arr_to_set_ordP (a : array int):
  (m < int_threshold)%nat ->
  (forall i, (i < length a)%O -> (a.[i] < m)%nat) ->
  array_set_ord a (arr_to_set_ord a).
Proof.
move=> m_threshold a_m.
apply/set_int_ordP; move=> x; apply/idP/idP.
- case/imageP=> j /[swap] ->; rewrite arr_to_setP.
  case/mapP=> i; rewrite mem_irangeE le0x /= => /[dup] i_len /a_m ai_m ->.
  apply/imageP; exists (Ordinal ai_m)=> //.
  rewrite inE int_to_natK arr_to_setP.
  by apply/mapP; exists i=> //; rewrite mem_irangeE le0x i_len.
- case/imageP=> /= j /[swap] ->; rewrite inE=> j_arr2set.
  apply/mapP; exists (nat_to_int j); rewrite ?mem_enum //.
  rewrite nat_to_intK // inE; exact/(@ltn_trans m).
Qed.

End ArrToSetOrd.


End ArraySetOrd. *)
