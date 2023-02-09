(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum zmodp matrix finmap vector order.
Require Import NArith.BinNat NArith.BinNatDef.

Import Order.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.

Lemma ord0_false (i: 'I_0) : False.
Proof.
by move: (ltn_ord i); rewrite ltn0.
Qed.

Lemma ord1_eq0 (i: 'I_1) : (i = ord0).
Proof.
apply/ord_inj => /=.
by move: (ltn_ord i); rewrite ltnS leqn0 => /eqP.
Qed.

Lemma ord1_setT : setT = [set ord0] :> {set 'I_1}.
Proof.
apply/setP => i; rewrite !inE.
by rewrite [i]ord1_eq0.
Qed.

Lemma enum_ord0_nil : (enum 'I_0) = [::].
Proof. by apply/eqP; rewrite -size_eq0 size_enum_ord. Qed.

Lemma exists_andP (T : Type) (A : pred T) (B : pred T) :
  (exists x, (A x /\ B x)) <-> (exists x, (A x && B x)).
Proof.
by split; move => [x H]; exists x; apply/andP.
Qed.

Lemma eq_imply (b b' : bool) : b = b' -> (b -> b').
Proof.
by move ->.
Qed.

Lemma eq_imply2 (b b' : bool) : b = b' -> (b' -> b).
Proof.
by move ->.
Qed.

Arguments exists_andP {T A B}.
Prenex Implicits exists_andP.

Lemma ex_iff T (P1 P2 : T -> Prop) :
  (forall x : T, P1 x <-> P2 x) -> ((exists x, P1 x) <-> (exists x, P2 x)).
Proof.
by move=> H; split; move=> [x Hx]; exists x; apply/H.
Qed.

Lemma ex2_iff T (P1 P2 Q : T -> Prop) :
  (forall x : T, P1 x <-> P2 x) -> ((exists2 x, P1 x & Q x) <-> (exists2 x, P2 x & Q x)).
Proof.
by move=> H; split; move=> [x Hx]; exists x; try by apply/H.
Qed.

Lemma intro_existsT (T: Type) (P: T -> Prop) (b: bool) (H: reflect (exists x, P x) b) (x: T):
  P x -> b.
Proof.
by move => Hx; apply/H; exists x.
Qed.


Lemma subseq_head (T : eqType) (x : T) (s1 s2 : seq T) :
  subseq (x :: s1) s2 -> x \in s2.
Proof.
rewrite -sub1seq.
apply: subseq_trans.
- by rewrite sub1seq; apply: mem_head.
Qed.

Lemma mem_subseq_nnil (T : eqType) (x : T) (s1 s2 : seq T) :
  subseq (x :: s1) s2 -> (x \in s2) /\ {subset s1 <= s2}.
Proof.
move/mem_subseq => H; split; first by move: (H x (@mem_head _ x s1)).
move => y Hy; apply: (H y).
- by apply: mem_behead.
Qed.

(*TODO : find a better name ?*)
Lemma subseq_lcat {T : eqType} (l A B : seq T) :
  subseq l (A ++ B) -> (forall x, x \in l -> x \notin B) ->
  subseq l A.
Proof.
move=> subAB HB.
elim: l A B subAB HB=> [|h t IH].
  by move=> ??; rewrite !sub0seq.
move=> A B subAB HB.
move: (HB h); rewrite in_cons eqxx /= => /(_ isT) /negPf hnB.
move/mem_subseq: (subAB) => /(_ h); rewrite in_cons eqxx /=.
move/(_ isT); rewrite mem_cat hnB orbF=> hA.
move: (in_take (index h A) hA); rewrite ltnn.
case/path.splitP: hA subAB HB=> Ag Ad + HB.
elim: Ag=> [| Agh Agt IHAg].
- rewrite /= eqxx=> subAB _; apply/(IH Ad B)=> //.
  by move=> x xt; apply: HB; rewrite in_cons xt orbT.
- rewrite rcons_cons /= in_cons => + /Bool.orb_false_elim [AghF AgtF].
  rewrite AghF=> subAB; exact: IHAg.
Qed.

Lemma subseq_split_cat {T : eqType} (l A B : seq T) :
  subseq l (A ++ B) -> exists A' B',
  [/\ l = A' ++ B', subseq A' A & subseq B' B].
Proof.
case: A=> [|a ta]; first by (move=> /= ?; exists [::]; exists l).
case: B=> [|b tb].
  by rewrite cats0; move=> ?; exists l; exists [::]; rewrite cats0.
set A := a :: ta; set B := b :: tb.
case/subseqP=> m /[dup] size_m; rewrite -(cat_take_drop (size A) m).
set mA := (take _ _); set mB := (drop _ _).
rewrite !size_cat=> size_mAB.
have size_mA: size mA = size A.
- rewrite size_take; suff ->: (size A < size m)%nat by [].
  by rewrite size_m size_cat -ltn_psubLR ?subnn.
rewrite mask_cat // => ?; exists (mask mA A); exists (mask mB B).
by rewrite !mask_subseq.
Qed.

Lemma take_rcons_last {T : Type} h (t : seq T) : take (size t) (rcons t h) = t.
Proof. by elim: t=> //= ?? ->. Qed.

Lemma take_rcons_body {T : Type} h (t : seq T) n : (n <= size t)%nat -> take n (rcons t h) = take n t.
Proof.
elim: n t=> [|n IH] t; rewrite ?take0 //.
case: t=> [|a l]; rewrite ?ltn0 //=.
by move/ltnSE/IH=> ->.
Qed.

Lemma mem_body {T : eqType} (x h : T) (t : seq T):
  x \in t -> x \in h :: t.
Proof.
elim: t=> //= a l IH; rewrite in_cons.
case/orP=> [/eqP ->|/IH]; rewrite !inE ?eq_refl ?orbT //.
case/orP=> [->|->]; rewrite ?orbT //.
Qed.


Lemma discr_seq (T : eqType) (x : T) (s : seq T) (P : pred T) :
  ~~ P x -> all P s -> x \notin s.
Proof.
move => Hx.
elim: s => [ | a s IH].
- by rewrite in_nil.
- rewrite /=; move/andP => [ H H'].
  rewrite in_cons negb_or.
  apply/andP; split.
  + apply/eqP => H''; move/negP: Hx; rewrite H''; done.
  + by apply: IH.
Qed.

Lemma iter_fixpoint (T : Type) (f : T -> T) (n : nat) : forall x: T, f x = x -> iter n f x = x.
Proof.
move => x Hx.
elim: n => [ | n IHn]; first by done.
by rewrite iterS IHn.
Qed.

Lemma card_sub_ord (k : nat) (P : 'I_k -> bool) :
  (#|[set l : 'I_k | P l]| <= k)%nat.
Proof.
  set S := [set l : 'I_k | P l].
  suff: (#|S| <= #|'I_k|)%nat.
    - by rewrite card_ord.
  exact: max_card.
Qed.

Lemma setT_proper (T : finType) (S : {set T}) : (setT \proper S) = false.
Proof.
by apply/negbTE/negP; move/properP => [_ [i _]]; rewrite inE.
Qed.

Lemma size_enum_predC1 (n : nat) (i : 'I_n) :
  size [seq i0 <- enum 'I_n | i0 != i] = n.-1.
Proof.
move/eqP: (count_predC (xpred1 i) (enum (ordinal_finType n))).
rewrite size_enum_ord count_uniq_mem; last by apply: enum_uniq.
rewrite mem_enum /= => ?.
apply/eqP.
rewrite size_filter -(eqn_add2r 1) addnC addn1 prednK //.
apply: contraT.
rewrite -(ltn0 i) -leqNgt => ?.
by apply: (leq_trans (ltn_ord i)).
Qed.

Lemma predC1_take_enum (n : nat) (i : 'I_n) :
  [seq i0 <- take i (enum 'I_n) | i0 != i] = take i (enum 'I_n).
Proof.
apply/all_filterP/allP => j j_in_take.
apply: contraT; rewrite negbK => /eqP j_eq_i.
move: (nth_index i j_in_take).
rewrite -index_mem size_take size_enum_ord (ltn_ord i) in j_in_take.
rewrite nth_take //.
move: (ltn_trans j_in_take (ltn_ord i)) => index_j_lt_n.
rewrite -{2}j_eq_i in j_in_take.
have ->: nth i (enum 'I_n) (index j (take i (enum 'I_n))) = Ordinal index_j_lt_n
  by apply: ord_inj; rewrite (nth_enum_ord _ index_j_lt_n).
move => index_eq_j.
by rewrite -(ltnn j) -{1}index_eq_j.
Qed.

Lemma take_val_predC1_enum (n : nat) (i : 'I_n) :
  take i (map val [seq i0 <- enum 'I_n | i0 != i]) = iota 0 i.
Proof.
rewrite -[enum 'I_n](cat_take_drop i) filter_cat predC1_take_enum map_cat -map_take take_size_cat;
  last by rewrite !size_map size_take -enumT size_enum_ord (ltn_ord i).
apply: (@eq_from_nth _ 0%nat _ _ _).
- by rewrite !size_map size_take -enumT size_enum_ord (ltn_ord i) size_iota.
- move => k k_lt_size.
  have k_lt_i: (k < i)%nat by rewrite !size_map size_take -enumT size_enum_ord (ltn_ord i) in k_lt_size.
  rewrite (@nth_map _ i _ 0%nat); last by rewrite size_map in k_lt_size.
  rewrite nth_iota // add0n (@nth_map _ i _ i); last by rewrite !size_map in k_lt_size.
  rewrite nth_take //= -enumT nth_enum_ord //.
  exact: (ltn_trans k_lt_i (ltn_ord i)).
Qed.

Lemma predC1_drop_enum (n : nat) (i : 'I_n) :
  [seq i0 <- drop i (enum 'I_n) | i0 != i] = drop i.+1 (enum 'I_n).
Proof.
have i_lt_size_enum : (i < size (enum 'I_n))%nat
  by rewrite size_enum_ord (ltn_ord i).
rewrite (drop_nth i i_lt_size_enum) /= nth_ord_enum eq_refl /=.
apply/all_filterP.
rewrite all_count -(@count_predC _ (pred1 i)).
suff ->: ((count_mem i) (drop i.+1 (enum 'I_n)) = 0)%N by rewrite add0n.
suff H: ((count_mem i) (take i.+1 (enum 'I_n)) = 1)%N
  by move/eqP: (count_uniq_mem i (enum_uniq 'I_n));
  rewrite -{1}[(enum 'I_n)](cat_take_drop i.+1) mem_enum /= count_cat H -[X in _ == X]addn0 eqn_add2l => /eqP <-.
have uniq_take: uniq (take i.+1 (enum 'I_n))
  by apply: (@subseq_uniq _ _ (enum 'I_n) _ (enum_uniq 'I_n));
  rewrite -{2}[(enum 'I_n)](cat_take_drop i.+1);
  exact: prefix_subseq.
rewrite (count_uniq_mem i uniq_take) -index_mem.
move: (@nth_take i.+1 _ i i (ltnSn i) (enum 'I_n)); rewrite nth_ord_enum => nth_eq_i.
have i_lt: (i < (if i.+1 < n then i.+1 else n))%nat
  by case: (boolP (i.+1 < n)%nat); [rewrite ltnSn | rewrite (ltn_ord i)].
by rewrite size_take size_enum_ord -{1}nth_eq_i (index_uniq _ _ uniq_take) ?size_take ?size_enum_ord !i_lt.
Qed.

Lemma drop_enum_predC1 (n : nat) (i : 'I_n) :
  drop i (map val [seq i0 <- enum 'I_n | i0 != i]) = (iota i.+1 (n-i.+1)%nat).
Proof.
rewrite -[enum 'I_n](cat_take_drop i) filter_cat predC1_take_enum map_cat drop_size_cat;
  last by rewrite !size_map size_take size_enum_ord (ltn_ord i).
rewrite predC1_drop_enum map_drop val_enum_ord.
apply: (@eq_from_nth _ 0%nat _ _ _).
- by rewrite size_drop !size_iota.
- move => k k_lt_size.
  rewrite size_drop size_iota in k_lt_size.
  rewrite nth_drop nth_iota; last by rewrite -ltn_subRL.
  by rewrite add0n nth_iota //.
Qed.

Lemma nth_predC1_enum (n k : nat) (i : 'I_n) :
  (k < n.-1)%nat ->
  (nat_of_ord (nth i [seq i0 <- enum 'I_n | i0 != i] k) = (i <= k) + k)%nat.
Proof.
move => k_lt_n_minus_1.
rewrite -(@nth_map _ _ _ 0%nat); last by rewrite size_enum_predC1.
have ->: map val [seq i0 <- enum 'I_n | i0 != i] = (iota 0 i) ++ (iota i.+1 (n-i.+1)%nat)
  by rewrite -[LHS](cat_take_drop (val i)) take_val_predC1_enum drop_enum_predC1.
rewrite nth_cat size_iota (leqNgt i k).
case: (boolP (k < i)%nat) => [? /= | i_leq_k /=]; first by rewrite nth_iota.
rewrite -leqNgt in i_leq_k.
rewrite nth_iota; first by rewrite -addn1 [X in (X+_)%nat]addnC -addnA (subnKC i_leq_k).
have k_lt_n: (k < n)%nat by apply: (leq_trans _ (leq_pred n)).
rewrite -[X in (n - X)%nat]addn1 addnC subnDA subn1.
apply: (ltn_sub2r _ k_lt_n_minus_1).
by apply: (leq_ltn_trans i_leq_k).
Qed.

Lemma predC1_enum (n : nat) (i : 'I_n) :
  [seq i0 <- enum (ordinal_finType n) | i0 != i] = [seq lift i i0 | i0 <- enum (ordinal_finType n.-1)].
Proof.
have size_eq: size [seq i0 <- enum (ordinal_finType n) | i0 != i] = size [seq lift i i0 | i0 <- enum (ordinal_finType n.-1)]
  by rewrite size_map size_enum_ord size_enum_predC1.
apply: (@eq_from_nth _ i _ _ size_eq) => k k_lt_size.
have k_lt_size': (k < size (enum (ordinal_finType n.-1)))%nat by rewrite size_eq size_map in k_lt_size.
have k_lt_n_minus_1: (k < n.-1)%nat by rewrite size_enum_ord in k_lt_size'.
rewrite (@nth_map _ (Ordinal k_lt_n_minus_1) _ i (lift i) _ _ k_lt_size') /=.
apply: ord_inj.
have ->: nth (Ordinal k_lt_n_minus_1) (enum 'I_n.-1) k = (Ordinal k_lt_n_minus_1)
  by apply: ord_inj; exact: (@nth_enum_ord _ (Ordinal k_lt_n_minus_1) _ k_lt_n_minus_1).
rewrite /= /bump.
by apply: nth_predC1_enum.
Qed.

Lemma ltn_divLR' m p d : (d > 0)%nat -> (m < p * d)%nat -> (m %/ d < p)%nat.
Proof.
by move => H ?; rewrite (ltn_divLR _ _ H).
Qed.


Lemma subn_inj (p q r : nat) : (p <= r)%nat -> (q <= r)%nat -> (r - p == r - q)%nat = (p == q).
Proof.
move => p_le_r q_le_r; apply/eqP/idP; last by move/eqP => ->.
move/(congr1 (addn^~ p)); rewrite subnK // addnC.
move/(congr1 (addn^~ q)); rewrite -addnA subnK // addnC.
by move/addIn => ->.
Qed.

Lemma eq_subl {T : Type} {m m' m'': mem_pred T} :
  eq_mem m m' -> (sub_mem m m'' <-> sub_mem m' m'').
Proof.
by move => eq; split => sub x x_in; apply/sub; rewrite ?eq // -?eq.
Qed.

Lemma eq_subr {T : Type} {m m' m'': mem_pred T} :
  eq_mem m' m'' -> (sub_mem m m' <-> sub_mem m m'').
Proof.
by move => eq; split => sub x x_in; [rewrite -eq | rewrite eq]; apply/sub.
Qed.

Lemma ltn_min m1 m2 n: (n < minn m1 m2)%nat = (n < m1)%nat && (n < m2)%nat.
Proof.
wlog le_m21: m1 m2 / (m2 <= m1)%nat.
  case/orP: (leq_total m2 m1)=> ?; last rewrite minnC andbC; exact.
rewrite /minn [X in (if X then _ else _)]ltnNge le_m21 /=; case lt_n_m1: (n < m1)%nat => //=.
apply/contraFF: lt_n_m1 => /leq_trans; exact.
Qed.

Lemma map_enum_ord_iota {T : Type} {n : nat} (f : nat -> T):
  [seq f i | i <- iota 0 n] = [seq f (val i) | i <- enum 'I_n ].
Proof. by rewrite [in RHS]map_comp val_enum_ord. Qed.

End Basic.

Section Big.

Variables (R : eqType) (idx : R).
Variable I : eqType.

Local Notation "1" := idx.

Variable op : Monoid.com_law 1.

Lemma big_and_idx r (P Q : pred I) F :
  (forall i, i \in r -> P i && ~~(Q i) -> F i = idx) -> \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- r | (P i) && Q i) F i.
Proof.
move => H.
rewrite (bigID Q).
have H': \big[op/idx]_(i <- r | P i && ~~Q i) F i = idx.
apply: big1_seq.
- by move => i /andP [ Hi' Hi'']; apply: H.
  by rewrite H' Monoid.mulm1.
Qed.

Lemma eq_big_seq_congr2 (T T' : eqType) (r : seq I) (F : T -> T' -> R) (F1 F2 : I -> T) (F' : I -> T') :
  {in r, (F1 =1 F2)} -> \big[op/idx]_(i <- r) F (F1 i) (F' i) = \big[op/idx]_(i <- r) F (F2 i) (F' i).
Proof.
move => H; apply: eq_big_seq.
move => i Hi; apply: congr2; last by done.
- by apply: H.
Qed.

Lemma eq_bigl_seq r (P1 P2 : pred I) F :
  {in r, P1 =1 P2 } ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Proof.
move => H.
rewrite big_seq_cond [in RHS]big_seq_cond.
apply: eq_bigl => i.
- by apply: andb_id2l; apply: H.
Qed.

End Big.

Arguments big_and_idx [R idx I op r P Q F].
Arguments eq_big_seq_congr2 [R idx I op T T' r F].
Arguments eq_bigl_seq [R idx I op r P1 P2 F].

Section ExtraNum.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory Num.Def.

Variable R : realFieldType.
Variable m n : nat.

Lemma ltr_neq (x y : R) : x < y -> x != y.
Proof.
by rewrite lt_neqAle => /andP [].
Qed.

Lemma addr_ltr_le0 (x y : R) :
  x < 0 -> y <= 0 -> x + y < 0.
Proof.
by rewrite -{3}[0]addr0; apply: ltr_le_add.
Qed.

Lemma sumr_le0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (F i <= 0)) -> \sum_(i <- r | P i) (F i) <= 0.
Proof.
apply: (big_ind (fun v => v <= 0)); first by done.
- move => x y.
  by rewrite -!oppr_ge0 opprD; apply: addr_ge0.
Qed.

Lemma sumr_ltrP (I : finType) (F : I -> R) (G : I -> R) :
  (forall i, F i <= G i) -> (exists i, F i < G i) -> \sum_i F i < \sum_i G i.
Proof.
move => F_le_G [i Fi_lt_Gi].
rewrite [X in X < _](bigD1 i) //= [X in _ < X](bigD1 i) //=.
by rewrite ltr_le_add // ler_sum.
Qed.

Fixpoint min_seq (S : seq R) (v : R) :=
  match S with
  | [::] => v
  | [:: x] => x
  | x :: S' => Order.min x (min_seq S' v)
  end.

Lemma min_seq_ler (S : seq R) v: forall i, i \in S -> min_seq S v <= i.
Proof.
elim: S => [ | x S' IH].
- by move => i; rewrite in_nil.
- move => i; rewrite in_cons; move/orP => [/eqP -> | H].
  + rewrite /=.
    case H': S'; first by done.
    * rewrite le_minl; apply/orP; left; done.
  + rewrite /=; move: H.
    case H': S'; first by rewrite in_nil.
    * by rewrite -H'; move => Hi; rewrite le_minl; apply/orP; right; apply: IH.
Qed.

Lemma min_seq_eq (S : seq R) (v : R) :  S != [::] -> has [pred i | min_seq S v == i] S.
Proof.
elim: S => [ | x S']; first by done.
- case: (altP (S' =P [::])) => [-> /= | HS /(_ is_true_true) IH _]; first by rewrite eq_refl.
  + apply/hasP. case: (leP x (min_seq S' v)) => [H'' |].
    * exists x; first by rewrite mem_head.
      rewrite /= min_l //. by case H: S'.
    * move/hasP: IH => [i Hi /= /eqP ->] ?.
      exists i; first by rewrite mem_behead.
      case H: S'; first by move: Hi; rewrite H in_nil.
      by rewrite min_r // ltW.
Qed.

Variant min_seq_spec (S : seq R) (v : R) : R -> Prop :=
| MinSeqEmpty of (S = [::]) : min_seq_spec S v v
| MinSeqNonEmpty x of (x \in S /\ (forall y, y \in S -> y >= x)) : min_seq_spec S v x.

Lemma min_seqP (S : seq R) (v : R) :
  min_seq_spec S v (min_seq S v).
Proof.
case: (altP (S =P [::])) => [->|].
- by constructor.
- move/(min_seq_eq v)/hasP => [x x_in_S]; rewrite inE eq_sym => /eqP x_eq.
  constructor; split.
  + by rewrite -x_eq.
  + exact: min_seq_ler.
Qed.

Lemma min_seq_positive (S : seq R) (v : R) :
  (S != [::]) \/ (v > 0) -> (min_seq S v > 0) = (all [pred i | i > 0] S).
Proof.
  move => H.
  apply/idP/idP.
  - move => H'. apply/allP; rewrite /= => x Hx.
    apply: (@lt_le_trans _ _ (min_seq S v) _ _); first by done.
    + by apply: min_seq_ler.
  - case: H => [Hne | He].
    + move/allP => H' /=. move/hasP: (min_seq_eq v Hne) => [i Hi /eqP -> /=].
      by apply: H'.
    + elim: S => [// | x S Hx].
        rewrite /= => /andP [Hxp H_].
        have Hsp: 0 < min_seq S v by apply: Hx. rewrite {H_ Hx}.
        case Haf: (S); first by apply: Hxp.
        by rewrite -Haf lt_minr Hxp.
Qed.

Fixpoint max_seq (S : seq R) (v : R) :=
  match S with
  | [::] => v
  | [:: x] => x
  | x :: S' => Order.max x (max_seq S' v)
  end.

Lemma max_seq_ger (S : seq R) v: forall i, i \in S -> max_seq S v >= i.
Proof.
elim: S => [ /= | x S' IH].
- by move => ?; rewrite inE.
- move => i; rewrite inE => /orP [/eqP -> | H].
  + rewrite /=.
    case: S' IH => // [?? _ ].
    by rewrite le_maxr lexx.
  + rewrite /=; move: H.
    case H': S'; first by rewrite in_nil.
    * by rewrite -H'; move => Hi; rewrite le_maxr; apply/orP; right; apply: IH.
Qed.

Lemma max_seq_eq (S : seq R) (v : R) :  S != [::] -> has [pred i | max_seq S v == i] S.
Proof.
elim: S => [ | x S']; first by done.
- case: (altP (S' =P [::])) => [-> /= | HS /(_ is_true_true) IH _]; first by rewrite eq_refl.
  + apply/hasP. case: (leP (max_seq S' v) x) => [H'' |].
    * exists x; first by rewrite mem_head.
      rewrite /= max_l //. by case H: S'.
    * move/hasP: IH => [i Hi /= /eqP ->] ?.
      exists i; first by rewrite mem_behead.
      case H: S'; first by move: Hi; rewrite H in_nil.
      by rewrite max_r // ltW.
Qed.

Variant max_seq_spec (S : seq R) (v : R) : R -> Prop :=
| MaxSeqEmpty of (S = [::]) : max_seq_spec S v v
| MaxSeqNonEmpty x of (x \in S /\ (forall y, y \in S -> y <= x)) : max_seq_spec S v x.

Lemma max_seqP (S : seq R) (v : R) :
  max_seq_spec S v (max_seq S v).
Proof.
case: (altP (S =P [::])) => [->|].
- by constructor.
- move/(max_seq_eq v)/hasP => [x x_in_S]; rewrite inE eq_sym => /eqP x_eq.
  constructor; split.
  + by rewrite -x_eq.
  + exact: max_seq_ger.
Qed.

Lemma ltW_lt (x y z : R) : (x < y < z) -> (x <= y < z).
Proof.
by move => /andP [??]; rewrite ltW //=.
Qed.

Lemma lt_ltW (x y z : R) : (x < y < z) -> (x < y <= z).
Proof.
by move => /andP [??]; rewrite ltW //= andbT.
Qed.

Lemma lt_leW (x y z : R) : (x < y <= z) -> (x <= y <= z).
Proof.
by move => /andP [??]; rewrite ltW //= andbT.
Qed.

Lemma ltW_le (x y z : R) : (x <= y < z) -> (x <= y <= z).
Proof.
by move => /andP [-> ?]; rewrite ltW //=.
Qed.

End ExtraNum.

Section ExtraBool.

Variable T : Type.

Lemma predsym (p1 p2: pred T) : p1 =i p2 -> p2 =i p1.
Proof.
by move => eq x; symmetry.
Qed.

End ExtraBool.

Section ExtraFinset.

Variable T T' : finType.

Lemma imset_inj (f : T -> T') (S S' : {set T}) : injective f -> f @: S = f @: S' -> S = S'.
Proof.
move => f_inj f_S_eq_f_S'.
apply/setP => i; apply/idP/idP; move/(imset_f f).
- by rewrite f_S_eq_f_S' => /imsetP [j j_in_S']; move/f_inj => ->.
- by rewrite -f_S_eq_f_S' => /imsetP [j j_in_S]; move/f_inj => ->.
Qed.

End ExtraFinset.

Section ExtraFinmap.

Lemma fproperP (K : choiceType) (A B : {fset K}) :
  reflect ({subset A <= B} /\ exists2 x, x \in B & x \notin A) (A `<` B)%fset.
Proof. apply: (iffP idP).
+ move=> ltAB; split; first by apply/fsubsetP/fproper_sub.
  suff: exists x, x \in (B `\` A)%fset.
  - by case=> x; rewrite inE => /andP[??]; exists x.
  apply/fset0Pn; rewrite -cardfs_gt0 cardfsDS 1?fproper_sub //.
  by rewrite subn_gt0 fproper_ltn_card.
+ case=> /fsubsetP leAB [x xB xNA]; rewrite fproperEcard.
  rewrite leAB /= -subn_gt0 -cardfsDS // cardfs_gt0.
  by apply/fset0Pn; exists x; rewrite inE xB xNA.
Qed.

Lemma imfset0 (K K' : choiceType) (f : K -> K') :
  (f @` fset0)%fset = fset0.
Proof. by apply/fsetP=> x; rewrite !inE; apply/negP => /imfsetP[]. Qed.

Lemma fsub_fsetval (K : choiceType) (A B : {fset K}) :
  (A `<=` B)%fset -> A = [fsetval x in [fset x : B | val x \in A]]%fset.
Proof.
move=> leAB; apply/fsetP=> x; apply/idP/imfsetP => /=.
+ by move=> xA; exists (fincl leAB [`xA])%fset; rewrite ?inE.
+ by case=> b; rewrite !inE /= => bA ->.
Qed.

Lemma fsubsizeP {K : choiceType} (S : {fset K}) :
  size S == #|` S |.
by [].
Qed.
Canonical fsubsize {K : choiceType} (S : {fset K}) := Tuple (fsubsizeP S).

Definition fnth (K : choiceType) (S : {fset K}) i := tnth [tuple of S] i.

Lemma fnthP (K : choiceType) (S : {fset K}) (i : 'I_#|`S|) :
  fnth i \in S.
Proof.
by apply/(tnthP [tuple of S]); exists i.
Qed.

Lemma fset_fnth (K : choiceType) (S : {fset K}) :
  S = [fset fnth i | i in 'I_#|`S|]%fset.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => [x].
- move/(tnthP [tuple of S]) => [i ->].
  by rewrite in_imfset.
- move/imfsetP => [i _ ->]; exact: fnthP.
Qed.

End ExtraFinmap.

Class expose (P : Prop) := Expose : P.

Global Hint Extern 0 (expose _) => (exact) : typeclass_instances.
Global Hint Extern 0 (expose (is_true _)) => (match goal with H : is_true _ |- _ => exact: H end) : typeclass_instances.

(*Hint Extern 0 (_ `<=` _)%fset => exact: fsubset_refl.
Global Hint Extern 0 (fset0 `<=` _)%fset => exact: fsub0set.*)

Module FSubset.
Section FSubset.

Local Open Scope fset_scope.

Variable (K : choiceType) (S : {fset K}).

Structure tagged_fset := Tag { untag : {fset K} }.
Local Coercion untag : tagged_fset >-> finset_of.

Lemma untag_inj : injective untag.
Proof.
move => x y; case: x => x' /= ->.
by case: y => ? /=.
Qed.

Lemma untagK : cancel untag Tag.
Proof.
by move => x; apply/untag_inj.
Qed.

Definition tagged_fset_eqMixin := CanEqMixin untagK.
Canonical tagged_fset_eqType := Eval hnf in EqType tagged_fset tagged_fset_eqMixin.
Definition tagged_fset_choiceMixin := CanChoiceMixin untagK.
Canonical tagged_fset_choiceType := Eval hnf in ChoiceType tagged_fset tagged_fset_choiceMixin.

Record fsubset_t := FSubset { tf : tagged_fset; _ : (tf `<=` S) }.
Local Coercion tf : fsubset_t >-> tagged_fset.
Canonical fsubset_subType := [subType for tf].
Definition fsubset_eqMixin := Eval hnf in [eqMixin of fsubset_t by <:].
Canonical fsubset_eqType := Eval hnf in EqType fsubset_t fsubset_eqMixin.
Definition fsubset_choiceMixin := [choiceMixin of fsubset_t by <:].
Canonical fsubset_choiceType := Eval hnf in ChoiceType fsubset_t fsubset_choiceMixin.

Definition fsetval_of_fsubset (A : fsubset_t) : {fset S} := [fset x : S | val x \in untag (val A)].

Lemma fsubset_of_fsetvalP (A : {fset S}) : Tag [fsetval x in A] `<=` S.
Proof.
apply/fsubsetP => ? /imfsetP [? _ ->].
exact: valP.
Qed.
Definition fsubset_of_fsetval (A : {fset S}) := FSubset (fsubset_of_fsetvalP A).

Lemma fsetval_of_fsubsetK : cancel fsetval_of_fsubset fsubset_of_fsetval.
Proof.
move => A; apply/val_inj => /=.
move/fsub_fsetval: (valP A) <-.
exact: untag_inj.
Qed.

Definition fsubset_countMixin := CanCountMixin fsetval_of_fsubsetK.
Canonical fsubset_countType := Eval hnf in CountType fsubset_t fsubset_countMixin.
Definition fsubset_finMixin := CanFinMixin fsetval_of_fsubsetK.
Canonical fsubset_finType := Eval hnf in FinType fsubset_t fsubset_finMixin.

Definition fsubset_of (A : fsubset_t) & (phantom {fset K} A) : fsubset_t := A.
Notation "A %:fsub" := (fsubset_of (Phantom {fset K} A)) (at level 0).

Definition tag0 x := Tag x.
Definition tag1 x := tag0 x.
Definition tag2 x := tag1 x.
Definition tag3 x := tag2 x.
Definition tag4 x := tag3 x.
Definition tag5 x := tag4 x.
Definition tag6 x := tag5 x.
Canonical tag6.

Canonical fsubset_expose (A : {fset K})
          (H : expose (A `<=` S)%fset) := @FSubset (tag0 _) H.
Canonical fsubset_fset0 := @FSubset (tag1 _) (fsub0set S).

Lemma fsubset_setUP (A B : {fset K}) :
  A `<=` S -> B `<=` S -> A `|` B `<=` S.
Proof. by move=> leAS leBS; rewrite -[S]fsetUid fsetUSS. Qed.

Canonical fsubset_setU
  (A B : {fset K}) (HA : expose (A `<=` S)) (HB : expose (B `<=` S))
:=
  @FSubset (tag2 _) (fsubset_setUP HA HB).

Lemma fsubset_bigUP (I : finType) (P : pred I) F :
  (forall i, P i -> F i `<=` S) -> (\bigcup_(i | P i) F i) `<=` S.
Proof. by move=> le_FS; apply/bigfcupsP=> i _; apply: le_FS. Qed.

Canonical fsubset_bigU
  (I : finType) (P : pred I) F (H : expose (forall i, P i -> F i `<=` S))
:=
  @FSubset (tag3 _) (fsubset_bigUP H).

Lemma fsubset_filterP (P : pred K) : [fset x in S | P x] `<=` S.
Proof. by apply/fsubsetP=> x; rewrite !inE /= => /andP[]. Qed.

Canonical fsubset_filter (P : pred K) := @FSubset (tag4 _) (fsubset_filterP P).

Global Instance expose_valP (A : fsubset_t) : expose (A `<=` S) := Expose (valP A).
Global Instance expose_funP (T : Type) (P : pred T) (f : T -> fsubset_t) :
  expose (forall i, P i -> f i `<=` S) := Expose (fun i _ => (valP (f i))).

(* TODO: strange that this cannot be implemented by adding a canonical. Apparently backtracking is not working *)
Global Instance expose_setT : expose (S `<=` S) := Expose (fsubset_refl S).

Global Instance expose_set1 (x : K) (_ : expose (x \in S)) : expose ([fset x] `<=` S)%fset.
Proof.
by rewrite fsub1set.
Qed.

(*
Section Test.
Check (fset0 %:fsub).
Check (S %:fsub).

Variable A : {fset K}.
Hypothesis (HA : (A `<=` S)).
Check (A %:fsub).
Goal (A `|` fset0)%:fsub = A%:fsub.
Abort.

Variable A' : fsubset_t.
Goal (A' `|` fset0)%:fsub = A%:fsub.
Abort.
Goal (A' `|` fset0%:fsub)%:fsub = A%:fsub.
rewrite /=; apply/val_inj/untag_inj => /=.
Abort.

Variable B : {fset K}.
Hypothesis (HB : (B `<=` S)).
Goal (A' `|` B)%:fsub = (B `|` A')%:fsub.
Abort.

Variable i : K.
Hypothesis (Hi : ([fset i] `<=` S)).
Goal (A' `|` [fset i])%:fsub = ([fset i] `|` A')%:fsub.
Abort.

Variable (I : finType) (P : pred I) (F : I -> fsubset_t).
Check (\bigcup_(i | P i) (F i))%:fsub.
Check (\bigcup_(i | P i) A')%:fsub.
End Test.
*)

End FSubset.

Module Import Exports.
Coercion untag : tagged_fset >-> finset_of.
Coercion tf : fsubset_t >-> tagged_fset.
Canonical tagged_fset_eqType.
Canonical tagged_fset_choiceType.
Canonical fsubset_subType.
Canonical fsubset_eqType.
Canonical fsubset_choiceType.
Canonical fsubset_countType.
Canonical fsubset_finType.
Canonical tag6.
Canonical fsubset_expose.
Canonical fsubset_fset0.
Canonical fsubset_setU.
Canonical fsubset_bigU.
Canonical fsubset_filter.
End Exports.
End FSubset.

Export FSubset.Exports.

Notation "'{fsubset'  S '}'" := (FSubset.fsubset_t S) (at level 2).
Notation "A %:fsub" := (FSubset.fsubset_of (Phantom {fset _} A)) (at level 0).

(*
Section Test.
Local Open Scope fset_scope.

Set Typeclasses Debug.

Variable (K : realFieldType) (S : {fset K}).
Check (fset0%:fsub) : {fsubset S}.
Check (S %:fsub) : {fsubset S}.

Variable A : {fset K}.
Hypothesis (HA : (A `<=` S)).
Check ((A %:fsub) : {fsubset S}).
Goal (A `|` fset0)%:fsub = A%:fsub :> {fsubset S}.
Abort.

Variable A' : {fsubset S}.
Goal (A' `|` fset0)%:fsub = A%:fsub.
Abort.
Goal (A' `|` fset0%:fsub)%:fsub = A%:fsub.
rewrite /=; apply/val_inj => /=.
Abort.

Variable (I : finType) (P : pred I) (F : I -> {fsubset S}).
Check (\bigcup_(i | P i) (F i))%:fsub.
End Test.
*)

Section FSubsetOther.

Local Open Scope fset_scope.

Variable (K : choiceType) (S : {fset K}).

Lemma fsubset_inj (A B : {fsubset S}) :
  (A = B :> {fset K}) -> A = B.
Proof.
by move => /FSubset.untag_inj ?; apply/val_inj => /=.
Qed.

Lemma fsubset_subP (A : {fsubset S}) : A `<=` S.
Proof. exact: (valP A). Qed.

Lemma fsubsetT_proper (A : {fsubset S}) : (S `<` A) = false.
Proof.
apply/negP; case: A => /= A leAS /(fsub_proper_trans leAS).
by apply/negP/fproper_irrefl.
Qed.

Definition fslice e (A : {fset K}) := e |` A.
Definition funslice e (A : {fset K}) := A `\ e.

Lemma fsubset_sliceP e (A : {fsubset S}) : fslice e A `<=` fslice e S.
Proof.
move/fsubsetP: (fsubset_subP A) => leAS; apply/fsubsetP=> x; rewrite !in_fset1U.
case/orP=> [/eqP->|]; first by rewrite eqxx.
by move/leAS=> ->; rewrite orbT.
Qed.

Canonical fsubset_slice e A :=
  @FSubset.FSubset _ _ (FSubset.tag5 _) (fsubset_sliceP e A).

Lemma fsubset_unsliceP e (A : {fsubset (fslice e S)}) :
  funslice e A `<=` S.
Proof.
by rewrite fsubDset (valP A).
Qed.

Canonical fsubset_unslice e (A : {fsubset (fslice e S)}) :=
  @FSubset.FSubset _ _ (FSubset.tag6 _) (fsubset_unsliceP A).

Lemma fsubset_fsubsetP (A B : {fsubset S}) :
  reflect {in S, {subset (A : {fset K}) <= (B : {fset K})}} (A `<=` B)%fset.
Proof.
apply: (iffP idP).
- move/fsubsetP => A_sub_B x _; exact: A_sub_B.
- move => A_sub_B; apply/fsubsetP => x x_in_A.
  suff x_in_S: x \in S by exact: A_sub_B.
  by apply/(fsubsetP (valP A)).
Qed.

Lemma fsubset_properT (A : {fsubset S}) :
  (A `<` S)%fset = (A != S%:fsub).
Proof.
by rewrite fproperEneq (valP A) andbT.
Qed.

End FSubsetOther.

Notation "e +|` A" := (fslice e A) (at level 52).
Notation "A `|- e" := (funslice e A) (at level 52).

(*Global Instance expose_valP (K : choiceType) (S : {fset K}) (A : {fsubset S}) : expose (A `<=` S)%fset := Expose (valP A).
Global Instance expose_funP (K : choiceType) (S : {fset K}) (T : Type) (P : pred T) (f : T -> {fsubset S}) :
  expose (forall i, P i -> (f i `<=` S)%fset) := Expose (fun i _ => (valP (f i))).

(* TODO: strange that this cannot be implemented by adding a canonical. Apparently backtracking is not working *)
Global Instance expose_setT (K : choiceType) (S : {fset K}) : expose (S `<=` S)%fset := Expose (fsubset_refl S).*)

(*
Section Test.

Variable (K : realFieldType) (S : {fset K}) (e : K) (A : {fsubset S}).
Check ((e +|` A)%:fsub : {fsubset (e +|` S)}).
Check ((e +|` fset0)%:fsub : {fsubset (e +|` S)}).
Check ((e +|` S)%:fsub : {fsubset (e +|` S)}).
Hypothesis He : ([fset e] `<=` S)%fset.
Check ([fset e]%fset%:fsub : {fsubset S}).
Check ((A `|` [fset e])%fset%:fsub : {fsubset S}).
Check (([fset e] `|` A )%fset%:fsub : {fsubset _}). (* this should be a {fsubset S} *)
End Test.
*)

Section Vector.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory.

Context {K : fieldType} {vT : vectType K}.

Lemma dim_add_line  (U : {vspace vT}) (v : vT) :
  v \notin U -> (\dim (U + <[ v ]>) = (\dim U).+1)%N.
Proof.
move => v_notin; rewrite dimv_disjoint_sum ?dim_vline -1?addn1.
- have -> //=: (v != 0).
  by move: v_notin; apply: contraNneq => ->; rewrite mem0v.
- apply/eqP; rewrite -subv0; apply/subvP => x /memv_capP [x_in /vlineP [μ x_eq]].
  rewrite {}x_eq in x_in *.
  suff -> : μ = 0 by rewrite scale0r memv0.
  move: v_notin; apply: contraNeq => μ_neq0.
  by move/(memvZ μ^-1) : x_in; rewrite scalerA mulVf // scale1r.
Qed.

Lemma dim_leqn (R : realFieldType) (n : nat) (U : {vspace 'cV[R]_n}) : (\dim U <= n)%nat.
Proof.
by move/dimvS: (subvf U); rewrite dimvf /Vector.dim /= muln1.
Qed.

End Vector.

Section SpanGen.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Inductive is_span_gen {K : fieldType} {vT : vectType K} : seq vT -> seq vT -> Prop :=
  | NilSpan : is_span_gen [::] [::] 
  | SpanMemF x s S (_ : x \notin <<s>>%VS) (_ : is_span_gen s S): is_span_gen (x::s) (x::S)
  | SpanMemT x s S (_ : x \in <<s>>%VS) (_ : is_span_gen s S) : is_span_gen s (x::S).

Lemma is_sg_sub {K : fieldType} {vT : vectType K} (s S : seq vT) :
  is_span_gen s S -> subseq s S.
Proof.
elim => //= => y s0 S0 _ _ ; rewrite ?eq_refl //.
case: s0=> // a l; case: (a == y) => //.
exact: cons_subseq.
Qed.


Lemma is_sg_eqcons {K : fieldType} {vT : vectType K} (s S : seq vT) x:
  is_span_gen (x :: s) (x :: S) -> x \notin S -> is_span_gen s S.
Proof.
inversion 1=> //.
move/is_sg_sub: H4 => /mem_subseq/(_ x).
by rewrite inE eq_refl=> /(_ isT) => ->.
Qed.

Lemma is_sg_neqcons {K : fieldType} {vT : vectType K}
  (s S : seq vT) x Y:
  is_span_gen (x::s) (Y::S) -> x != Y -> is_span_gen (x::s) S.
Proof. by move=> H; inversion H=> //; rewrite eq_refl. Qed.

Lemma is_sg_nil_cons {K : fieldType} {vT : vectType K}
  (S : seq vT) x:
    is_span_gen [::] (x::S) -> is_span_gen [::] S.
Proof. by move=> H; inversion H. Qed.

Lemma is_sg_ex {K : fieldType} {vT : vectType K} (S : seq vT) :
  exists s, is_span_gen s S.
Proof.
elim: S; first (exists [::]; exact: NilSpan).
move=> y S [s is_spans].
case/boolP: (y \in <<s>>%VS) => H.
- exists s; exact/SpanMemT.
- exists (y::s); exact/SpanMemF.
Qed.

Lemma is_sg_nil {K : fieldType} {vT : vectType K} (s : seq vT) :
  is_span_gen s [::] -> s = [::].
Proof.
by move=> H; inversion H.
Qed.

Lemma is_sg0 {K : fieldType} {vT : vectType K} (S : seq vT) :
  is_span_gen [::] S -> forall x, x \in S -> x = 0.
Proof.
elim: S=> // a l IH H.
inversion H as [ | | x s S a0 spang_l] => x0; rewrite inE.
case/orP; last exact: IH.
move/eqP => ->; apply/eqP; move: a0.
by rewrite span_nil memv0.
Qed.

Lemma is_sg_inv {K : fieldType} {vT : vectType K} (S s : seq vT) x:
  is_span_gen s (x :: S) ->
  ([/\ s = x :: (behead s), is_span_gen (behead s) S & x \notin <<behead s>>%VS]) \/
  (x \in <<s>>%VS /\ is_span_gen s S).
Proof.
move=> H; inversion H as [ | ? s' ? | ].
- by left.
- by right.
Qed.

Lemma is_sg_basis {K : fieldType} {vT : vectType K} (s S : seq vT) :
  is_span_gen s S -> basis_of <<S>>%VS s.
Proof.
elim; rewrite ?span_nil ?nil_basis // => y s0 S0.
+ move=> yS0F _ base0; rewrite span_cons -[in X in basis_of _ X]cat1s.
  apply: cat_basis=> //.
  - apply/directv_addP/eqP; rewrite -subv0; apply/subvP=> z.
    rewrite memv0 memv_cap andbC; case/andP.
    move/[swap]/vlineP=> [k ->].
    case/boolP : (k == 0); first move/eqP=> ->; rewrite ?scale0r //.
    move=> k0N /(memvZ k^-1); rewrite scalerA mulVr ?unitfE //= scale1r.
    rewrite -(span_basis base0); exact/contraLR.
  - apply/seq1_basis; move: yS0F; apply/contraNneq=> ->; exact/mem0v.
  + move=> + _ base0; rewrite span_cons memvE -(span_basis base0).
    by move/addv_idPr => ->; rewrite (span_basis base0).
Qed.

Definition max_basis {K : fieldType} {vT : vectType K} (b S : seq vT):=
  forall x b1 b2, b = b1 ++ (x :: b2) ->
  exists S1 S2,
  [/\ S = S1 ++ (x :: S2), subseq b1 S1, subseq b2 S2,
  x \notin S2 & (<<S2>> <= <<b2>>)%VS].


Lemma is_sg_max {K : fieldType} {vT : vectType K} (S b : seq vT):
  is_span_gen b S -> max_basis b S.
Proof.
elim=> [| b0 b' S' b0_span is_sgH IH | b0 b' S' b0_span is_sgH IH].
- by move=> x b1 b2 /(congr1 size); rewrite size_cat /= addnS.
- move=> x b1 b2; case: b1.
  + move/eqP; rewrite eqseq_cons=> /andP [/eqP <- /eqP <-].
    exists [::]; exists S'; split=> //; rewrite ?(is_sg_sub is_sgH) //.
    * apply: contraT; rewrite negbK=> b0S'.
      move/is_sg_basis/span_basis: is_sgH b0_span=> ->.
      by move/memv_span: b0S' => ->.
    * by rewrite (span_basis (is_sg_basis is_sgH)) subvv.
  + move=> b1h b1t /eqP; rewrite cat_cons eqseq_cons=> /andP [] /=.
    move/eqP=> <- /eqP/IH [S1 [S2 [????]]].
    exists (b0 :: S1); exists S2=> /=; rewrite eqxx; split=> //.
    apply/eqP; rewrite eqseq_cons eqxx; exact/eqP.
- move=> x b1 b2 /IH [S1 [S2]].
  case=> -> ???; exists (b0 :: S1); exists S2; split=> //.
  apply: (@subseq_trans _ S1)=> //; exact: subseq_cons.
Qed.

Lemma max_basis_cons {K : fieldType} {vT : vectType K} (h : vT) E B:
  basis_of << h :: E >>%VS (h :: B) ->
  max_basis (h :: B) (h :: E) ->
  max_basis B E.
Proof.
move=> base_hB max_hB x b1 b2 B_eq.
move: (max_hB x (h::b1) b2); rewrite B_eq cat_cons.
case/(_ erefl)=> E1 [E2] [].
have /negPf x_n_h: h != x.
- apply/contraT; rewrite negbK=> /eqP contr.
  move/basis_free: base_hB; rewrite free_cons.
  by rewrite memv_span // B_eq contr mem_cat in_cons eqxx orbT.
case: E1; first move/eqP; rewrite ?eqseq_cons ?x_n_h //.
move=> a l /eqP; rewrite cat_cons eqseq_cons.
case/andP=> /eqP -> /eqP /=; rewrite eqxx.
by move=> ????; exists l; exists E2; split.
Qed.

Lemma max_basis_cons_cat {K : fieldType} {vT : vectType K}
  (h v: vT) E1 E2 B: 
  basis_of <<v :: E1 ++ h :: E2>>%VS (h :: B) ->
  max_basis (h :: B) (v :: E1 ++ h :: E2) ->
  subseq B E2 -> (<<E2>> <= <<B>>)%VS ->
  h \notin E2 ->
  max_basis (h :: B) (E1 ++ h :: E2).
Proof.
move=> base_hB max_hB sub_B span_B hnE2 x [|b0 b1'] b2.
- move/eqP; rewrite eqseq_cons; case/andP=> /eqP <- /eqP <-.
  by exists E1; exists E2; rewrite sub0seq; split.
- move=> /[dup] /eqP; rewrite {1}cat_cons eqseq_cons.
  case/andP=> /eqP <- /eqP B_eq.
  case/max_hB=> S1 [S2] [].
  case: S1=> // ? S1' /eqP; rewrite cat_cons eqseq_cons.
  case/andP=> /eqP <- /eqP E_eq sub_b1 sub_b2 xnS2 span_b2.
  exists S1'; exists S2; split=> //.
  move: sub_b1=> /=; case: ifP=> // /eqP h_eq sub_S1'.
  apply: (subseq_lcat (B:= x :: S2)).
  + rewrite -E_eq -[h :: b1']cat0s cat_subseq ?sub0seq //=.
    rewrite eqxx; apply: (subseq_trans _ sub_B).
    by rewrite B_eq prefix_subseq.
  + move=> y y_hb1'; apply: contraT; rewrite negbK=> y_xS2.
    move/basis_free : base_hB=> /[dup] free_hB.
    rewrite B_eq -cat_cons cat_free.
    case/and3P => _ _ /directv_addP /eqP.
    rewrite -subv0; move/subvP=> /(_ y).
    rewrite (_ : y \in _) => [/(_ isT)|].
    * rewrite memv0=> /eqP y0.
      move: (@free_not0 _ _ y _ free_hB).
      rewrite B_eq -cat_cons mem_cat y_hb1' y0 eqxx; exact.
    * rewrite memv_cap memv_span //= span_cons.
      suff ->: (<<b2>> = <<S2>>)%VS by rewrite -span_cons memv_span.
      apply/eqP; rewrite eqEsubv span_b2 sub_span //.
      exact: mem_subseq.
Qed.


Lemma is_max_sg {K : fieldType} {vT : vectType K} (E B : seq vT):
  basis_of <<E>>%VS B -> subseq B E -> max_basis B E ->
  is_span_gen B E.
Proof.
elim: E B=> [|hE tE IH].
  move=> B _; rewrite subseq0=> /eqP -> _; exact: NilSpan.
case=> [|hB tB].
- move=> span_b sub_b max_b.
  apply/SpanMemT; rewrite ?(span_basis span_b) ?memv_span ?in_cons ?eqxx //.
  apply/IH; rewrite ?sub0seq //.
  + apply/andP; rewrite nil_free; split=> //.
    rewrite (span_basis span_b) eqEsubv [X in _ && X]sub_span ?andbT.
    * by rewrite -(span_basis span_b) span_nil sub0v.
    * by move=> x; rewrite in_cons=> ->; rewrite orbT.
  + move=> x b1 b2; case: b1=> //.
- move=> + + /[dup] /(_ hB [::] tB erefl) [E1] [E2] [E_eq _ sub_tB hBnE2 span_tB].
  rewrite E_eq; case: E1 E_eq => /= [|E1h E1t].
  + move/eqP; rewrite eqseq_cons=> /andP [_ /eqP tE_E2]; rewrite -tE_E2.
    move=> base_B _ max_B; apply: SpanMemF.
      by move/basis_free: base_B; rewrite free_cons=> /andP [].
    apply/IH; rewrite ?tE_E2 //.
    * apply/andP.
      move/basis_free: (base_B); rewrite free_cons=> /andP [_ ->].
      split=> //; rewrite eqEsubv span_tB sub_span //.
      exact: mem_subseq.
    * by apply: (max_basis_cons (h:=hB)); rewrite -tE_E2.
  + move/eqP; rewrite eqseq_cons=> /andP [/eqP hE_eq /eqP tE_eq].
    move=> base_B _ max_B; apply/SpanMemT.
      by rewrite (span_basis base_B) memv_span // in_cons eqxx.
    rewrite -tE_eq; apply/IH; rewrite tE_eq.
    * apply/andP; move/basis_free: (base_B)=> ->; split=> //.
      rewrite (span_basis base_B) eqEsubv [X in _ && X]sub_span ?andbT.
      - rewrite -(span_basis base_B); apply/span_subvP.
        move=> x x_B; apply/memv_span; rewrite mem_cat.
        apply/orP; right; move: x x_B; apply/mem_subseq=> /=.
        by rewrite eqxx.
      - by move=> x xH; rewrite in_cons xH orbT.
    * by rewrite -[X in subseq X _]cat0s cat_subseq ?sub0seq //= eqxx.
    * exact: (max_basis_cons_cat (v:=E1h)).
Qed.

Lemma is_sgP {K : fieldType} {vT : vectType K} (E B : seq vT):
  is_span_gen B E <->
  [/\ basis_of <<E>>%VS B, subseq B E & max_basis B E].
Proof.
split.
- move=> is_sgH; split;
  [exact: is_sg_basis | exact: is_sg_sub | exact: is_sg_max ].
- case; exact: is_max_sg.
Qed.

Lemma foo {T : eqType} (x y : T) (A1 A2 B1 B2 : seq T) :
  A1 ++ x :: A2 = B1 ++ y :: B2 -> x != y ->
  x \notin B2 -> y \in A2.
Proof.
elim: A1 A2 B1 B2=> [|a1 A1' IH] A2 B1 B2.
- case: B1=> /= [|b1 B1'] /eqP; rewrite eqseq_cons; case/andP.
  + by move=> ->.
  + by move=> _ /eqP -> _ _; rewrite mem_cat in_cons eq_refl orbT.
- case: B1=> [|b1 B1'].
  + move=> /= l_eq.
    have: x \in y :: B2 by
      rewrite -l_eq !(in_cons, mem_cat) eq_refl !orbT.
    by rewrite in_cons; case/orP=> ->.
- move=> /= /eqP; rewrite eqseq_cons; case/andP=> _ /eqP.
  exact: IH.
Qed.

(* Lemma bar {K : fieldType} {vT : vectType K} (E1 E2 B : seq vT) x y :
  is_span_gen B (E1 ++ y :: E2) -> x \in B -> x \in E1 -> x != y ->
  x \notin E2.
Proof.
Admitted. *)


(* Lemma is_sg_maxlex {K : fieldType} {vT : vectType K} (E B : seq vT) y :
  is_span_gen B E -> y \in E -> y \notin B ->
  exists B1 B2, B = B1 ++ B2 /\
  (exists E1 E2,
  [/\ E = E1 ++ (y :: E2), subseq B1 E1, subseq B2 E2 & y \in <<B2>>%VS]).
Proof.
move/[dup]; case/is_sgP=> ++++ yE.
case/path.splitP: yE=> E1 E2 + subE.
case: (subseq_split_cat subE)=> B1 [B2].
case=> -> subB1y subB2 baseB maxB is_sgB ynB.
have subB1: subseq B1 E1.
- apply: (subseq_lcat (B:=[:: y])); rewrite ?cats1 //.
  move=> x; apply: contraTN; rewrite mem_seq1=> /eqP ->.
  move: ynB; rewrite mem_cat negb_or.
  by case/andP.
exists B1; exists B2; split=> //.
exists E1; exists E2; rewrite cat_rcons; split=> //.
elim/last_ind: B1 {subB1y} baseB maxB ynB subB1 is_sgB => [|B1' x _].
- move/span_basis => -> _ _ _ _; apply: memv_span.
  by rewrite mem_cat mem_rcons in_cons eq_refl.
- rewrite !cat_rcons.
  move=> baseB maxB ynB subE1.
  case: (maxB x B1' B2 erefl)=> S1 [S2].
  case=> E_eq subS1 subS2 xnS2 spanS2 is_sgB.
  apply/(subvP spanS2)/memv_span.
  move/esym/foo: (E_eq); apply.
  + move: ynB; rewrite mem_cat in_cons !negb_or eq_sym.
    by case/and3P.
  + apply: (bar is_sgB).
    * by rewrite mem_cat in_cons eq_refl orbT.
    * move/mem_subseq/(_ x): subE1.
      rewrite mem_rcons in_cons eq_refl /=.
      exact.
    * move: ynB; rewrite mem_cat in_cons eq_sym !negb_or.
      by case/and3P.
Qed. *)

 

Fixpoint span_gen  {K : fieldType} {vT : vectType K} (S : seq vT) := match S with
  | [::] => [::]
  | h::t => if h \in <<span_gen t>>%VS then span_gen t else (h::(span_gen t))
end.

Lemma span_genP {K : fieldType} {vT : vectType K} (S : seq vT) : is_span_gen (span_gen S) S.
Proof.
elim : S;  first exact: NilSpan.
move=> y S is_spanH /=.
case: ifP.
- move=> ?; exact: SpanMemT.
- move/negbT=> ?; exact: SpanMemF.
Qed.

Lemma span_gen_max {K : fieldType} {vT : vectType K} (S : seq vT):
  [/\ basis_of <<S>>%VS (span_gen S), subseq (span_gen S) S &
  max_basis (span_gen S) S].
Proof. by move/is_sgP: (span_genP S). Qed.

Lemma span_gen_basis {K : fieldType} {vT : vectType K} (S : seq vT):
  basis_of <<S>>%VS (span_gen S).
Proof. by case/is_sgP: (span_genP S). Qed. 

Lemma span_gen_free {K : fieldType} {vT : vectType K} (S : seq vT) :
  free (span_gen S).
Proof. by case: (span_gen_max S)=> /basis_free. Qed.

Lemma span_gen_sub {K : fieldType} {vT : vectType K} (S : seq vT) :
  subseq (span_gen S) S.
Proof. by case : (span_gen_max S). Qed.

Lemma span_gen_uniq {K : fieldType} {vT : vectType K} (S : seq vT) :
  uniq (span_gen S).
Proof. move: (span_gen_free S); exact: free_uniq. Qed.

Lemma span_gen_span_eq {K : fieldType} {vT : vectType K} (S : seq vT):
  (<<S>> = <<span_gen S>>)%VS.
Proof. by case/is_sgP: (span_genP S)=> /span_basis ->. Qed.

End SpanGen.

Section Free.

Lemma free_subset (K : fieldType) (V : vectType K) (S T: seq V):
  {subset S <= T} -> free T -> uniq S -> free S.
Proof.
move=> subST freeT uniqS.
rewrite (@perm_free _ _ _ [seq x <- T | x \in S]) ?filter_free //.
apply/uniq_perm; rewrite ?filter_uniq // ?free_uniq //.
move=> z; rewrite mem_filter; exact/esym/andb_idr/subST.
Qed.

Lemma free_tr_rV {n : nat} {R : realFieldType}
  {T : finType} {pT : predType T}
  (f : T -> 'rV[R]_n) (s : pT) :
  free [seq (f x)^T | x in s] = free [seq (f x) | x in s].
Proof.
rewrite /image_mem; elim: (enum s)=> [|h t ih]; rewrite ?nil_free //=.
rewrite !free_cons ih; congr andb.
apply/idP/idP; apply/contraNN.
- move/(memv_img (linfun trmx)); rewrite lfunE /= limg_span.
  move: (f h)^T; apply/subvP/sub_span=> a /mapP [b /mapP [c ? ->] ->].
  by rewrite lfunE /=; apply/map_f.
- move/(memv_img (linfun trmx)); rewrite lfunE /= limg_span trmxK.
  move: (f h); apply/subvP/sub_span=> a /mapP [b /mapP [c ? ->] ->].
  by rewrite lfunE /= trmxK; apply/map_f.
Qed.

Lemma free_tr_cV {n : nat} {R : realFieldType}
  {T : finType} {pT : predType T}
  (f : T -> 'cV[R]_n) (s : pT) :
  free [seq (f x)^T | x in s] = free [seq (f x) | x in s].
Proof.
have f_id: (f =1 (fun x => ((f x)^T)^T)) by move=> x; rewrite trmxK.
by rewrite /image_mem (eq_map f_id) free_tr_rV.
Qed.


Definition free_tr n R T pT:=
  (@free_tr_rV n R T pT, @free_tr_cV n R T pT).

Lemma size_free_rV {n : nat} {R : realFieldType} (s : seq 'rV[R]_n) :
  free s -> (size s <= n)%nat.
Proof.
apply/contraTT; rewrite -ltnNge.
elim: s=> //= h t IH; rewrite free_cons negb_and negbK.
case/boolP: (n == size t).
- move/eqP=> t_eq_n _; case/boolP: (free t); rewrite ?orbT ?orbF //.
  move=> free_t.
  suff/span_basis ->: basis_of fullv t by exact: memvf.
  rewrite basisEfree free_t subvf -t_eq_n dimvf /=.
  by rewrite /Vector.dim /= mul1n leqnn.
- move=> /negPf t_gt_n /ltnSE; rewrite leq_eqVlt t_gt_n /=.
  by move/IH=> ->; rewrite orbT.
Qed.

(*TODO : repeated proof to delete*)
Lemma size_free_cV {n : nat} {R : realFieldType} (s : seq 'cV[R]_n) :
  free s -> (size s <= n)%nat.
Proof.
apply/contraTT; rewrite -ltnNge.
elim: s=> //= h t IH; rewrite free_cons negb_and negbK.
case/boolP: (n == size t).
- move/eqP=> t_eq_n _; case/boolP: (free t); rewrite ?orbT ?orbF //.
  move=> free_t.
  suff/span_basis ->: basis_of fullv t by exact: memvf.
  rewrite basisEfree free_t subvf -t_eq_n dimvf /=.
  by rewrite /Vector.dim /= muln1 leqnn.
- move=> /negPf t_gt_n /ltnSE; rewrite leq_eqVlt t_gt_n /=.
  by move/IH=> ->; rewrite orbT.
Qed.


End Free.

Section Path.

Context {T: eqType} (e : rel T) (P Q : T -> Prop) (x : T) (s : seq T).
Hypothesis path_s : path e x s.
Hypothesis PQ_s : {in s, forall x, P x \/ Q x}.
Hypothesis P_x : P x.
Hypothesis Q_last : Q (last x s).
Hypothesis s_prop0 : s != [::].

Lemma foobar : exists v w, [/\ v \in x :: s, w \in s, e v w, P v & Q w].
Proof.
elim: s x path_s PQ_s P_x Q_last s_prop0=> //= h t IH.
move=> x' /andP [exh path_ht] P_Q P_x' Q_last' _.
case: (P_Q h (mem_head _ _)).
- move=> P_h; case/boolP: (t == [::]).
  + move/eqP=> t_nil; exists x'; exists h.
    split=> //; rewrite ?mem_head //.
    by move: Q_last'; rewrite t_nil.
  + move=> t_cons.
    have P_Q': {in t, forall x, P x \/ Q x} by
      move=> z z_in; apply/P_Q; rewrite in_cons z_in orbT.
    move: (IH h path_ht P_Q' P_h Q_last' t_cons).
    case => v [w] [v_ht w_t e_vw P_v Q_w].
    by exists v; exists w; split=> //; rewrite in_cons ?v_ht ?w_t orbT.
- by move=> Q_h; exists x'; exists h; split=> //; rewrite in_cons eqxx.
Qed.


End Path.

Section FSetEqCard.

Context {T : choiceType} (I J : {fset T}).

Lemma witness_eq_card : #|` I| = #|` J| -> I != J ->
  exists2 k, k \in I & k \notin J.
Proof.
move=> card_eq_IJ.
rewrite eqEfcard negb_and card_eq_IJ leqnn orbF.
by move/fsubsetPn.
Qed.

End FSetEqCard.
Section EnumValMap.

Context {p : nat} (S : {set 'I_p}) (T : Type) (f : 'I_p -> T).

Lemma enum_val_map : [seq f (enum_val i) | i <- enum 'I_#|S|] = [seq f i | i in S].
Proof.
move: (erefl #|S|); case: {2}#|S|=> [S0| n Ssn].
- have ->: enum 'I_#|S| = [::] by rewrite [enum _]size0nil ?size_enum_ord.
  rewrite (cards0_eq S0) /=.
  by apply/esym/size0nil; rewrite size_map -cardE cards0.
- have ltnS: (0 < #|S|)%nat by rewrite Ssn ltnS leq0n.
  have ord0S := Ordinal ltnS.
  pose f0 := f (enum_val ord0S).
  apply: (eq_from_nth (x0:=f0)).
  + by rewrite /image_mem !size_map -enumT ?size_enum_ord -cardE.
  + move=> i; rewrite size_map size_enum_ord=> i_ltnS.
    rewrite !(nth_map (enum_val ord0S)) -?cardE //.
    rewrite (nth_map ord0S) ?size_enum_ord //.
    rewrite (enum_val_nth (enum_val ord0S)); congr f; congr nth.
    exact: nth_enum_ord.
Qed.

End EnumValMap.

Section Foo.

Lemma set_nth_takedrop {T : Type} (x0 y: T) (s : seq T) (i : nat):
  (i < size s)%nat -> set_nth x0 s i y = take i s ++ y :: drop i.+1 s.
Proof.
elim: s i=> //= h t IH.
move=> i; case: i=> [|i]; rewrite ?drop0 //=.
by move/ltnSE/IH=> ->.
Qed.

Lemma mask_set_nthr {T : Type} (x0 : T) (s : seq T) (m : bitseq) (i : nat):
  size s = size m -> (i < size m)%nat ->
  (forall j, nth false m j -> (j < i)%nat) ->
  mask (set_nth false m i true) s = rcons (mask m s) (nth x0 s i).
Proof.
move=> size_sm i_m h_m.
have m_r_false: drop i m = nseq (size m - i)%nat false.
- apply/(@eq_from_nth _ false); rewrite ?size_drop ?size_nseq //.
  move=> j _; rewrite nth_drop nth_nseq if_same.
  move: (h_m (i + j)%nat); apply/contraPF=> -> /(_ isT).
  by rewrite -ltn_subRL subnn ltn0.
rewrite set_nth_takedrop // -[in RHS](cat_take_drop i m) m_r_false.
rewrite -(cat_take_drop i s) !mask_cat ?size_take ?size_sm //.
rewrite mask_false cats0 cat_take_drop (drop_nth x0) ?size_sm //=.
move: m_r_false; rewrite (drop_nth false) // => /(congr1 behead) /= ->.
suff ->: forall n, behead (nseq n false) = nseq n.-1 false by rewrite mask_false cats1.
by elim.
Qed.

Lemma sorted_rcons {T : Type} (s : seq T) (x : T) (r : rel T):
  sorted r (rcons s x) = sorted r s && ((0 < seq.size s)%nat ==> r (last x s) x).
Proof.
elim: s=> // h t.
case: t=> /=; rewrite ?andbT //.
by move=> a l ->; rewrite andbA.
Qed.

Lemma count_nth {T : Type} (x0 : T) (s : seq T) (a : pred T):
  count a s = \big[addn/0%nat]_(i < (size s)) a (nth x0 s i).
Proof.
elim: s=> [|h t IH]; rewrite ?big_ord0 //= IH.
by rewrite big_ord_recl /=.
Qed.

Lemma all_eq_same_mask {T1 T2 : Type} (p1 : pred T1) (p2 : pred T2)
  (s1 : seq T1) (s2 : seq T2) (m : bitseq) (x1 : T1) (x2 : T2):
  size s1 = size s2 -> size m = size s1 ->
  (forall i, (i < size s1)%nat -> p1 (nth x1 s1 i) = p2 (nth x2 s2 i)) -> 
  all p1 (mask m s1) = all p2 (mask m s2).
Proof.
elim: m s1 s2=> //= h t IH.
case=> //= h1 t1 [|h2 t2] //=.
move/succn_inj=> size_t12 /succn_inj size_tt1 nth_t12.
have: all p1 (mask t t1) = all p2 (mask t t2) by
  apply/IH=> // i; rewrite -ltnS=> /nth_t12 /=.
by case: ifP=> _ /= -> //=; move: (nth_t12 0%nat (ltn0Sn _))=> /= ->.
Qed.

Lemma iotaS_rcons (m n : nat): iota m n.+1 = rcons (iota m n) (m + n)%nat.
Proof.
elim: n m=> [|n IH].
- move=> ? /=; rewrite addn0 //.
- by move=> m /=; rewrite addnS -addSn -IH.
Qed.

Lemma cardsI_nth {T : finType} (I J : {set T}) x0:
  I :&: J = [set nth x0 (enum I) n | n : 'I_#|I| & [exists n' : 'I_#|J|, nth x0 (enum I) n == nth x0 (enum J) n'] ].
Proof.
apply/setP=> x.
rewrite !inE; apply/idP/idP.
- case/andP=> xI xJ.
  move/(_ x xI): (nth_enum_rank_in x0 xI)=> <-.
  apply/imset_f; rewrite inE; apply/existsP.
  exists (enum_rank_in xJ x).
  by rewrite (nth_enum_rank_in x0 xI) // (nth_enum_rank_in x0 xJ).
- case/imsetP=> n; rewrite inE; case/existsP=> n' /eqP nn' ->.
  by rewrite {2}nn' -!enum_val_nth !enum_valP.
Qed.

Lemma ordS_neq0 {m : nat} (k : 'I_m.+1): k != ord0 -> (k.-1 < m)%nat.
Proof. by move=> k_n0; rewrite prednK ltnSE // ltnS lt0n. Qed.

Lemma takeS_rcons {T : Type} (x : T) (s : seq T) k:
  (k < seq.size s)%nat ->
  take k.+1 s = rcons (take k s) (nth x s k).
Proof.
elim: s k; rewrite ?ltn0 //.
move=> h t IH /=; case; rewrite ?take0 //.
by move=> k /=; rewrite ltnS=> /IH ->.
Qed.

Lemma nth_eq_dflt {T : Type} (x1 x2 : T) (s : seq T) i:
  (i < seq.size s)%nat ->
  nth x1 s i = nth x2 s i.
Proof. by elim: s i=> //= h t IH []. Qed.

Lemma sorted_rel_pair {T T' : Type} (s : seq T) (s' : seq T')  
  (r : T -> T' -> Prop) (le : rel T) (le' : rel T') (x : T) (x' : T'):
  (forall x y x' y', r x x' -> r y y' -> le x y = le' x' y') ->
  size s = size s' -> 
  (forall k, (k < size s)%nat -> r (nth x s k) (nth x' s' k)) ->
  sorted le s = sorted le' s'.
Proof.
move=> le_le'.
elim: s s'=> [|h t IH] [] //= h' t' /succn_inj len_tt' r_nth.
move: (IH _ len_tt').
case: t t' len_tt' r_nth {IH}=> [|a l] [] //= a' l' _ r_nth ->.
- move: (r_nth 0%nat (ltn0Sn _)) (r_nth 1%nat)=> /=; rewrite ltnS ltn0Sn.
  by move/le_le'=> + /(_ isT); move=> /[apply] ->.
- by move=> k; rewrite -ltnS=> /r_nth /=.
Qed.

Lemma uniq_map_inj {T T': eqType} (s : seq T) (f : T -> T'):
  uniq [seq f x | x <- s] -> {in s &, injective f}.
Proof.
elim: s=> //= h t IH /andP [fh_not uniq_t].
move=> x y; rewrite !in_cons.
case/orP=> [/eqP xh|xt]; case/orP=> [/eqP yh|yt].
- by rewrite xh yh.
- by rewrite xh=> f_hy; move: yt fh_not=> /(map_f f); rewrite -f_hy=> ->.
- by rewrite yh=> f_xh; move: xt fh_not=> /(map_f f); rewrite f_xh=> ->.
- exact/IH.
Qed.  

Lemma uniq_size_ltn {T : eqType} (s s': seq T):
  uniq s -> uniq s' -> (forall i, i \in s -> i \in s') -> (size s <= size s')%nat.
Proof.
elim: s s'=> //= h t IH s'.
case/andP=> hnt uniq_t uniq_s' in_ht.
move: (in_ht h); rewrite in_cons eq_refl /= => /(_ isT).
move/perm_to_rem/perm_size=> -> /=; rewrite ltnS.
apply/IH=> //; first exact/rem_uniq.
move=> x xt; move: (in_ht x); rewrite in_cons xt orbT=> /(_ isT).
rewrite mem_rem_uniq // !inE=> ->; rewrite andbT.
by move: xt; apply: contraTneq=> ->.
Qed.

Lemma big_rcons [R : Type] (idx : R) (op : Monoid.com_law idx) [I : Type] 
  (r : seq I) (F : I -> R) (P : pred I) (t : I): 
  \big[op/idx]_(i <- rcons r t | P i) F i = 
  if (P t) then op (\big[op/idx]_(i <- r | P i) F i) (F t) else (\big[op/idx]_(i <- r | P i) F i).
Proof.
elim: r=> /=; first by rewrite big_nil BigOp.bigopE /= Monoid.mulmC.
move=> h l IH; rewrite !big_cons IH.
by case: ifP; case: ifP=> // _ _; rewrite Monoid.mulmA.
Qed. 

Lemma iter0 {T : Type} (f : T -> T) (x : T): iter 0 f x = x.
Proof. by []. Qed.
  
Lemma perm_foldl {T : eqType} {R : Type}
  (f : R -> T -> R) (x : R) (s s': seq T):
  perm_eq s s' ->
  (forall x t t', f (f x t) t' = f (f x t') t) ->
  foldl f x s = foldl f x s'.
Proof.
move=> + f_eq.
apply/catCA_perm_subst=> s1 s2 s3; rewrite !foldl_cat.
congr foldl.
elim/last_ind: s1 s2 x=> // t h IH s2 x.
rewrite !foldl_rcons -IH.
set F := foldl f x t.
elim/last_ind: s2=> // t2 h2 IH2.
by rewrite [in RHS]foldl_rcons f_eq -IH2 foldl_rcons.
Qed.

Lemma eq_foldl {T R : Type} (f f': R -> T -> R) (x : R)
  (s : seq T):
  f =2 f' -> foldl f x s = foldl f' x s.
Proof. by move=> ff'; elim: s x=> //= a l IH x; rewrite ff' IH. Qed.

Lemma sorted_cat {T : Type} (leT : rel T) (s t : seq T):
  transitive leT ->
  reflect 
  ([/\ sorted leT s, sorted leT t & allrel leT s t]) 
  (sorted leT (s ++ t)).
Proof.
move=> leT_trans; apply/(iffP idP).
- elim: s t=> /= [t ->|]; rewrite ?allrel0l //.
  move=> a l IH t /[dup] /path_sorted /IH [stt_l stt_t all_lt]. 
  rewrite cat_path=> /andP [path_al path_alt].
  rewrite path_al stt_t; split=> //.
  rewrite allrel_consl all_lt andbT.
  case: l all_lt path_al path_alt {IH stt_l}.
  + move=> /= ??; exact/order_path_min.
  + move=> a' l'; rewrite /= path_sortedE // allrel_consl=> /andP [all_a't _].
    case/and3P=> le_aa' _ _ _; move: all_a't; apply/sub_all=> z.
    exact/leT_trans.
- case; case: s t=> // a l /= t.
  rewrite cat_path=> path_al stt_t.
  rewrite allrel_consl=> /andP [all_at allrel_lt].
  apply/andP; split=> //; rewrite path_sortedE // stt_t andbT.
  elim: l a t allrel_lt all_at {path_al stt_t}=> //=.
  move=> a' l' IH a t + _; rewrite allrel_consl=> /andP [] /[swap].
  exact/IH.
Qed.
  

  
End Foo. 

Section BinNatExtra.

Lemma nat_of_binE (n : nat) : nat_of_bin (N.of_nat n) = n.
Proof.
elim: n=> //= n; case: n=> //= n <-.
by rewrite nat_of_succ_pos.
Qed.

Lemma bar (x y : N): (BinNat.N.to_nat x < BinNat.N.to_nat y)%nat -> (x < y)%nat.
Proof.
case: x; case: y=> //=.
- by move=> p _; elim: p=> //= p; rewrite NatTrec.doubleE double_gt0.
- move=> p q /ssrnat.ltP/Pnat.Pos2Nat.inj_lt.
  move: p; apply: BinPos.Pos.lt_ind.
  + by rewrite nat_of_succ_pos.
  + move=> p _ /(ltn_trans); apply.
    by rewrite nat_of_succ_pos.
Qed.

Lemma N_minE (x y : N) : N.min x y = minn x y :> nat.
Proof.
rewrite /N.min; rewrite Nnat.N2Nat.inj_compare.
case E: (PeanoNat.Nat.compare _ _).
- by move/PeanoNat.Nat.compare_eq: E=> /Nnat.N2Nat.inj_iff ->; rewrite minnn.
- move/Compare_dec.nat_compare_Lt_lt: E=> /ssrnat.ltP h.
  exact/esym/minn_idPl/ltnW/bar.
- move/Compare_dec.nat_compare_Gt_gt: E=> /ssrnat.ltP h.
  exact/esym/minn_idPr/ltnW/bar.
Qed.

Lemma N_maxE (x y : N) : N.max x y = maxn x y :> nat.
Proof.
rewrite /N.max; rewrite Nnat.N2Nat.inj_compare.
case E: (PeanoNat.Nat.compare _ _).
- by move/PeanoNat.Nat.compare_eq: E=> /Nnat.N2Nat.inj_iff ->; rewrite maxnn.
- move/Compare_dec.nat_compare_Lt_lt: E=> /ssrnat.ltP h.
  exact/esym/maxn_idPr/ltnW/bar.
- move/Compare_dec.nat_compare_Gt_gt: E=> /ssrnat.ltP h.
  exact/esym/maxn_idPl/ltnW/bar.
Qed.

End BinNatExtra.

Section OApply.

Context {T U : Type} (f : T -> T + U).

Definition oapply (v : T+U) :=
  match v with
  | inl v => f v
  | inr _ => v
  end.

Lemma oapply_inl (x : T): oapply (inl x) = f x.
Proof. by []. Qed.

Lemma oapply_inr (x : U): oapply (inr x) = inr x.
Proof. by []. Qed.

End OApply.

Section UndupFirst.

Fixpoint undup' {T : eqType} (s : seq T):=
  match s with
  |[::] => [::]
  |h :: t => h :: [seq y <- undup' t | y != h]
  end.

Lemma undup'_uniq {T : eqType} (s : seq T):
  uniq (undup' s).
Proof.
elim: s=> // h t IH /=.
apply/andP; split; last exact/filter_uniq.
elim: (undup' t)=> //= a l IH2; case: ifP=> //.
by move=> ?; rewrite in_cons negb_or IH2 eq_sym andbT.
Qed.

Lemma mem_undup' {T : eqType} (s : seq T):
  undup' s =i s.
Proof.
move=> x; elim: s=> //= h t IH.
rewrite !inE; case/boolP: (x == h)=> //= x_n_h.
by rewrite mem_filter x_n_h.
Qed.

Lemma has_undup' {T : eqType} (s : seq T) (p : pred T):
  has p s = has p (undup' s).
Proof.
elim: s=> //= h t IH; case/boolP: (p h)=> //= phF.
rewrite IH; elim: (undup' t)=> //= a l IH2.
case: ifP=> /= [_|]; first by congr orb.
by move/eqP=> ->; rewrite (negPf phF).
Qed.

Lemma map_undup' {T T' : eqType} (s : seq T) (f : T -> T'):
  injective f -> undup' [seq f x | x <- s] = [seq f x | x <- undup' s].
Proof.
move=> inj_f; elim: s=> //= h t IH; congr (_ :: _).
rewrite IH; elim: (undup' t)=> //= a l.
case: ifP; case: ifP=> [|/eqP ->]; rewrite ?eq_refl //.
- by move=> ahF fahF -> /=.
- by move=> /[swap] /eqP /inj_f ->; rewrite eq_refl.
Qed.

Lemma map_in_undup' {T T' : eqType} (s : seq T) (f : T -> T'):
  {in s &, injective f} -> 
  undup' [seq f x | x <- s] = [seq f x | x <- undup' s].
Proof.
elim: s=> //= h t IH inj_f; congr cons.
rewrite IH; last (move=> ?? /(mem_body h) + /(mem_body h); exact: inj_f).
have /=: {in undup' (h :: t) &, injective f} by
  move=> ??; rewrite !mem_undup'; exact: inj_f.
elim: (undup' t)=> //= a l.
case: ifP; case: ifP=> //=.
- move=> fahF ahF + inj_f_hal; move=> -> //.
  move=> z z'; rewrite !inE => z_in z'_in.
  by apply: inj_f_hal; rewrite !inE orbCA ?z_in ?z'_in orbT.
- move/eqP=> + + + inj_f_hal; move/inj_f_hal.
  by rewrite !inE !eq_refl orbT /= => ->; rewrite ?eq_refl.
- by move=> /[swap] /eqP ->; rewrite eq_refl.
Qed.


Lemma filter_undup' {T : eqType} (s : seq T) (p : pred T):
  undup' [seq x <- s | p x] = [seq x <- undup' s | p x].
Proof.
elim: s=> //= h t IH; case: ifP=> /=.
- move=> ph; rewrite IH; congr (_ :: _).
  elim: (undup' t)=> // a l /=; case: ifP; case: ifP=> //=.
  + by move=> -> -> ->.
  + by move/eqP=> -> _; rewrite eq_refl /=.
  + by move=> _ ->.
- move=> phF; rewrite IH; elim: (undup' t)=> // a l /=.
  case: ifP; case: ifP=> //=.
  + by move=> ahF -> ->.
  + by move/eqP=> ->; rewrite phF.
  + by move=> ? -> ->.
Qed.


End UndupFirst.

Section PrefixSeq.

Fixpoint prefix_seq {T : eqType} (l r : seq T):=
  match l,r with
  |[::], [::] => true
  |_, [::] => false
  |[::], _ => true
  |h::t, h'::t'=> if h == h' then prefix_seq t t' else false
  end.

Lemma prefix_seq_path {T : eqType} (l r : seq T) (e : rel T) (x : T):
  prefix_seq l r -> path e x r -> path e x l.
Proof.
elim: l r x=> //= h t IH [] // h' t' /= x.
case: ifP=> // /eqP -> + /andP [-> +] /=.
exact: IH.
Qed.

Lemma prefix_seq_notin {T : eqType} (l r : seq T) (x : T):
  prefix_seq l r -> x \notin r -> x \notin l.
Proof.
elim: l r=> // h t IH [] //= h' t'; case: ifP=> // /eqP -> /IH.
rewrite !in_cons !negb_or => + /andP [->] /=.
exact.
Qed.

Lemma prefix_seq_uniq {T : eqType} (l r : seq T):
  prefix_seq l r -> uniq r -> uniq l.
Proof.
elim: l r=> // h t IH [] //= h' t'.
case: ifP=> // /eqP -> + /andP [].
move=> /[dup] /IH + /prefix_seq_notin /[apply].
move=> + -> /=; exact.
Qed.

Lemma prefix_seq_in_out {T : eqType} (s : seq T) (p : pred T) (x : T):
  p x -> ~~ p (last x s) ->
  exists s', [&& prefix_seq s' s, all p (belast x s') & ~~ p (last x s')].
Proof.
elim: s x=> /= [? ->|] // h t IH x px.
case/boolP: (p h).
- move/IH=> /[apply] -[s'] /and3P [pref_s' all_s' last_s'].
  by exists (h :: s'); apply/and3P=> /=; split; rewrite ?eq_refl ?px.
- move=> nph _; exists [:: h]; apply/and3P=> /=; split; rewrite ?eq_refl ?andbT //.
  by case: t {IH}.
Qed.

Lemma prefix_seq_size {T : eqType} (l r : seq T):
  prefix_seq l r -> (seq.size l <= seq.size r)%nat.
Proof.
elim: l r=> //= h t IH [] // h' t'; case: ifP=> //= _.
by move/IH; rewrite ltnS.
Qed.

Lemma prefix_seq_belast {T : eqType} (s : seq T) (x : T):
  prefix_seq (behead (belast x s)) s.
Proof.
case: s x=> //= h t _; elim: t h=> //= a l IH h.
rewrite eq_refl; exact/IH.
Qed.


End PrefixSeq.

Section Nat.

Lemma leq_ltn_addn (a b c d : nat):
  (a <= b)%nat -> (c < d)%nat -> (a + c < b + d)%nat.
Proof. by move/leq_add=> /[apply]; rewrite addnS. Qed.

End Nat.

