(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix finmap vector.

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

Arguments exists_andP [T A B].
Prenex Implicits exists_andP.

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
  (#|[set l : 'I_k | P l]| <= k)%N.
Proof.
  set S := [set l : 'I_k | P l].
  suff: (#|S| <= #|'I_k|)%N.
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
apply: (@eq_from_nth _ 0 _ _ _).
- by rewrite !size_map size_take -enumT size_enum_ord (ltn_ord i) size_iota.
- move => k k_lt_size.
  have k_lt_i: (k < i)%N by rewrite !size_map size_take -enumT size_enum_ord (ltn_ord i) in k_lt_size.
  rewrite (@nth_map _ i _ 0); last by rewrite size_map in k_lt_size.
  rewrite nth_iota // add0n (@nth_map _ i _ i); last by rewrite !size_map in k_lt_size.
  rewrite nth_take //= -enumT nth_enum_ord //.
  exact: (ltn_trans k_lt_i (ltn_ord i)).
Qed.

Lemma predC1_drop_enum (n : nat) (i : 'I_n) :
  [seq i0 <- drop i (enum 'I_n) | i0 != i] = drop i.+1 (enum 'I_n).
Proof.
have i_lt_size_enum : (i < size (enum 'I_n))%N
  by rewrite size_enum_ord (ltn_ord i).
rewrite (drop_nth i i_lt_size_enum) /= nth_ord_enum eq_refl /=.
apply/all_filterP.
rewrite all_count -(@count_predC _ (pred1 i)).
suff ->: (count_mem i) (drop i.+1 (enum 'I_n)) = 0 by rewrite add0n.
suff H: (count_mem i) (take i.+1 (enum 'I_n)) = 1
  by move/eqP: (count_uniq_mem i (enum_uniq 'I_n));
  rewrite -{1}[(enum 'I_n)](cat_take_drop i.+1) mem_enum /= count_cat H -[X in _ == X]addn0 eqn_add2l => /eqP <-.
have uniq_take: uniq (take i.+1 (enum 'I_n))
  by apply: (@subseq_uniq _ _ (enum 'I_n) _ (enum_uniq 'I_n));
  rewrite -{2}[(enum 'I_n)](cat_take_drop i.+1);
  exact: prefix_subseq.
rewrite (count_uniq_mem i uniq_take) -index_mem.
move: (@nth_take i.+1 _ i i (ltnSn i) (enum 'I_n)); rewrite nth_ord_enum => nth_eq_i.
have i_lt: i < (if i.+1 < n then i.+1 else n)
  by case: (boolP (i.+1 < n)%N); [rewrite ltnSn | rewrite (ltn_ord i)].
by rewrite size_take size_enum_ord -{1}nth_eq_i (index_uniq _ _ uniq_take) ?size_take ?size_enum_ord !i_lt.
Qed.

Lemma drop_enum_predC1 (n : nat) (i : 'I_n) :
  drop i (map val [seq i0 <- enum 'I_n | i0 != i]) = (iota i.+1 (n-i.+1)%N).
Proof.
rewrite -[enum 'I_n](cat_take_drop i) filter_cat predC1_take_enum map_cat drop_size_cat;
  last by rewrite !size_map size_take size_enum_ord (ltn_ord i).
rewrite predC1_drop_enum map_drop val_enum_ord.
apply: (@eq_from_nth _ 0 _ _ _).
- by rewrite size_drop !size_iota.
- move => k k_lt_size.
  rewrite size_drop size_iota in k_lt_size.
  rewrite nth_drop nth_iota; last by rewrite -ltn_subRL.
  by rewrite add0n nth_iota //.
Qed.

Lemma nth_predC1_enum (n k : nat) (i : 'I_n) :
  (k < n.-1) -> nat_of_ord (nth i [seq i0 <- enum 'I_n | i0 != i] k) = (i <= k) + k.
Proof.
move => k_lt_n_minus_1.
rewrite -(@nth_map _ _ _ 0); last by rewrite size_enum_predC1.
have ->: map val [seq i0 <- enum 'I_n | i0 != i] = (iota 0 i) ++ (iota i.+1 (n-i.+1)%N)
  by rewrite -[LHS](cat_take_drop (val i)) take_val_predC1_enum drop_enum_predC1.
rewrite nth_cat size_iota (leqNgt i k).
case: (boolP (k < i)) => [? /= | i_leq_k /=]; first by rewrite nth_iota.
rewrite -leqNgt in i_leq_k.
rewrite nth_iota; first by rewrite -addn1 [X in X+_]addnC -addnA (subnKC i_leq_k).
have k_lt_n: (k < n)%N by apply: (leq_trans _ (leq_pred n)).
rewrite -[X in n - X]addn1 addnC subnDA subn1.
apply: (ltn_sub2r _ k_lt_n_minus_1).
by apply: (leq_ltn_trans i_leq_k).
Qed.

Lemma predC1_enum (n : nat) (i : 'I_n) :
  [seq i0 <- enum (ordinal_finType n) | i0 != i] = [seq lift i i0 | i0 <- enum (ordinal_finType n.-1)].
Proof.
have size_eq: size [seq i0 <- enum (ordinal_finType n) | i0 != i] = size [seq lift i i0 | i0 <- enum (ordinal_finType n.-1)]
  by rewrite size_map size_enum_ord size_enum_predC1.
apply: (@eq_from_nth _ i _ _ size_eq) => k k_lt_size.
have k_lt_size': (k < size (enum (ordinal_finType n.-1)))%N by rewrite size_eq size_map in k_lt_size.
have k_lt_n_minus_1: (k < n.-1)%N by rewrite size_enum_ord in k_lt_size'.
rewrite (@nth_map _ (Ordinal k_lt_n_minus_1) _ i (lift i) _ _ k_lt_size') /=.
apply: ord_inj.
have ->: nth (Ordinal k_lt_n_minus_1) (enum 'I_n.-1) k = (Ordinal k_lt_n_minus_1)
  by apply: ord_inj; exact: (@nth_enum_ord _ (Ordinal k_lt_n_minus_1) _ k_lt_n_minus_1).
rewrite /= /bump.
by apply: nth_predC1_enum.
Qed.

Lemma ltn_divLR' m p d : (d > 0)%N -> (m < p * d)%N -> (m %/ d < p)%N.
Proof.
by move => H ?; rewrite (ltn_divLR _ _ H).
Qed.


Lemma subn_inj (p q r : nat) : (p <= r)%N -> (q <= r)%N -> (r - p == r - q)%N = (p == q).
Proof.
move => p_le_r q_le_r; apply/eqP/idP; last by move/eqP => ->.
move/(congr1 (addn^~ p)); rewrite subnK // addnC.
move/(congr1 (addn^~ q)); rewrite -addnA subnK // addnC.
by move/addIn => ->.
Qed.

End Basic.

Section Big.

Variables (R : eqType) (idx : R).
Variable I : eqType.

Local Notation "1" := idx.

Variable op : Monoid.com_law 1.

Lemma big_rem_idx r (P Q : pred I) F :
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

Arguments big_rem_idx [R idx I op r P Q F].
Arguments eq_big_seq_congr2 [R idx I op T T' r F].
Arguments eq_bigl_seq [R idx I op r P1 P2 F].

Section ExtraNum.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R : realFieldType.
Variable m n : nat.

Lemma ltr_neq (x y : R) : x < y -> x != y.
Proof.
by rewrite ltr_neqAle => /andP [].
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
  | x :: S' => Num.min x (min_seq S' v)
  end.

Lemma min_seq_ler (S : seq R) v: forall i, i \in S -> min_seq S v <= i.
Proof.
elim: S => [ | x S' IH].
- by move => i; rewrite in_nil.
- move => i; rewrite in_cons; move/orP => [/eqP -> | H].
  + rewrite /=.
    case H': S'; first by done.
    * rewrite ler_minl; apply/orP; left; done.
  + rewrite /=; move: H.
    case H': S'; first by rewrite in_nil.
    * by rewrite -H'; move => Hi; rewrite ler_minl; apply/orP; right; apply: IH.
Qed.

Lemma min_seq_eq (S : seq R) (v : R) :  S != [::] -> has [pred i | min_seq S v == i] S.
Proof.
elim: S => [ | x S']; first by done.
- case: (altP (S' =P [::])) => [-> /= | HS /(_ is_true_true) IH _]; first by rewrite eq_refl.
  + apply/hasP. case: (minrP x (min_seq S' v)) => [H'' |].
    * exists x; first by rewrite mem_head.
      rewrite /= minr_l //. by case H: S'.
    * move/hasP: IH => [i Hi /= /eqP ->] ?.
      exists i; first by rewrite mem_behead.
      case H: S'; first by move: Hi; rewrite H in_nil.
      by rewrite minr_r // ltrW.
Qed.

Variant min_seq_spec (S : seq R) (v : R) : R -> Prop :=
| MinSeqEmpty of (S = [::]) : min_seq_spec S v v
| MinSeqNonEmpty x of (x \in S /\ (forall y, y \in S -> y >= x)) : min_seq_spec S v x.

Lemma min_seqP (S : seq R) (v : R) :
  min_seq_spec S v (min_seq S v).
Proof.
case: (altP (S =P [::])) => [->|].
- by constructor.
- move/(min_seq_eq v)/hasP => [x [x_in_S]]; rewrite inE eq_sym => /eqP x_eq.
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
    apply: (@ltr_le_trans _ (min_seq S v) _ _); first by done.
    + by apply: min_seq_ler.
  - case: H => [Hne | He].
    + move/allP => H' /=. move/hasP: (min_seq_eq v Hne) => [i Hi /eqP -> /=].
      by apply: H'.
    + elim: S => [// | x S Hx].
        rewrite /= => /andP [Hxp H_].
        have Hsp: 0 < min_seq S v by apply: Hx. rewrite {H_ Hx}.
        case Haf: (S); first by apply: Hxp. rewrite -Haf.
        case: minrP => //.
Qed.

Lemma ltW_lt (x y z : R) : (x < y < z) -> (x <= y < z).
Proof.
by move => /andP [??]; rewrite ltrW //=.
Qed.

Lemma lt_ltW (x y z : R) : (x < y < z) -> (x < y <= z).
Proof.
by move => /andP [??]; rewrite ltrW //= andbT.
Qed.

Lemma lt_leW (x y z : R) : (x < y <= z) -> (x <= y <= z).
Proof.
by move => /andP [??]; rewrite ltrW //= andbT.
Qed.

Lemma ltW_le (x y z : R) : (x <= y < z) -> (x <= y <= z).
Proof.
by move => /andP [-> ?]; rewrite ltrW //=.
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
apply/setP => i; apply/idP/idP; move/(mem_imset f).
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

Hint Extern 0 (expose _) => (exact) : typeclass_instances.
Hint Extern 0 (expose (is_true _)) => (match goal with H : is_true _ |- _ => exact: H end) : typeclass_instances.

(*Hint Extern 0 (_ `<=` _)%fset => exact: fsubset_refl.
Hint Extern 0 (fset0 `<=` _)%fset => exact: fsub0set.*)

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
Admitted.

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
Admitted.

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

End Vector.
