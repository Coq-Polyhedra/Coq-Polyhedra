(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix finmap.

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
Admitted.

Lemma imfset0 (K K' : choiceType) (f : K -> K') :
  (f @` fset0)%fset = fset0.
Admitted.

Lemma fsub_fsetval (K : choiceType) (A B : {fset K}) :
  (A `<=` B)%fset -> A = [fsetval x in [fset x : B | val x \in A]]%fset.
Admitted.

End ExtraFinmap.

Class expose (P : Prop) := Expose : P.
Hint Extern 0 (expose _) => (exact) : typeclass_instances.


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
Notation "A %:fsub" := (fsubset_of (Phantom _ A)) (at level 0).

Definition tag0 x := Tag x.
Definition tag1 x := tag0 x.
Definition tag2 x := tag1 x.
Definition tag3 x := tag2 x.
Definition tag4 x := tag3 x.
Definition tag5 x := tag4 x.
Canonical tag5.

Canonical fsubset_expose (A : {fset K})
          (H : expose (A `<=` S)%fset) := @FSubset (tag1 _) H.
Canonical fsubset_fset0 := @FSubset (tag2 _) (fsub0set S).

Lemma fsubset_setUP (A B : {fset K}) :
  A `<=` S -> B `<=` S -> A `|` B `<=` S.
Admitted.
Canonical fsubset_setU (A B : {fset K}) (HA : expose (A `<=` S)) (HB : expose (B `<=` S)) :=
  @FSubset (tag3 _) (fsubset_setUP HA HB).

Lemma fsubset_bigUP (I : finType) (P : pred I) F :
  (forall i, F i `<=` S) -> (\bigcup_(i | P i) F i) `<=` S.
Admitted.
Canonical fsubset_bigU (I : finType) (P : pred I) F
          (H : expose (forall i, F i `<=` S)) := @FSubset (tag4 _) (fsubset_bigUP P H).

Global Instance expose_setT : expose (S `<=` S) := Expose (fsubset_refl S).
Global Instance expose_valP (A : fsubset_t) : expose (A `<=` S) := Expose (valP A).
Global Instance expose_funP (T : Type) (f : T -> fsubset_t) :
  expose (forall i, f i `<=` S) := Expose (fun i => (valP (f i))).

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

Variable (I : finType) (P : pred I) (F : I -> fsubset_t).
Check (\bigcup_(i | P i) (F i))%:fsub.
End Test.

End FSubset.

Module Import Exports.
Canonical tagged_fset_eqType.
Canonical tagged_fset_choiceType.
Canonical fsubset_subType.
Canonical fsubset_eqType.
Canonical fsubset_choiceType.
Canonical fsubset_countType.
Canonical fsubset_finType.
Canonical tag5.
Canonical fsubset_expose.
Canonical fsubset_fset0.
Canonical fsubset_setU.
Canonical fsubset_bigU.
Coercion untag : tagged_fset >-> finset_of.
Coercion tf : fsubset_t >-> tagged_fset.
End Exports.
End FSubset.

Export FSubset.Exports.

Notation "'{fsubset'  S '}'" := (FSubset.fsubset_t S) (at level 2).
Notation "A %:fsub" := (FSubset.fsubset_of (Phantom _ A)) (at level 0).

Section Test.
Local Open Scope fset_scope.

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