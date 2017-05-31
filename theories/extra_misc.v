(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.

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

End Basic.

Section Big.

Variables (R : eqType) (idx : R).
Variable I : eqType.

Local Notation "1" := idx.

Variable op : Monoid.com_law 1.

Notation Local "'*%M'" := op (at level 0).
Notation Local "x * y" := (op x y).

Lemma big_rem_idx r (P Q : pred I) F :
  (forall i, i \in r -> P i && ~~(Q i) -> F i = idx) -> \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- r | (P i) && Q i) F i.
Proof.
move => H.
rewrite (bigID Q).
have H': \big[*%M/1]_(i <- r | P i && ~~Q i) F i = idx.
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

Implicit Arguments big_rem_idx [R op idx I r P F].
Implicit Arguments eq_big_seq_congr2 [R op idx I T T' r F].
Implicit Arguments eq_bigl_seq [R op idx I r P1 F].

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

Fixpoint min_seq (S : seq R) := (* TODO: add an extra element returned in case the list is empty *)
                     match S with
                      | [::] => 0
                      | [:: x] => x
                      | x :: S' => Num.min x (min_seq S')
                     end.

Lemma min_seq_ler (S : seq R): forall i, i \in S -> min_seq S <= i.
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

Lemma min_seq_eq (S : seq R): S != [::] -> has [pred i | min_seq S == i] S.
Proof.
elim: S => [ | x S']; first by done.
- case: (altP (S' =P [::])) => [-> /= | HS /(_ is_true_true) IH _]; first by rewrite eq_refl.
  + apply/hasP. case: (minrP x (min_seq S')) => [H'' |].
    * exists x; first by rewrite mem_head.
      rewrite /= minr_l //. by case H: S'.
    * move/hasP: IH => [i Hi /= /eqP ->] ?.
      exists i; first by rewrite mem_behead.
      case H: S'; first by move: Hi; rewrite H in_nil.
      by rewrite minr_r // ltrW.
Qed.

Lemma min_seq_positive (S : seq R): S != [::] -> (min_seq S > 0) = all [pred i | i > 0] S.
Proof.
move => H.
apply/idP/idP.
- move => H'; apply/allP; rewrite /=.
  move => x Hx. 
  apply: (@ltr_le_trans _ (min_seq S) _ _); first by done.
  + by apply: min_seq_ler.
- move/allP => H' /=. move/hasP: (min_seq_eq H) => [i Hi /eqP -> /=].
  by apply: H'.
Qed.

End ExtraNum.

(*
Section Induction.

Variable n : nat.

Lemma strong_ind (P : nat -> Prop): 
  P 0%N -> (forall k, (forall l, (l <= k)%N -> P l) -> P k.+1) -> forall k, P k.
Proof.
move => H0 IH k.
elim: k {-2}k (leqnn k).
- by move => ?; rewrite leqn0; move/eqP ->.
- move => p IH'.
  move => k. rewrite leq_eqVlt; move/orP; case.
  + by move/eqP -> ; apply: (IH p).
  + by apply: IH'.
Qed.

Lemma bounded_strong_ind (p: nat) (P: nat -> Prop):
  P 0%N -> (forall k, (k < p)%N -> (forall l, (l <= k)%N -> P l) -> P k.+1) -> forall k, (k <= p)%N -> P k.
Proof.
move => H0 IH k.
elim: k {-2}k (leqnn k).
- by move => ?; rewrite leqn0; move/eqP ->.
- move => k IH'.
  move => l. rewrite leq_eqVlt; move/orP; case.
  + move/eqP -> => Hk; apply: (IH k); first by done.
    move => i Hi; apply: IH'; first by done.
    by rewrite leq_eqVlt; move: (leq_ltn_trans Hi Hk) ->; rewrite orbT.
  + by move => Hl Hl'; apply: IH'.
Qed.

Lemma decr_strong_ind (P: nat -> Prop) :
  P n.-1 -> (forall k, (0 < k <= n.-1)%N -> (forall l, (k <= l <= n.-1)%N -> P l) -> P (k.-1)) -> forall k, (k <= n.-1)%N -> P k.
Proof.
move => Hn IH.
suff: forall k: nat, (k <= n.-1)%N -> P ((n.-1)-k)%N.
- move => H k Hk; move: (H ((n.-1)-k)%N).
  by rewrite !subKn // leq_subr; move/(_ isT).
apply: bounded_strong_ind; first by rewrite subn0.
move => k; rewrite subnS => H H'.
apply: IH.
- by rewrite subn_gt0 leq_subr H.
- move => l /andP [Hl Hl'].
  rewrite -(subKn Hl').
  by apply: H'; rewrite leq_subLR addnC -leq_subLR.
Qed.

End Induction.
*)