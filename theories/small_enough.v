(**************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect           *)
(*                                                                        *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr)  *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)   *)
(* All rights reserved.                                                   *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(**************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section small_enough.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R: realFieldType.

Definition holds_for_small_enough (P: R -> bool) := exists eps, eps > 0 /\ forall eps', (0 < eps' <= eps) -> P eps'.

Lemma small_enough_eq (P Q: R -> bool) : (P =1 Q) -> (holds_for_small_enough P) -> (holds_for_small_enough Q).
Proof.
move => H [eps [Heps Heps']].
exists eps; split; first by done.
- by move => ?; rewrite -H; apply: Heps'.
Qed.

Lemma small_enough_imply (P Q : R -> bool) : (forall eps: R, (P eps -> Q eps)) -> (holds_for_small_enough P) -> (holds_for_small_enough Q).
Proof.
move => H [eps [Heps Heps']].
exists eps; split; first by done.
- by move => eps' ?; apply/H; apply: Heps'.
Qed.

Lemma small_enough_cons (b: bool) : b -> (holds_for_small_enough (fun eps => b)).
Proof.
move => ?; exists 1; split; by [apply: ltr01 | move => ? _].
Qed.

Lemma small_enough_sequence (T: eqType) (S: seq T) (P : T -> R -> bool) :
  (forall x, x \in S -> holds_for_small_enough (P x)) -> holds_for_small_enough (fun eps => all (P^~ eps) S).
Proof.
elim S => [| s S' IH].
- move => _; exists 1; split; first by apply: ltr01.
  + by move => ? ?; rewrite all_nil.
- move => H.
  move: (H s). rewrite mem_head; move/(_ is_true_true) => [eps_s [Hs Hs']]. 
  have [eps_S' [HS HS']]: holds_for_small_enough (fun eps : R => all (P^~ eps) S').
  + by apply: IH; move => x Hx; apply: H; rewrite mem_behead.
  exists (Num.min eps_s eps_S'); split; first by rewrite ltr_minr; apply/andP; split.
  + move => eps'. rewrite ler_minr; move/and3P => [Hesp0 Heps1 Heps2].
    apply/andP; split.
    * by apply: Hs'; apply/andP; split.
    * by apply: HS'; apply/andP; split.
Qed.

Lemma small_enough_fintype (T: finType) (P : T -> R -> bool) :
  (forall i: T, holds_for_small_enough (P i)) -> holds_for_small_enough (fun eps => [forall i, P i eps]).
Proof.
move => H.
pose S := enum T.
have [eps [Heps1 Heps2]] : holds_for_small_enough (fun eps => all (P^~ eps) S).
- apply: small_enough_sequence; move => ? _; apply: H.
exists eps; split; first by done.
- move => eps' Heps'.
  apply/forallP => x; move/allP: (Heps2 _ Heps') => Hx.
  by apply: Hx; rewrite mem_enum.
Qed.

Lemma small_enough_ordinal (p: nat) (P : 'I_p -> R -> bool) :
  (forall i: 'I_p, holds_for_small_enough (P i)) -> holds_for_small_enough (fun eps => [forall i, P i eps]).
Proof.
by apply: small_enough_fintype.  
Qed.

End small_enough.
