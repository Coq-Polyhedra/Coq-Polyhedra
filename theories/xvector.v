(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 * Copyright (c) - 2020       - Quentin Canu <qcanu17@gmail.com>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg vector finmap.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope vspace_scope.
Import GRing.Theory.

Section FSetOfSeq.

Variable (K : choiceType).
Implicit Type (X : seq K).

Definition fset_of_seq X :=
  [fset e in X]%fset.

Lemma in_fset_of_seq X :
  fset_of_seq X =i X.
Proof.
move => x; apply/idP/idP.
- by case/imfsetP => y /= ? ->.
- by move => x_in_X; apply/imfsetP; exists x.
Qed.

Lemma perm_eq_fset_of_seq X :
  uniq X -> perm_eq (fset_of_seq X) X.
Proof.
move/undup_id => {2}<-.
rewrite -[X' in perm_eq X']undup_id //.
by apply/perm_undup/in_fset_of_seq.
Qed.

Lemma card_fset_of_seq X :
  uniq X -> #|` fset_of_seq X | = size X.
Proof.
by move => ?; apply/perm_size/perm_eq_fset_of_seq.
Qed.

End FSetOfSeq.

Section EBasis.

Variable (K : fieldType) (vT : vectType K).

Fixpoint ebasis (X Y: seq vT):=
  if X is x :: X' then
    if (x \in <<X' ++ Y>>) then ebasis X' Y
    else x :: (ebasis X' Y)
  else Y.

Lemma ebasis_sub (X Y: seq vT) :
  {subset (ebasis X Y) <= X ++ Y}.
Proof.
elim: X => [| a l Hind x] //=.
case: ifP => _.
- by move/Hind; rewrite inE => ->; rewrite orbT.
- by rewrite !inE => /orP; case => [| /Hind] ->; rewrite ?orbT.
Qed.

Lemma ebasis_complete (X Y: seq vT) :
  {subset Y <= (ebasis X Y)}.
Proof.
elim: X => [| a l Hind] //=.
case: ifP => _ // x xinY.
by move: (Hind x xinY); rewrite inE => ->; rewrite orbT.
Qed.


Lemma ebasis_free (X Y: seq vT):
  free Y -> free (ebasis X Y).
Proof.
move => freeY; elim : X => [| a l Hind]; rewrite ?nil_free //=.
case: ifPn => [_ //| a_notin_span].
rewrite free_cons Hind andbT.
by apply/contra: a_notin_span; apply/subvP/sub_span/ebasis_sub.
Qed.

Lemma ebasis_span (X Y : seq vT) :
  (<<ebasis X Y>> = <<X++Y>>).
Proof.
elim: X => [| a l Hind] //=.
case: ifP => [| _]; rewrite !span_cons Hind //.
rewrite memvE => a_in; symmetry; by apply/addv_idPr.
Qed.

Lemma ebasis_basis (X Y: seq vT):
  free Y -> basis_of <<X++Y>>%VS (ebasis X Y).
Proof.
move => freeY; apply/andP; split.
- by apply/eqP/ebasis_span.
- exact: ebasis_free.
Qed.

Lemma ebasisP (X Y: {fset vT}) :
free Y -> exists Z : {fset vT},
    [/\ (Z `<=` X `|` Y)%fset, (Y `<=` Z)%fset & basis_of <<(X `|` Y)%fset>> Z].
(* TODO:
   perhaps write into an exists2 and with (Y `<=` Z `<=` X `|` Y)%fset *)
Proof.
move => freeY.
pose Z := fset_of_seq (ebasis X Y).
exists Z; split.
- apply/fsubsetP => x; rewrite in_fset_of_seq /fsetU in_fset /=.
  exact: ebasis_sub.
- apply/fsubsetP => x; rewrite in_fset_of_seq; exact: ebasis_complete.
- apply/andP; split.
  + rewrite (eq_span (in_fset_of_seq _)); apply/eqP; rewrite ebasis_span.
    by apply eq_span; rewrite /eq_mem /fsetU => x; rewrite in_fset /=.
  + by rewrite (perm_free (perm_eq_fset_of_seq _)) ?free_uniq ?ebasis_free.
Qed.

Lemma ebasisP' (X Y: {fset vT}) :
Y `<=` X -> free Y -> exists2 Z : {fset vT}, (Y `<=` Z `<=` X)%fset & basis_of <<X>> Z.
Admitted.

(* TODO:
Lemma ebasisP0 (X: {fset vT}) :
exists2 Z : {fset vT}, (Z `<=` X)%fset & basis_of <<X>> Z.
*)

Lemma card_basis (U : {vspace vT}) (X : {fset vT}) :
  basis_of U X -> #|` X | = (\dim U)%N.
Proof.
move => X_basis.
apply/anti_leq/andP; split; move: X_basis.
- by rewrite basisEdim => /andP [].
- by rewrite basisEfree => /and3P [].
Qed.

End EBasis.
