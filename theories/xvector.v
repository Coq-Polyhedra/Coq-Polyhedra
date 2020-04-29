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

Fixpoint ebasis (X : seq vT) :=
  if X is x :: X' then
    if (x \in <<X'>>) then ebasis X'
    else x :: (ebasis X')
  else [::].

Lemma ebasis_sub (X : seq vT) :
  {subset (ebasis X) <= X}.
Proof.
elim : X => [| a l Hind x] //=.
case: ifP => _.
- by move/Hind; rewrite inE => ->; rewrite orbT.
- by rewrite !inE => /orP; case => [| /Hind] ->; rewrite ?orbT.
Qed.

Lemma ebasis_free (X : seq vT):
  free (ebasis X).
Proof.
elim : X => [| a l Hind]; rewrite ?nil_free //=.
case: ifPn => [_ //| a_notin_span].
rewrite free_cons Hind andbT.
by apply/contra: a_notin_span; apply/subvP/sub_span/ebasis_sub.
Qed.

Lemma ebasis_span (X : seq vT) :
  (<<ebasis X>> = <<X>>).
Proof.
elim: X => [| a l Hind] //=.
case: ifP => [| _]; rewrite !span_cons Hind //.
rewrite memvE => a_in; symmetry; by apply/addv_idPr.
Qed.

Lemma ebasis_basis (X : seq vT):
  basis_of <<X>>%VS (ebasis X).
Proof.
apply/andP; split.
- by apply/eqP/ebasis_span.
- exact: ebasis_free.
Qed.

Lemma ebasisP (X : {fset vT}) :
  exists2 Y, (Y `<=` X)%fset & basis_of <<X>>%VS Y.
Proof.
pose Y := fset_of_seq (ebasis X).
exists Y.
- apply/fsubsetP => x; rewrite in_fset_of_seq.
  by apply/ebasis_sub.
- apply/andP; split.
  + rewrite (eq_span (in_fset_of_seq _)); apply/eqP/ebasis_span.
  + by rewrite (perm_free (perm_eq_fset_of_seq _)) ?free_uniq ?ebasis_free.
Qed.

Lemma card_basis (U : {vspace vT}) (X : {fset vT}) :
  basis_of U X -> #|` X | = (\dim U)%N.
Proof.
move => X_basis.
apply/anti_leq/andP; split; move: X_basis.
- by rewrite basisEdim => /andP [].
- by rewrite basisEfree => /and3P [].
Qed.

End EBasis.
