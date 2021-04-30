(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect finmap.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope order_scope.
Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Fact fset_display : unit. Proof. exact: tt. Qed.

(* -------------------------------------------------------------------- *)
Section BDistrLatticeType.
Context {T : choiceType}.

Program Definition fset_meetJoinMixin :=
  @DistrMeetJoinMixin [choiceType of {fset T}]
    fsubset fproper fsetI fsetU (fun _ _ => erefl _) _
     (@fsetIC T) (@fsetUC T) (@fsetIA T) (@fsetUA T)
     (fun x y => fsetKU y x) (fun x y => fsetKI y x) (@fsetIUl T) (@fsetIid T).

Next Obligation. Proof. by rewrite fproperEneq eq_sym. Qed.

Canonical fset_porderType := POrderType fset_display {fset T} fset_meetJoinMixin.
Canonical fset_bPOrderType := BPOrderType {fset T} (BottomMixin (@fsub0set T)).
Canonical fset_meetSemilatticeType := MeetSemilatticeType {fset T} fset_meetJoinMixin.
Canonical fset_bMeetSemilatticeType := [bMeetSemilatticeType of {fset T}].
Canonical fset_joinSemilatticeType := JoinSemilatticeType {fset T} fset_meetJoinMixin.
Canonical fset_bJoinSemilatticeType := [bJoinSemilatticeType of {fset T}].
Canonical fset_latticeType := [latticeType of {fset T}].
Canonical fset_bLatticeType := [bLatticeType of {fset T}].
Canonical fset_distrLatticeType := DistrLatticeType {fset T} fset_meetJoinMixin.
Canonical fset_bDistrLatticeType := [bDistrLatticeType of {fset T}].

Program Canonical fset_cbDistrLatticeType := CBDistrLatticeType {fset T}
  (@CBDistrLatticeMixin _ _ fsetD _ (fun x y => fsetID y x)).

Next Obligation. Proof.
rewrite (rwP eqP) -lex0; apply/fsubsetP.
by move=> v; rewrite !inE => /and3P[->].
Qed.
End BDistrLatticeType.

(* -------------------------------------------------------------------- *)
Section FinLattice.
Context {T : finType}.

Definition fsetT := [fset x in T].

Definition fsetC (A : {fset T}) := fsetT `\` A.

Lemma fsetTE x : x \in fsetT.
Proof. by rewrite !inE. Qed.

Lemma fsetCE (A : {fset T}) x : (x \in fsetC A) = (x \notin A).
Proof. by rewrite !(inE, fsetTE) andbT. Qed.

Definition inE := (inE, fsetTE, fsetCE).

Program Canonical fset_tPOrderType :=
  TPOrderType {fset T} (@TopMixin _ _ fsetT _).

Next Obligation. Proof. by apply/fsubsetP=> v _; rewrite inE. Qed.

Canonical fset_tbPOrderType := [tbPOrderType of {fset T}].

Canonical finPOrderType := [finPOrderType of {fset T}].
Canonical finBPOrderType := [finBPOrderType of {fset T}].
Canonical finTPOrderType := [finTPOrderType of {fset T}].
Canonical finTBPOrderType := [finTBPOrderType of {fset T}].

Canonical tLatticeType := [tLatticeType of {fset T}].
Canonical tbLatticeType := [tbLatticeType of {fset T}].
Canonical finLatticeType := [finLatticeType of {fset T}].
Canonical finTBLatticeType := [finTBLatticeType of {fset T}].

Canonical tDistrLatticeType := [tDistrLatticeType of {fset T}].
Canonical tbDistrLatticeType := [tbDistrLatticeType of {fset T}].
Canonical finDistrLatticeType := [finDistrLatticeType of {fset T}].
Canonical finTBDistrLatticeType := [finTBDistrLatticeType of {fset T}].

Program Canonical ctbDistrLatticeType := CTBDistrLatticeType {fset T}
  (@CTBDistrLatticeMixin _ _ fsetD fsetC _).

Canonical finCTBDistrLatticeType := [finCTBDistrLatticeType of {fset T}].
End FinLattice.
