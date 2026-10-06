(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import boot order finmap.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope order_scope.
Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Fact fset_display : Order.disp_t. Proof. exact: Order.Disp tt tt. Qed.

(* -------------------------------------------------------------------- *)
Section BDistrLatticeType.
Context {T : choiceType}.

Fact fset_lt_def (A B : {fset T}) : fproper A B = (B != A) && fsubset A B.
Proof. by rewrite fproperEneq eq_sym. Qed.

HB.instance Definition _ :=
  Order.isMeetJoinDistrLattice.Build fset_display {fset T}
    (fun _ _ => erefl _) fset_lt_def
    (@fsetIC T) (@fsetUC T) (@fsetIA T) (@fsetUA T)
    (fun x y => fsetKU y x) (fun x y => fsetKI y x) (@fsetIUl T) (@fsetIid T).

HB.instance Definition _ :=
  Order.hasBottom.Build fset_display {fset T} (@fsub0set T).

Fact fset_diffKI (A B : {fset T}) : B `&` (A `\` B) = \bot.
Proof.
rewrite (rwP eqP) -lex0; apply/fsubsetP.
by move=> v; rewrite !inE => /and3P[->].
Qed.

HB.instance Definition _ :=
  Order.BDistrLattice_hasSectionalComplement.Build fset_display {fset T}
    fset_diffKI (fun x y => fsetID y x).
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

Fact fset_lex1 (A : {fset T}) : A `<=` fsetT.
Proof. by apply/fsubsetP=> v _; rewrite inE. Qed.

HB.instance Definition _ :=
  Order.hasTop.Build fset_display {fset T} fset_lex1.

HB.instance Definition _ :=
  Order.CBDistrLattice_hasComplement.Build fset_display {fset T}
    (fun A => erefl (fsetC A)).
End FinLattice.
