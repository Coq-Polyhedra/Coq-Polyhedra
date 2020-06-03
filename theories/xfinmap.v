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
Canonical fset_meetSemilatticeType := MeetSemilatticeType {fset T} fset_meetJoinMixin.
Canonical fset_latticeType := LatticeType {fset T} fset_meetJoinMixin.
Canonical fset_bSemilatticeType := BSemilatticeType {fset T} (BottomMixin (@fsub0set T)).
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

Program Canonical fset_tbLatticeType :=
  TBLatticeType {fset T} (@TopMixin _ _ fsetT _).

Next Obligation. Proof. by apply/fsubsetP=> v _; rewrite inE. Qed.

Canonical fset_tbDistrLatticeType := [tbDistrLatticeType of {fset T}].

Program Canonical ctbDistrLatticeType := CTBDistrLatticeType {fset T}
  (@CTBDistrLatticeMixin _ _ fsetD fsetC _).

Canonical finPOrderType        := [finPOrderType of {fset T}].
Canonical finLatticeType       := [finLatticeType of {fset T}].
Canonical finDistrLatticeType  := [finDistrLatticeType of {fset T}].
Canonical finCDistrLatticeType := [finCDistrLatticeType of {fset T}].
End FinLattice.
