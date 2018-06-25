(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ExtEquality.

Section ExtEquality.
Variable U : Type.

Definition axiom (T : predType U) (e : rel T) := forall x y, reflect (x =i y) (e x y).

Structure mixin_of (T : predType U) := Mixin {op : rel T; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> predType.
Variables (T : predType U) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

End ExtEquality.

Module Exports.
Coercion sort : type >-> predType.
Notation extEqType := type.
Notation ExtEqMixin := Mixin.
Notation ExtEqType T m := (@pack T m).
Notation "[ 'extEqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'extEqMixin'  'of'  T ]") : form_scope.
Notation "[ 'extEqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'extEqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'extEqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'extEqType'  'of'  T ]") : form_scope.
End Exports.

End ExtEquality.
Export ExtEquality.Exports.

Section BasicProp.
Variable U : Type.
Implicit Type T : extEqType U.

Definition ext_eq_op T := ExtEquality.op (ExtEquality.class T).

Lemma ext_eqE T x : ext_eq_op x = ExtEquality.op (ExtEquality.class T) x.
Proof. by []. Qed.

Lemma ext_eqP T : ExtEquality.axiom (@ext_eq_op T).
Proof. by case: T => ? []. Qed.
Arguments ext_eqP [T x y].

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation "x ==i y" := (ext_eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x ==i y :> T" := ((x : T) ==i (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x !=i y" := (~~ (x ==i y))
  (at level 70, no associativity) : bool_scope.
Notation "x !=i y :> T" := (~~ (x ==i y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =iP y" := (ext_eqP : reflect (x =i y) (x ==i y))
  (at level 70, no associativity) : eq_scope.
Notation "x =iP y :> T" := (ext_eqP : reflect (x = y :> T) (x ==i y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Prenex Implicits ext_eq_op ext_eqP.

Lemma ext_eq_refl (T : extEqType U) (x : T) : x ==i x. Proof. exact/ext_eqP. Qed.
Notation ext_eqxx := ext_eq_refl.

Lemma ext_eq_sym (T : extEqType U) (x y : T) : (x ==i y) = (y ==i x).
Proof. by apply/ext_eqP/ext_eqP => ?. Qed.

Lemma ext_eq_trans (T : extEqType U) : transitive (@ext_eq_op T).
Proof.
move => x y z.
move => /ext_eqP yx /ext_eqP xz.
by apply/ext_eqP => ?; rewrite yx.
Qed.

End BasicProp.

Arguments ext_eqP [U T x y].
Arguments ext_eq_refl [U].
Arguments ext_eq_sym [U].
Arguments ext_eq_trans [U].

Section EquivRel.

Variable U : Type.
Variable T : extEqType U.

Canonical ext_eq_equiv_rel : equiv_rel T :=
  EquivRel _ (ext_eq_refl T) (ext_eq_sym T) (ext_eq_trans T).

End EquivRel.

Arguments ext_eq_equiv_rel [U].

Notation "x ==i y" := (ext_eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x ==i y :> T" := ((x : T) ==i (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x !=i y" := (~~ (x ==i y))
  (at level 70, no associativity) : bool_scope.
Notation "x !=i y :> T" := (~~ (x ==i y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =iP y" := (ext_eqP : reflect (x =i y) (x ==i y))
  (at level 70, no associativity) : eq_scope.
Notation "x =iP y :> T" := (ext_eqP : reflect (x = y :> T) (x ==i y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.
