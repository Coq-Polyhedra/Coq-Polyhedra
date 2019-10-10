From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.

(* -------------------------------------------------------------------- *)
Module Test1.
Parameter (T   : eqType).
Parameter (F   : T -> eqType).
Parameter (U   : eqType).
Parameter (val : forall t, F t -> U).

Definition eqv {t1 t2} (f1 : F t1) (f2 : F t2) :=
  val f1 == val f2.

Lemma eqv_refl {t} (f : F t) : eqv f f.
Proof. by apply: eqxx. Qed.

Lemma eqv_sym {t1 t2} (f1 : F t1) (f2 : F t2) :
  eqv f2 f1 -> eqv f1 f2.
Proof. by rewrite /eqv; move/eqP=> ->. Qed.

Lemma eqv_trans {t1 t2 t3} (f2 : F t2) (f1 : F t1) (f3 : F t3) :
  eqv f1 f2 -> eqv f2 f3 -> eqv f1 f3.
Proof. by rewrite /eqv => /eqP-> /eqP->. Qed.

Variant reprType (u : U) : Type :=
  Repr (t : T) (f : F t) of (val f = u).

Parameter val_surj : forall u : U, reprType u.

Definition base0 (u : U) (r : reprType u) :=
  let: Repr t _ _ := r in t.

Definition base (u : U) :=
  let: Repr t _ _ := val_surj u in t.

Definition repr (u : U) : F (base u) :=
  let: Repr _ f _ as r := val_surj u return F (base0 r) in f.

Parameter (E : eqType).

Parameter (h : forall t, F t -> E).

Axiom h_ok : forall {t1 t2} (f1 : F t1) (f2 : F t2),
  eqv f1 f2 -> h f1 = h f2.

Lemma reprK u : val (repr u) = u.
Proof. by rewrite /repr /base; case: (val_surj u). Qed.

Lemma valK {t} (f : F t) : eqv (repr (val f)) f.
Proof. by rewrite /eqv reprK. Qed.

Definition lift (u : U) : E := h (repr u).

Lemma h_quot {t} (f : F t) :
  h (repr (val f)) = h f.
Proof. by apply/h_ok/valK. Qed.

Lemma g_ok {t1 t2} (f1 : F t1) (f2 : F t2) :
  eqv f1 f2 -> lift (val f1) = lift (val f2).
Proof. by move=> eqv_f; rewrite /lift !h_quot; apply: h_ok. Qed.
End Test1.

(* -------------------------------------------------------------------- *)
Module Test2.
Parameter (T     : Type).
Parameter (F     : T -> Type).
Parameter (U     : Type).
Parameter (piV   : { t & F t } -> U).
Parameter (reprV : U -> { t & F t }).

Axiom (reprVK : cancel reprV piV).

Definition mixin := QuotClass reprVK.
Canonical  type  := QuotType U mixin.

Parameter (u : U) (f : { t & F t }).

Parameter (E : eqType).

Parameter (h : { t & F t } -> E).

Definition lift : U -> E := lift_fun1 type h.

Lemma h_ok : {mono \pi_type : x / h x >-> lift x}.
Proof. Admitted.
End Test2.
