(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Import Order.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module GradedFinLattice.
Section ClassDef.

Record mixin_of d (T : finLatticeType d) := Mixin {
  rank : T -> nat;
  _ : forall x y : T, x < y -> (rank x < rank y)%N;
  _ : forall x y : T, ((rank x).+1 < rank y)%N -> exists z, x < z < y
}.

Record class_of (T : Type) := Class {
  base  : FinLattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (FinLattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> FinLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack disp0 (T0 : finLatticeType disp0) (m0 : mixin_of T0) :=
  fun bT b & phant_id (@FinLattice.class disp bT) b =>
  fun m    & phant_id m0 m => Pack disp (@Class T b disp0 m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition finPOrderType := @FinPOrder.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition bLatticeType := @BLattice.Pack disp cT xclass.
Definition tbLatticeType := @TBLattice.Pack disp cT xclass.
Definition finLatticeType := @FinLattice.Pack disp cT xclass.
Definition count_latticeType := @Lattice.Pack disp countType xclass.
Definition count_bLatticeType := @BLattice.Pack disp countType xclass.
Definition count_tbLatticeType := @TBLattice.Pack disp countType xclass.
Definition fin_latticeType := @Lattice.Pack disp finType xclass.
Definition fin_bLatticeType := @BLattice.Pack disp finType xclass.
Definition fin_tbLatticeType := @TBLattice.Pack disp finType xclass.
Definition finPOrder_latticeType := @Lattice.Pack disp finPOrderType xclass.
Definition finPOrder_bLatticeType := @BLattice.Pack disp finPOrderType xclass.
Definition finPOrder_tbLatticeType := @TBLattice.Pack disp finPOrderType xclass.
Definition finLattice_latticeType := @Lattice.Pack disp finLatticeType xclass.
Definition finLattice_bLatticeType := @BLattice.Pack disp finLatticeType xclass.
Definition finLattice_tbLatticeType := @TBLattice.Pack disp finLatticeType xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> FinLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical count_latticeType.
Canonical count_bLatticeType.
Canonical count_tbLatticeType.
Canonical fin_latticeType.
Canonical fin_bLatticeType.
Canonical fin_tbLatticeType.
Canonical finPOrder_latticeType.
Canonical finPOrder_bLatticeType.
Canonical finPOrder_tbLatticeType.
Canonical finLattice_latticeType.
Canonical finLattice_bLatticeType.
Canonical finLattice_tbLatticeType.

Notation gradedFinLatticeType  := type.
Notation gradedFinLatticeMixin := mixin_of.
Notation GradedFinLatticeMixin := Mixin.
Notation GradedFinLatticeType T m := (@pack T _ _ _ m _ _ id _ id).
Notation "[ 'gradedFinLatticeType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'gradedFinLatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'gradedFinLatticeType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'gradedFinLatticeType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'gradedFinLatticeType' 'of' T ]" := [gradedFinLatticeType of T for _]
  (at level 0, format "[ 'gradedFinLatticeType'  'of'  T ]") : form_scope.
Notation "[ 'gradedFinLatticeType' 'of' T 'with' disp ]" :=
  [gradedFinLatticeType of T for _ with disp]
  (at level 0, format "[ 'gradedFinLatticeType'  'of'  T  'with' disp ]") : form_scope.
End Exports.
End GradedFinLattice.
Export GradedFinLattice.Exports.

Section GradedDef.
Context {disp : unit}.
Local Notation gradedFinLatticeType := (gradedFinLatticeType disp).
Context {T : gradedFinLatticeType}.
Definition rank : T -> nat := GradedFinLattice.rank
  (GradedFinLattice.mixin (GradedFinLattice.class T)). (* FIXME *)
End GradedDef.
