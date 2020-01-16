(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Import Order.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* -------------------------------------------------------------------- *)
Module MeetBTFinMixin.
Section MeetBTFinMixin.
Context {T : finType}.

Record of_ := Build {
  le     : rel T;
  lt     : rel T;
  top    : T;
  bottom : T;
  meet   : T -> T -> T;
  le_def : forall x y : T, le x y = (meet x y == x);
  lt_def : forall x y : T, lt x y = (y != x) && le x y;
  meetC  : commutative meet;
  meetA  : associative meet;
  meetxx : idempotent meet;
  le0x   : forall x, le bottom x;
  lex1   : forall x, le x top;
}.

Local Lemma meet1x (m : of_) : left_id (top m) (meet m).
Proof. by move=> x; rewrite (rwP eqP) meetC -le_def lex1. Qed.

Local Lemma meetx1 (m : of_) : right_id (top m) (meet m).
Proof. by move=> x; rewrite meetC meet1x. Qed.

Variable (disp : unit) (m : of_).

Local Canonical meet_monoid := Monoid.Law (meetA m) (meet1x m) (meetx1 m).
Local Canonical meet_comoid := Monoid.ComLaw (meetC m).

Local Lemma le_refl : reflexive (le m).
Proof. by move=> x; rewrite le_def meetxx. Qed.

Local Lemma le_anti : antisymmetric (le m).
Proof. by move=> x y; rewrite !le_def meetC => /andP [] /eqP {2}<- /eqP ->. Qed.

Local Lemma le_trans : transitive (le m).
Proof.
move=> y x z; rewrite !le_def => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -meetA leyz lexy.
Qed.

Definition join (x y : T) : T :=
  \big[meet m/top m]_(z : T | le m x z && le m y z) z.

Lemma joinC : commutative join.
Proof. by move=> x y; apply: eq_bigl => z; rewrite andbC. Qed.

Lemma joinKI (y x : T) : meet m x (join x y) = x.
Proof.
rewrite (rwP eqP) -le_def /join; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !le_def meetA => /eqP -> /eqP ->.
+ by move=> z /andP[].
Qed.

Lemma meetKU (y x : T) : join x (meet m x y) = x.
Proof.
rewrite /join (bigD1 x) /=; last first.
+ by rewrite !le_def /= -meetA [meet _ y x]meetC meetA !meetxx !eqxx.
rewrite (rwP eqP) -le_def; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !le_def meetA => /eqP-> /eqP->.
+ by move=> z /andP[/andP[]].
Qed.

Lemma le_def_dual x y : le m x y = (join x y == y).
Proof.
rewrite le_def; apply/eqP/eqP=> <-.
+ by rewrite joinC meetC meetKU.
+ by rewrite joinKI.
Qed.

Lemma joinA : associative join.
Proof. Admitted.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin (lt_def m) le_refl le_anti le_trans.

Let T_porderType := POrderType disp T porderMixin.

Definition latticeMixin : latticeMixin T_porderType :=
  @LatticeMixin disp (POrderType disp T porderMixin)
    (meet m) join (meetC m) joinC
    (meetA m) joinA joinKI meetKU (le_def m).

Definition bLatticeMixin : bLatticeMixin T_porderType :=
  @BLatticeMixin disp (POrderType disp T porderMixin)
    (bottom m) (le0x m).

Definition tbLatticeMixin : tbLatticeMixin T_porderType :=
  @TBLatticeMixin disp (POrderType disp T porderMixin)
    (top m) (lex1 m).
End MeetBTFinMixin.

Module Exports.
Notation meetBTFinMixin := of_.
Notation MeetBTFinMixin := Build.
Coercion porderMixin : meetBTFinMixin >-> lePOrderMixin.
Coercion latticeMixin : meetBTFinMixin >-> Lattice.mixin_of.
Coercion bLatticeMixin : meetBTFinMixin >-> BLattice.mixin_of.
Coercion tbLatticeMixin : meetBTFinMixin >-> TBLattice.mixin_of.
End Exports.
End MeetBTFinMixin.

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
Module OMorphism.
Section ClassDef.

Context (dL dG : unit) (L : latticeType dL) (G : latticeType dG).

Definition axiom (f : L -> G) :=
     {morph f : x y / meet x y}
  /\ {morph f : x y / join x y}.

Structure map (phLG : phant (L -> G)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Context (phLG : phant (L -> G)) (f g : L -> G) (cF : map phLG).

Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phLG f fA.
End ClassDef.

Module Exports.
Notation omorphism f := (axiom f).
Coercion apply : map >-> Funclass.
Notation OMorphism fM := (Pack (Phant _) fM).
Notation "{ 'omorphism' fLG }" := (map (Phant fLG))
  (at level 0, format "{ 'omorphism'  fLG }") : order_scope.
Notation "[ 'omorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'omorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'omorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'omorphism'  'of'  f ]") : form_scope.
End Exports.
End OMorphism.

Include OMorphism.Exports.

(* -------------------------------------------------------------------- *)
Section OMorphismTheory.
Context (dL dG : unit) (L : latticeType dL) (G : latticeType dG).
Context (f : {omorphism L -> G}).

Lemma omorphI : {morph f : x y / meet x y}.
Proof. by case: (OMorphism.class f). Qed.

Lemma omorphU : {morph f : x y / join x y}.
Proof. by case: (OMorphism.class f). Qed.

Lemma omorph_homo : {homo f : x y / x <= y}.
Proof. by move=> x y; rewrite !leEmeet -omorphI => /eqP->. Qed.

Lemma omorph_mono : injective f -> {mono f : x y / x <= y}.
Proof.
move=> inj_f x y; apply/idP/idP => [|/omorph_homo //].
by rewrite !leEmeet -omorphI => /eqP /inj_f ->.
Qed.
End OMorphismTheory.

(* -------------------------------------------------------------------- *)
Module BOMorphism.
Section ClassDef.
Context (dL dG : unit) (L : bLatticeType dL) (G : bLatticeType dG).

Definition mixin_of (f : L -> G) := f 0 = 0.

Record class_of f : Prop := Class {base : omorphism f; mixin : mixin_of f}.
Local Coercion base : class_of >-> omorphism.

Structure map (phLG : phant (L -> G)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phLG : phant (L -> G)) (f g : L -> G) (cF : map phLG).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone f0 of phant_id g (apply cF) & phant_id f0 class :=
  @Pack phLG f f0.

Definition pack (f0 : mixin_of f) :=
  fun (bF : OMorphism.map phLG) fO & phant_id (OMorphism.class bF) fO =>
  Pack phLG (Class fO f0).

Canonical omorphism := OMorphism.Pack phLG class.
End ClassDef.

Module Exports.
Notation bottom_compat f := (mixin_of f).
Notation bomorphism f := (class_of f).
Coercion base : bomorphism >-> OMorphism.axiom.
Coercion mixin : bomorphism >-> bottom_compat.
Coercion apply : map >-> Funclass.
Notation BOMorphism fM := (Pack (Phant _) fM).
Notation AddBOMorphism fM := (pack fM id).
Notation "{ 'bomorphism' fLG }" := (map (Phant fLG))
  (at level 0, format "{ 'bomorphism'  fLG }") : order_scope.
Notation "[ 'bomorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'bomorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'bomorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'bomorphism'  'of'  f ]") : form_scope.
Coercion omorphism : map >-> OMorphism.map.
Canonical omorphism.
End Exports.
End BOMorphism.

Include BOMorphism.Exports.

(* -------------------------------------------------------------------- *)
Section BOMorphismTheory.
Context (dL dG : unit) (L : bLatticeType dL) (G : bLatticeType dG).
Context (f : {bomorphism L -> G}).

Lemma omorph0 : f 0 = 0.
Proof. by case: (BOMorphism.class f). Qed.
End BOMorphismTheory.

(* -------------------------------------------------------------------- *)
Module TBOMorphism.
Section ClassDef.
Context (dL dG : unit) (L : tbLatticeType dL) (G : tbLatticeType dG).

Definition mixin_of (f : L -> G) := f 1 = 1.

Record class_of f : Prop := Class {base : bomorphism f; mixin : mixin_of f}.
Local Coercion base : class_of >-> bomorphism.

Structure map (phLG : phant (L -> G)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phLG : phant (L -> G)) (f g : L -> G) (cF : map phLG).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone f1 of phant_id g (apply cF) & phant_id f1 class :=
  @Pack phLG f f1.

Definition pack (f1 : mixin_of f) :=
  fun (bF : BOMorphism.map phLG) fO & phant_id (BOMorphism.class bF) fO =>
  Pack phLG (Class fO f1).

Canonical omorphism := OMorphism.Pack phLG class.
Canonical bomorphism := BOMorphism.Pack phLG class.
End ClassDef.

Module Exports.
Notation top_compat f := (mixin_of f).
Notation tbomorphism f := (class_of f).
Coercion base : tbomorphism >-> BOMorphism.class_of.
Coercion mixin : tbomorphism >-> top_compat.
Coercion apply : map >-> Funclass.
Notation TBOMorphism fM := (Pack (Phant _) fM).
Notation AddTBOMorphism fM := (pack fM id).
Notation "{ 'tbomorphism' fLG }" := (map (Phant fLG))
  (at level 0, format "{ 'tbomorphism'  fLG }") : order_scope.
Notation "[ 'tbomorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'tbomorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'tbomorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'tbomorphism'  'of'  f ]") : form_scope.
Coercion omorphism : map >-> OMorphism.map.
Canonical omorphism.
Coercion bomorphism : map >-> BOMorphism.map.
Canonical bomorphism.
End Exports.
End TBOMorphism.

Include TBOMorphism.Exports.

(* -------------------------------------------------------------------- *)
Section TBOMorphismTheory.
Context (dL dG : unit) (L : tbLatticeType dL) (G : tbLatticeType dG).
Context (f : {tbomorphism L -> G}).

Lemma omorph1 : f 1 = 1.
Proof. by case: (TBOMorphism.class f). Qed.
End TBOMorphismTheory.

(* -------------------------------------------------------------------- *)
Reserved Notation "'[< a ; b >]"
  (at level 2, a, b at level 8, format "''[<' a ;  b '>]'").

Section LatticeClosed.
Context (d : unit) (L : latticeType d).

Definition lattice_closed (p : {pred L}) :=
  [/\ {in p &, forall x y, x `&` y \in p}
    & {in p &, forall x y, x `|` y \in p}].
End LatticeClosed.

(* -------------------------------------------------------------------- *)
Module LatticePred.
Structure lattice d (L : latticeType d) S :=
  Lattice { lattice_key : pred_key S; _ : @lattice_closed d L S }.

Section Extensionality.
Lemma lattice_ext d (G : latticeType d) S k (kS : @keyed_pred G S k) :
  lattice_closed kS -> lattice_closed S.
Proof.
case=> [hI hU]; split=> x y; rewrite -!(keyed_predE kS);
  by [apply hI | apply hU].
Qed.
End Extensionality.

Module Default.
Definition lattice d (L : latticeType d) S lctS :=
  @Lattice d L S (DefaultPredKey S) lctS.
End Default.

Module Exports.
Notation lattice_closed := lattice_closed.
Coercion lattice_key : lattice >-> pred_key.
Notation latticePred := lattice.
Definition LatticePred d (L : latticeType d) S k kS NkS :=
  Lattice k (@lattice_ext d L S k kS NkS).
End Exports.
End LatticePred.

Import LatticePred.Exports.

Module DefaultLatticePred.
Canonical LatticePred.Default.lattice.
End DefaultLatticePred.

Section LatticePredFacts.
Context (d : unit) (L : latticeType d) (S : {pred L}).
Context (ltcS : latticePred S) (kS : keyed_pred ltcS).

Lemma lpredIU : lattice_closed kS.
Proof.
split=> x y; rewrite !keyed_predE.
+ by case: ltcS => _ [h _]; apply: h.
+ by case: ltcS => _ [_ h]; apply: h.
Qed.

Lemma lpredI : {in kS &, forall x y, x `&` y \in kS}.
Proof. by case: lpredIU. Qed.

Lemma lpredU : {in kS &, forall x y, x `|` y \in kS}.
Proof. by case: lpredIU. Qed.
End LatticePredFacts.

(* -------------------------------------------------------------------- *)
Module SubLattices.
Section Def.
Context (d : unit) (V : latticeType d) (S : {pred V}).
Context (subS : latticePred S) (kS : keyed_pred subS).
Context (U : subType (mem kS)).

Let inU v Sv : U := Sub v Sv.

Let meetU (u1 u2 : U) := inU (lpredI (valP u1) (valP u2)).
Let joinU (u1 u2 : U) := inU (lpredU (valP u1) (valP u2)).

Fact meetC : commutative meetU.
Proof. by move=> x y; apply: val_inj; rewrite !SubK meetC. Qed.

Fact meetA : associative meetU.
Proof. by move=> x y z; apply: val_inj; rewrite !SubK meetA. Qed.

Fact joinC : commutative joinU.
Proof. by move=> x y; apply: val_inj; rewrite !SubK joinC. Qed.

Fact joinA : associative joinU.
Proof. by move=> x y z; apply: val_inj; rewrite !SubK joinA. Qed.

Fact joinKI (y x : U) : meetU x (joinU x y) = x.
Proof. by apply: val_inj; rewrite !SubK joinKI. Qed.

Fact meetKU (y x : U) : joinU x (meetU x y) = x.
Proof. by apply: val_inj; rewrite !SubK meetKU. Qed.

Fact le_def (x y : U) : (x <= y) = (meetU x y == x).
Proof. by rewrite -val_eqE !SubK -leEmeet leEsub. Qed.

Definition latticeMixin of phant U :=
  LatticeMixin meetC joinC meetA joinA joinKI meetKU le_def.
End Def.

Module Exports.
Notation "[ 'latticeMixin' 'of' U 'by' <: ]" := (latticeMixin (Phant U))
  (at level 0, format "[ 'latticeMixin'  'of'  U  'by'  <: ]") : form_scope.
End Exports.
End SubLattices.

Import SubLattices.Exports.

(* -------------------------------------------------------------------- *)
Section Interval.
Context (d : unit) (L : latticeType d).

Definition interval (a b : L) := fun x => a <= x <= b.

Notation "'[< a ; b >]" := (interval a b).

Lemma intervalP (a b x : L) :
  reflect (a <= x /\ x <= b) (x \in '[< a; b >]).
Proof. by apply: (iffP andP). Qed.

Lemma intervalE (a b x : L) :
  (x \in '[< a; b >]) = (a <= x <= b).
Proof. by []. Qed.

Lemma interval_is_lclosed a b : lattice_closed (interval a b).
Proof.
split=> x y /intervalP[le_ax le_xb] /intervalP[le_ay le_yb].
+ by rewrite intervalE !lexI !(le_ax, le_ay) /= leIxl.
+ by rewrite intervalE !leUx (le_xb, le_yb) lexUl.
Qed.

Fact interval_key a b : pred_key (interval a b). Proof. by []. Qed.
Canonical interval_keyed a b := KeyedPred (interval_key a b).

Canonical interval_lclosed a b :=
  LatticePred (interval_is_lclosed a b).
End Interval.

(* -------------------------------------------------------------------- *)
Section IntervalLattice.
Context (d : unit) (L : latticeType d) (a b : L).

Inductive interval_of : predArgType :=
  Interval x & x \in interval a b.

Definition interval_val r := let: Interval x _ := r in x.

Canonical interval_subType := Eval hnf in [subType for interval_val].
Definition interval_eqMixin := Eval hnf in [eqMixin of interval_of by <:].
Canonical interval_eqType := Eval hnf in EqType interval_of interval_eqMixin.
Definition interval_choiceMixin := [choiceMixin of interval_of by <:].
Canonical interval_choiceType := ChoiceType interval_of interval_choiceMixin.
Definition interval_porderMixin := [porderMixin of interval_of by <:].
Canonical interval_porderType := POrderType d interval_of interval_porderMixin.
Definition interval_latticeMixin := [latticeMixin of interval_of by <:].
Canonical interval_latticeType := LatticeType interval_of interval_latticeMixin.

Lemma interval_val_is_omorphism : omorphism interval_val.
Proof. by []. Qed.
Canonical internval_omorphism := OMorphism interval_val_is_omorphism.
End IntervalLattice.

Notation "'[< a ; b >]" := (interval_of a b).
