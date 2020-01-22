(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
Require Import extra_misc.

Import Order.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* -------------------------------------------------------------------- *)
Section Misc.
Context (d : unit) (T : latticeType d).

Lemma leIU (x y : T) : meet x y <= join x y.
Proof. exact: (le_trans (leIl _ _) (leUl _ _)). Qed.
End Misc.

(* -------------------------------------------------------------------- *)
Module MeetBTFinMixin.
Section MeetBTFinMixin.
Context (d : unit) (T : finPOrderType d).

Record of_ := Build {
  top    : T;
  bottom : T;
  meet   : T -> T -> T;
  le_def : forall x y : T, x <= y = (meet x y == x);
  meetC  : commutative meet;
  meetA  : associative meet;
  meetxx : idempotent meet;
  le0x   : forall x, bottom <= x;
  lex1   : forall x, x <= top;
}.

Local Lemma meet1x (m : of_) : left_id (top m) (meet m).
Proof. by move=> x; rewrite (rwP eqP) meetC -le_def lex1. Qed.

Local Lemma meetx1 (m : of_) : right_id (top m) (meet m).
Proof. by move=> x; rewrite meetC meet1x. Qed.

Variable (m : of_).

Local Canonical meet_monoid := Monoid.Law (meetA m) (meet1x m) (meetx1 m).
Local Canonical meet_comoid := Monoid.ComLaw (meetC m).

Definition join (x y : T) : T :=
  \big[meet m/top m]_(z : T | (x <= z) && (y <= z)) z.

Lemma joinC : commutative join.
Proof. by move=> x y; apply: eq_bigl => z; rewrite andbC. Qed.

Lemma joinKI (y x : T) : meet m x (join x y) = x.
Proof.
rewrite (rwP eqP) -le_def /join; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !(le_def m) meetA => /eqP-> /eqP->.
+ by move=> z /andP[].
Qed.

Lemma meetKU (y x : T) : join x (meet m x y) = x.
Proof.
rewrite /join (bigD1 x) /=; last first.
+ by rewrite !(le_def m) /= -meetA [meet _ y x]meetC meetA !meetxx !eqxx.
rewrite (rwP eqP) -le_def; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !(le_def m) meetA => /eqP-> /eqP->.
+ by move=> z /andP[/andP[]].
Qed.

Lemma le_def_dual x y : x <= y = (join x y == y).
Proof.
rewrite (le_def m); apply/eqP/eqP=> <-.
+ by rewrite joinC meetC meetKU.
+ by rewrite joinKI.
Qed.

Lemma joinA : associative join.
Proof. Admitted.

Definition latticeMixin : latticeMixin T :=
  @LatticeMixin d T
    (meet m) join (meetC m) joinC
    (meetA m) joinA joinKI meetKU (le_def m).

Definition bLatticeMixin : bLatticeMixin T :=
  @BLatticeMixin d T (bottom m) (le0x m).

Definition tbLatticeMixin : tbLatticeMixin T :=
  @TBLatticeMixin d T (top m) (lex1 m).
End MeetBTFinMixin.

Module Exports.
Notation meetBTFinMixin := of_.
Notation MeetBTFinMixin := Build.
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
  _ : rank bottom = 0%N;
  _ : forall x y : T, x < y -> (rank x < rank y)%N;
  _ : forall x y : T, ((rank x).+1 < rank y)%N -> exists z, x < z < y
}.

Record class_of (T : Type) := Class {
  base  : FinLattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (FinLattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> FinLattice.class_of.
Local Coercion base2 T (c : class_of T) : Finite.class_of T :=
  @Finite.Class T c c.
Local Coercion base3 T (c : class_of T) : FinPOrder.class_of T :=
  @FinPOrder.Class T c c.

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
Coercion base2 : class_of >-> Finite.class_of.
Coercion base3 : class_of >-> FinPOrder.class_of.
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
Canonical finLatticeType.
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
Section GradedTheory.
Context (d : unit) (L : gradedFinLatticeType d).

Lemma rank0 : rank (0 : L) = 0%N.
Proof. by case: L => [? [? ? []]]. Qed.

Lemma homo_rank : {homo (@rank d L) : x y / x < y >-> (x < y)%N}.
Proof. by case: L => [? [? ? []]]. Qed.

Lemma le_homo_rank : {homo (@rank d L) : x y / x <= y >-> (x <= y)%N}.
Proof. by apply: (ltW_homo homo_rank). Qed.

Lemma graded_rank (x y : L) : ((rank x).+1 < rank y)%N -> exists z, x < z < y.
Proof. by case: L x y => [? [? ? []]]. Qed.

Lemma rank_eq0 (x : L) : (rank x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [zrk|->]; last by rewrite rank0.
apply/contra_eq: zrk; rewrite -!(lt0x, lt0n).
by move/homo_rank; rewrite rank0.
Qed.

Lemma rank_gt0 (x : L) : (0 < rank x)%N = (0 < x).
Proof.
apply/idP/idP => [gt0_rank|/homo_rank]; last by rewrite rank0.
by rewrite lt_neqAle le0x eq_sym -rank_eq0 andbT -lt0n.
Qed.

Lemma rankI (x y : L) : (rank (x `&` y) <= minn (rank x) (rank y))%N.
Proof. by rewrite leq_min !le_homo_rank // (leIl, leIr). Qed.
End GradedTheory.

(* -------------------------------------------------------------------- *)
Section RankInd.
Context (d : unit) (L : gradedFinLatticeType d) (P : L -> Prop).

Hypothesis PH :
  forall x, (forall y, (rank y < rank x)%N -> P y) -> P x.

Lemma rank_ind x : P x.
Proof.
move: {2}(rank x) (leqnn (rank x)) => n; elim: n x => [|n ih] x.
+ by rewrite leqn0 rank_eq0 => /eqP->; apply: PH => y; rewrite rank0.
rewrite leq_eqVlt=> /orP[]; last by rewrite ltnS => /ih.
by move/eqP => rkx; apply: PH => y; rewrite rkx ltnS => /ih.
Qed.
End RankInd.

(* -------------------------------------------------------------------- *)
Section GradedRankS.
Context (d : unit) (L : gradedFinLatticeType d).

Lemma graded_rankS (x : L) :
  (0 < rank x)%N -> exists2 y : L, y < x & (rank y).+1 = rank x.
Proof. Admitted.
End GradedRankS.

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
Section OMorphismP.
Context (dL dG : unit) (L : latticeType dL) (G : latticeType dG).

Lemma omorphismP (f : L -> G) :
     {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> omorphism f.
Proof. by move=> *; do! split. Qed.
End OMorphismP.

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
Section OMorphismRank.
Context (dL dG : unit) (L : gradedFinLatticeType dL) (G : gradedFinLatticeType dG).

Lemma can_omorphism (f : L -> G) (g : G -> L) :
  cancel f g -> cancel g f -> omorphism f -> omorphism g.
Proof.
move=> fK gK [hD hM]; split.
+ by move=> x y; apply: (can_inj fK); rewrite gK hD !gK.
+ by move=> x y; apply: (can_inj fK); rewrite gK hM !gK.
Qed.

Lemma rank_morph (f : L -> G) x :
  omorphism f -> injective f -> (rank x <= rank (f x))%N.
Proof.
move=> morph_f inj_f; elim/rank_ind: x => x ih.
case: (x =P 0) => [->|]; first by rewrite rank0.
move/eqP; rewrite -rank_eq0 -lt0n => /graded_rankS.
case=> y lt_yx <-; apply: (leq_ltn_trans (ih _ _)).
+ by apply: homo_rank.
+ pose cf := OMorphism morph_f.
  by apply/homo_rank/(inj_homo_lt inj_f (omorph_homo cf)).
Qed.
End OMorphismRank.

(* -------------------------------------------------------------------- *)
Section OMorphismBijRank.
Context (dL dG : unit) (L : gradedFinLatticeType dL) (G : gradedFinLatticeType dG).

Lemma rank_morph_bij (f : L -> G) x :
  omorphism f -> bijective f -> rank (f x) = rank x.
Proof.
move=> morph_f bij_f; rewrite (rwP eqP) eqn_leq.
rewrite rank_morph // ?andbT; last by apply/bij_inj.
case: bij_f => g fK gK; pose morph_g := can_omorphism fK gK morph_f.
by apply: (leq_trans (rank_morph (f x) morph_g (can_inj gK))); rewrite fK.
Qed.
End OMorphismBijRank.

(* -------------------------------------------------------------------- *)
Section OMorphismComp.
Context (dL dG dH : unit).
Context (L : latticeType dL).
Context (G : latticeType dG).
Context (H : latticeType dH).
Context (fLG : {omorphism L -> G}) (fGH : {omorphism G -> H}).

Lemma comp_is_omorphism : omorphism (fGH \o fLG).
Proof. by apply/omorphismP=> x y /=; rewrite !(omorphI, omorphU). Qed.

Canonical comp_omorphism := OMorphism comp_is_omorphism.
End OMorphismComp.

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
Section BOMorphismP.
Context (dL dG : unit) (L : bLatticeType dL) (G : bLatticeType dG).

Lemma bomorphismP (f : L -> G) :
     f 0 = 0
  -> {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> bomorphism f.
Proof. by move=> *; do! split. Qed.
End BOMorphismP.

(* -------------------------------------------------------------------- *)
Section BOMorphismTheory.
Context (dL dG : unit) (L : bLatticeType dL) (G : bLatticeType dG).
Context (f : {bomorphism L -> G}).

Lemma omorph0 : f 0 = 0.
Proof. by case: (BOMorphism.class f). Qed.
End BOMorphismTheory.

(* -------------------------------------------------------------------- *)
Section BOMorphismComp.
Context (dL dG dH : unit).
Context (L : bLatticeType dL).
Context (G : bLatticeType dG).
Context (H : bLatticeType dH).
Context (fLG : {bomorphism L -> G}) (fGH : {bomorphism G -> H}).

Lemma comp_is_bomorphism : bomorphism (fGH \o fLG).
Proof.
apply: bomorphismP => /=; first by rewrite !omorph0.
+ by apply: omorphI. + by apply: omorphU.
Qed.

Canonical comp_bomorphism := BOMorphism comp_is_bomorphism.
End BOMorphismComp.

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
Section TBOMorphismP.
Context (dL dG : unit) (L : tbLatticeType dL) (G : tbLatticeType dG).

Lemma tbomorphismP (f : L -> G) :
     f 0 = 0
  -> f 1 = 1
  -> {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> tbomorphism f.
Proof. by move=> *; do! split. Qed.
End TBOMorphismP.

(* -------------------------------------------------------------------- *)
Section TBOMorphismTheory.
Context (dL dG : unit) (L : tbLatticeType dL) (G : tbLatticeType dG).
Context (f : {tbomorphism L -> G}).

Lemma omorph1 : f 1 = 1.
Proof. by case: (TBOMorphism.class f). Qed.
End TBOMorphismTheory.

(* -------------------------------------------------------------------- *)
Section TBOMorphismComp.
Context (dL dG dH : unit).
Context (L : tbLatticeType dL).
Context (G : tbLatticeType dG).
Context (H : tbLatticeType dH).
Context (fLG : {tbomorphism L -> G}) (fGH : {tbomorphism G -> H}).

Lemma comp_is_tbomorphism : tbomorphism (fGH \o fLG).
Proof.
apply: tbomorphismP => /=; rewrite ?(omorph0, omorph1) //.
+ by apply: omorphI. + by apply: omorphU.
Qed.

Canonical comp_tbomorphism := TBOMorphism comp_is_tbomorphism.
End TBOMorphismComp.

(* -------------------------------------------------------------------- *)
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
Reserved Notation "'[< a ; b >]"
  (at level 2, a, b at level 8, format "''[<' a ;  b '>]'").

Section Interval.
Context (d : unit) (L : latticeType d).

Definition interval (a b : L) := fun x => a <= x <= b.

Notation "'[< a ; b >]" := (interval a b).

Lemma intervalP (a b x : L) :
  reflect (a <= x /\ x <= b) (x \in '[< a; b >]).
Proof. by apply: (iffP andP). Qed.

Lemma intervalPL (a b x : L) :
  x \in '[< a; b >] -> a <= x.
Proof. by case/intervalP. Qed.

Lemma intervalPR (a b x : L) :
  x \in '[< a; b >] -> x <= b.
Proof. by case/intervalP. Qed.

Lemma intervalE (a b x : L) :
  (x \in '[< a; b >]) = (a <= x <= b).
Proof. by []. Qed.

Lemma intervalL (a b : L) : a <= b -> a \in '[< a; b >].
Proof. by rewrite intervalE lexx. Qed.

Lemma intervalR (a b : L) : a <= b -> b \in '[< a; b >].
Proof. by rewrite intervalE lexx andbT. Qed.

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
Context (d : unit) (L : latticeType d) (a b : L) (a_le_b : expose (a <= b)).

Inductive interval_of : predArgType :=
  Interval x & x \in interval a b.

Definition interval_val r := let: Interval x _ := r in x.

Canonical interval_subType := Eval hnf in [subType for interval_val].
Definition interval_eqMixin := Eval hnf in [eqMixin of interval_of by <:].
Canonical interval_eqType := Eval hnf in EqType interval_of interval_eqMixin.
Definition interval_choiceMixin := [choiceMixin of interval_of by <:].
Canonical interval_choiceType := Eval hnf in ChoiceType interval_of interval_choiceMixin.
Definition interval_porderMixin := [porderMixin of interval_of by <:].
Canonical interval_porderType := Eval hnf in POrderType d interval_of interval_porderMixin.
Definition interval_latticeMixin := [latticeMixin of interval_of by <:].
Canonical interval_latticeType := Eval hnf in LatticeType interval_of interval_latticeMixin.

Lemma interval_val_is_omorphism : omorphism interval_val.
Proof. by []. Qed.

Canonical interval_omorphism := OMorphism interval_val_is_omorphism.
End IntervalLattice.

Notation "'[< a ; b >]" := (interval_of a b).

Global Instance expose_le0x (disp : unit) (L : tbLatticeType disp) (x : L) :
  expose (0 <= x)%O := Expose (le0x x).
Global Instance expose_lex1 (disp : unit) (L : tbLatticeType disp) (x : L) :
  expose (x <= 1)%O := Expose (lex1 x).

(* -------------------------------------------------------------------- *)
Section IntervalTBLattice.
Context (d : unit) (L : latticeType d) (a b : L) (a_le_b : expose (a <= b)).

Let bottom := Interval (intervalL a_le_b).
Let top    := Interval (intervalR a_le_b).

Fact le0R (x : '[< a; b >]) : bottom <= x.
Proof. by rewrite leEsub /=; case/intervalP: (valP x).
Qed.

Fact leR1 (x : '[< a; b >]) : x <= top.
Proof. by rewrite leEsub /=; case/intervalP: (valP x).
Qed.

Definition interval_bLatticeMixin  := BLatticeMixin  le0R.
Definition interval_tbLatticeMixin := TBLatticeMixin leR1.

Canonical interval_blatticeType :=
  Eval hnf in BLatticeType '[< a; b >] interval_bLatticeMixin.

Canonical interval_tblatticeType :=
  Eval hnf in TBLatticeType '[< a; b >] interval_tbLatticeMixin.
End IntervalTBLattice.

(* -------------------------------------------------------------------- *)
Section IntervalFinLattice.
Context (d : unit) (L : finLatticeType d) (a b : L) (a_le_b : expose (a <= b)).

Definition interval_countMixin := [countMixin of '[< a; b >] by <:].
Canonical interval_countType := Eval hnf in CountType '[< a; b >] interval_countMixin.
Canonical interval_subCountType := [subCountType of '[< a; b >]].

Definition interval_finMixin := [finMixin of '[< a; b >] by <:].
Canonical interval_finType := Eval hnf in FinType '[< a; b >] interval_finMixin.
Canonical interval_subFinType := [subFinType of '[< a; b >]].

Canonical interval_finPOrderType := Eval hnf in [finPOrderType of '[< a; b >]].
Canonical interval_finLatticeType := Eval hnf in [finLatticeType of '[< a; b >]].
End IntervalFinLattice.

(* -------------------------------------------------------------------- *)
Section IntervalGradedLattice.
Context (d : unit) (L : gradedFinLatticeType d) (a b : L) (a_le_b : expose (a <= b)).

Definition vrank (x : '[< a; b >]) := rank (val x) - rank a.

Lemma intv_rankL (x : '[< a; b >]) : (rank a <= rank (val x))%N.
Proof. by apply/(ltW_homo (@homo_rank _ _)); case/intervalP: (valP x). Qed.

Lemma intv_rankR (x : '[< a; b >]) : (rank (val x) <= rank b)%N.
Proof. by apply/(ltW_homo (@homo_rank _ _)); case/intervalP: (valP x). Qed.

Lemma vrank0 : vrank 0 = 0.
Proof. by rewrite /vrank subnn. Qed.

Lemma homo_intv_rank (x y : '[< a; b >]) : x < y -> (vrank x < vrank y)%N.
Proof.
rewrite ltEsub /vrank => /homo_rank h; rewrite ltn_sub2r //.
by rewrite (leq_trans _ h) // ltnS intv_rankL.
Qed.

Lemma graded_intv_rank (x y : '[< a; b >]) :
  ((vrank x).+1 < vrank y)%N -> exists z : '[< a; b >], x < z < y.
Proof.
rewrite /vrank -subSn ?intv_rankL // ltn_subLR; last first.
+ by rewrite (leq_trans (intv_rankL x)).
rewrite subnKC ?intv_rankL // => /graded_rank[z rg_z].
exists (insubd (0 : '[< a; b >]) z).
rewrite !ltEsub /insubd insubT //= intervalE.
rewrite (le_trans (intervalPL (valP x))) //=; last by apply: ltW; case/andP: rg_z.
by rewrite (le_trans _ (intervalPR (valP y))) //= ltW //; case/andP: rg_z.
Qed.

Definition interval_gradedFinLatticeMixin :=
  GradedFinLatticeMixin vrank0 homo_intv_rank graded_intv_rank.
Canonical interval_gradedFinLatticeType :=
  Eval hnf in GradedFinLatticeType '[< a; b >] interval_gradedFinLatticeMixin.
End IntervalGradedLattice.

(* -------------------------------------------------------------------- *)
Section IntVInj.
Context (d : unit) (L : latticeType d) (a b : L) (le_a_b : a <= b).

Definition in_intv x := (insubd (0 : '[< a; b >])) x.
End IntVInj.

Notation "x %:I_[< a ; b >]" := (@in_intv _ _ a b _ x)
  (at level 2, left associativity, format "x %:I_[<  a ;  b  >]").

Section InIntVRank.
Context (d : unit) (L : gradedFinLatticeType d) (a b : L) (le_a_b : a <= b).

Lemma in_intv_valE x : (a <= x <= b)%O -> val (in_intv le_a_b x) = x.
Proof. by move=> h; rewrite /in_intv /insubd insubT. Qed.

Lemma interval_valK (x : '[< a; b >]) : (in_intv le_a_b (val x)) = x.
Proof. by rewrite /in_intv valKd. Qed.

Lemma in_intv_rankE x : (a <= x <= b)%O ->
  rank (in_intv le_a_b x) = (rank x - rank a)%N.
Proof. by move=> inintv; rewrite {1}/rank /= /vrank /= in_intv_valE. Qed.
End InIntVRank.

(* -------------------------------------------------------------------- *)
Section Atomic.
Context (d : unit) (L : finLatticeType d).

Definition atom (a : L) :=
  (0 < a) && ~~ [exists x : L, 0 < x < a].

Definition coatom (a : L) :=
  (a < 1) && ~~ [exists x : L, a < x < 1].

Definition atomistic (a : L) :=
  [exists S : {set L},
     [forall x in S, atom x] && (a == \join_(x in S) x)].

Definition coatomistic (a : L) :=
  [exists S : {set L},
     [forall x in S, atom x] && (a == \meet_(x in S) x)].
End Atomic.

(* -------------------------------------------------------------------- *)
Section AtomicTheory.
Context (d : unit) (L : finLatticeType d).

Lemma atomP (a : L) : 0 < a ->
  reflect (forall x, x != 0 -> ~ (x < a)) (atom a).
Proof.
move=> gt0_a; apply: (iffP andP).
+ case=> _ /existsPn h x nz_x; move/(_ x): h.
  by rewrite negb_and lt_neqAle eq_sym nz_x le0x /= (rwP negP).
+ move=> ata; split=> //; apply/negP => /existsP[x].
  by case/andP=> gt0_x; apply/ata; rewrite gt_eqF.
Qed.

Lemma atom0n : ~ (atom (0 : L)).
Proof. by case/andP; rewrite ltxx. Qed.

Lemma atomisticP (a : L) :
  reflect
    (exists2 S : {set L},
       (forall x, x \in S -> atom x) & a = \join_(x in S) x)
    (atomistic a).
Proof. apply: (iffP idP).
+ case/existsP=> /= S /andP[/forallP h /eqP->].
  by exists S=> // x; have/implyP := h x.
+ case=> S atx ->; apply/existsP; exists S; apply/andP; split=> //.
  by apply/forallP => x; apply/implyP=> /atx.
Qed.
End AtomicTheory.

(* -------------------------------------------------------------------- *)
Section GradedAtomicTheory.
Context (d : unit) (L : gradedFinLatticeType d).

Lemma atomE (a : L) : (atom a) = (rank a == 1%N).
Proof.
apply/idP/eqP.
+ case: (posxP a) => [-> /atom0n //|gt0_a /atomP -/(_ gt0_a) h].
  rewrite (rwP eqP) eqn_leq rank_gt0 gt0_a andbT.
  rewrite leqNgt; apply/negP; rewrite -[0%N](@rank0 _ L).
  by case/graded_rank => x /andP[]; rewrite lt0x => /h.
+ move=> eq1_rk; have gt0_a: 0 < a by rewrite -rank_gt0 eq1_rk.
  apply/atomP=> // x nz_x /homo_rank; rewrite eq1_rk ltnS.
  by rewrite leqn0 rank_eq0 (negbTE nz_x).
Qed.
End GradedAtomicTheory.
