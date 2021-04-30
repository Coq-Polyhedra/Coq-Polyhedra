(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

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

Variable (m : of_).

Local Lemma meet1x : left_id (top m) (meet m).
Proof. by move=> x; rewrite (rwP eqP) meetC -le_def lex1. Qed.

Local Lemma meetx1 : right_id (top m) (meet m).
Proof. by move=> x; rewrite meetC meet1x. Qed.

Local Canonical meet_monoid := Monoid.Law (meetA m) meet1x meetx1.
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

Lemma ge_joinL a b x : (x >= join a b) -> x >= a.
Proof.
rewrite /join => /(le_trans _); apply; elim: index_enum.
+ by rewrite big_nil lex1.
move=> y ys ih; rewrite big_cons; case: ifP => //.
case/andP=> le_ay _; rewrite !(le_def m) in le_ay, ih |- *.
by rewrite meetA (eqP le_ay) (eqP ih).
Qed.

Lemma ge_joinP a b x : (x >= join a b) = (x >= a) && (x >= b).
Proof.
apply/idP/andP; last first.
+ case=> le_ax le_bx; rewrite /join (bigD1 x) ?(le_ax, le_bx) //=.
  set y := (X in meet m x X); rewrite (le_def m) /=.
  by rewrite -meetA meetC -meetA meetxx meetC.
+ move=> h; split; first by apply: (ge_joinL h).
  by rewrite joinC in h; apply: (ge_joinL h).
Qed.

Lemma joinA : associative join.
Proof.
move=> y x z; pose P t := [&& x <= t, y <= t & z <= t].
rewrite [X in X = _]/join (eq_bigl P); last first.
+ by move=> t; rewrite ge_joinP andbCA.
apply/esym; rewrite [X in X = _]/join [in LHS](eq_bigl P) //.
+ by move=> t; rewrite ge_joinP -andbA andbCA.
Qed.

Definition latticeMixin : latticePOrderRelMixin T :=
  @LatticePOrderMixin d T (meet m) join
                      (meetC m) joinC (meetA m) joinA joinKI meetKU (le_def m).

Definition bottomMixin : bottomRelMixin T := @BottomMixin d T _ (le0x m).

Definition topMixin : topRelMixin T := @TopMixin d T _ (lex1 m).

End MeetBTFinMixin.

Module Exports.
Notation meetBTFinMixin := of_.
Notation MeetBTFinMixin := Build.
Coercion latticeMixin : meetBTFinMixin >-> latticePOrderRelMixin.
Coercion bottomMixin : meetBTFinMixin >-> bottomRelMixin.
Coercion topMixin : meetBTFinMixin >-> topRelMixin.
End Exports.
End MeetBTFinMixin.

(* -------------------------------------------------------------------- *)
Module GradedFinLattice.
Section ClassDef.

Record mixin_of d (T : finTBLatticeType d) := Mixin {
  rank : T -> nat;
  _ : rank bottom = 0%N;
  _ : forall x y : T, x < y -> (rank x < rank y)%N;
  _ : forall x y : T, x <= y -> ((rank x).+1 < rank y)%N -> exists z, x < z < y
}.

Record class_of (T : Type) := Class {
  base  : FinTBLattice.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (FinTBLattice.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> FinTBLattice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack disp0 (T0 : finTBLatticeType disp0) (m0 : mixin_of T0) :=
  fun bT b & phant_id (@FinTBLattice.class disp bT) b =>
  fun m    & phant_id m0 m => Pack disp (@Class T b disp0 m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition countType := @Countable.Pack cT xclass.
Definition finType := @Finite.Pack cT xclass.
Definition porderType := @POrder.Pack disp cT xclass.
Definition bPOrderType := @BPOrder.Pack disp cT xclass.
Definition tPOrderType := @TPOrder.Pack disp cT xclass.
Definition tbPOrderType := @TBPOrder.Pack disp cT xclass.
Definition finPOrderType := @FinPOrder.Pack disp cT xclass.
Definition finBPOrderType := @FinBPOrder.Pack disp cT xclass.
Definition finTPOrderType := @FinTPOrder.Pack disp cT xclass.
Definition finTBPOrderType := @FinTBPOrder.Pack disp cT xclass.
Definition meetSemilatticeType := @MeetSemilattice.Pack disp cT xclass.
Definition bMeetSemilatticeType := @BMeetSemilattice.Pack disp cT xclass.
Definition tMeetSemilatticeType := @TMeetSemilattice.Pack disp cT xclass.
Definition tbMeetSemilatticeType := @TBMeetSemilattice.Pack disp cT xclass.
Definition joinSemilatticeType := @JoinSemilattice.Pack disp cT xclass.
Definition bJoinSemilatticeType := @BJoinSemilattice.Pack disp cT xclass.
Definition tJoinSemilatticeType := @TJoinSemilattice.Pack disp cT xclass.
Definition tbJoinSemilatticeType := @TBJoinSemilattice.Pack disp cT xclass.
Definition latticeType := @Lattice.Pack disp cT xclass.
Definition bLatticeType := @BLattice.Pack disp cT xclass.
Definition tLatticeType := @TLattice.Pack disp cT xclass.
Definition tbLatticeType := @TBLattice.Pack disp cT xclass.
Definition finLatticeType := @FinLattice.Pack disp cT xclass.
Definition finTBLatticeType := @FinTBLattice.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> FinTBLattice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> POrder.type.
Coercion bPOrderType : type >-> BPOrder.type.
Coercion tPOrderType : type >-> TPOrder.type.
Coercion tbPOrderType : type >-> TBPOrder.type.
Coercion finPOrderType : type >-> FinPOrder.type.
Coercion finBPOrderType : type >-> FinBPOrder.type.
Coercion finTPOrderType : type >-> FinTPOrder.type.
Coercion finTBPOrderType : type >-> FinTBPOrder.type.
Coercion meetSemilatticeType : type >-> MeetSemilattice.type.
Coercion bMeetSemilatticeType : type >-> BMeetSemilattice.type.
Coercion tMeetSemilatticeType : type >-> TMeetSemilattice.type.
Coercion tbMeetSemilatticeType : type >-> TBMeetSemilattice.type.
Coercion joinSemilatticeType : type >-> JoinSemilattice.type.
Coercion bJoinSemilatticeType : type >-> BJoinSemilattice.type.
Coercion tJoinSemilatticeType : type >-> TJoinSemilattice.type.
Coercion tbJoinSemilatticeType : type >-> TBJoinSemilattice.type.
Coercion latticeType : type >-> Lattice.type.
Coercion bLatticeType : type >-> BLattice.type.
Coercion tLatticeType : type >-> TLattice.type.
Coercion tbLatticeType : type >-> TBLattice.type.
Coercion finLatticeType : type >-> FinLattice.type.
Coercion finTBLatticeType : type >-> FinTBLattice.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical bPOrderType.
Canonical tPOrderType.
Canonical tbPOrderType.
Canonical finPOrderType.
Canonical finBPOrderType.
Canonical finTPOrderType.
Canonical finTBPOrderType.
Canonical meetSemilatticeType.
Canonical bMeetSemilatticeType.
Canonical tMeetSemilatticeType.
Canonical tbMeetSemilatticeType.
Canonical joinSemilatticeType.
Canonical bJoinSemilatticeType.
Canonical tJoinSemilatticeType.
Canonical tbJoinSemilatticeType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tLatticeType.
Canonical tbLatticeType.
Canonical finLatticeType.
Canonical finTBLatticeType.
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

Lemma graded_rank (x y : L) : x <= y -> ((rank x).+1 < rank y)%N -> exists z, x < z < y.
Proof. by case: L x y => [? [? ? []]]. Qed.

Lemma rank_eq0 (x : L) : (rank x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [zrk|->]; last by rewrite rank0.
apply/contra_eq: zrk; rewrite -!(lt0x, lt0n).
by move/homo_rank; rewrite rank0.
Qed.

Lemma rank_eq1 (x : L) : (rank x == rank ((1 : L))%O) = (x == 1).
Proof.
apply/eqP/idP=> [eqrk|/eqP ->//].
have := lex1 x; rewrite le_eqVlt => /orP[] //.
by move/homo_rank; rewrite eqrk ltnn.
Qed.

Lemma rank_gt0 (x : L) : (0 < rank x)%N = (0 < x).
Proof.
apply/idP/idP => [gt0_rank|/homo_rank]; last by rewrite rank0.
by rewrite lt_neqAle le0x eq_sym -rank_eq0 andbT -lt0n.
Qed.

Lemma rank_le1 (x : L) : (rank x <= rank (1%O : L))%N.
Proof. by apply/le_homo_rank/lex1. Qed.

Lemma rank_gt1 (x : L) : (rank x < rank (1 : L)%O)%N = (x < 1).
Proof.
apply/idP/idP => [lt1_rank|/homo_rank //].
by rewrite lt_neqAle lex1 andbT -rank_eq1 ltn_eqF.
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
Proof.
rewrite lt0n rank_eq0 => nz_x; case/boolP: (rank x < 2)%N.
+ rewrite ltnS leq_eqVlt ltnS leqn0 rank_eq0 (negbTE nz_x) orbF.
  by move=> /eqP->; exists 0; rewrite ?(lt0x) // rank0.
rewrite -leqNgt => gt1_rkx; case: (graded_rank (le0x x)).
+ by rewrite rank0.
move=> y; move: {2}(rank x - rank y) (leqnn (rank x - rank y)).
move=> n; elim: n y => [|n ih] y.
+ rewrite leqn0  subn_eq0 => le_rk_xy.
  by case/andP=> _ /homo_rank; rewrite ltnNge le_rk_xy.
rewrite leq_eqVlt => /orP[]; last by rewrite ltnS => /ih.
move=> h; have {h}: rank x = ((rank y).+1 + n)%N.
+ have: rank x - rank y != 0 by rewrite (eqP h).
  rewrite subn_eq0 -ltnNge => lt_rk_yx.
  by rewrite addSnnS -(eqP h) addnC subnK // ltnW.
case: (n =P 0)%N => [{ih}-> rkxE /andP[_ lt_yx]|].
+ by exists y => //; rewrite rkxE addn0.
move=> /eqP nz_n rkxE /andP[gt0_y lt_yx]; case: (graded_rank (ltW lt_yx)).
+ by rewrite rkxE -[X in (X < _)%N]addn0 ltn_add2l lt0n.
move=> z /andP[lt_yz lt_zx]; case: (ih z).
+ by rewrite rkxE leq_subCl addnK; apply: homo_rank.
+ by rewrite (lt_trans gt0_y lt_yz) lt_zx.
by move=> t lt_tx <-; exists t.
Qed.
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
Section OMorphismInv.
Context (dL dG : unit) (L : latticeType dL) (G : latticeType dG).
Context (f : L -> G) (fI : G -> L) (fK : cancel f fI) (Kf : cancel fI f).

Lemma inv_is_omorphism : omorphism f -> omorphism fI.
Proof. case=> hfI hfU; split=> x y.
+ by rewrite -{1}[x]Kf -{1}[y]Kf -hfI fK.
+ by rewrite -{1}[x]Kf -{1}[y]Kf -hfU fK.
Qed.
End OMorphismInv.

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
Section BijOMorphismB.
Context (d : unit) (L G : bLatticeType d) (f : L -> G).

Lemma bij_omorphism_bomorphism : bijective f -> omorphism f -> bomorphism f.
Proof.
case=> [fI fK Kf] mF; case: (mF) => [hfI hfU]; apply/bomorphismP => //.
rewrite (rwP eqP) eq_le le0x andbT; have mFI := inv_is_omorphism fK Kf mF.
by rewrite -(omorph_mono (f := OMorphism mFI) (can_inj Kf)) /= fK le0x.
Qed.
End BijOMorphismB.

(* -------------------------------------------------------------------- *)
Section BijOMorphismTB.
Context (d : unit) (L G : tbLatticeType d) (f : L -> G).

Lemma bij_omorphism_tbomorphism : bijective f -> omorphism f -> tbomorphism f.
Proof.
case=> [fI fK Kf] mF; case: (mF) => [hfI hfU]; apply/tbomorphismP => //.
+ have mbF := bij_omorphism_bomorphism (Bijective fK Kf) mF.
  by have := (omorph0 (BOMorphism mbF)).
rewrite (rwP eqP) eq_le lex1 /=; have mFI := inv_is_omorphism fK Kf mF.
by rewrite -(omorph_mono (f := OMorphism mFI) (can_inj Kf)) /= fK lex1.
Qed.
End BijOMorphismTB.

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
  @LatticePOrderMixin d _ _ _ meetC joinC meetA joinA joinKI meetKU le_def.

Canonical sub_meetSemilatticeType :=
  Eval hnf in MeetSemilatticeType U (latticeMixin (Phant U)).

Canonical sub_joinSemilatticeType :=
  Eval hnf in JoinSemilatticeType U (latticeMixin (Phant U)).

(* FIXME: the head constant of (U : Type) is sub_sort. Thus, the above        *)
(*        declarations are redundant with Order.SubOrder.                     *)
(* Canonical sub_latticeType := [latticeType of U]. *)
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

Reserved Notation "'[< a ; b >]_ R"
  (at level 2, a, b at level 8, format "''[<' a ;  b '>]_' R").

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

Let bottom := Interval (intervalL a_le_b).
Let top    := Interval (intervalR a_le_b).

Fact le0R x : bottom <= x.
Proof. by rewrite leEsub /=; case/intervalP: (valP x). Qed.

Fact leR1 x : x <= top.
Proof. by rewrite leEsub /=; case/intervalP: (valP x). Qed.

Definition interval_bottomMixin := BottomMixin le0R.
Definition interval_topMixin := TopMixin leR1.

Canonical interval_bPOrderType :=
  Eval hnf in BPOrderType interval_of interval_bottomMixin.
Canonical interval_tPOrderType :=
  Eval hnf in TPOrderType interval_of interval_topMixin.
Canonical interval_tbPOrderType := [tbPOrderType of interval_of].

Definition interval_latticeMixin := [latticeMixin of interval_of by <:].

Canonical interval_meetSemilatticeType :=
  Eval hnf in MeetSemilatticeType interval_of interval_latticeMixin.
Canonical interval_bMeetSemilatticeType :=
  [bMeetSemilatticeType of interval_of].
Canonical interval_tMeetSemilatticeType :=
  [tMeetSemilatticeType of interval_of].
Canonical interval_tbMeetSemilatticeType :=
  [tbMeetSemilatticeType of interval_of].

Canonical interval_joinSemilatticeType :=
  Eval hnf in JoinSemilatticeType interval_of interval_latticeMixin.
Canonical interval_bJoinSemilatticeType :=
  [bJoinSemilatticeType of interval_of].
Canonical interval_tJoinSemilatticeType :=
  [tJoinSemilatticeType of interval_of].
Canonical interval_tbJoinSemilatticeType :=
  [tbJoinSemilatticeType of interval_of].

Canonical interval_latticeType := [latticeType of interval_of].
Canonical interval_bLatticeType := [bLatticeType of interval_of].
Canonical interval_tLatticeType := [tLatticeType of interval_of].
Canonical interval_tbLatticeType := [tbLatticeType of interval_of].

Lemma interval_val_is_omorphism : omorphism interval_val.
Proof. by []. Qed.

Canonical interval_omorphism := OMorphism interval_val_is_omorphism.
End IntervalLattice.

Notation "'[< a ; b >]" := (interval_of a b).
Notation "'[< a ; b >]_ R" := (@interval_of _ R a b) (only parsing).

Global Instance expose_le0x (disp : unit) (L : bPOrderType disp) (x : L) :
  expose (0 <= x) := Expose (le0x x).
Global Instance expose_lex1 (disp : unit) (L : tPOrderType disp) (x : L) :
  expose (x <= 1) := Expose (lex1 x).

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
Canonical interval_finBPOrderType := Eval hnf in [finBPOrderType of '[< a; b >]].
Canonical interval_finTPOrderType := Eval hnf in [finTPOrderType of '[< a; b >]].
Canonical interval_finTBPOrderType := Eval hnf in [finTBPOrderType of '[< a; b >]].
Canonical interval_finLatticeType := Eval hnf in [finLatticeType of '[< a; b >]].
Canonical interval_finTBLatticeType := Eval hnf in [finTBLatticeType of '[< a; b >]].
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
  x <= y -> ((vrank x).+1 < vrank y)%N -> exists z : '[< a; b >], x < z < y.
Proof.
rewrite /vrank -subSn ?intv_rankL // ltn_subLR; last first.
+ by rewrite (leq_trans (intv_rankL x)).
rewrite subnKC ?intv_rankL // => /graded_rank h /h [z rg_z].
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
Section InIntvExpose.
Context (d : unit) (L : latticeType d) (a b : L).
Context (x : L) (hx0 : expose (a <= x)) (hx1 : expose (x <= b)).

Local Lemma in_interval : x \in interval a b.
Proof. by rewrite intervalE !(hx0, hx1). Qed.

Definition intv_inject := Interval in_interval.
End InIntvExpose.

Global Instance expose_ltW
  (disp : unit) (L : tbLatticeType disp) (x y : L) (h : expose (x < y))
: expose (x <= y)%O := Expose (ltW h).

Notation "x %:I_[< a ; b >]" := (@intv_inject _ _ a b x _ _)
  (at level 2, only parsing).

Notation "x %:I" := x%:I_[< _; _ >]
  (at level 2, format "x %:I").

(* -------------------------------------------------------------------- *)
Section IntvWiddenL.
Context (d : unit) (L : latticeType d) (a b : L).
Context (a' : L) (le_a : expose (a' <= a)) (x : '[< a; b >]).

Local Lemma in_intervalL : val x \in interval a' b.
Proof.
rewrite intervalE (intervalPR (valP x)) andbT.
by rewrite (le_trans le_a) // (intervalPL (valP x)).
Qed.

Definition intv_widdenL := Interval in_intervalL.
End IntvWiddenL.

Notation "x %:I_[< a <~ a' ; b >]" := (@intv_widdenL _ _ a b a' _ x)
 (at level 2, format "x %:I_[< a <~ a' ;  b >]").

Notation "x %:I_[< <~ a' ; >]" := (x %:I_[< _ <~ a' ;  _ >])
 (at level 2, format "x %:I_[<  <~  a' ;  >]").

(* -------------------------------------------------------------------- *)
Section IntvWiddenR.
Context (d : unit) (L : latticeType d) (a b : L).
Context (b' : L) (le_b : expose (b <= b')) (x : '[< a; b >]).

Local Lemma in_intervalR : val x \in interval a b'.
Proof.
rewrite intervalE (intervalPL (valP x)) /=.
by rewrite (le_trans _ le_b) // (intervalPR (valP x)).
Qed.

Definition intv_widdenR := Interval in_intervalR.
End IntvWiddenR.

Notation "x %:I_[< a ; b' ~> b >]" := (@intv_widdenR _ _ a b b' _ x)
 (at level 2, format "x %:I_[< a ;  b' ~> b  >]").

Notation "x %:I_[< ; b' ~> >]" := (x %:I_[< _ ; b' ~> _ >])
 (at level 2, format "x %:I_[<  ;  b' ~>  >]").

(* -------------------------------------------------------------------- *)
Section WiddenLMorph.
Context (d : unit) (L : latticeType d) (a b : L).
Context (a' : L) (le_b : expose (a' <= a)).

Let wd (z : '[< a; b >]) := z%:I_[< <~ a'; >].

Lemma widdenLI (z1 z2 : '[<a; b>]) : wd (z1 `&` z2) = wd z1 `&` wd z2.
Proof. by apply: val_inj. Qed.

Lemma widdenLU (z1 z2 : '[<a; b>]) : wd (z1 `|` z2) = wd z1 `|` wd z2.
Proof. by apply: val_inj. Qed.
End WiddenLMorph.

(* -------------------------------------------------------------------- *)
Section WiddenRMorph.
Context (d : unit) (L : latticeType d) (a b : L).
Context (b' : L) (le_b : expose (b <= b')).

Let wd (z : '[< a; b >]) := z%:I_[< ; b' ~> >].

Lemma widdenRI (z1 z2 : '[<a; b>]) : wd (z1 `&` z2) = wd z1 `&` wd z2.
Proof. by apply: val_inj. Qed.

Lemma widdenRU (z1 z2 : '[<a; b>]) : wd (z1 `|` z2) = wd z1 `|` wd z2.
Proof. by apply: val_inj. Qed.
End WiddenRMorph.

(* -------------------------------------------------------------------- *)
Section IntvRankE.
Context (d : unit) (L : gradedFinLatticeType d) (a b : L) (le_ab: expose (a <= b)).
Context (x : '[< a ; b >]).

Lemma intv_rankE : rank x = (rank (val x) - rank a)%N.
Proof. by []. Qed.
End IntvRankE.

(* -------------------------------------------------------------------- *)
Section FullIntvMorphism.
Context (d : unit) (L : tbLatticeType d).

Let ival := (@val L _ [subType of '[< 0%O; 1%O >]_L]).

Lemma bij_full_intv_val : bijective ival.
Proof.
exists (insubd (0%O : '[< 0%O; 1%O >]_L)); first by apply: valKd.
by move=> x; apply: insubdK; rewrite intervalE le0x lex1.
Qed.

Lemma omorph_full_intv_val : tbomorphism ival.
Proof. by apply/tbomorphismP. Qed.
End FullIntvMorphism.

(* -------------------------------------------------------------------- *)
Section Atomic.
Context (d : unit) (L : finTBLatticeType d).

Definition atom (a : L) :=
  (0 < a) && ~~ [exists x : L, 0 < x < a].

Definition coatom (a : L) :=
  (a < 1) && ~~ [exists x : L, a < x < 1].

Definition atomistic (a : L) :=
  [exists S : {set L},
     [forall x in S, atom x] && (a == \join_(x in S) x)].

Definition coatomistic (a : L) :=
  [exists S : {set L},
     [forall x in S, coatom x] && (a == \meet_(x in S) x)].
End Atomic.

(* -------------------------------------------------------------------- *)
Section CoatomAtom.
Lemma coatom_atom (d : unit) (L : finTBLatticeType d) (a : L) :
  coatom a -> atom (a : L^d).
Proof.
case/andP=> gt0_a /existsPn h; apply/andP.
split; first by apply: gt0_a.
by apply/existsPn => /= x; rewrite andbC h.
Qed.

Lemma coatom_atom_V (d : unit) (L : finTBLatticeType d) (a : L) :
  coatom (a : L^d) -> atom a.
Proof. exact/coatom_atom. Qed.
End CoatomAtom.

(* -------------------------------------------------------------------- *)
Section AtomCoatom.
Lemma atom_coatom (d : unit) (L : finTBLatticeType d) (a : L) :
  atom a -> coatom (a : L^d).
Proof.
case/andP=> gt0_a /existsPn h; apply/andP.
split; first by apply: gt0_a.
by apply/existsPn => /= x; rewrite andbC h.
Qed.

Lemma atom_coatom_V (d : unit) (L : finTBLatticeType d) (a : L) :
  atom (a : L^d) -> coatom a.
Proof. exact/atom_coatom. Qed.
End AtomCoatom.

(* -------------------------------------------------------------------- *)
Section AtomicTheory.
Context (d : unit) (L : finTBLatticeType d).

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
Section CoatomicTheory.
Context (d : unit) (L : finTBLatticeType d).

Lemma coatom1n : ~ (coatom (1 : L)).
Proof. by move=> /coatom_atom /atom0n. Qed.

Lemma coatomP (a : L) : a < 1 ->
  reflect (forall x, x != 1 -> ~ (a < x)) (coatom a).
Proof.
move=> gt1_a; apply: (iffP idP).
+ by move/coatom_atom/atomP=> -/(_ gt1_a); apply.
move=> h; apply/atom_coatom_V/andP; split.
- by apply: gt1_a.
apply/existsPn=> /= x; apply/negP=> /andP[gt0_x].
by move/h; apply; rewrite lt_eqF.
Qed.

Lemma coatomisticP (a : L) :
  reflect
    (exists2 S : {set L},
       (forall x, x \in S -> coatom x) & a = \meet_(x in S) x)
    (coatomistic a).
Proof.
apply: (iffP existsP) => /= -[S].
+ move=> /andP [/forallP h /eqP->]; exists S => //.
  by move=> x; move/(_ x): h => /implyP.
+ move=> h ->; exists S; rewrite eqxx andbT.
  by apply/forallP=> x; apply/implyP=> /h.
Qed.
End CoatomicTheory.

(* -------------------------------------------------------------------- *)
Section GradedAtomicTheory.
Context (d : unit) (L : gradedFinLatticeType d).

Lemma atomE (a : L) : (atom a) = (rank a == 1%N).
Proof.
apply/idP/eqP.
+ case: (posxP a) => [-> /atom0n //|gt0_a /atomP -/(_ gt0_a) h].
  rewrite (rwP eqP) eqn_leq rank_gt0 gt0_a andbT.
  rewrite leqNgt; apply/negP; rewrite -[0%N](@rank0 _ L).
  by case/(graded_rank (le0x _)) => x /andP[]; rewrite lt0x => /h.
+ move=> eq1_rk; have gt0_a: 0 < a by rewrite -rank_gt0 eq1_rk.
  apply/atomP=> // x nz_x /homo_rank; rewrite eq1_rk ltnS.
  by rewrite leqn0 rank_eq0 (negbTE nz_x).
Qed.
End GradedAtomicTheory.
(* -------------------------------------------------------------------- *)
Section GradedCoAtomicTheory.
Context (d : unit) (L : gradedFinLatticeType d).

Lemma coatomE (a : L) : (coatom a) = (rank (1 : L) == (rank a).+1%N).
Proof.
apply/idP/eqP.
+ have := lex1 a; rewrite le_eqVlt => /orP[/eqP-> /coatom1n //|].
  move=> lt1_a /coatomP -/(_ lt1_a) h; move/homo_rank: lt1_a.
  rewrite (rwP eqP) eqn_leq => ->; rewrite andbT leqNgt.
  apply/negP => /(graded_rank (lex1 _)) [x].
  by rewrite andbC lt_neqAle -andbA => /and3P[/h].
+ move=> h; have lt1_a: a < 1 by rewrite -rank_gt1 h.
  apply/coatomP=> // x neq1_x /homo_rank; rewrite -ltnS -h.
  by apply/negP; rewrite -leqNgt rank_gt1 lt_neqAle neq1_x lex1.
Qed.
End GradedCoAtomicTheory.
