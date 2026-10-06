(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
Require Import extra_misc.

Import Order.
Import Order.Theory.

Set SsrOldRewriteGoalsOrder.  (* TODO: port to the new rewrite subgoal order (MathComp >= 2.6) *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

(* MathComp 1.x notations for bottom and top, still used throughout.     *)
(* TODO: replace by \bot / \top and remove.                             *)
Notation "0" := \bot : order_scope.
Notation "1" := \top : order_scope.

(* -------------------------------------------------------------------- *)
Section Misc.
Context (d : disp_t) (T : latticeType d).

Lemma leIU (x y : T) : meet x y <= join x y.
Proof. exact: (le_trans (leIl _ _) (leUl _ _)). Qed.
End Misc.

(* -------------------------------------------------------------------- *)
(* A finite partial order with a top, a bottom and a meet is a lattice:  *)
(* the join is computed as the meet of all upper bounds.                 *)
HB.factory Record FinPOrder_isMeetBTLattice d T & FinPOrder d T := {
  top    : T;
  bottom : T;
  meet   : T -> T -> T;
  le_def : forall x y : T, x <= y = (meet x y == x);
  meetC  : commutative meet;
  meetA  : associative meet;
  meetxx : idempotent_op meet;
  le0x   : forall x, bottom <= x;
  lex1   : forall x, x <= top;
}.

HB.builders Context d T & FinPOrder_isMeetBTLattice d T.

Local Lemma meet1x : left_id top meet.
Proof. by move=> x; rewrite (rwP eqP) meetC -le_def lex1. Qed.

#[local] HB.instance Definition _ :=
  Monoid.isComLaw.Build T top meet meetA meetC meet1x.

Definition join (x y : T) : T :=
  \big[meet/top]_(z : T | (x <= z) && (y <= z)) z.

Local Lemma joinC : commutative join.
Proof. by move=> x y; apply: eq_bigl => z; rewrite andbC. Qed.

Local Lemma joinKI (y x : T) : meet x (join x y) = x.
Proof.
rewrite (rwP eqP) -le_def /join; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !le_def meetA => /eqP-> /eqP->.
+ by move=> z /andP[].
Qed.

Local Lemma meetKU (y x : T) : join x (meet x y) = x.
Proof.
rewrite /join (bigD1 x) /=; last first.
+ by rewrite !le_def /= -meetA [meet y x]meetC meetA !meetxx !eqxx.
rewrite (rwP eqP) -le_def; elim/big_ind: _.
+ by rewrite lex1.
+ by move=> x' y'; rewrite !le_def meetA => /eqP-> /eqP->.
+ by move=> z /andP[/andP[]].
Qed.

Local Lemma ge_joinL a b x : (x >= join a b) -> x >= a.
Proof.
rewrite /join => /(le_trans _); apply; elim: index_enum.
+ by rewrite big_nil lex1.
move=> y ys ih; rewrite big_cons; case: ifP => //.
case/andP=> le_ay _; rewrite !le_def in le_ay, ih |- *.
by rewrite meetA (eqP le_ay) (eqP ih).
Qed.

Local Lemma ge_joinP a b x : (x >= join a b) = (x >= a) && (x >= b).
Proof.
apply/idP/andP; last first.
+ case=> le_ax le_bx; rewrite /join (bigD1 x) ?(le_ax, le_bx) //=.
  set y := (X in meet x X); rewrite le_def /=.
  by rewrite -meetA meetC -meetA meetxx meetC.
+ move=> h; split; first by apply: (ge_joinL h).
  by rewrite joinC in h; apply: (ge_joinL h).
Qed.

Local Lemma joinA : associative join.
Proof.
move=> y x z; pose P t := [&& x <= t, y <= t & z <= t].
rewrite [X in X = _]/join (eq_bigl P); last first.
+ by move=> t; rewrite ge_joinP andbCA.
apply/esym; rewrite [X in X = _]/join [in LHS](eq_bigl P) //.
+ by move=> t; rewrite ge_joinP -andbA andbCA.
Qed.

HB.instance Definition _ :=
  POrder_isLattice.Build d T meetC joinC meetA joinA joinKI meetKU le_def.
HB.instance Definition _ := hasBottom.Build d T le0x.
HB.instance Definition _ := hasTop.Build d T lex1.
HB.end.

(* -------------------------------------------------------------------- *)
HB.mixin Record FinTBLattice_isGraded d T & FinTBLattice d T := {
  rank : T -> nat;
  rank0_subproof : rank \bot = 0%N;
  homo_rank_subproof : {homo rank : x y / x < y >-> (x < y)%N};
  graded_rank_subproof : forall x y : T,
    x <= y -> ((rank x).+1 < rank y)%N -> exists z, x < z < y;
}.

#[short(type="gradedFinLatticeType")]
HB.structure Definition GradedFinLattice d :=
  { T of FinTBLattice d T & FinTBLattice_isGraded d T }.

(* -------------------------------------------------------------------- *)
Section GradedTheory.
Context (d : disp_t) (L : gradedFinLatticeType d).

Lemma rank0 : rank (0 : L) = 0%N.
Proof. exact: rank0_subproof. Qed.

Lemma homo_rank : {homo (@rank d L) : x y / x < y >-> (x < y)%N}.
Proof. exact: homo_rank_subproof. Qed.

Lemma le_homo_rank : {homo (@rank d L) : x y / x <= y >-> (x <= y)%N}.
Proof. by apply: (ltW_homo homo_rank). Qed.

Lemma graded_rank (x y : L) : x <= y -> ((rank x).+1 < rank y)%N -> exists z, x < z < y.
Proof. exact: graded_rank_subproof. Qed.

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
Context (d : disp_t) (L : gradedFinLatticeType d) (P : L -> Prop).

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
Context (d : disp_t) (L : gradedFinLatticeType d).

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
(* Lattice morphisms (preserving meets and joins) are MathComp's         *)
(* `{lmorphism L -> G}`; `omorphism f` is the corresponding property.    *)
Section OMorphismDef.
Context (dL dG : disp_t) (L : latticeType dL) (G : latticeType dG).

Definition omorphism (f : L -> G) :=
     {morph f : x y / meet x y}
  /\ {morph f : x y / join x y}.

Lemma omorphismP (f : L -> G) :
     {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> omorphism f.
Proof. by move=> *; do! split. Qed.

Lemma omorphism_homo (f : L -> G) : omorphism f -> {homo f : x y / x <= y}.
Proof. by case=> hI _ x y; rewrite !leEmeet -hI => /eqP->. Qed.
End OMorphismDef.

HB.factory Record isOMorphism dL (L : latticeType dL) dG (G : latticeType dG)
    (f : L -> G) := {
  omorphism_subproof : omorphism f;
}.

HB.builders Context dL L dG G f & isOMorphism dL L dG G f.
HB.instance Definition _ :=
  isOrderMorphism.Build dL L dG G f (omorphism_homo omorphism_subproof).
HB.instance Definition _ :=
  isLatticeMorphism.Build dL L dG G f
    (proj1 omorphism_subproof) (proj2 omorphism_subproof).
HB.end.

Definition OMorphism dL (L : latticeType dL) dG (G : latticeType dG)
  (f : L -> G) (fM : omorphism f) : {lmorphism L -> G} :=
  HB.pack_for {lmorphism L -> G} f (isOMorphism.Build dL L dG G f fM).

(* -------------------------------------------------------------------- *)
Section OMorphismTheory.
Context (dL dG : disp_t) (L : latticeType dL) (G : latticeType dG).
Context (f : {lmorphism L -> G}).

Lemma lmorphismP : omorphism f.
Proof. by split; [apply: omorphI | apply: omorphU]. Qed.

Lemma omorph_homo : {homo f : x y / x <= y}.
Proof. exact: omorph_le. Qed.

Lemma omorph_mono : injective f -> {mono f : x y / x <= y}.
Proof.
move=> inj_f x y; apply/idP/idP => [|/omorph_homo //].
by rewrite !leEmeet -omorphI => /eqP /inj_f ->.
Qed.
End OMorphismTheory.

(* -------------------------------------------------------------------- *)
Section OMorphismRank.
Context (dL dG : disp_t) (L : gradedFinLatticeType dL) (G : gradedFinLatticeType dG).

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
Context (dL dG : disp_t) (L : gradedFinLatticeType dL) (G : gradedFinLatticeType dG).

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
Context (dL dG dH : disp_t).
Context (L : latticeType dL) (G : latticeType dG) (H : latticeType dH).
Context (fLG : {lmorphism L -> G}) (fGH : {lmorphism G -> H}).

Lemma comp_is_omorphism : omorphism (fGH \o fLG).
Proof. by apply/omorphismP=> x y /=; rewrite !(omorphI, omorphU). Qed.
End OMorphismComp.

(* -------------------------------------------------------------------- *)
Section OMorphismInv.
Context (dL dG : disp_t) (L : latticeType dL) (G : latticeType dG).
Context (f : L -> G) (fI : G -> L) (fK : cancel f fI) (Kf : cancel fI f).

Lemma inv_is_omorphism : omorphism f -> omorphism fI.
Proof. case=> hfI hfU; split=> x y.
+ by rewrite -{1}[x]Kf -{1}[y]Kf -hfI fK.
+ by rewrite -{1}[x]Kf -{1}[y]Kf -hfU fK.
Qed.
End OMorphismInv.

(* -------------------------------------------------------------------- *)
(* Lattice morphisms that also preserve the bottom (resp. bottom & top). *)
HB.structure Definition LatticeBMorphism dL (L : bLatticeType dL)
    dG (G : bLatticeType dG) :=
  {f of @LatticeMorphism dL L dG G f & @BLatticeMorphism dL L dG G f}.

HB.structure Definition LatticeTBMorphism dL (L : tbLatticeType dL)
    dG (G : tbLatticeType dG) :=
  {f of @LatticeBMorphism dL L dG G f & @TLatticeMorphism dL L dG G f}.

Reserved Notation "'{' 'bomorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'bomorphism'  U  ->  V }").
Reserved Notation "'{' 'tbomorphism' U '->' V '}'"
  (U at level 98, V at level 99, format "{ 'tbomorphism'  U  ->  V }").

Notation "{ 'bomorphism' L -> G }" := (@LatticeBMorphism.type _ L%type _ G%type)
  : type_scope.
Notation "{ 'tbomorphism' L -> G }" := (@LatticeTBMorphism.type _ L%type _ G%type)
  : type_scope.

Section BOMorphismDef.
Context (dL dG : disp_t) (L : bLatticeType dL) (G : bLatticeType dG).

Definition bomorphism (f : L -> G) := omorphism f /\ f \bot = \bot.

Lemma bomorphismP (f : L -> G) :
     f \bot = \bot
  -> {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> bomorphism f.
Proof. by move=> *; do! split. Qed.
End BOMorphismDef.

Section TBOMorphismDef.
Context (dL dG : disp_t) (L : tbLatticeType dL) (G : tbLatticeType dG).

Definition tbomorphism (f : L -> G) := bomorphism f /\ f \top = \top.

Lemma tbomorphismP (f : L -> G) :
     f \bot = \bot
  -> f \top = \top
  -> {morph f : x y / Order.meet x y}
  -> {morph f : x y / Order.join x y}
  -> tbomorphism f.
Proof. by move=> *; do! split. Qed.
End TBOMorphismDef.

Definition BOMorphism_pack dL (L : bLatticeType dL) dG (G : bLatticeType dG)
  (f : L -> G) (fM : bomorphism f) : {bomorphism L -> G} :=
  HB.pack_for {bomorphism L -> G} f
    (isOMorphism.Build dL L dG G f fM.1)
    (isBLatticeMorphism.Build dL L dG G f fM.2).

Definition TBOMorphism_pack dL (L : tbLatticeType dL) dG (G : tbLatticeType dG)
  (f : L -> G) (fM : tbomorphism f) : {tbomorphism L -> G} :=
  HB.pack_for {tbomorphism L -> G} f
    (isOMorphism.Build dL L dG G f fM.1.1)
    (isBLatticeMorphism.Build dL L dG G f fM.1.2)
    (isTLatticeMorphism.Build dL L dG G f fM.2).

Notation BOMorphism fM := (BOMorphism_pack fM).
Notation TBOMorphism fM := (TBOMorphism_pack fM).

(* -------------------------------------------------------------------- *)
Section BijOMorphismB.
Context (d : disp_t) (L G : bLatticeType d) (f : L -> G).

Lemma bij_omorphism_bomorphism : bijective f -> omorphism f -> bomorphism f.
Proof.
case=> [fI fK Kf] mF; case: (mF) => [hfI hfU]; apply/bomorphismP => //.
rewrite (rwP eqP) eq_le le0x andbT; have mFI := inv_is_omorphism fK Kf mF.
by rewrite -(omorph_mono (f := OMorphism mFI) (can_inj Kf)) /= fK le0x.
Qed.
End BijOMorphismB.

(* -------------------------------------------------------------------- *)
Section BijOMorphismTB.
Context (d : disp_t) (L G : tbLatticeType d) (f : L -> G).

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
Section Interval.
Context (d : disp_t) (L : latticeType d).

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

Lemma interval_is_lclosed a b :
  meet_closed (interval a b) /\ join_closed (interval a b).
Proof.
split=> x y /intervalP[le_ax le_xb] /intervalP[le_ay le_yb].
+ by rewrite intervalE !lexI !(le_ax, le_ay) /= leIxl.
+ by rewrite intervalE !leUx (le_xb, le_yb) lexUl.
Qed.
End Interval.

(* -------------------------------------------------------------------- *)
Section IntervalLattice.
Context (d : disp_t) (L : latticeType d) (a b : L).

Inductive interval_of : predArgType :=
  Interval x & x \in interval a b.

Definition interval_val r := let: Interval x _ := r in x.

HB.instance Definition _ := [isSub for interval_val].
HB.instance Definition _ := [Choice of interval_of by <:].
HB.instance Definition _ := SubChoice_isSubLattice.Build d L (interval a b)
  d interval_of (interval_is_lclosed a b).1 (interval_is_lclosed a b).2.

Lemma interval_val_is_omorphism : omorphism interval_val.
Proof. by []. Qed.
End IntervalLattice.

Section IntervalBLattice.
Context (d : disp_t) (L : latticeType d) (a b : L) (a_le_b : expose (a <= b)).

Fact le0R (x : interval_of a b) : Interval (intervalL a_le_b) <= x.
Proof. by rewrite leEsub /=; case/intervalP: (valP x). Qed.

Fact leR1 (x : interval_of a b) : x <= Interval (intervalR a_le_b).
Proof. by rewrite leEsub /=; case/intervalP: (valP x). Qed.

HB.instance Definition _ := hasBottom.Build d (interval_of a b) le0R.
HB.instance Definition _ := hasTop.Build d (interval_of a b) leR1.
End IntervalBLattice.

Notation "'[< a ; b >]" := (interval_of a b).
Notation "'[< a ; b >]_ R" := (@interval_of _ R a b) (only parsing).

Global Instance expose_le0x (disp : disp_t) (L : bPOrderType disp) (x : L) :
  expose (\bot <= x) := Expose (le0x x).
Global Instance expose_lex1 (disp : disp_t) (L : tPOrderType disp) (x : L) :
  expose (x <= \top) := Expose (lex1 x).

(* -------------------------------------------------------------------- *)
Section IntervalFinLattice.
Context (d : disp_t) (L : finLatticeType d) (a b : L).

HB.instance Definition _ := [Finite of '[< a; b >] by <:].
End IntervalFinLattice.

(* -------------------------------------------------------------------- *)
Section IntervalGradedLattice.
Context (d : disp_t) (L : gradedFinLatticeType d) (a b : L) (a_le_b : expose (a <= b)).

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

HB.instance Definition _ :=
  FinTBLattice_isGraded.Build d '[< a; b >] vrank0 homo_intv_rank graded_intv_rank.
End IntervalGradedLattice.

(* -------------------------------------------------------------------- *)
Section InIntvExpose.
Context (d : disp_t) (L : latticeType d) (a b : L).
Context (x : L) (hx0 : expose (a <= x)) (hx1 : expose (x <= b)).

Local Lemma in_interval : x \in interval a b.
Proof. by rewrite intervalE !(hx0, hx1). Qed.

Definition intv_inject := Interval in_interval.
End InIntvExpose.

Global Instance expose_ltW
  (disp : disp_t) (L : tbLatticeType disp) (x y : L) (h : expose (x < y))
: expose (x <= y)%O := Expose (ltW h).

Notation "x %:I_[< a ; b >]" := (@intv_inject _ _ a b x _ _)
  (at level 2, only parsing).

Notation "x %:I" := x%:I_[< _; _ >]
  (at level 2, format "x %:I").

(* -------------------------------------------------------------------- *)
Section IntvWiddenL.
Context (d : disp_t) (L : latticeType d) (a b : L).
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
Context (d : disp_t) (L : latticeType d) (a b : L).
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
Context (d : disp_t) (L : latticeType d) (a b : L).
Context (a' : L) (le_b : expose (a' <= a)).

Let wd (z : '[< a; b >]) := z%:I_[< <~ a'; >].

Lemma widdenLI (z1 z2 : '[<a; b>]) : wd (z1 `&` z2) = wd z1 `&` wd z2.
Proof. by apply: val_inj. Qed.

Lemma widdenLU (z1 z2 : '[<a; b>]) : wd (z1 `|` z2) = wd z1 `|` wd z2.
Proof. by apply: val_inj. Qed.
End WiddenLMorph.

(* -------------------------------------------------------------------- *)
Section WiddenRMorph.
Context (d : disp_t) (L : latticeType d) (a b : L).
Context (b' : L) (le_b : expose (b <= b')).

Let wd (z : '[< a; b >]) := z%:I_[< ; b' ~> >].

Lemma widdenRI (z1 z2 : '[<a; b>]) : wd (z1 `&` z2) = wd z1 `&` wd z2.
Proof. by apply: val_inj. Qed.

Lemma widdenRU (z1 z2 : '[<a; b>]) : wd (z1 `|` z2) = wd z1 `|` wd z2.
Proof. by apply: val_inj. Qed.
End WiddenRMorph.

(* -------------------------------------------------------------------- *)
Section IntvRankE.
Context (d : disp_t) (L : gradedFinLatticeType d) (a b : L) (le_ab: expose (a <= b)).
Context (x : '[< a ; b >]).

Lemma intv_rankE : rank x = (rank (val x) - rank a)%N.
Proof. by []. Qed.
End IntvRankE.

(* -------------------------------------------------------------------- *)
Section FullIntvMorphism.
Context (d : disp_t) (L : tbLatticeType d).

Let ival : '[< \bot; \top >]_L -> L := val.

Lemma bij_full_intv_val : bijective ival.
Proof.
exists (insubd (\bot : '[< \bot; \top >]_L)); first by apply: valKd.
by move=> x; apply: insubdK; rewrite intervalE le0x lex1.
Qed.

Lemma omorph_full_intv_val : tbomorphism ival.
Proof. by apply/tbomorphismP. Qed.
End FullIntvMorphism.

(* -------------------------------------------------------------------- *)
Section Atomic.
Context (d : disp_t) (L : finTBLatticeType d).

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
Lemma coatom_atom (d : disp_t) (L : finTBLatticeType d) (a : L) :
  coatom a -> atom (a : L^d).
Proof.
case/andP=> gt0_a /existsPn h; apply/andP.
split; first by apply: gt0_a.
by apply/existsPn => /= x; rewrite andbC h.
Qed.

Lemma coatom_atom_V (d : disp_t) (L : finTBLatticeType d) (a : L) :
  coatom (a : L^d) -> atom a.
Proof. exact/coatom_atom. Qed.
End CoatomAtom.

(* -------------------------------------------------------------------- *)
Section AtomCoatom.
Lemma atom_coatom (d : disp_t) (L : finTBLatticeType d) (a : L) :
  atom a -> coatom (a : L^d).
Proof.
case/andP=> gt0_a /existsPn h; apply/andP.
split; first by apply: gt0_a.
by apply/existsPn => /= x; rewrite andbC h.
Qed.

Lemma atom_coatom_V (d : disp_t) (L : finTBLatticeType d) (a : L) :
  atom (a : L^d) -> coatom a.
Proof. exact/atom_coatom. Qed.
End AtomCoatom.

(* -------------------------------------------------------------------- *)
Section AtomicTheory.
Context (d : disp_t) (L : finTBLatticeType d).

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
Context (d : disp_t) (L : finTBLatticeType d).

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
Context (d : disp_t) (L : gradedFinLatticeType d).

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
Context (d : disp_t) (L : gradedFinLatticeType d).

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
