(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop ssralg ssrnum zmodp matrix fingroup perm.
Require Import extra_misc inner_product.

Import Order.Theory.

Definition lte_anti := (=^~ @eq_le, @lt_asym, @lt_le_asym, @le_lt_asym).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section Order.

Variable R : realFieldType.

Section Core.

Variable n : nat.

Implicit Types x y z : 'cV[R]_n.

Definition lev x y := [forall i, x i 0 <= y i 0].

Notation "<=m" := lev: ring_scope.
Notation ">=m x" := (lev x) (at level 0): ring_scope.
Notation "<=m x" := (lev^~ x) (at level 0): ring_scope.
Notation "x <=m y" := (lev x y) (at level 0): ring_scope.
Notation "x >=m y" := (y <=m x) (only parsing, at level 0) : ring_scope.

Lemma lev_add2l x :
  {mono +%R x : y z / y <=m z}.
Proof.
by move => y z; apply: eq_forallb => i; rewrite !mxE ler_add2l.
Qed.

Lemma lev_add2r x :
  {mono +%R^~ x : y z / y <=m z}.
Proof.
by move => y z; apply: eq_forallb => i; rewrite !mxE ler_add2r.
Qed.

Lemma lev_opp2 :
  {mono -%R: x y /~ x <=m y}.
Proof.
by move => x y; apply: eq_forallb => i; rewrite !mxE ler_opp2.
Qed.

(* Addition of vector inequalities retains order *)
Lemma lev_add x y (l1 l2 : 'cV[R]_n) :
  (l1 <=m x) -> (l2 <=m y) -> ((l1 + l2) <=m (x + y)).
Proof.
  rewrite /lev; move => /forallP Hx /forallP Hy.
  by apply/forallP => ?; rewrite !mxE ler_add //.
Qed.

Lemma lev_pscalar (a : R) :
  0 < a -> {mono *:%R a : x y / x <=m y }.
Proof.
by move => Ha x y; apply: eq_forallb => i; rewrite !mxE ler_pmul2l.
Qed.

Lemma lev_wpscalar a x y :
  0 <= a -> x <=m y -> (a *: x) <=m (a *: y).
Proof.
move => Ha /forallP Hxy.
apply/forallP => i; rewrite !mxE.
by apply: ler_wpmul2l.
Qed.

Lemma gev0P x :
  reflect (forall i, 0 <= x i 0) (x >=m 0).
Proof.
apply: (iffP forallP) => [H i | H i].
- by move/(_ i): H; rewrite mxE.
- by rewrite mxE; apply: H.
Qed.

Lemma lev0P x :
  reflect (forall i, x i 0 <= 0) (x <=m 0).
Proof.
apply: (iffP forallP) => [H i | H i].
- by move/(_ i): H; rewrite mxE.
- by rewrite mxE; apply: H.
Qed.

Lemma paddv_eq0 x y :
  (0 <=m x) -> (0 <=m y) -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move => /forallP Hx /forallP Hy.
apply/idP/idP.
- move/eqP/colP => Hxy; apply/andP; split;
  apply/eqP; apply/colP => i; move/(_ i)/eqP: Hxy; rewrite !mxE paddr_eq0;
  by [move/andP => [/eqP H /eqP H'] | move/(_ i): Hx; rewrite mxE | move/(_ i): Hy; rewrite mxE].
- by move/andP => [/eqP -> /eqP ->]; rewrite addr0.
Qed.

Lemma subv_ge0 x y :
  (0 <=m (y - x)) = (x <=m y).
Proof.
by apply: eq_forallb => i; rewrite !mxE subr_ge0.
Qed.

Lemma subv_le0 x y :
  (0 >=m (y - x)) = (x >=m y).
Proof.
by apply: eq_forallb => i; rewrite !mxE subr_le0.
Qed.

Lemma lev_refl x :
  (x <=m x).
Proof.
by apply/forallP => i.
Qed.

Lemma oppv_ge0 x :
  (0 <=m -x) = (x <=m 0).
Proof.
by apply: eq_forallb => i; rewrite !mxE oppr_ge0.
Qed.

Lemma lev_antisym:
  antisymmetric (<=m).
Proof.
move => x y /andP [/forallP Hx /forallP Hy].
apply/colP => i; apply: le_anti; apply/andP; split; by [move/(_ i): Hx; move/(_ i): Hy].
Qed.

Lemma lev_trans:
  transitive (<=m).
Proof.
move => x y z /forallP Hx /forallP Hy.
apply/forallP => i; move/(_ i): Hy; move/(_ i): Hx.
by apply: le_trans.
Qed.

Lemma eqv_le x y :
  (x == y) = (x <=m y) && (y <=m x).
Proof.
apply/idP/idP.
- by move/eqP ->; rewrite lev_refl.
- by move/lev_antisym/eqP.
Qed.

Lemma vdot_lev x y z :
  x >=m 0 -> y <=m z -> '[x,y] <= '[x,z].
Proof.
move => /forallP Hx /forallP Hyz.
rewrite -subr_ge0 -vdotBr /vdot.
apply: sumr_ge0 => i _; apply: mulr_ge0.
- by move/(_ i): Hx; rewrite mxE.
- by rewrite !mxE subr_ge0.
Qed.

Lemma vdot_lev_eq0 x y :
  [forall i, x i 0 > 0] -> y >=m 0 -> '[x,y] = 0 -> y = 0.
Proof.
move => Hx Hy Hxy.
suff: forall i, x i 0 * y i 0 = 0.
- move => H; apply/colP => i; rewrite mxE; move/(_ i)/eqP: H.
  rewrite mulf_eq0; move/forallP/(_ i)/lt0r_neq0/negbTE: Hx ->.
  by rewrite /=; move/eqP.
- move => i; move: Hxy i is_true_true; apply: psumr_eq0P => i _.
  rewrite (pmulr_rge0 _ ((forallP Hx) i)).
  by move/forallP/(_ i): Hy; rewrite mxE.
Qed.

Lemma vdot_lev_eq x y z : [forall i, x i 0 > 0] -> y >=m z -> '[x,y] = '[x,z] -> y = z.
Proof.
move => Hx.
rewrite -subv_ge0 => Hyz.
move/eqP; rewrite -subr_eq0 -vdotBr => /eqP Hdot.
apply/eqP; rewrite -subr_eq0.
apply/eqP; exact: (vdot_lev_eq0 Hx).
Qed.

Definition lev_max x y := \col_i (Num.max (x i 0) (y i 0)).
Definition lev_min x y := \col_i (Num.min (x i 0) (y i 0)).

Lemma lev_maxC x y :
  lev_max x y = lev_max y x.
Proof.
apply/colP => i; rewrite !mxE; apply: maxC.
Qed.

Lemma lev_minC x y :
  lev_min x y = lev_min y x.
Proof.
apply/colP => i; rewrite !mxE; apply: minC.
Qed.

Lemma lev_maxl x y :
  (lev_max x y) >=m x.
Proof.
by apply/forallP => i; rewrite !mxE le_maxr lexx.
Qed.

Lemma lev_maxr x y :
  (lev_max x y) >=m y.
Proof.
by rewrite lev_maxC; apply: lev_maxl.
Qed.

Lemma lev_minl x y :
  (lev_min x y) <=m x.
Proof.
by apply/forallP => i; rewrite !mxE le_minl lexx.
Qed.

Lemma lev_minr x y :
  (lev_min x y) <=m y.
Proof.
by rewrite lev_minC; apply: lev_minl.
Qed.

Lemma add_lev_min_max x y :
  lev_min x y + lev_max x y = x + y.
Proof.
by apply/colP => i; rewrite !mxE /= addr_min_max.
Qed.

Definition pos_part x := lev_max x 0.
Definition neg_part x := -(lev_min x 0).

Lemma pos_part_gev0 x :
  (pos_part x) >=m 0.
Proof.
by apply: lev_maxr.
Qed.

Lemma neg_part_gev0 x :
  (neg_part x) >=m 0.
Proof.
by rewrite oppv_ge0; apply: lev_minr.
Qed.

Lemma add_pos_neg_part x :
  (pos_part x) - (neg_part x) = x.
Proof.
by rewrite opprK addrC add_lev_min_max addr0.
Qed.

Lemma row_perm_lev (s : {perm 'I_n}) x y :
  (x <=m y) = ((row_perm s x) <=m (row_perm s y)).
Proof.
apply/idP/idP => /forallP H; apply/forallP => i.
- by move/(_ (s i)): H; rewrite !mxE.
- by move/(_ ((s^-1)%g i)): H; rewrite !mxE permKV.
Qed.

Lemma row_perm_gev0 (s : {perm 'I_n}) x :
  (x >=m 0) = ((row_perm s x) >=m 0).
Proof.
by rewrite (row_perm_lev s) row_perm_const.
Qed.

End Core.

Notation "<=m" := lev: ring_scope.
Notation ">=m x" := (lev x) (at level 0): ring_scope.
Notation "<=m x" := (lev^~ x) (at level 0): ring_scope.
Notation "x <=m y" := (lev x y) (at level 0): ring_scope.
Notation "x >=m y" := (y <=m x) (only parsing, at level 0) : ring_scope.

Section ExtraOrder.

Variable n p : nat.

Lemma lev_castmx (eq_np : n = p) :
  {mono (@castmx R n 1 p 1 (eq_np, erefl _)) : x y / x <=m y }.
Proof.
move => x y.
apply/idP/idP.
- move/forallP => H; apply/forallP => i.
  by move/(_ (cast_ord eq_np i)): H; rewrite !castmxE //= cast_ord_id cast_ordK.
- move/forallP => H; apply/forallP => ?.
  by rewrite !castmxE /= cast_ord_id; apply: H.
Qed.

Lemma castmx_gev0 (eq_np : n = p) x :
  ((castmx (eq_np, erefl _) x) >=m 0) = (x >=m 0).
Proof.
have {1}<-: (castmx (eq_np, erefl 1%N) 0 = (0:'cV[R]_p)) by rewrite castmx_const.
apply: lev_castmx.
Qed.

Lemma col_mx_lev (x y : 'cV[R]_n) (v w : 'cV[R]_p) :
  ((col_mx x v) <=m (col_mx y w)) = ((x <=m y) && (v <=m w)).
Proof.
apply/idP/idP.
- move/forallP => H.
  apply/andP; split.
    + by apply/forallP => i; move: (H (lshift p i)); rewrite !col_mxEu.
    + by apply/forallP => i; move: (H (rshift n i)); rewrite !col_mxEd.
- move/andP => [/forallP H1  /forallP H2].
  apply/forallP =>i.
  rewrite !mxE.
  by case: splitP => [ k _ | k _ ]; [move: (H1 k) | move: (H2 k)].
Qed.

Lemma col_mx_lev0 (x : 'cV[R]_n) (v : 'cV[R]_p) :
  ((col_mx x v) <=m 0) = ((x <=m 0) && (v <=m 0)).
Proof.
by rewrite -{1}[0]vsubmxK col_mx_lev !linear0.
Qed.

Lemma col_mx_gev0 (y : 'cV[R]_n) (w : 'cV[R]_p) :
  (0 <=m (col_mx y w)) = ((0 <=m y) && (0 <=m w)).
Proof.
by rewrite -{1}[0]vsubmxK col_mx_lev !linear0.
Qed.

Lemma gev0_vsubmx (x : 'cV[R]_(n+p)) :
  (0 <=m x) = (0 <=m (usubmx x)) && (0 <=m (dsubmx x)).
Proof.
by rewrite -{1}[x]vsubmxK col_mx_gev0.
Qed.

Lemma lev0_vsubmx (x : 'cV[R]_(n+p)) :
  (0 >=m x) = (0 >=m (usubmx x)) && (0 >=m (dsubmx x)).
Proof.
by rewrite -{1}[x]vsubmxK col_mx_lev0.
Qed.

Lemma lev_sum I (r : seq I) (P : pred I) (F G : I -> 'cV[R]_n) :
    (forall i, P i -> (F i) <=m (G i)) ->
    (\sum_(i <- r | P i) F i) <=m (\sum_(i <- r | P i) G i).
Proof.
move => H.
apply/forallP => i.
- rewrite !summxE.
  apply: ler_sum => j Hj.
  + by move/(_ _ Hj)/forallP/(_ i): H.
Qed.

Lemma lev_scalar_mx (a b : R) : (a <= b) = ((a%:M) <=m (b%:M)).
Proof.
apply/idP/forallP => [? i| /(_ ord0)];
  by rewrite !mxE ?[i]ord1_eq0 /= !mulr1n.
Qed.

End ExtraOrder.

End Order.

Section LexOrder.

Variable R : realFieldType.

Section Core.

Variable n : nat.
Implicit Types x y u v : 'rV[R]_n.

Fixpoint leqlex_seq x y l :=
  match l with
  | [::] => true
  | i :: l' =>
    if x 0 i < y 0 i then true
    else if x 0 i == y 0 i then leqlex_seq x y l'
         else false
  end.

Definition leqlex x y := leqlex_seq x y (enum 'I_n).
Definition ltrlex x y := (x != y) && (leqlex x y).
Definition geqlex x y := leqlex y x.

Notation "<=lex" := leqlex: ring_scope.
Notation ">=lex" := geqlex: ring_scope.

Notation "<=lex x" := (geqlex x) (at level 0): ring_scope.
Notation ">=lex x" := (leqlex x) (at level 0): ring_scope.

Notation "x <=lex y" := (leqlex x y) (at level 0): ring_scope.
Notation "x >=lex y" := (y <=lex x) (only parsing, at level 0) : ring_scope.

Notation "x <lex y" := (ltrlex x y) (at level 0): ring_scope.
Notation "x >lex y" := (y <lex x) (only parsing, at level 0) : ring_scope.

Lemma order_preserving_equiv x y u v :
  (forall i, ((x 0 i < y 0 i) = (u 0 i < v 0 i)) /\ (x 0 i == y 0 i) = (u 0 i == v 0 i)) -> (x <=lex y) = (u <=lex v).
Proof.
move => H.
suff /(_ (enum 'I_n)): forall s, (leqlex_seq x y s = leqlex_seq u v s) by done.
move => s.
elim: s => [| i s' IH]; first by done.
- rewrite /= IH.
  by move/(_ i): H => [-> ->].
Qed.

Lemma lex_add2l x :
  {mono +%R x : y z / y <=lex z}.
Proof.
move => y z; symmetry.
apply: order_preserving_equiv => i.
move/(_ (y 0 i) (z 0 i)): (leW_mono (ler_add2l (x 0 i))) <-.
rewrite !mxE; split; first done.
symmetry; apply/inj_eq; exact: GRing.addrI.
Qed.

Lemma lex_add2r x :
  {mono +%R^~ x : y z / y <=lex z}.
Proof.
move => y z; symmetry.
apply: order_preserving_equiv => i.
move/(_ (y 0 i) (z 0 i)): (leW_mono (ler_add2r (x 0 i))) <-.
rewrite !mxE; split; first done.
symmetry; apply/(inj_eq (GRing.addIr _)).
Qed.

Lemma lex_pscalar (a : R) :
  0 < a -> {mono *:%R a : x y / x <=lex y }.
Proof.
move => Ha y z; symmetry.
apply: order_preserving_equiv => i.
rewrite !mxE.
move/(_ (y 0 i) (z 0 i)): (leW_mono (ler_pmul2l Ha)) <-.
split; first done.
symmetry; apply/inj_eq; apply/mulfI; exact: lt0r_neq0.
Qed.

Lemma subv_gelex0 x y :
  (0 <=lex (y - x)) = (x <=lex y).
Proof.
by move/(_ x y): (lex_add2r (-x)); rewrite addrN.
Qed.

Lemma lex_refl x :
  (x <=lex x).
Proof.
suff /(_ (enum 'I_n)): forall s, (leqlex_seq x x s) by done.
move => s.
elim: s => [| i s' IH]; first by done.
by rewrite /= IH ltxx eq_refl.
Qed.

Lemma oppv_gelex0 x :
  (0 <=lex -x) = (x <=lex 0).
Proof.
by move/(_ x 0): (lex_add2l (-x)); rewrite addNr addr0.
Qed.

Lemma scalar_neg_mul_lex_pos  a x :
  a < 0 -> (0 <=lex x) = ((a *: x) <=lex 0).
Proof.
move => Ha.
rewrite -oppr_gt0 in Ha.
by rewrite -(lex_pscalar Ha 0 x) scaler0 scaleNr oppv_gelex0.
Qed.

Lemma lex_antisym :
  antisymmetric (<=lex).
Proof.
move => x y H.
suff: forall s, (leqlex_seq x y s && leqlex_seq y x s)
                -> (forall i, i \in s -> x 0 i = y 0 i).
- move/(_ (enum 'I_n) H) => H'.
  apply/rowP => i.
  apply: (H' i); last by apply: mem_enum.
- move => s.
  elim: s => [ _ ? | i s' IH]; first by rewrite in_nil.
  rewrite /=.
  case: (ltrgtP (x 0 i) (y 0 i)); try by [rewrite andbF | rewrite andFb].
  + move => Hxyi; move/IH => IH' j.
    rewrite in_cons; move/orP; case.
    * by move/eqP ->.
    * apply: IH'.
Qed.

Lemma lex_trans :
  transitive (<=lex).
Proof.
move => y x z Hxy Hyz.
suff: forall s, leqlex_seq x y s -> leqlex_seq y z s
                -> leqlex_seq x z s
  by move/(_ (enum 'I_n))/(_ Hxy Hyz).
move => s.
elim: s => [ | i s' IH]; first by done.
rewrite /=.
case: (ltrgtP (x 0 i) (y 0 i)) (ltrgtP (y 0 i) (z 0 i))
  => [H [H' | H' | H'] | H [H' | H' | H'] | H [H' | H' | H']]; try by done.
- by move: (lt_trans H H') ->.
- by rewrite -H' ifT //.
- by rewrite H ifT //.
- by rewrite -H' H eq_refl ltxx; apply: IH.
Qed.

Lemma lex0_total :
  forall x, (0 <=lex x) || (x <=lex 0).
Proof.
move => x.
suff: forall s, (leqlex_seq 0 x s) || (leqlex_seq x 0 s)
  by move/(_ (enum 'I_n)).
move => s.
elim: s => [ | i s' IH /=]; first by done.
by rewrite mxE; case: (sgrP (x 0 i)).
Qed.

Lemma lex_total :
  total (<=lex).
Proof.
move => x y.
suff: (0 <=lex (y - x)) || ((y - x) <=lex 0)
  by rewrite subv_gelex0 -[X in _ || X](lex_add2r x) -addrA addNr add0r addr0.
by apply: lex0_total.
Qed.

Lemma lex_ltrW x y :
  (x <lex y) -> (x <=lex y).
Proof.
by move/andP => [_].
Qed.

Lemma lex_nnscalar a x y :
  0 <= a -> x <=lex y -> (a *: x) <=lex (a *: y).
Proof.
move => Ha Hxy.
case: (ltrgt0P a).
- by move/lex_pscalar ->.
- by move/(le_lt_trans Ha); rewrite ltxx.
- by move ->; rewrite !scale0r; apply: lex_refl.
Qed.

Lemma lex0_nnscalar a x :
  0 <= a -> 0 <=lex x -> 0 <=lex (a *: x).
Proof.
move => a_nn x_nn.
suff: (a *: 0) <=lex (a *: x).
- by rewrite linear0.
- exact: lex_nnscalar.
Qed.

Lemma lex_scalar_le0 a x :
  a <= 0 -> x <=lex 0 -> 0 <=lex (a *: x).
Proof.
move => a_np x_np.
suff: 0 <=lex ((-a) *: (-x)).
- by rewrite scaleNr linearN /= opprK.
- apply: lex0_nnscalar.
  + by rewrite oppr_ge0.
  + by rewrite oppv_gelex0.
Qed.

Lemma lex_negscalar a x y :
  a < 0 -> (x <=lex y) = ((a *: y) <=lex (a *: x)).
Proof.
move => Ha.
by rewrite -subv_gelex0 (scalar_neg_mul_lex_pos (y-x) Ha) scalerBr -oppv_gelex0 opprB subv_gelex0.
Qed.

Lemma lex_add x y z t :
  x <=lex y -> z <=lex t -> (x + z) <=lex (y + t).
Proof.
move => Hxy Hzt.
apply: (@lex_trans (x + t)).
- by rewrite lex_add2l.
- by rewrite lex_add2r.
Qed.

Lemma lex_subr_addr x y z :
  (x <=lex (y + z)) = ((x - y) <=lex z).
Proof.
apply/idP/idP.
- move => H.
  move: (lex_refl (-y)) => H'.
  move: (lex_add H H').
  by rewrite -addrA [z - y]addrC addrA addrN add0r.
- move => H.
  move: (lex_refl y) => H'.
  move: (lex_add H H').
  by rewrite -addrA addNr addr0 addrC.
Qed.

Lemma lex_subr_le0 x y :
  ((y - x) <=lex 0) = (y <=lex x).
Proof.
rewrite -lex_subr_addr.
by rewrite addr0.
Qed.

Lemma lex_ltrNge x y :
  (x <lex y) = ~~(y <=lex x).
Proof.
rewrite /ltrlex -[X in X = _]negbK negb_and.
apply/(congr1 negb); rewrite negbK.
case: (boolP (x <=lex y)).
- rewrite /= orbF => H.
  apply/idP/idP; first by move/eqP ->; apply: lex_refl.
  move => H'; move/andP/lex_antisym: (conj H H') ->; by apply: eq_refl.
- rewrite /= orbT.
  by move/orP: (lex_total x y); case; try by move ->.
Qed.

Lemma lex_nmulr_rlt0 a x :
  a < 0 -> ((a *: x) <lex (0) ) = ((0) <lex x).
Proof.
move => a_is_neg.
rewrite 2!lex_ltrNge.
by apply/idP/idP; apply: contra; rewrite (lex_negscalar x 0 a_is_neg) scaler0.
Qed.

Lemma lex_gtr_addl x y :
  ((x + y) <lex x) = (y <lex 0).
Proof.
rewrite 2!lex_ltrNge; apply: congr1.
by rewrite lex_subr_addr addrN.
Qed.

Lemma lex_ltr_addl x y :
  x <lex (x + y) = 0 <lex y.
Proof.
rewrite lex_ltrNge -[y]opprK -lex_subr_addr -lex_ltrNge addrC lex_gtr_addl.
by rewrite !lex_ltrNge oppv_gelex0 opprK.
Qed.

Lemma lex_le_ltr_trans x y z :
  (x <=lex y) -> (y <lex z) -> (x <lex z).
Proof.
move => Hxy Hyz.
apply/andP; split; last by exact: (lex_trans Hxy (lex_ltrW Hyz)).
apply: contraT; rewrite negbK; move/eqP => Hxz.
by move: Hyz; rewrite -Hxz lex_ltrNge Hxy.
Qed.

Lemma lex_ltr_le_trans x y z :
  (x <lex y) -> (y <=lex z) -> (x <lex z).
Proof.
move => Hxy Hyz.
apply/andP; split; last by exact: (lex_trans (lex_ltrW Hxy) Hyz).
apply: contraT; rewrite negbK; move/eqP => Hxz.
by move: Hxy; rewrite Hxz lex_ltrNge Hyz.
Qed.

Definition lex_min x y := if x <=lex y then x else y.

Lemma lex_minC x y :
  (lex_min x y) = (lex_min y x).
Proof.
rewrite /lex_min.
case: (boolP (x <=lex y)).
- case: ifP; last by done.
  by move => H H'; move/andP/lex_antisym: (conj H H') ->.
- by rewrite -lex_ltrNge; move/lex_ltrW => ?; rewrite ifT //.
Qed.

Lemma lex_ler_minl x y z :
  ((lex_min y z) <=lex x) = ((y <=lex x) || (z <=lex x)).
Proof.
rewrite /lex_min.
apply/idP/idP.
- case: ifP => [_ | _].
  + by move => ?; apply/orP; left.
  + by move => ?; apply/orP; right.
- move => H; case: ifP => [H' | H'].
  + move/orP: H; case; first by done.
    * by move/(lex_trans H').
  + move/negbT: H'; rewrite -lex_ltrNge; move/lex_ltrW.
    move/orP: H; case; last by done.
    * by move => H H'; apply: (lex_trans H' H).
Qed.

Lemma lex_min_l x y :
  x <=lex y -> lex_min x y = x.
Proof.
by apply: ifT.
Qed.

Lemma lex_min_r x y :
  y <=lex x -> lex_min x y = y.
Proof.
rewrite lex_minC; apply: lex_min_l.
Qed.

Fixpoint lex_min_seq S :=
  match S with
  | [::] => 0
  | [:: x] => x
  | x :: S' => lex_min x (lex_min_seq S')
  end.

Lemma lex_min_seq_ler S :
  forall i, i \in S -> (lex_min_seq S) <=lex i.
Proof.
elim: S => [ | x S' IH].
- by move => i; rewrite in_nil.
- move => i. rewrite in_cons. move/orP => [/eqP -> | H].
  + rewrite /=.
    case H': S'; first by apply: lex_refl.
    * rewrite lex_ler_minl; apply/orP; left; by apply: lex_refl.
  + rewrite /=; move: H.
    case H': S'; first by rewrite in_nil.
    * by rewrite -H'; move => Hi; rewrite lex_ler_minl; apply/orP; right; apply: IH.
Qed.

Lemma lex_min_seq_eq S :
  S != [::] -> has [pred i | lex_min_seq S == i] S.
Proof.
elim: S => [ | x S']; first by done.
- case: (altP (S' =P [::])) => [-> /= | HS /(_ is_true_true) IH _]; first by rewrite eq_refl.
  + apply/hasP.
    case: (boolP (x <=lex (lex_min_seq S'))) => [ H'' | ]. (* TODO: error if the space | ] is removed *)
    * exists x; first by rewrite mem_head.
      by rewrite /= lex_min_l //; case H: S'.
    * rewrite -lex_ltrNge => H''.
      move/hasP: IH => [i Hi /= /eqP Hi'].
      exists i; first by rewrite mem_behead.
      case H: S'; first by move: Hi; rewrite H in_nil.
      rewrite lex_min_r -H Hi' //.
      by rewrite -Hi'; apply: lex_ltrW.
Qed.

End Core.

Notation "<=m" := lev: ring_scope.
Notation ">=m x" := (lev x) (at level 0): ring_scope.
Notation "<=m x" := (lev^~ x) (at level 0): ring_scope.
Notation "x <=m y" := (lev x y) (at level 0): ring_scope.
Notation "x >=m y" := (y <=m x) (only parsing, at level 0) : ring_scope.

Notation "<=lex" := leqlex: ring_scope.
Notation ">=lex" := geqlex: ring_scope.

Notation "<=lex x" := (geqlex x) (at level 0): ring_scope.
Notation ">=lex x" := (leqlex x) (at level 0): ring_scope.

Notation "x <=lex y" := (leqlex x y) (at level 0): ring_scope.
Notation "x >=lex y" := (y <=lex x) (only parsing, at level 0) : ring_scope.

Notation "x <lex y" := (ltrlex x y) (at level 0): ring_scope.
Notation "x >lex y" := (y <lex x) (only parsing, at level 0) : ring_scope.

Section ExtraLexOrder.

Variable n : nat.
Implicit Types u v : 'rV[R]_n.

Lemma lex_ord0 (u v : 'rV[R]_(1+n)) :
  (u <=lex v) -> u 0 0 <= v 0 0.
Proof.
rewrite /leqlex.
case: {2}(enum _) (erefl (enum 'I_(1+n))) => [| x0 ? Henum];
  first by move/(congr1 size); rewrite size_enum_ord {1}add1n.
have <-: x0 = 0.
- apply/ord_inj.
  move/(congr1 (head 0))/(congr1 (@nat_of_ord _)): Henum.
  by rewrite -2!nth0 nth_enum_ord //.
rewrite Henum /=; case: ifP => [|_]; first by move/ltW.
- case: ifP => [|_]; last by done.
  + by move/eqP ->; rewrite lexx.
Qed.

Lemma leqlex_seq_cons S1 S2 u v :
  (leqlex_seq u v S1) && (leqlex_seq u v S2) -> leqlex_seq u v (S1 ++ S2).
Proof.
elim: S1 => [| i S1' IH]; first by rewrite /=.
rewrite /=.
case: ifP => [| Hi]; first by done.
case: ifP; done.
Qed.

Lemma leqlex_seq_lev S u v :
  [forall i in S, u 0 i <= v 0 i] -> leqlex_seq u v S.
Proof.
elim: S => [| i S' IH H]; first by done.
rewrite /=; case: ifP => [| /negbT Hi]; first by done.
rewrite -leNgt in Hi.
move/forallP/(_ i)/implyP/(_ (mem_head _ _)): (H) => Hi'.
move/andP: (conj Hi' Hi); rewrite lte_anti; move ->.
apply: IH.
apply/forallP => j; apply/implyP => Hj.
by move/forallP/(_ j): H; rewrite in_cons Hj orbT.
Qed.

Lemma leqlex_seq_head i S u v :
  (u 0 i < v 0 i) -> leqlex_seq u v (i :: S).
Proof.
by move => Hi; rewrite /=; rewrite ifT //.
Qed.

Lemma leqlex_seq_cons_head i S1 S2 u v :
  [forall j in S1, u 0 j <= v 0 j] && (u 0 i < v 0 i) ->
    leqlex_seq u v (S1 ++ (i :: S2)).
Proof.
move/andP => [/leqlex_seq_lev H /(leqlex_seq_head S2) H'].
by apply: leqlex_seq_cons; apply/andP; split.
Qed.

Lemma enum_ord_split i0 :
  enum 'I_n = (filter (fun j => (nat_of_ord j < nat_of_ord i0)%N) (enum 'I_n)) ++ (i0:: filter (fun j => (nat_of_ord i0 < nat_of_ord j < n)%N) (enum 'I_n)).
Proof.
apply: (inj_map (@ord_inj _)).
rewrite !val_enum_ord map_cat map_cons.
have ->: filter (fun j => (nat_of_ord i0 < nat_of_ord j < n)%N) (enum 'I_n) =
filter (preim (@nat_of_ord n) (fun j => (nat_of_ord i0 < j < n)%N)) (enum 'I_n)
  by apply: eq_filter => j; rewrite /=.
have ->: filter (fun j => (nat_of_ord j < nat_of_ord i0)%N) (enum 'I_n) =
filter (preim (@nat_of_ord n) (fun j => (j < nat_of_ord i0)%N)) (enum 'I_n)
  by apply: eq_filter => j; rewrite /=.
rewrite -2!filter_map !val_enum_ord.
have Hi0 : (nat_of_ord i0 < n)%N by apply: ltn_ord.
have ->: [seq j <- iota 0 n | (j < i0)%N] = iota 0 i0.
- have /eq_filter -> : (fun j => (j < i0)%N) =1 (fun j => j \in iota 0 i0).
  + by move => j; rewrite mem_iota leq0n /= add0n.
  symmetry; apply/(subseq_uniqP (iota_uniq _ _)).
  rewrite -{2}[n](subnKC (ltnW Hi0)).
  by rewrite iotaD add0n; apply: prefix_subseq.
have ->: [seq j <- iota 0 n | (i0 < j < n )%N] = iota (i0.+1) (n - (i0.+1)).
- have /eq_filter -> : (fun j => (i0 < j < n)%N) =1 (fun j => j \in iota (i0.+1) (n - (i0.+1))).
  + by move => j; rewrite mem_iota subnKC //.
  symmetry; apply/(subseq_uniqP (iota_uniq _ _)).
  rewrite -{4}[n](subnKC Hi0).
  by rewrite iotaD add0n; apply: suffix_subseq.
rewrite -{1}[n](subnKC (ltnW Hi0)) iotaD add0n.
apply/(congr1 (fun s => _ ++ s)).
suff ->: (n - i0 = 1 + (n - i0.+1))%N
  by rewrite iotaD addn1 /=.
- by rewrite -subn_gt0 in Hi0; rewrite add1n subnS prednK.
Qed.

Lemma lex_lev_strict u v i :
  [forall (j | (nat_of_ord j < nat_of_ord i)%N), u 0 j <= v 0 j] && (u 0 i < v 0 i) -> (u <lex v).
Proof.
move/andP => [H H'].
rewrite /ltrlex; apply/andP; split.
- move: H'. apply: contraL.
  by move/eqP/rowP/(_ i) ->; rewrite ltxx.
- rewrite /leqlex (enum_ord_split i).
  apply: leqlex_seq_cons_head; apply/andP; split; last by done.
  apply/forallP => j; apply/implyP; rewrite mem_filter => /andP [Hj _].
  by move/forallP/(_ j)/implyP/(_ Hj): H.
Qed.

Lemma lex_lev u v :
  (forall j, u 0 j <= v 0 j) -> (u <=lex v).
Proof.
move => u_lev_v.
by apply: leqlex_seq_lev; apply/forall_inP.
Qed.

Lemma sum_lex {p : nat} (v w : 'I_p -> 'rV[R]_n) (P : pred 'I_p):
  (forall i, P i -> (v i) <=lex (w i)) -> (\sum_(i | P i) v i) <=lex \sum_(i | P i) w i.
Proof.
move=> ?; rewrite (@big_ind2 _ _ (leqlex (n:=n))) ?lex_refl //.
exact/lex_add.
Qed.

Lemma lev_mul_lex {p: nat} (v : 'rV[R]_p) (M N : 'M[R]_(p,n)):
  0 <=m (v^T) -> (forall i, (row i M) <=lex (row i N)) -> (v *m M) <=lex (v *m N).
Proof.
move/gev0P=> v_ge0 le_MN.
rewrite !mulmx_sum_row; apply/sum_lex=> i _.
apply/lex_nnscalar; rewrite ?le_MN //.
by move: (v_ge0 i); rewrite mxE.
Qed.

Lemma ltlex_seqP (x y : 'rV_n) l i: i \in l -> x 0 i != y 0 i -> leqlex_seq x y l -> 
  (exists i l1 l2, [/\ l = l1 ++ i :: l2, (forall j, j \in l1 -> x 0 j = y 0 j) & x 0 i < y 0 i]).
Proof.
elim: l=> //= h t ih i_ht xy_n_i; case: ltrgtP=> //; first by (move=> ? _; exists h; exists [::]; exists t).
move=> xy_h_eq leqlex_xy.
have i_t: (i \in t).
- move: i_ht; rewrite in_cons; case/orP=> // /eqP contr. 
  by move: xy_h_eq xy_n_i; rewrite contr=> ->; rewrite eqxx.
case: (ih i_t xy_n_i leqlex_xy)=> i' [l1] [l2] [-> j_lt_i' xy_lt_i'].
exists i'; exists (h :: l1); exists l2; split=> //.
by move=> j; rewrite in_cons; case/orP=> [/eqP ->|/j_lt_i' ->].
Qed.

Lemma lex_lev_strictP (u v : 'rV_n): reflect
  (exists i, (forall j, (nat_of_ord j < nat_of_ord i)%N -> u 0 j = v 0 j) /\ u 0 i < v 0 i)
  (u <lex v).
Proof.
apply/(iffP idP).
- rewrite /ltrlex /leqlex; case/andP=> xy_n leqlex_xy.
  have [i [i_In uv_n_i]]: exists i, (i \in enum 'I_n) /\ (u 0 i != v 0 i).
  + move: xy_n; rewrite -subr_eq0; case/rV0Pn=> i.
    rewrite !mxE subr_eq0=> ?; exists i; split=> //.
    by rewrite mem_enum.
  case: (ltlex_seqP i_In uv_n_i leqlex_xy)=> j [l1] [l2] [In_eq j_lt_eq uv_lt_j].
  exists j; split=> //.
  move=> k kj_lt; apply/j_lt_eq.
  move/eqP: In_eq; rewrite (enum_ord_split j) eqseq_pivotl ?mem_filter ?ltnn //.
  by case/andP=> /eqP <- _; rewrite mem_filter kj_lt mem_enum.
- case=> i [eq_le_i lt_i]; apply/(lex_lev_strict (i:=i)); rewrite lt_i andbT.
  by apply/forallP=> j; apply/implyP=> j_lt_i; rewrite (eq_le_i j j_lt_i) lexx.
Qed.

Lemma lex_eqOlt (u v : 'rV[R]_n) : (u <=lex v) = (u == v) || (u <lex v).
Proof. by rewrite /ltrlex; case/boolP: (u == v)=> //= /eqP ->; rewrite lex_refl. Qed.

Lemma lex_ltr_addlt (a b c d : 'rV[R]_n): a <=lex b -> c <lex d ->
  (a + c) <lex (b + d).
Proof.
rewrite lex_eqOlt; case/orP.
- move/eqP=> -> /andP [+ cd_lex]; rewrite /ltrlex (lex_add2l b) cd_lex andbT.
  apply/contra_neq=> ?; exact/(addrI b).
- case/lex_lev_strictP=> i_ab [j_ab_eq i_ab_lt] /lex_lev_strictP [i_cd] [j_cd_eq i_cd_lt].
  have min_abcd: (minn i_ab i_cd < n)%N by apply/(leq_ltn_trans (n:=i_ab))=> //; exact/geq_minl.
  apply/lex_lev_strictP; exists (Ordinal min_abcd); split.
  + by move=> /= j; rewrite ltn_min=> /andP [??]; rewrite !mxE j_ab_eq ?j_cd_eq.
  + rewrite !mxE.
    have [h_eq | min_ab | min_cd]: [\/ i_ab = i_cd, (i_ab < i_cd)%N | (i_ab > i_cd)%N] by
      case: ltngtP=> ?; [exact/Or32 | exact/Or33 | exact/Or31/val_inj].
    * have ->: (Ordinal min_abcd = i_ab) by apply/val_inj; rewrite /= h_eq minnn.
      by apply/ltr_add=> //; rewrite h_eq.
    * have ->: (Ordinal min_abcd = i_ab) by exact/val_inj/minn_idPl/ltnW.
      by rewrite j_cd_eq //; apply/ltr_le_add.
    * have ->: (Ordinal min_abcd = i_cd) by exact/val_inj/minn_idPr/ltnW.
      by rewrite j_ab_eq //; apply/ler_lt_add.
Qed.

Lemma ltrlex_sum {p : nat} (A B : 'I_p -> 'rV[R]_n):
  (forall i, (A i) <=lex (B i)) -> (exists j, (A j) <lex (B j)) ->
  (\sum_i A i) <lex (\sum_i B i).
Proof.
move=> AB_lex [j ABj_ltr].
rewrite !(bigD1_seq j) ?index_enum_uniq ?mem_index_enum //=.
rewrite addrC [X in _ <lex X]addrC; apply/lex_ltr_addlt=> //.
apply/sum_lex=> i _; exact/AB_lex.
Qed.


Section IndLexOrder.

Fixpoint ind_lexleq (a b : seq R) := 
  match a, b with
  |[::], [::]=> true
  |ha::ta, hb::tb=> if ha < hb then true else
                    if ha == hb then ind_lexleq ta tb else false 
  |_, _=> false
  end.

Lemma lex_foo (v w : 'rV[R]_n):
  v <=lex w =
  ind_lexleq [seq (v 0 i) | i <- (enum 'I_n)] [seq (w 0 i) | i <- (enum 'I_n)].
Proof.
rewrite /leqlex.
elim: (enum 'I_n)=> //= h t ->.
by case: ifP=> //.
Qed.

End IndLexOrder.

End ExtraLexOrder.

End LexOrder.

Notation "<=m" := lev: ring_scope.
Notation ">=m x" := (lev x) (at level 0): ring_scope.
Notation "<=m x" := (lev^~ x) (at level 0): ring_scope.
Notation "x <=m y" := (lev x y) (at level 0): ring_scope.
Notation "x >=m y" := (y <=m x) (only parsing, at level 0) : ring_scope.

Notation "<=lex" := leqlex: ring_scope.
Notation ">=lex" := geqlex: ring_scope.

Notation "<=lex x" := (geqlex x) (at level 0): ring_scope.
Notation ">=lex x" := (leqlex x) (at level 0): ring_scope.

Notation "x <=lex y" := (leqlex x y) (at level 0): ring_scope.
Notation "x >=lex y" := (y <=lex x) (only parsing, at level 0) : ring_scope.

Notation "x <lex y" := (ltrlex x y) (at level 0): ring_scope.
Notation "x >lex y" := (y <lex x) (only parsing, at level 0) : ring_scope.
