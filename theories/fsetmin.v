(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Import Order.Theory Order.TTheory Num.Theory.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.
Local Open Scope fset.

(* -------------------------------------------------------------------- *)
Section FSetMin.
Context (R : realFieldType).

Lemma fset_min_r (S : {fset R}) : S <> fset0 ->
  { x : R | x \in S & (forall y, y \in S -> x <= y) }.
Proof.
elim/finSet_rect: S => S ih /eqP /fset0Pn => h.
have := xchooseP h; move: {h} (xchoose h) => a.
move=> /[dup] aS /fsetD1K /esym SE.
case: ((S `\ a) =P fset0) => [h|{}/ih ih].
- by exists a => // y; rewrite SE h fsetU0 in_fset1 => /eqP->.
case: ih; rewrite ?fproperD1 // => x x_SDa ih.
exists (Num.min a x); first case: lerP => // _.
- by move: x_SDa; rewrite !inE => /andP[].
- move=> y yS; rewrite le_minl; case: lerP => //=.
  move/lt_eqF=> /negbT ne_ya; apply: ih.
  by rewrite !inE ne_ya yS.
Qed.

Definition fset_min (x0 : R) (S : {fset R}) :=
  if S =P fset0 is ReflectF h then
    tag (@fset_min_r _ h)
  else x0.

Lemma fset_min0 x0 : fset_min x0 fset0 = x0.
Proof. by rewrite /fset_min; case: eqP. Qed.

Lemma fset_minP x0 S : S != fset0 ->
  [/\ fset_min x0 S \in S & forall y, y \in S -> fset_min x0 S <= y].
Proof.
move/eqP=> nz_S; rewrite /fset_min; case: eqP => //.
by move=> {}nz_S; case: fset_min_r.
Qed.
End FSetMin.
Section FSetMax.
Context (R : realFieldType).

Definition fset_max (x0 : R) (S : {fset R}) :=
  if S =P fset0 is ReflectF _ then
  - (fset_min x0 [fset -x | x in S]%fset) else x0.

Lemma fset_maxP x0 S : S != fset0 ->
  [/\ fset_max x0 S \in S & forall y, y \in S -> y <= fset_max x0 S].
Proof.
rewrite /fset_max; case: eqP=> //= h _.
have S'0: [fset -x | x in S] != fset0 by
  case/eqP/fset0Pn: h=> x xS; apply/fset0Pn; exists (-x); exact/in_imfset.
case: (fset_minP x0 S'0)=> /imfsetP /= [max] maxS ->; rewrite GRing.opprK maxS.
move=> max_def; split=> // y yS.
move: (max_def (-y)); rewrite in_imfset //=; move/(_ isT).
by rewrite ler_oppl GRing.opprK.
Qed.

Lemma fset_max0 x0: fset_max x0 fset0 = x0.
Proof. by rewrite /fset_max; case: eqP. Qed.

End FSetMax.

