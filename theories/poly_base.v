(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp.
From mathcomp Require Import matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix.
Require Import xorder vector_order row_submx.
Require Import hpolyhedron affine barycenter lrel polyhedron.
From mathcomp.bigenough Require Import bigenough.
Import BigEnough.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope polyh_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "\pdim P" (at level 10, P at level 8, format "\pdim  P").

(* -------------------------------------------------------------------- *)
Section PointedType.
Context (R : realFieldType) (n : nat).

Record pointedPoly : predArgType :=
  Pointed { pointed_poly :> 'poly[R]_n; _ : pointed pointed_poly }.

Canonical pointedPoly_subType :=
  Eval hnf in [subType for pointed_poly].
Definition pointedPoly_eqMixin :=
  Eval hnf in [eqMixin of pointedPoly by <:].
Canonical pointedPoly_eqType :=
  Eval hnf in EqType pointedPoly pointedPoly_eqMixin.
Definition pointedPoly_choiceMixin :=
  Eval hnf in [choiceMixin of pointedPoly by <:].
Canonical pointedPoly_choiceType :=
  Eval hnf in ChoiceType pointedPoly pointedPoly_choiceMixin.

Definition pointedPoly_of of phant R := pointedPoly.
Identity Coercion type_pointedPoly_of : pointedPoly_of >-> pointedPoly.
End PointedType.

Bind Scope ring_scope with pointedPoly_of.
Bind Scope ring_scope with pointedPoly.

Reserved Notation "''pointed[' R ]_ n"
  (at level 8, n at level 2, format "''pointed[' R ]_ n").

Notation "''pointed[' R ]_ n" := (@pointedPoly_of _ n (Phant R)).

Section PointedTheory.
Context {R : realFieldType} (n : nat).

Canonical pointedPoly_of_subType :=
  Eval hnf in [subType of 'pointed[R]_n].
Canonical pointedPoly_of_eqType :=
  Eval hnf in [eqType of 'pointed[R]_n].
Canonical pointedPoly_of_choiceType :=
  Eval hnf in [choiceType of 'pointed[R]_n].

Lemma pointed_slice (P : 'pointed[R]_n) e : pointed (slice e P).
Proof. by apply/(pointedS _ (valP P))/le_slice. Qed.
Canonical pointed_slice_pointed (P : 'pointed[R]_n) e :=
  Pointed (pointed_slice P e).

End PointedTheory.

(* -------------------------------------------------------------------- *)
Section CompactType.
Context (R : realFieldType) (n : nat).

Record compactPoly : predArgType :=
  mkCompact { compact_poly :> 'pointed[R]_n; _ : compact compact_poly }.

Canonical compactPoly_subType :=
  Eval hnf in [subType for compact_poly].
Definition compactPoly_eqMixin :=
  Eval hnf in [eqMixin of compactPoly by <:].
Canonical compactPoly_eqType :=
  Eval hnf in EqType compactPoly compactPoly_eqMixin.
Definition compactPoly_choiceMixin :=
  Eval hnf in [choiceMixin of compactPoly by <:].
Canonical compactPoly_choiceType :=
  Eval hnf in ChoiceType compactPoly compactPoly_choiceMixin.

Definition compactPoly_of of phant R := compactPoly.
Identity Coercion type_compactPoly_of : compactPoly_of >-> compactPoly.
End CompactType.

Bind Scope ring_scope with compactPoly_of.
Bind Scope ring_scope with compactPoly.

Reserved Notation "''compact[' R ]_ n"
  (at level 8, n at level 2, format "''compact[' R ]_ n").

Notation "''compact[' R ]_ n" := (@compactPoly_of _ n (Phant R)).

Section CompactTheory.
Context {R : realFieldType} (n : nat).

Canonical compactPoly_of_subType :=
  Eval hnf in [subType of 'compact[R]_n].
Canonical compactPoly_of_eqType :=
  Eval hnf in [eqType of 'compact[R]_n].
Canonical compactPoly_of_choiceType :=
  Eval hnf in [choiceType of 'compact[R]_n].

End CompactTheory.

(* -------------------------------------------------------------------- *)
Section CompactPointed.
Context (R : realFieldType) (n : nat) .

Definition Compact (P : 'poly[R]_n) (cp : compact P) :=
  @mkCompact R n (Pointed (compact_pointed cp)) cp.

Lemma compact_slice (P : 'poly[R]_n) e : compact P -> compact (slice e P).
Proof. by move=> P_compact; apply/(subset_compact P_compact)/le_slice. Qed.
Canonical compact_slice_compact (P : 'compact[R]_n) e := Compact (compact_slice e (valP P)).
End CompactPointed.

(* -------------------------------------------------------------------- *)
Section PolyPO.
Context (R : realFieldType) (n : nat).

Implicit Types P Q : 'poly[R]_n.

Definition pointedPoly_porderMixin :=
  [porderMixin of @pointedPoly R n by <:].
Canonical pointedPoly_porderType :=
  Eval hnf in POrderType ring_display (@pointedPoly R n) pointedPoly_porderMixin.

Definition pointedPoly_of_porderType :=
  Eval hnf in [porderType of 'pointed[R]_n].
End PolyPO.

(* -------------------------------------------------------------------- *)
Section PolyBase.

Variable (R : realFieldType) (n : nat).

Section FixedBase.

Definition has_base (base : base_t[R,n]) (P : 'poly[R]_n) :=
  (P `>` [poly0]) ==>
 [exists I : {fsubset base}, P == 'P^=(base; I)].

Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : polyh_scope.

Context {base : base_t[R,n]}.

Lemma has_baseP {P : 'poly[R]_n} :
  reflect (P `>` [poly0] -> exists I : {fsubset base}, P = 'P^=(base; I))
          [P has \base base].
Proof.
by apply/(iffP implyP) => [H /H /exists_eqP [I ->]| H /H [I ->]];
  [|apply/exists_eqP]; exists I.
Qed.

Inductive poly_base :=
  PolyBase { pval :> 'poly[R]_n ; _ : [pval has \base base]}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin :=
  Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType :=
  Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin :=
  Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType :=
  Eval hnf in ChoiceType poly_base poly_base_choiceMixin.

(*
Definition poly_base_porderMixin := [porderMixin of poly_base by <:].
Canonical poly_base_porderType :=
  Eval hnf in POrderType polyh_display poly_base poly_base_porderMixin.
*)

Lemma pvalP (P : poly_base) : [pval P has \base base].
Proof.
by apply/valP.
Qed.

Lemma pval_inj : injective pval.
Proof.
by apply/val_inj.
Qed.

Lemma poly0_baseP : [ [poly0] has \base base].
Proof.
by rewrite /has_base ltxx.
Qed.
Canonical poly0_base := PolyBase poly0_baseP.

End FixedBase.

Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : polyh_scope.
Notation "'{poly'  base '}'" := (@poly_base base) : polyh_scope.
Definition poly_base_of base (x : {poly base}) & (phantom 'poly[R]_n x) : {poly base} := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : polyh_scope.

Lemma polyEq_baseP base I :
  (I `<=` base)%fset -> [('P^=(base; I)) has \base base].
Proof.
move => Isub.
by apply/implyP => _; apply/exists_eqP => /=; exists (I %:fsub).
Qed.

Canonical polyEq_base base I (H : expose (I `<=` base)%fset) := PolyBase (polyEq_baseP H).

Variable base : base_t[R,n].

Variant poly_base_spec (P : {poly base}) : Prop :=
| PolyBase0 of (P = ([poly0])%:poly_base) : poly_base_spec P
| PolyBaseN0 (I : {fsubset base}) of
             (P = 'P^=(base; I)%:poly_base /\ P `>` [poly0]) : poly_base_spec P.

Lemma poly_baseP (P : {poly base}) : poly_base_spec P.
Proof.
case: (emptyP P) => [/pval_inj -> | P_prop0]; first by constructor.
move/implyP/(_ P_prop0)/exists_eqP: (pvalP P) => [I ?].
constructor 2 with I.
split; [exact: val_inj | done].
Qed.

Lemma poly_base_subset (P : {poly base}) :
  P `<=` 'P(base) :> 'poly_n.
Proof.
case/poly_baseP : (P) => [->| I [-> _]];
  [ exact: le0x | exact: polyEq_antimono0].
Qed.

Lemma poly_base_subset_hs (P : {poly base}) e :
  e \in base -> pval P `<=` [hs e].
Proof.
move => ?; apply/(le_trans (poly_base_subset _)).
exact: poly_of_base_subset_hs.
Qed.

Definition set_of_poly_base (P : {poly base}) : option {fsubset base} :=
  if @idP (P `>` [poly0]) is ReflectT H then
    let I := xchoose (existsP (implyP (pvalP P) H)) in
    Some I
  else
    None.

Definition set_of_poly_base_pinv (I : option {fsubset base}) : {poly base} :=
  match I with
  | Some I' =>
    let P := 'P^=(base; I')%:poly_base in
    if set_of_poly_base P == Some I' then P else [poly0]%:poly_base
  | None => [poly0]%:poly_base
  end.

Lemma set_of_poly_baseK :
  cancel set_of_poly_base set_of_poly_base_pinv.
Proof.
move => P.
move: (erefl (set_of_poly_base P)).
rewrite {2 3}/set_of_poly_base.
case: {-}_/idP => [P_prop0 /=| /negP h _].
- set prop := existsP _; set I := xchoose _; set Q := 'P^=(base; I)%:poly_base.
  suff ->: P = Q.
  + by move => eq; rewrite /set_of_poly_base_pinv /Q ifT ?eq.
  + by apply/val_inj => /=; move/eqP: (xchooseP prop) ->.
- rewrite lt0x negbK in h.
  by rewrite /=; apply/val_inj => /=; move/eqP: h ->.
Qed.

Definition poly_base_countMixin := CanCountMixin set_of_poly_baseK.
Canonical poly_base_countType := Eval hnf in CountType {poly base} poly_base_countMixin.
Definition poly_base_finMixin := CanFinMixin set_of_poly_baseK.
Canonical poly_base_finType := Eval hnf in FinType {poly base} poly_base_finMixin.
Canonical poly_base_subFinType := [subFinType of {poly base}].

Lemma poly_of_baseP :
  ['P(base) has \base base].
Proof.
suff ->: 'P(base) = 'P^=(base; fset0)%:poly_base by exact: pvalP.
by rewrite /= polyEq0.
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

Lemma polyI_baseP (P Q : {poly base}) & (phantom _ P) & (phantom _ Q):
  [pval P `&` pval Q has \base base].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= meet0x (valP ([poly0]%:poly_base)).
case: (poly_baseP Q) => [->| I' [-> _]]; first by rewrite /= meetx0 (valP ([poly0]%:poly_base)).
apply/has_baseP => _; exists (I `|` I')%fset%:fsub; by rewrite polyEq_polyI.
Qed.
Canonical polyI_base P Q := PolyBase (polyI_baseP (Phantom _ P) (Phantom _ Q)).

Lemma slice_baseP (e : lrel) (P : {poly base}) :
  [(slice e P) has \base (e +|` base)].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= slice0 (valP ([poly0]%:poly_base)).
apply/has_baseP => _.
by exists (e +|` I)%:fsub; rewrite slice_polyEq.
Qed.
Canonical slice_base e P := PolyBase (slice_baseP e P).

Lemma argmin_baseP (P : {poly base}) c :
  [(argmin P c) has \base base].
Proof.
(* we first suppose that flat_prop holds, ie this is the situation in which
 * P (here quantified as Q) would play the role of the base *)
suff flat_prop: forall base0, bounded ('P(base0) : 'poly[R]_n) c -> [(argmin ('P(base0) : 'poly[R]_n) c) has \base base0].
- apply/has_baseP; rewrite -bounded_argminN0.
  case/poly_baseP : (P) => [->| I [-> _]]; first by rewrite bounded_poly0.
  rewrite /= (polyEq_flatten _) => bounded_PI.
  move/flat_prop/has_baseP: (bounded_PI); rewrite -bounded_argminN0.
  move => /(_ bounded_PI) => [[J] ->].
  by move: (polyEq_of_polyEq J)
    => [K] ->; exists K.
- (* now this is the classic proof of Schrijver *)
  move => base0 c_bounded.
  move: (dual_opt_sol c_bounded) => [w w_ge0 w_comb].
  apply/has_baseP; exists (finsupp w)%:fsub.
  move: (opt_point c_bounded) => [x x_in_P0 c_x_eq_opt_val].
  have: x \in [hp (combine w)].
  - by rewrite in_hp w_comb /=; apply/eqP.
  move/(compl_slack_cond w_ge0 x_in_P0) => x_in_P0I.
  have ->: c = (combine w).1 by rewrite w_comb.
  apply/dual_sol_argmin; try by done.
  by apply/proper0P; exists x.
Qed.
Canonical argmin_base (P : {poly base}) c := PolyBase (argmin_baseP P c).

Lemma affine_base : [[affine << base >>]%:PH has \base base].
Proof.
by rewrite -polyEqT_affine pvalP.
Qed.
Canonical affine_baseP := PolyBase affine_base.

End PolyBase.

Notation "'{poly'  base '}'" := (@poly_base _ _ base) : polyh_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : polyh_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : polyh_scope.

Module BaseQuotient.
Section BaseQuotient.

Variable (R : realFieldType) (n : nat).

Lemma poly_has_base P :
  exists (x : { base : base_t[R,n] & {poly base}}),
    P == (tagged x) :> 'poly_n.
Proof.
move: (is_poly_of_base P) => [base /eqP ->].
by exists (Tagged _ ('P(base)%:poly_base : {poly base})) => /=.
Qed.

Definition of_poly (P : 'poly[R]_n) :=
  xchoose (poly_has_base P).
Definition to_poly (x : { base : base_t[R,n] & {poly base} })
  := pval (tagged x).

Lemma of_polyK : cancel of_poly to_poly.
Proof.
move => P; rewrite /of_poly; symmetry; apply/eqP.
exact: (xchooseP (poly_has_base _)).
Qed.

Definition base_quot_class := QuotClass of_polyK.

Canonical base_quot := QuotType 'poly[R]_n base_quot_class.

Definition repr_base (P : 'poly[R]_n) := (tag (repr P)).
Definition repr_poly_base (P : 'poly[R]_n) : {poly (repr_base P)} := tagged (repr P).

Lemma repr_baseP P : [P has \base (repr_base P)].
Proof.
rewrite -{-1}[P]reprK unlock; exact: pvalP.
Qed.
(*Canonical poly_base_repr_baseP (P : 'poly[R]_n) := PolyBase (repr_baseP P).*)

End BaseQuotient.
Module Import Exports.
Canonical base_quot.
(*Canonical poly_base_repr_baseP.*)
End Exports.
End BaseQuotient.

Export BaseQuotient.Exports.

Notation "\repr_base P" := (BaseQuotient.repr_base P) (at level 40).
Notation "\repr P" := (BaseQuotient.repr_poly_base P) (at level 40).

Section BaseQuotientAux.

Variable (R : realFieldType) (n : nat).

Lemma reprK (P : 'poly[R]_n) : \repr P = P :> 'poly_n.
Proof.
by rewrite -[P in RHS]reprK [in RHS]unlock.
Qed.

Lemma polybW (Pt : 'poly[R]_n -> Prop) :
  (forall (base : base_t[R,n]) (Q : {poly base}), Pt Q) -> (forall P : 'poly[R]_n, Pt P).
Proof.
by move => ? P; rewrite -[P]reprK.
Qed.

Lemma non_redundant_baseW (Pt : 'poly[R]_n -> Prop) :
  (forall (base : base_t[R,n]), non_redundant_base base -> Pt 'P(base)%:poly_base)
    -> (forall P : 'poly[R]_n, Pt P).
Proof.
move => h P.
move: (is_poly_of_base P) => [base /eqP ->].
rewrite -poly_of_non_redundant_base.
have ->: 'P(mk_non_redundant_base base) = 'P(mk_non_redundant_base base)%:poly_base by [].
by apply/h/mk_non_redundant_baseP.
Qed.

End BaseQuotientAux.

Section PolyBaseFace.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition pb_face_set (P : {poly base}) : {set {poly base}} :=
  [set Q : {poly base} | Q `<=` P :> 'poly_n].

Notation "\face_set P" := (pb_face_set P) (at level 40).

CoInductive pb_face_spec (P : {poly base}) : {poly base} -> Prop :=
| PbEmptyFace : pb_face_spec P ([poly0])%:poly_base
| PbArgMin c of (bounded P c) : pb_face_spec P (argmin P c)%:poly_base.

Lemma pb_faceP (P Q : {poly base}) :
  Q \in \face_set P -> pb_face_spec P Q.
Proof.
case: (emptyP ('P(base) : 'poly[R]_n))
  => [base_eq0 | base_prop0].
- suff ->: (P = ([poly0]%:poly_base)).
  + rewrite inE lex0 => /eqP.
    move/val_inj ->; constructor.
    move: (poly_base_subset P); rewrite base_eq0 //=.
      by rewrite lex0 => /eqP/val_inj.
- case: (poly_baseP Q) => [-> | ]; first constructor.
  move => I [Q_eq Q_prop0].
  rewrite inE; move => Q_sub_P.
  pose w : {conic lrel ~> R} := (fconicu I).
  pose c := (combine w).1.
  have c_bounded : bounded ('P(base) : 'poly[R]_n) c.
  + apply: dual_sol_bounded => //; rewrite finsupp_fconicu; exact: fsubset_subP.
  have c_bounded_P : (bounded P c).
  + apply: (bounded_mono1 c_bounded); apply/andP; split;
      [ exact: (lt_le_trans Q_prop0) | exact: poly_base_subset ].
  have c_argmin: argmin 'P(base) c = Q.
  + rewrite Q_eq in Q_prop0 *.
    rewrite dual_sol_argmin /=; rewrite ?/w ?finsupp_fconicu //.
    exact: fsubset_subP.
  suff <- : (argmin P c)%:poly_base = Q by constructor.
  apply: val_inj => /=. rewrite -c_argmin.
  apply/subset_argmin; first by done.
  apply/andP; split; [ by rewrite c_argmin | exact: poly_base_subset ].
Qed.

Lemma argmin_pb_face_set (P : {poly base}) c:
  (argmin P c)%:poly_base \in \face_set P.
Proof.
by rewrite inE argmin_subset.
Qed.

End PolyBaseFace.

Notation "\face_set P" := (pb_face_set P) (at level 40).

Section Face.
Variable (R : realFieldType) (n : nat).

Definition face_set (P : 'poly[R]_n) :=
  [fset pval x | x in \face_set (\repr P)]%fset.

Lemma face_set_morph (base : base_t[R,n]) (P : {poly base}) :
  face_set P = [fset pval x | x in \face_set P]%fset.
Proof.
suff H: forall (base1 base2 : base_t[R,n]) (P1 : {poly base1}) (P2 : {poly base2}),
    P1 = P2 :> 'poly_n ->
    ([fset pval x | x in \face_set P1] `<=` [fset pval x | x in \face_set P2])%fset.
- by apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/H; rewrite reprK.
- move => base1 base2 P1 P2 eq_P12.
  apply/fsubsetP => F /imfsetP [F' /= F'_in ->].
  case/pb_faceP : F'_in.
  + apply/imfsetP; exists ([poly0]%:poly_base) => //=.
    rewrite inE; exact: le0x.
  + move => c c_bounded.
    apply/imfsetP; exists ((argmin P2 c)%:poly_base) => /=.
    rewrite inE; exact: argmin_subset.
    by rewrite eq_P12.
Qed.

Lemma face_set_has_base (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) :
  Q \in face_set P -> [Q has \base base].
Proof.
rewrite face_set_morph => /imfsetP [{}Q _ ->].
exact: pvalP.
Qed.

(*Canonical face_set_has_baseP (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) (H : expose (Q \in face_set P)) :=
  PolyBase (face_set_has_base H).*)

(*Parameter (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n).
Hypothesis H : (Q \in face_set P).
Check (Q%:poly_base) : {poly base}.*)

Lemma face_setE (base : base_t[R,n]) (P : {poly base}) :
    (forall F : {poly base}, (pval F \in face_set P) = (F `<=` P :> 'poly_n))
    * (forall F : 'poly[R]_n, forall H : [F has \base base], (F \in face_set P) = (F `<=` P)).
Proof.
set X := (X in (X * _)%type).
suff hX: X.
- split => //.
  move => F F_base; by have ->: F = PolyBase F_base.
- move => F; rewrite face_set_morph.
  apply/imfsetP/idP => [[{}F H /=->]| F_sub_P]; first by rewrite inE in H.
  by exists F; rewrite ?inE.
Qed.

Lemma face_set_self (P : 'poly[R]_n) : P \in (face_set P).
Proof.
elim/polybW: P => base P.
rewrite face_setE; exact: lexx.
Qed.

(*Lemma in_face_setP (base : base_t[R,n]) (F : 'poly[R]_n) (P : {poly base}) & (F \in face_set P) :
  F%:poly_base `<=` P.
Proof.
by rewrite -face_setE.
Qed.*)

Variant face_set_spec (base : base_t[R, n]) (P : {poly base}) : 'poly[R]_n -> Type :=
| FaceSetSpec (Q : {poly base}) of (Q `<=` P :> 'poly_n) : face_set_spec P Q.

Lemma face_setP (base : base_t[R, n]) (P : {poly base}) (Q : 'poly[R]_n) :
  (Q \in face_set P) -> @face_set_spec base P Q.
Proof.
move => Q_face_P.
have Q_eq : Q = (PolyBase (face_set_has_base Q_face_P)) by [].
move: (Q_face_P); rewrite Q_eq => Q_face_P'.
constructor; by rewrite face_setE in Q_face_P'.
Qed.

Lemma face_set_of_face (P Q : 'poly[R]_n) :
  Q \in face_set P -> face_set Q = [fset Q' in (face_set P) | (Q' `<=` Q)%PH]%fset.
Proof.
elim/polybW: P => base P.
case/face_setP => {}Q Q_sub_P.
apply/fsetP => Q'; apply/idP/idP.
- case/face_setP => {}Q' Q'_sub_Q.
  apply/imfsetP; exists (pval Q') => //.
  rewrite inE face_setE Q'_sub_Q andbT.
  exact: (le_trans Q'_sub_Q).
- rewrite mem_imfset => //= /andP[].
  case/face_setP => {}Q' _.
  by rewrite face_setE.
Qed.

Corollary face_setS (P Q : 'poly[R]_n) :
  Q \in face_set P -> (face_set Q `<=` face_set P)%fset.
Proof.
move/face_set_of_face ->; apply/fsubsetP => Q'.
by rewrite mem_imfset // => /andP[].
Qed.

Lemma face_subset (F : 'poly[R]_n) (P : 'poly[R]_n)  :
  F \in face_set P -> F `<=` P.
Proof.
elim/polybW: P => base P.
by case/face_setP => ?.
Qed.

Lemma poly0_face_set (P : 'poly[R]_n) : [poly0] \in face_set P.
Proof.
elim/polybW: P => base P.
by rewrite face_setE ?le0x ?pvalP.
Qed.

Lemma face_set0 : face_set ([poly0]) = [fset [poly0]]%fset.
Proof.
apply/fsetP => P; rewrite !inE /=; apply/idP/idP.
- by move/face_subset; rewrite lex0.
- move/eqP ->; exact: face_set_self.
Qed.

Lemma face_set_polyI (P F F' : 'poly[R]_n) :
  F \in face_set P -> F' \in face_set P -> F `&` F' \in face_set P.
Proof.
elim/polybW: P => base P.
case/face_setP => {}F F_sub_P.
case/face_setP => {}F' F'_sub_P.
by rewrite face_setE leIxl.
Qed.

Lemma argmin_in_face_set (P : 'poly[R]_n) c :
  bounded P c -> argmin P c \in face_set P.
Proof.
elim/polybW: P => base P c_bounded.
by rewrite face_setE ?pvalP ?argmin_subset.
Qed.

Lemma face_argmin (P Q : 'poly[R]_n) :
  Q \in face_set P -> Q `>` ([poly0]) -> exists2 c, bounded P c & Q = argmin P c.
Proof.
rewrite /face_set; move/imfsetP => [{}Q /= Q_face ->].
by case: (pb_faceP Q_face) => [| c]; rewrite /= ?reprK ?ltxx //; exists c.
Qed.

Lemma face_compact (P Q : 'poly[R]_n) :
  compact P -> Q \in face_set P -> compact Q.
Proof.
by move => ? /face_subset; apply/subset_compact.
Qed.

Lemma face_pointed (P Q : 'poly[R]_n) :
  pointed P -> Q \in face_set P -> pointed Q.
Proof.
move => P_pointed.
by move/face_subset/pointedS/(_ P_pointed).
Qed.

End Face.

(* -------------------------------------------------------------------- *)
Section FaceSetOrder.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Definition face_set_porderMixin :=
  Eval hnf in [porderMixin of face_set P by <:].
Canonical face_set_porderType :=
  Eval hnf in POrderType ring_display (face_set P) face_set_porderMixin.
Canonical face_set_finPOrderType :=
  Eval hnf in [finPOrderType of face_set P].
End FaceSetOrder.

(* -------------------------------------------------------------------- *)
Section FacesSetOrderTheory.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma leEfaces (F1 F2 : face_set P) :
  (F1 <= F2) = (val F1 `<=` val F2 :> 'poly[R]_n).
Proof. by []. Qed.

Lemma ltEfaces (F1 F2 : face_set P) :
  (F1 < F2) = (val F1 `<` val F2 :> 'poly[R]_n).
Proof. by []. Qed.

Definition lteEfaces := (leEfaces, ltEfaces).
End FacesSetOrderTheory.

(* -------------------------------------------------------------------- *)
Import MeetBTFinMixin.Exports.

Section FacesLattice.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma poly0_fp : [poly0] \in face_set P.
Proof. by apply: poly0_face_set. Qed.

Lemma polyP_fp : P \in face_set P.
Proof. by apply: face_set_self. Qed.

Let fp0 := [`poly0_fp]%fset.
Let fp1 := [`polyP_fp]%fset.

Definition fpI (F1 F2 : face_set P) : face_set P :=
  [`face_set_polyI (valP F1) (valP F2)]%fset.

Lemma fpIC : commutative fpI.
Proof.
move=> F1 F2; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbC.
Qed.

Lemma fp_le_def (F1 F2 : face_set P) : (F1 <= F2) = (fpI F1 F2 == F1).
Proof. by rewrite leEfaces -val_eqE fpIC /=; apply/esym/eq_meetr. Qed.

Lemma fp_lt_def (F1 F2 : face_set P) : (F1 < F2) = (F2 != F1) && (F1 <= F2).
Proof. by rewrite !lteEfaces lt_neqAle eq_sym. Qed.

Lemma fpIA : associative fpI.
Proof.
move=> F1 F2 F3; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbA.
Qed.

Lemma fpII : idempotent fpI.
Proof.
move=> F; apply: val_inj; rewrite !SubK.
by apply/poly_eqP=> x; rewrite !in_polyI andbb.
Qed.

Lemma fp0I (F : face_set P) : fp0 <= F.
Proof. by apply: le0x. Qed.

Lemma fpI1 (F : face_set P) : F <= fp1.
Proof. by apply/face_subset/valP. Qed.

Definition polyFaces_latticeMixin :=
   MeetBTFinMixin fp_le_def fpIC fpIA fpII fp0I fpI1.

Canonical face_set_bPOrderType := Eval hnf in BPOrderType (face_set P) polyFaces_latticeMixin.
Canonical face_set_tPOrderType := Eval hnf in TPOrderType (face_set P) polyFaces_latticeMixin.
Canonical face_set_meetSemilatticeType :=
  Eval hnf in MeetSemilatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_bMeetSemilatticeType := [bMeetSemilatticeType of (face_set P)].
Canonical face_set_tMeetSemilatticeType := [tMeetSemilatticeType of (face_set P)].
Canonical face_set_tbMeetSemilatticeType := [tbMeetSemilatticeType of (face_set P)].
Canonical face_set_joinSemilatticeType :=
  Eval hnf in JoinSemilatticeType (face_set P) polyFaces_latticeMixin.
Canonical face_set_bJoinSemilatticeType := [bJoinSemilatticeType of (face_set P)].
Canonical face_set_tJoinSemilatticeType := [tJoinSemilatticeType of (face_set P)].
Canonical face_set_tbJoinSemilatticeType := [tbJoinSemilatticeType of (face_set P)].
Canonical face_set_latticeType := [latticeType of (face_set P)].
Canonical face_set_blatticeType := [bLatticeType of (face_set P)].
Canonical face_set_tlatticeType := [tLatticeType of (face_set P)].
Canonical face_set_tblatticeType := [tbLatticeType of (face_set P)].
Canonical face_set_finLatticeType := [finLatticeType of (face_set P)].
Canonical face_set_finTBLatticeType := [finTBLatticeType of (face_set P)].
End FacesLattice.

Section Active.

Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.

Fact active_key : unit. by []. Qed.

Definition active (P : {poly base}) := (* TODO: fix broken notation *)
  locked_with active_key
    ((\big[@fsetU _/fset0]_(I : {fsubset base} | (P `<=` 'P^=(base; I) :> 'poly_n)) I)%:fsub).

Notation "'{eq'  P }" := (active P) : polyh_scope.

Lemma repr_active (P : {poly base}) :
  P `>` [poly0] -> P = ('P^=(base; {eq P}))%:poly_base.
Proof.
case/poly_baseP: (P) => [->|]; first by rewrite ltxx.
move => I [P_eq _] Pprop0; apply: val_inj => /=.
suff ->: 'P^=(base; {eq P}) =
  \meet_(I : {fsubset base} | val P `<=` 'P^=(base; I)) 'P^= (base; I) :> 'poly_n.
- rewrite (rwP eqP) eq_le; apply/andP; split.
  + by apply/meetsP.
  + rewrite P_eq; apply/meets_inf; exact: lexx.
- rewrite polyEq_big_polyI /active; first by rewrite unlock_with.
  apply/pred0Pn; rewrite P_eq /=; exists I.
  exact: lexx.
Qed.

Lemma activeP (P : {poly base}) (I : {fsubset base}) :
  (P `<=` 'P^=(base; I) :> 'poly_n) = (I `<=` {eq P})%fset.
Proof.
apply/idP/idP.
- by move => Psub; rewrite /active unlock_with; apply/bigfcup_sup.
- case: (emptyP P) => [/= -> _|]; first exact: le0x.
  move/repr_active => {2}-> /=.
  exact: polyEq_antimono.
Qed.

Lemma subset_repr_active {P : {poly base}} :
  P `<=` 'P^=(base; {eq P}) :> 'poly_n.
apply/poly_leP => x x_in_P.
have h: P `>` [poly0] by apply/proper0P; exists x.
by rewrite [P]repr_active in x_in_P.
Qed.

Lemma active0 :
  {eq ([poly0]%:poly_base : {poly base})} = base%:fsub.
Proof.
set A := {eq _}.
apply/val_inj/FSubset.untag_inj => /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; first exact: fsubset_subP.
- rewrite -activeP => /=; exact: le0x.
Qed.

Lemma active_polyEq (I : {fsubset base}) :
  (I `<=` {eq 'P^=(base; I)%:poly_base})%fset.
Proof.
rewrite -activeP; exact: lexx.
Qed.

Lemma poly_base_subset_hp {P : {poly base}} {e} :
  (e \in ({eq P} : {fset _})) -> (P `<=` [hp e]%:PH :> 'poly_n).
Proof.
move => h.
have e_in_base : ([fset e] `<=` base)%fset.
- rewrite fsub1set.
  by apply/(fsubsetP (fsubset_subP {eq P})).
set se := [fset e]%:fsub%fset : {fsubset base}.
have: (se `<=` {eq P})%fset by  rewrite fsub1set.
rewrite -activeP polyEq1 => P_sub.
by apply: (le_trans P_sub); exact: leIr.
Qed.

Lemma in_active {P : {poly base}} {e} :
  e \in base -> (e \in ({eq P} : {fset _})) = (P `<=` [hp e]%:PH :> 'poly_n).
Proof.
move => e_in_base.
apply/idP/idP; first exact: poly_base_subset_hp.
set se := [fset e]%:fsub%fset : {fsubset base}.
move => P_sub.
suff: (se `<=` {eq P})%fset by  rewrite fsub1set.
by rewrite -activeP polyEq1 lexI poly_base_subset.
Qed.

Lemma activeS :
  {homo active : P Q / (P `<=` Q :> 'poly_n) >-> (Q `<=` P)%fset}.
Proof.
move => P Q; case: (poly_baseP P) => [-> | ? [_ P_prop0]].
- rewrite active0 le0x => _; exact: fsubset_subP.
- case: (poly_baseP Q) => [-> | ? [_ Q_prop0]].
  + rewrite lt0x -lex0 in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma activeI (P Q : {poly base}) :
  ({eq P} `|` {eq Q} `<=` {eq ((pval P `&` pval Q)%PH)%:poly_base})%fset.
Proof. by rewrite -activeP -polyEq_polyI leI2 ?activeP. Qed.

Lemma poly_base_proper (P Q : {poly base}) :
  ({eq Q} `<` {eq P})%fset -> P `<` Q :> 'poly_n.
Proof.
case: (poly_baseP Q) => [->| J [Q_eq Q_prop0]]; first by rewrite active0 fsubsetT_proper.
case: (poly_baseP P) => [->| I [P_eq P_prop0]]; first by [].
rewrite {2}[Q]repr_active // => /fproperP [/fsubsetP eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; last exact: polyEq_antimono.
rewrite eq_le /= polyEq_antimono //=.
apply/poly_lePn.
move: i_notin; rewrite in_active.
- move/poly_lePn => [x x_in_Q x_notin].
  exists x; first by move/(poly_leP subset_repr_active): x_in_Q.
  move: x_notin; apply: contra; move: x {x_in_Q}.
  by apply/poly_leP/polyEq_hp.
- move: i_in; apply/fsubsetP; exact: fsubset_subP.
Qed.

Lemma active_proper (P Q : {poly base}) :
  [poly0] `<` P -> P `<` Q :> 'poly_n -> ({eq Q} `<` {eq P})%fset.
Proof.
move => P_prop0 P_prop_Q; rewrite fproperEneq.
have Q_prop0: Q `>` [poly0] by apply/lt_trans: P_prop_Q.
move/ltW/activeS: (P_prop_Q) ->.
rewrite andbT; move: P_prop_Q; apply: contraTneq.
rewrite {2}[P]repr_active // {2}[Q]repr_active // /val_inj /= => ->.
by rewrite ltxx.
Qed.

Lemma active_affine :
  {eq [affine <<base>>]%:PH%:poly_base} = base%:fsub.
Proof.
apply/fsubset_inj/eqP; rewrite eqEfsubset.
rewrite fsubset_subP //=.
apply/fsubsetP => i ?; rewrite in_active //= affS.
by apply/affineS1/memv_span.
Qed.

End Active.

Notation "'{eq'  P }" := (active P) : polyh_scope.

Section ActiveSlice.

Variable (R : realFieldType) (n : nat).

Lemma active_slice e (base : base_t[R,n]) (P : {poly base}) :
  ((e +|` {eq P}) `<=` {eq (slice e P)%:poly_base})%fset.
Proof.
rewrite -activeP -slice_polyEq.
case: (poly_baseP P) => [-> /= | ? [_ P_prop0] /=].
- rewrite {1}(slice0 _); exact: le0x.
- move/repr_active: P_prop0 => {1}->.
  exact: le_trans.
Qed.

End ActiveSlice.

Section Relint.

Context {R : realFieldType} {n : nat}.

Implicit Type base : base_t[R,n].

Context {base : base_t[R,n]} (P : {poly base}).

Hypothesis (Pneq0 : P `>` [poly0]).

Lemma inactive_pt e :
  e \in (base `\` {eq P})%fset -> exists x, ((x \in P) && (x \notin [hp e])).
Proof.
rewrite in_fsetE; case/andP => e_notin_eqP e_in_base.
rewrite (in_active e_in_base) in e_notin_eqP.
case/poly_lePn: e_notin_eqP => x x_in_P x_notin_hp.
by exists x; rewrite ?x_in_P ?affE in x_notin_hp *.
Qed.

Definition mk_inactive_pt e :=
  match @idP (e \in (base `\` {eq P})%fset) with
  | ReflectT H => xchoose (inactive_pt H)
  | _ => 0
  end.

Lemma mk_inactive_ptP e :
  e \in (base `\` {eq P})%fset ->
  ((mk_inactive_pt e) \in P) && ((mk_inactive_pt e) \notin [hp e]).
Proof.
move=> e_inactive; rewrite /mk_inactive_pt.
case: {-}_/idP; [|rewrite e_inactive //].
by move=> e_inactive2; move: (xchooseP (inactive_pt e_inactive2)).
Qed.

Lemma vdot_sumDr (I: eqType) r (Q: pred I) (F : I -> 'cV[R]_n) x :
  '[x, \sum_(i <- r | Q i) F i] = \sum_(i <- r | Q i) '[x, F i ].
Proof.
apply: (big_morph (fun y => '[x,y])).
- move => y y'; exact: vdotDr.
- exact: vdot0r.
Qed.

Lemma combine_hs_hp  (w : {convex 'cV[R]_n ~> R}) (e : lrel[R]_n) :
  {subset (finsupp w) <= [hs e]} -> combine w \in [hp e] ->
  {subset (finsupp w) <= [hp e]}.
Proof.
set x0 := combine w.
move => supp_sub_hs x0_in x x_in.
move: x0_in; apply: contraTT => x_notin_hp.
have x_inactive: '[e.1, x] > e.2.
- rewrite -notin_hp //.
  by apply/supp_sub_hs.
rewrite /x0 combineE in_hp vdot_sumDr.
rewrite eq_sym; apply/ltr_neq.
have ->: e.2 = \sum_(y : finsupp w) (w (fsval y)) * e.2.
- by rewrite -mulr_suml -weightE wgt1_fconvex mul1r.
apply/sumr_ltrP => [y|].
- move/(_ _ (fsvalP y)): supp_sub_hs; rewrite in_hs.
  rewrite vdotZr ler_pmul2l //.
  by apply/gt0_fconvex.
- exists [` x_in]%fset => /=.
  rewrite vdotZr /=; rewrite ltr_pmul2l //.
  by apply/gt0_fconvex.
Qed.

Definition relint_pt :=
  if (base `\` {eq P} != fset0)%fset
  then fsavg (mk_inactive_pt @` (base `\` {eq P}))%fset
  else ppick P.

Lemma relint_pt_in :
  relint_pt \in P.
Proof.
rewrite /relint_pt fun_if if_arg.
case: ifP; last by move => _; rewrite ppickP.
move=> beqPprop0; rewrite -cvxavg_fsavg //.
- case/fset0Pn: beqPprop0 => x x_in_beqP.
    apply/fset0Pn; exists (mk_inactive_pt x).
    by apply: in_imfset.
- move => mk_beqP_prop0; apply: convexW; first by exact: mem_poly_convex.
  move => x; rewrite fsuni_finsupp.
  case/imfsetP => /= x0 x0_in_beqP ->.
  by case/andP: (mk_inactive_ptP x0_in_beqP).
Qed.

Lemma relint_ptP e :
  e \in (base `\` {eq P})%fset -> relint_pt \notin [hp e].
Proof.
move => e_in_beqP; rewrite /relint_pt.
have beqP_prop0: (base `\` {eq P})%fset != fset0 by apply/fset0Pn; exists e.
set mk_beqP:= [fset mk_inactive_pt x | x in base `\` {eq P}]%fset.
rewrite beqP_prop0 -cvxavg_fsavg.
- case/fset0Pn: beqP_prop0 => x x_in_beqP.
    apply/fset0Pn; exists (mk_inactive_pt x).
    by apply: in_imfset.
- move => mk_beqP_prop0.
  rewrite /cvxavg.
  set uni:= (cvxuni mk_beqP_prop0).
  have supp_sub_hse: {subset (finsupp uni) <= [hs e]}.
  + rewrite fsuni_finsupp => x /imfsetP [x0 /= x0_in_beqP ->].
    case/andP : (mk_inactive_ptP x0_in_beqP).
    move: (e_in_beqP); rewrite in_fsetE.
    case/andP => _ /(poly_base_subset_hs P) /poly_leP P_leq_hse.
    by move/P_leq_hse.
  apply: contraT; move/negbNE/(combine_hs_hp supp_sub_hse).
  rewrite fsuni_finsupp => mk_beqP_sub_hpe.
  case/andP: (mk_inactive_ptP e_in_beqP) => _.
  have: mk_inactive_pt e \in mk_beqP by apply/imfsetP; exists e.
  by move/mk_beqP_sub_hpe => ->.
Qed.

End Relint.

Section AffineHull.

Context {R : realFieldType} {n : nat}.

Implicit Type base : base_t[R,n].

Lemma in_span_active base (P : {poly base}) e :
  (e \in << {eq P} >>%VS) -> (P `<=` [hp e]%:PH :> 'poly_n).
Proof.
move/coord_span ->.
apply/poly_leP => x x_in_P; rewrite inE in_hp; apply/eqP.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : lrel[R]_n => x.1)) //.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : lrel[R]_n => x.2)) //=.
rewrite vdot_sumDl; under eq_big do [| rewrite /= vdotZl].
apply/eq_bigr => i _; apply: congr1.
apply/eqP; rewrite -in_hp.
move: x x_in_P; apply/(eq_subr affE)/poly_leP/poly_base_subset_hp.
by rewrite mem_nth ?size_tuple.
Qed.

Definition pb_hull base (P : {poly base}) : 'affine_n :=
  if P `>` [poly0] then
    [affine << {eq P} >>]
  else
    [affine0].

Lemma pb_hull_subset base (P : {poly base}) :
  (P `<=` (pb_hull P)%:PH :> 'poly[R]_n).
Proof.
rewrite /pb_hull; case/emptyP : (P) => [->|Pprop0].
- by rewrite aff0.
- apply/poly_leP => x x_in; rewrite affE.
  apply/in_affineP => e /in_span_active/poly_leP P_sub.
  by move/P_sub: x_in; rewrite affE in_hp => /eqP.
Qed.

Lemma in_polyEqP_fsub x base (I : {fsubset base}) :
  reflect
    ((forall e, e \in (I : {fset _}) -> x \in [hp e]) /\
     (forall e, e \in (base `\` I)%fset -> x \in [hs e])) (x \in 'P^=(base; I)).
Proof.
apply/(iffP (in_polyEqP _ _ _)) => [[x_in_hs x_in_Pbase] | [x_in_hs x_in_hp]]; split => //.
- move => e; rewrite inE => /andP [_] e_in.
  by apply/(poly_leP (poly_of_base_subset_hs e_in)).
- apply/in_poly_of_baseP => e.
  case: (boolP (e \in (I : {fset _}))).
  + by move => e_in _; apply/hp_subset_hs/x_in_hs.
  + by move => e_in e_notin; apply/x_in_hp; rewrite inE; apply/andP.
Qed.

Lemma relint_interior base (P : {poly base}) d:
  P `>` [poly0] -> d \in dir (pb_hull P) ->
    exists2 ϵ, ϵ != 0 & relint_pt P + ϵ *: d \in P.
Proof.
move=> Pneq0 d_in_dir.
set x := relint_pt _.
pose E e := '[ e.1, d] / (e.2 - '[ e.1, x]).
pose M   := \sum_(e : base) `|E (val e)|.
have ge0_M: 0 <= M by rewrite sumr_ge0.
pose ϵ := (1 + M)^-1; exists ϵ.
- by apply/invr_neq0/lt0r_neq0/(lt_le_trans ltr01); rewrite ler_addl.
- set y := x + ϵ *: d.
  have y_in_hp: forall e, e \in ({eq P} : {fset _}) -> y \in [hp e].
  + move=> e e_in; move: d_in_dir; rewrite /pb_hull ifT // => d_in.
    rewrite in_hp vdotDr vdotZr; apply/eqP.
    suff ->: '[e.1, d] = 0.
    * rewrite mulr0 addr0.
      move/relint_pt_in: Pneq0 => /(poly_leP (poly_base_subset_hp e_in)).
      by rewrite in_hp => /eqP ->.
    * rewrite dir_affine in d_in.
      - apply/(orthvP d_in).
        have->: e.1 = befst e by rewrite lfunE.
        by apply/memv_img/memv_span.
      - move/(lt_le_trans Pneq0): (pb_hull_subset P).
        by rewrite aff_lt0x /pb_hull ifT.
  have y_in_hs: forall e, e \in (base `\` {eq P})%fset -> y \in [hs e].
  + move=> e /[dup] e_in /(fsubsetP (fsubsetDl _ _)) e_in_base.
    rewrite in_hs vdotDr vdotZr -ler_subl_addl ler_pdivl_mull ?(lt_le_trans ltr01) ?ler_addl //.
    rewrite -ler_ndivr_mulr.
    * apply/(le_trans (y := M)); rewrite ?ler_addr //.
      apply/(le_trans (y := `|E e|)); rewrite ?ler_norm //.
      rewrite /M (bigD1 [`e_in_base]%fset) //= ler_addl sumr_ge0 //.
    * rewrite subr_lt0; rewrite -notin_hp ?relint_ptP //.
      by move/relint_pt_in: Pneq0 => /(poly_leP (poly_base_subset_hs _ e_in_base)).
  by rewrite [P]repr_active //; apply/in_polyEqP_fsub.
Qed.

Lemma vline_eqP (K : fieldType) (vT : vectType K) (ϵ : K) (v : vT) :
  ϵ != 0 -> (<[ϵ *: v]> = <[v]>)%VS.
Proof.
move => ϵ_neq0; apply/subv_anti/andP; split.
- by apply/vlineP; exists ϵ.
- by apply/vlineP; exists (ϵ^-1); rewrite scalerA mulVf ?scale1r.
Qed.

Lemma in_dir_pb_hull base (P : {poly base}) d :
  P `>` [poly0] ->
  reflect (exists x, exists y, [/\ x \in P, y \in P & (<[d]> = <[x-y]>)%VS])
          (d \in dir (pb_hull P)).
Proof.
move => Pprop0; apply/(iffP idP).
- case/relint_interior=> // ϵ ϵ_neq0.
  set x := relint_pt _.
  set y := x + ϵ *: d => y_in_P.
  exists y; exists x; split; rewrite ?relint_pt_in //.
  by rewrite /y addrAC addrN add0r vline_eqP.
- case=> x [y [x_in_P y_in_P /eqP]].
  rewrite eqEsubv => /andP [/vlineP [k -> _]].
  rewrite memvZ //.
  move/poly_leP: (pb_hull_subset P) => sub_hull.
  move: (sub_hull y y_in_P) (sub_hull x x_in_P);
    rewrite !affE => y_hull x_hull.
  by rewrite (in_dirP y_hull) addrC -addrA addNr addr0.
Qed.

Lemma pb_hullP base (P : {poly base}) V :
  (P `<=` V%:PH :> 'poly[R]_n) = (pb_hull P `<=` V).
Proof.
case: (emptyP P) => [P_eq0| P_prop0].
- by rewrite /pb_hull P_eq0 ifF // !le0x.
- apply/idP/idP; last first.
  + rewrite -affS; apply/le_trans/pb_hull_subset.
  + move/poly_leP; rewrite (eq_subr affE) => P_sub_V.
    case/proper0P: (P_prop0) => x0 x0_in_P.
    have /mk_affine_dir ->: x0 \in pb_hull P
      by rewrite -affE; apply/(poly_leP (pb_hull_subset _)).
    have /mk_affine_dir ->: x0 \in V by rewrite P_sub_V.
    rewrite mk_affineS; apply/subvP => d.
    case/in_dir_pb_hull => // x [y] [x_in y_in].
    rewrite memvE => ->; rewrite -memvE.
    by rewrite (in_dirP (x := y)) ?P_sub_V // addrCA addrN addr0.
Qed.

Definition hull (P : 'poly[R]_n) := pb_hull (\repr P).

Lemma hullE base (P : {poly base}) :
  hull P = pb_hull P.
Proof.
rewrite /hull.
apply/le_anti/andP; split.
- by rewrite -pb_hullP reprK pb_hull_subset.
- by rewrite -pb_hullP -[X in X `<=` _]reprK pb_hull_subset.
Qed.

Lemma subset_hull P : {subset P <= (hull P)}.
Proof.
move=> x x_in_P; rewrite /hull -affE.
by move/poly_leP: (pb_hull_subset (\repr P)); apply; rewrite reprK.
Qed.

Lemma hull0 : hull ([poly0] : 'poly[R]_n) = affine0.
by rewrite /hull /pb_hull reprK ifF ?poly_properxx.
Qed.

Lemma hullN0 P : (P `>` [poly0]) = (hull P `>` affine0).
Proof.
case/emptyP : (P) => [-> | P_prop0]; first by rewrite hull0 ltxx.
apply/esym; rewrite -aff_lt0x.
apply/(lt_le_trans P_prop0)/poly_leP=> x ?; rewrite affE.
exact: subset_hull.
Qed.

Lemma hullN0_eq base (P : {poly base}) :
  (P `>` [poly0]) -> hull P = [affine << {eq P} >>].
Proof.
by rewrite hullE /pb_hull => ->.
Qed.

Lemma dir_hull base (P : {poly base}) :
  P `>` [poly0] -> dir (hull P) = (befst @: << {eq P} >>)^OC%VS.
Proof.
move => P_prop0.
by rewrite hullN0_eq // dir_affine // -hullN0_eq // -hullN0.
Qed.

Lemma hullP P V :
  (P `<=` V%:PH) = (hull P `<=` V).
Proof.
rewrite -{1}(reprK P) /hull; exact: pb_hullP.
Qed.

Lemma hull_affine V :
  hull V%:PH = V.
Proof.
apply/le_anti/andP; split.
- by rewrite -hullP.
- by apply/affine_leP => x; rewrite -affE; move/subset_hull.
Qed.

Lemma hullI (P : 'poly[R]_n) : hull (hull P)%:PH = hull P.
Proof.
by rewrite hull_affine.
Qed.

Lemma hullS : {homo hull : P Q / P `<=` Q}.
Proof.
move => P Q.
case: (emptyP Q) => [->|];
  first by rewrite lex0 => /eqP ->; exact: lexx.
elim/polybW : Q => base Q Q_prop0 P_sub_Q.
rewrite hullN0_eq // -affS hullP hullI -hullP.
rewrite -hullN0_eq //; apply/(le_trans P_sub_Q).
by rewrite hullP.
Qed.

Lemma line_subset_hull (P : 'poly[R]_n) (v v' : 'cV[R]_n) :
  v \in P -> v' \in P -> ([line (v' - v) & v] `<=` hull P).
Proof.
elim/polybW: P => base P v_in_P v'_in_P.
have P_prop0: P `>` [poly0] by apply/proper0P; exists v.
rewrite hullN0_eq //; rewrite affine_span; apply/meetsP => e _.
apply/line_subset_hp; [move: v v_in_P | move: v' v'_in_P];
  apply/(eq_subr affE)/poly_leP/(poly_base_subset_hp (valP _)).
Qed.

Lemma hull_line (v v' : 'cV[R]_n) :
  hull [segm v & v'] = [line (v' - v) & v].
Proof.
apply/le_anti/andP; split; last first.
- by apply/line_subset_hull; [rewrite in_segml | rewrite in_segmr].
- rewrite -hullP; apply/conv_subset => x.
  rewrite !inE => /orP; case => /eqP ->.
  + by rewrite orig_affine.
  + by rewrite in_mk_affine memv_line.
Qed.

Lemma hull_pt (v : 'cV[R]_n) : hull [pt v]%:PH = [pt v].
Proof.
have {1}->: [pt v]%:PH = [segm v & v].
- by rewrite -conv_pt; apply/congr1/fsetP => ?; rewrite !inE orbb.
- by rewrite hull_line subrr.
Qed.

Lemma face_hullI (P Q : 'poly[R]_n) :
  Q \in face_set P -> Q = P `&` (hull Q)%:PH.
Proof.
elim/polybW : P => base P.
case/face_setP => {}Q Q_sub_P.
case: (emptyP Q) => [->| Q_prop0]; first by rewrite hull0 aff0 meetx0.
rewrite hullN0_eq // [Q in LHS]repr_active //= meetC.
rewrite [P]repr_active /= ?polyEq_affine -?polyIA.
- move: (Q_sub_P) => /activeS/fsubsetP/sub_span/affineS/meet_r.
  by rewrite meetA meetC -affI => ->.
- by apply/lt_le_trans: Q_sub_P.
Qed.

Lemma in_span_activeP base (P : {poly base}) e :
  (P `>` [poly0]) ->
  (P `<=` [hp e]%:PH :> 'poly_n) = (e \in << {eq P} >>%VS).
Proof.
move=> P_prop0.
apply/idP/idP; last by apply/in_span_active.
have hullP_prop0: hull P `>` [affine0] by rewrite -hullN0.
rewrite hullP hullN0_eq // in hullP_prop0 *.
by rewrite affine_mono ?memvE.
Qed.

End AffineHull.

Section Dimension.

Variable (R : realFieldType) (n : nat).

Notation "\pdim P" := (adim (hull P)) : polyh_scope.

Lemma dim0 :
  (\pdim ([poly0] : 'poly[R]_n) = 0%N)
  * (forall base : base_t[R,n], \pdim ([poly0] %:poly_base : {poly base}) = 0%N).
Proof.
suff H : forall base : base_t[R,n], \pdim ([poly0] %:poly_base : {poly base}) = 0%N.
- split => //.
  pose base0 := fset0 : base_t[R,n].
  by rewrite H.
- by move => base; rewrite hull0 adim0.
Qed.

Lemma dimN0 (P : 'poly[R]_n) : (P `>` [poly0]) = (\pdim P > 0)%N.
Proof. by rewrite hullN0 adimN0. Qed.

Lemma dimN0_eq (P : 'poly[R]_n) :
  (P `>` [poly0]) -> \pdim P = (\dim (dir (hull P))).+1%N.
Proof.
move => P_prop0; rewrite /adim ifF //.
by apply/negbTE; rewrite -lt0x -hullN0.
Qed.

Lemma dim_eq0 (P : 'poly[R]_n) :
  \pdim P = 0%N <-> P = [poly0].
Proof.
split; last by move ->; rewrite dim0.
by apply/contra_eq; rewrite -lt0x dimN0 lt0n.
Qed.

Variant dim_spec : 'poly[R]_n -> nat -> Prop :=
| DimEmpty : dim_spec [poly0] 0%N
| DimNonEmpty (base : base_t[R,n]) (P : {poly base}) of (P `>` [poly0]) :
    dim_spec P (\dim (dir (hull P))).+1%N.

Lemma dimP P : dim_spec P (\pdim P).
case: (emptyP P) => [->| ]; first by rewrite dim0; constructor.
by elim/polybW: P => base P P_prop0; rewrite dimN0_eq //; constructor.
Qed.

Lemma dim_hull (P : 'poly[R]_n) :
  \pdim P = \pdim (hull P)%:PH.
Proof. by rewrite hull_affine. Qed.

Lemma dimS : {homo (fun P : 'poly[R]_n => \pdim P) : P Q / (P `<=` Q) >-> (P <= Q)%N}.
Proof. by move => P Q /hullS/adimS. Qed.

Lemma face_dim_leqif_eq (P Q : 'poly[R]_n) :
  (P \in face_set Q) -> (\pdim P <= \pdim Q ?= iff (P == Q))%N.
Proof.
move => P_face_Q; split; first by apply/dimS/face_subset.
apply/eqP/eqP => [ dim_eq | -> //].
have: hull P = hull Q.
- apply/sub_eq_adim => //.
  by apply/hullS/face_subset.
- rewrite {2}(face_hullI P_face_Q) => ->.
  by apply/meet_l; rewrite hullP.
Qed.

Lemma face_dim_geq (P Q : 'poly[R]_n) :
  P \in face_set Q -> (\pdim P >= \pdim Q)%N -> P = Q.
Proof.
move/face_dim_leqif_eq/geq_leqif => h dim_geq.
by rewrite dim_geq in h; move/esym/eqP: h.
Qed.

Lemma face_dim_eq (P Q : 'poly[R]_n) :
  P \in face_set Q -> \pdim P = \pdim Q -> P = Q.
Proof.
by move => ? dim_eq; apply/face_dim_geq; rewrite ?dim_eq.
Qed.

Lemma face_dim_lt (P Q Q' : 'poly[R]_n) :
  Q \in face_set P -> Q' \in face_set P -> Q `<` Q' -> (\pdim Q < \pdim Q')%N.
Proof.
move => Q_face Q'_face Q_prop_Q'.
have {Q_face Q'_face} Q_face_Q': Q \in face_set Q'
  by rewrite (face_set_of_face Q'_face) !inE Q_face ltW.
move: Q_prop_Q'; apply/contraTT.
rewrite -leqNgt => /(face_dim_geq Q_face_Q') ->.
by rewrite ltxx.
Qed.

Lemma dim_pt (x : 'cV[R]_n) :
  \pdim [pt x]%:PH = 1%N.
Proof. by rewrite hull_affine adim_pt. Qed.

Lemma dim1P (P : 'poly[R]_n) :
  \pdim P = 1%N -> exists x, P = [pt x]%:PH.
Proof.
move => dimP1.
move: (dimP1); case/adim1P => x hull_eq; exists x.
apply/le_anti/andP; split; first by rewrite -hull_eq hullP.
have /proper0P [y y_in_P]: P `>` [poly0] by rewrite dimN0 dimP1.
suff /eqP <-: y == x by rewrite pt_subset.
move: (subset_hull y_in_P).
by rewrite hull_eq in_pt.
Qed.

Lemma dim_segm (v v' : 'cV[R]_n) : \pdim [segm v & v'] = (v != v').+1.
Proof.
by rewrite hull_line adim_line subr_eq0 eq_sym.
Qed.

Lemma dim2P (P : 'poly[R]_n) :
  compact P -> \pdim P = 2%nat -> exists v, exists2 w, P = [segm v & w] & v != w.
Proof.
move => P_compact dimP2.
have P_prop0 : P `>` [poly0] by rewrite dimN0 dimP2.
have [d d_neq0 dir_eq] :
  exists2 d, d != 0 & dir (hull P) = <[d]>%VS.
- case/adim2P: dimP2 => ? [d d_neq0] ->.
  by exists d; rewrite ?dir_mk_affine.
have d_bounded : bounded P d by apply/(compactP P_prop0).
have d_bounded' : bounded P (-d) by apply/(compactP P_prop0).
set v := ppick (argmin P d); set w := ppick (argmin P (-d)).
have [v_in_P d_v] : (v \in P /\ '[d,v] = opt_value d_bounded).
- suff: v \in argmin P d
    by rewrite argmin_polyI in_polyI in_hp => /andP [? /eqP].
  by apply/ppickP; rewrite -bounded_argminN0.
have [w_in_P d_w] : (w \in P /\ '[d,w] = -(opt_value d_bounded')).
- suff: w \in argmin P (-d)
    by rewrite argmin_polyI in_polyI in_hp vdotNl => /andP [? /= /eqP <-];
       rewrite opprK.
  by apply/ppickP; rewrite -bounded_argminN0.
have hull_P : hull P = [line d & v].
- rewrite -dir_eq; apply/mk_affine_dir.
  exact: (subset_hull v_in_P).
pose μ x := ('[d,x] - '[d,v]) / '[|d |]^2.
have μ_ge0: forall x, x \in P -> μ x >= 0.
- move => x x_in_P; apply/divr_ge0; rewrite ?vnorm_ge0 ?subr_ge0 //.
  move/poly_leP/(_ _ x_in_P): (opt_value_lower_bound d_bounded).
  by rewrite in_hs /= -d_v.
have μ_le_μ_w : forall x, x \in P -> μ x <= μ w.
- move => x /(poly_leP (opt_value_lower_bound d_bounded')).
  rewrite in_hs /= vdotNl ler_oppr -d_w => ?.
  by apply/ler_wpmul2r; rewrite ?invr_ge0 ?vnorm_ge0 ?ler_add2r.
have x_eq : forall x, x \in P -> x = v + μ x *: d.
- move => x /subset_hull.
  rewrite hull_P => /in_lineP [μ_x x_eq].
  suff <-: μ_x = μ x by []; move/(congr1 (vdot d)): (x_eq).
  rewrite vdotDr vdotZr addrC mulrC => /(canLR (addrK _)).
  rewrite -vnorm_eq0 in d_neq0.
    by move/(canLR (mulKf d_neq0)); rewrite mulrC => <-.
have P_sub: P `<=` [segm v & w].
- apply/poly_leP => x x_in_P.
  have μ_x_eq0: μ w <= 0 -> μ x = 0.
  + move => ?; apply/le_anti/andP; split; last by apply/μ_ge0.
    by apply/(le_trans (μ_le_μ_w _ _)).
  pose μ' := μ x / μ w.
  have μ_eq : μ x = μ' * μ w.
  + case: (ler0P (μ w)) => [?|?].
    * by rewrite /μ' μ_x_eq0 ?mul0r.
    * by rewrite mulfVK ?lt0r_neq0.
  rewrite (x_eq _ x_in_P) (x_eq _ w_in_P); apply/in_segmP; exists μ'; last first.
  + rewrite scalerBl scalerDr scale1r.
    by rewrite addrA -[(_ - _ + _) in RHS]addrA addNr addr0 scalerA -μ_eq.
  + apply/andP; split; first by apply/divr_ge0 => //; apply/μ_ge0.
    case: (ler0P (μ w)) => [?| ?].
    * by rewrite /μ' μ_x_eq0 ?mul0r ?ler01.
    * by rewrite lter_pdivr_mulr ?mul1r ?μ_le_μ_w.
exists v; exists w.
- apply/le_anti; apply/andP; split => //.
  by apply/conv_subset => x /fset2P; case => ->.
- move: P_sub => /dimS; rewrite dimP2.
  by apply/contraTneq => ->; rewrite dim_segm eq_refl.
Qed.

Lemma dim_hp (e : lrel[R]_n) :
  [hp e]%:PH `>` [poly0] -> \pdim [hp e]%:PH = ((e.1 == 0%R) + n)%N.
Proof. by move=> h; rewrite hull_affine adim_hp // -aff_ltE aff0. Qed.

Lemma dim_sub_affine 
  (P : 'poly[R]_n)  (x0 : 'cV[R]_n) (X : seq 'cV[R]_n):
  x0 \in P -> {in X, forall x, x \in P} ->
  (adim [affine (span [seq (x - x0)%R | x <- X]) & x0] <= 
  \pdim P)%nat.
Proof.
move=> x0_base X_base; rewrite dimN0_eq; last by (apply/proper0P; exists x0).
rewrite (adimN0_eq (mk_affine_proper0 _ _)) dir_mk_affine.
rewrite ltnS; apply/dimvS/subvP=> z.
set S := map _ _; have ->: span S = span (in_tuple S) by [].
move/coord_span=> ->; apply/memv_suml=> i _; apply/memvZ.
rewrite /=; case/mapP: (mem_nth 0 (ltn_ord i))=> /= x xX ->.
move: (subset_hull x0_base)=> x0_hull.
rewrite (in_dirP x0_hull); apply/subset_hull.
rewrite addrA addrC addKr; exact/X_base.
Qed.
End Dimension.

Notation "\pdim P" := (adim (hull P)) : polyh_scope.

Section Facet.

Context {R : realFieldType} {n : nat} (base : base_t[R,n]).
Hypothesis non_redundant : non_redundant_base base.

Let P := 'P(base)%:poly_base.
Hypothesis P_prop0 : P `>` [poly0].

Lemma activeU1 (e : lrel) & (e \in base) :
  {eq 'P^=(base; [fset e])%:poly_base } = ({eq P} `|` [fset e])%fset%:fsub.
Proof.
case: (boolP (e \in ({eq P} : base_t))).
- move => e_in_eqP.
  have ->: 'P^= (base; [fset e])%:poly_base = 'P(base)%:poly_base.
  + apply/val_inj => /=; rewrite polyEq1; apply/meet_l.
    by apply/poly_base_subset_hp.
  apply/fsubset_inj => /=.
  by move: e_in_eqP; rewrite -fsub1set => /fsetUidPl ->.
- set I := ({eq P} `|` [fset e])%fset %:fsub.
  move => e_notin_eq; apply/fsubset_inj/eqP; rewrite eqEfsubset.
  apply/andP; split; last first.
  + apply/fsubUsetP; split; last exact: active_polyEq.
    apply/activeS => /=; exact: polyEq_antimono0.
  + apply/fsubset_fsubsetP => i i_in_eq; apply: contraLR.
    rewrite 2!inE negb_or => /andP [i_notin_eqP i_neq_e].
    apply/(contra poly_base_subset_hp)/poly_lePn.
    move/non_redundant_baseP/(_ _ H)/poly_lePn: non_redundant => [z z_in_P' z_notin_e].
    move: i_notin_eqP; rewrite in_active //.
    move/poly_lePn => [y y_in_P y_notin_i].
    have y_in_e : y \in [hs e] by apply/(poly_leP _ _ y_in_P)/poly_of_base_subset_hs.
    move: (hp_itv y_in_e z_notin_e) => [α α01]; rewrite {y_in_e}.
    set x := _ + _ => x_in_e; exists x.
    * rewrite /= polyEq1 !inE x_in_e andbT.
      apply/in_poly_of_baseP => j.
      case: (j =P e) => [-> _| /eqP j_neq_e j_in_base].
      - by apply/hp_subset_hs.
      - have y_in_P' : y \in 'P(base `\ e)
          by move: y_in_P; apply/poly_leP/poly_of_base_antimono; exact: fsubD1set.
        have: x \in 'P(base `\ e) by apply/mem_poly_convex => //; exact: ltW_le.
        apply/poly_leP/poly_of_base_subset_hs.
        by rewrite !inE j_neq_e.
    * move: y_notin_i; rewrite !inE; apply/contraNN/hp_extremeL => //.
      - by move: y_in_P; apply/poly_leP/poly_of_base_subset_hs.
      - move: z_in_P'; apply/poly_leP/poly_of_base_subset_hs.
        by rewrite !inE i_neq_e.
Qed.

Lemma facet_proper (i : lrel) & (i \in base) :
  i \notin ({eq P} : {fset _}) -> 'P^=(base; [fset i])%:poly_base `<` P :> 'poly_n.
Proof.
move => i_notin_eqP.
rewrite lt_neqAle andbC; apply/andP; split.
- by rewrite /= -polyEq0; apply: polyEq_antimono.
- move: i_notin_eqP; apply: contraNneq => /pval_inj <-.
  rewrite -fsub1set; exact: active_polyEq.
Qed.

Lemma facet_proper0 (i : lrel) & (i \in base) : (* A LOT IN COMMON WITH activeU1 *)
  i \notin ({eq P} : {fset _}) -> 'P^=(base; [fset i])%:poly_base `>` [poly0].
Proof.
move => i_notin_eqP.
move/non_redundant_baseP/(_ _ H)/poly_lePn: non_redundant => [y y_in_P' y_notin_i].
move/proper0P: (P_prop0) => [x x_in_P].
have x_in_i : x \in [hs i] by move: x_in_P; apply/poly_leP/poly_of_base_subset_hs.
move: (hp_itv x_in_i y_notin_i) => [α α01].
set z := _ + _ => z_in_i; apply/proper0P; exists z.
rewrite /= polyEq1 !inE z_in_i andbT.
apply/in_poly_of_baseP => j.
case: (j =P i) => [-> _| /eqP j_neq_i j_in_base].
- by apply/hp_subset_hs.
- have x_in_P' : x \in 'P(base `\ i)
    by move: x_in_P; apply/poly_leP/poly_of_base_antimono; exact: fsubD1set.
  have: z \in 'P(base `\ i) by apply/mem_poly_convex => //; exact: ltW_le.
  by apply/poly_leP/poly_of_base_subset_hs; rewrite !inE j_neq_i.
Qed.

Lemma dim_facet (i : lrel) (i_in : i \in base) :
  i \notin ({eq P} : {fset _}) -> \pdim P = (\pdim 'P^=(base; [fset i])%:poly_base).+1%N.
Proof.
set S := 'P^=(_; _)%:poly_base.
move=> /[dup] i_notin_eqP /(facet_proper i_in)=> S_prop_P.
have i_notin_span: i \notin << {eq P} >>%VS.
- move: S_prop_P; apply/contraTN; move/in_span_active.
  by rewrite /= polyEq1 => /meet_l ->; rewrite ltxx.
have hull_S: hull S = hull P `&` [hp i].
- rewrite !hullN0_eq ?facet_proper0 //.
  by rewrite activeU1 span_fsetU span_fset1 affine_addv.
rewrite dim_hull [in RHS]dim_hull hull_S !hull_affine.
apply/dim_affineI; last by rewrite -hull_S -hullN0 facet_proper0.
move: S_prop_P; apply/contraTN; move: hull_S => /[swap].
move/meet_l => -> hull_eq.
rewrite (face_hullI (P := P) (Q := S)) ?hull_eq -?(face_hullI (face_set_self _)) ?ltxx //.
by rewrite face_setE polyEq_antimono0.
Qed.

Lemma facetP (F : {poly base}) :
  (F `>` [poly0]) -> \pdim P = (\pdim F).+1%N ->
  exists i, exists2 _ : (i \in base), i \notin ({eq P} : {fset _}) & F = 'P^=(base; [fset i])%:poly_base.
Proof.
move => F_prop0 dimF.
suff: ~~ ({eq F} `<=` {eq P})%fset.
- case/fsubsetPn => i i_in_F i_notin_P.
  have i_in_base: i \in base by move: i_in_F; apply/fsubsetP/fsubset_subP.
  exists i; exists i_in_base => //.
  apply/val_inj/face_dim_eq => /=; last first.
  + by apply/succn_inj; rewrite -dimF -dim_facet.
  + by rewrite face_setE activeP /= fsub1set.
- suff: ~~ (P `<=` F :> 'poly_n).
  + by rewrite {1}[F]repr_active // activeP.
  + by move: dimF; apply/contra_eqN; move/dimS; rewrite -ltnS ltn_neqAle => /andP [].
Qed.

Lemma polyI_facet (F : {poly base}) :
  [poly0] `<` F -> F `<` P :> 'poly_n ->
    F = \meet_(i : ({eq F} `\` {eq P})%fset) 'P^=(base; [fset (val i)]) :> 'poly_n.
Proof.
move => F_prop0 F_prop_P.
set Q := (RHS).
have /fproperP [_ [i i_in i_notin]] : ({eq P} `<` {eq F})%fset
  by rewrite active_proper.
have {i_notin} {}i_in: i \in ({eq F} `\` {eq P})%fset
  by rewrite inE i_notin.
have Q_sub : Q `<=` P.
- by rewrite (meets_max (j := [` i_in]%fset)) ?polyEq1 ?leIl.
have <-: pval P `&` Q = Q by apply/meet_r.
rewrite /Q polyEq_big_polyI; last by apply/pred0Pn; exists [` i_in]%fset.
rewrite {1}[P]repr_active ?polyEq_polyI; last by apply/lt_trans: F_prop_P.
rewrite {1}[F]repr_active //=; apply/congr1.
apply/fsetP => e; apply/idP/idP.
- case: (boolP (e \in ({eq P} : {fset _}))).
  + by rewrite in_fsetU => ->.
  + move => e_notin e_in.
    rewrite inE; apply/orP; right.
    have {e_notin} {}e_in: e \in ({eq F} `\` {eq P})%fset by rewrite inE e_notin.
    apply/bigfcupP; exists ([`e_in]%fset).
    * by rewrite andbT /index_enum unlock -enumT mem_enum.
    * by rewrite in_fset1.
- rewrite inE; case/orP.
  + by apply/fsubsetP/activeS/poly_base_subset.
  + case/bigfcupP => e' _.
    rewrite in_fset1 => /eqP ->.
    by move: (fsvalP e'); rewrite in_fsetD => /andP[].
Qed.

End Facet.

Section PointedFacet.

Context {R : realFieldType} {n : nat}.

Lemma pointed_facet (P : 'poly[R]_n) :
  P `>` ([poly0]) -> pointed P -> exists2 F, F \in face_set P & \pdim P = (\pdim F).+1.
Proof.
elim/non_redundant_baseW: P => base non_redundant.
set P := 'P(base)%:poly_base => P_prop0 P_pointed.
case: (leqP (\pdim P) 1%N) => [dimP_le1 | dimP_gt1].
- rewrite dimN0 in P_prop0.
  have ->: \pdim P = 1%N by apply/anti_leq/andP; split.
  exists (pval (([poly0]%:poly_base) : {poly base})).
  + by rewrite face_setE le0x.
  + by rewrite dim0.
- suff: ({eq P} `<` base)%fset.
  + move/fproperP => [_ [i i_base i_notin_eqP]].
    set F := 'P^=(base; [fset i]%fset)%:poly_base.
    exists (pval F); last exact: dim_facet.
    by rewrite face_setE ltW ?facet_proper.
  + move: P_pointed; apply: contraTT.
    rewrite fsubset_properT negbK => /eqP eqP_eq_base.
    move: (P_prop0) dimP_gt1; rewrite [P]repr_active //=.
    rewrite eqP_eq_base polyEqT_affine -aff0 aff_lt.
    case/affine_proper0P => x x_in_aff.
    rewrite (mk_affine_dir x_in_aff) pointed_affine.
    by apply/contraTneq => ->; rewrite hull_affine adim_pt.
Qed.

End PointedFacet.

Section VertexSet.

Context {R : realFieldType} {n : nat}.

Definition vertex_set (P : 'poly[R]_n) :=
  [fset ppick F | F in face_set P & \pdim F == 1%N]%fset.

Lemma in_vertex_setP (P : 'poly[R]_n) x :
  (x \in vertex_set P) = ([pt x]%:PH \in face_set P).
Proof.
apply/imfsetP/idP => /=.
- move => [F] /andP [F_face /eqP/dim1P [y F_eq]].
  move: F_face; rewrite {}F_eq => ?.
  by rewrite ppick_pt => ->.
- move => pt_x_face.
  exists [pt x]%:PH; rewrite ?ppick_pt //=.
  by apply/andP; split; rewrite ?dim_pt.
Qed.

Lemma dim1_pt_ppick (P : 'poly[R]_n) :
  \pdim P = 1%N -> P = [pt (ppick P)]%:PH.
Proof.
by move/dim1P => [? ->]; rewrite ppick_pt.
Qed.

Lemma face_dim1 (P Q : 'poly[R]_n) :
  Q \in face_set P -> \pdim Q = 1%N ->
    exists2 x, Q = [pt x]%:PH & x \in vertex_set P.
Proof.
move => Q_face dimQ1; exists (ppick Q).
- by apply/dim1_pt_ppick.
- by apply/in_imfset => /=; rewrite !inE Q_face dimQ1 eq_refl.
Qed.

Lemma vertex_setS (P Q : 'poly[R]_n) :
  P \in face_set Q -> (vertex_set P `<=` vertex_set Q)%fset.
Proof.
move => P_face.
apply/fsubsetP => x; rewrite 2!in_vertex_setP.
apply/fsubsetP; exact: face_setS.
Qed.

Lemma vertex_set_face (P Q : 'poly[R]_n) :
  Q \in face_set P -> vertex_set Q = [fset x in (vertex_set P) | x \in Q]%fset.
Proof.
move => Q_face; apply/fsetP => x.
rewrite !inE !in_vertex_setP -pt_subset.
by rewrite (face_set_of_face Q_face) !inE.
Qed.

Lemma vertex_set_subset P : {subset (vertex_set P) <= P}.
Proof.
move => x; rewrite in_vertex_setP => /face_subset.
by rewrite pt_subset.
Qed.

Lemma vertex_set0 : (vertex_set ([poly0])) = fset0.
Proof.
apply/fsetP => x; rewrite in_vertex_setP.
by rewrite face_set0 !inE; apply/negbTE; rewrite -lt0x pt_proper0.
Qed.

Lemma vertex_set1 (v : 'cV[R]_n) : vertex_set [pt v]%:PH = [fset v]%fset.
Proof.
apply/fsetP => x; apply/idP/idP.
- by move/vertex_set_subset; rewrite in_pt => /eqP ->; rewrite inE.
- rewrite inE => /eqP ->.
  by rewrite in_vertex_setP face_set_self.
Qed.

Lemma vertex_setN0 (P : 'poly[R]_n) :
  P `>` ([poly0]) -> pointed P -> vertex_set P != fset0.
Proof.
pose H k :=
  forall (P : 'poly[R]_n), \pdim P = k -> P `>` ([poly0]) -> pointed P ->
                      vertex_set P != fset0.
suff: forall k, H k by move/(_ (\pdim P) P (erefl _)).
elim => [ Q | k IHk Q ].
- by rewrite dimN0 => ->.
- case: (posnP k) => [-> dimQ1 _ _ | k_gt0 dimQ _ Q_pointed].
  + apply/fset0Pn; exists (ppick Q).
    by rewrite [Q]dim1_pt_ppick ?ppick_pt ?vertex_set1 ?inE.
  + have : Q `>` [poly0] by rewrite dimN0 dimQ.
    move/pointed_facet/(_ _); move/(_ Q_pointed) => [F F_face].
    rewrite dimQ; move/succn_inj/esym => dimF.
    move: (IHk _ dimF); rewrite dimN0 dimF.
    move/(_ k_gt0 (face_pointed Q_pointed F_face)).
    apply/contra_neq => vtx_Q0.
    by move: (vertex_setS F_face); rewrite {}vtx_Q0 fsubset0 => /eqP ->.
Qed.

Lemma opt_vertex (P : 'poly[R]_n) c :
  pointed P -> bounded P c -> exists2 x, x \in vertex_set P & x \in argmin P c.
Proof.
move => P_pointed c_bounded.
set F := argmin P c.
have F_face : F \in face_set P by apply/argmin_in_face_set.
have F_pointed : pointed F by apply/(pointedS (argmin_subset _ _)).
have F_prop0 : F `>` [poly0] by rewrite -bounded_argminN0.
move/(vertex_setN0 F_prop0)/fset0Pn: F_pointed => [x x_vtx_F].
exists x.
- by apply/(fsubsetP (vertex_setS _)): x_vtx_F.
- by apply/vertex_set_subset.
Qed.

End VertexSet.

Section FaceSetGraded.

Context {R : realFieldType} {n : nat} .

Lemma dim_proper (P Q : 'poly[R]_n) :
  (P `<=` Q) -> (\pdim P < \pdim Q)%N -> (P `<` Q).
Proof.
rewrite lt_neqAle => ->; rewrite andbT.
by apply/contraTneq; rewrite -leqNgt => ->.
Qed.

Implicit Type P : 'pointed[R]_n.

Lemma graded (P0 : 'pointed[R]_n) (Q Q' : 'poly[R]_n) :
  Q \in face_set P0 -> Q' \in face_set P0
  -> Q `<=` Q' -> ((\pdim Q).+1 < (\pdim Q'))%N ->
    exists2 F, F \in face_set P0 & Q `<` F `<` Q'.
Proof.
move => Q_face Q'_face Q_sub_Q'.
have Q'_pointed : pointed Q' by apply/(face_pointed (valP P0)).
have {Q_face Q_sub_Q'} : Q \in face_set Q'.
  by rewrite (face_set_of_face Q'_face) !inE Q_face Q_sub_Q'.
move: Q' Q'_face Q'_pointed Q; elim/non_redundant_baseW => base non_redundant.
set P := 'P(base)%:poly_base => P_face P_pointed Q.
case/face_setP => {}Q Q_sub_P dim_lt.
have {Q_sub_P} Q_prop_P : Q `<` P :> 'poly_n.
- rewrite dim_proper //.
  (*by apply/ltn_trans: dim_lt. QC : That line seems to be irrelevant now*)
have P_prop0 : P `>` [poly0] by apply: (le_lt_trans (le0x (pval Q))).
case: (emptyP Q) dim_lt => [ -> | Q_prop0].
- rewrite dim0 => dimP_gt1.
  case/fset0Pn : (vertex_setN0 P_prop0 P_pointed) => x.
  rewrite in_vertex_setP => x_vtx.
  exists [pt x]%:PH.
  + by move: x_vtx; apply/fsubsetP/(face_setS P_face).
  + by rewrite pt_proper0 dim_proper ?dim_pt ?face_subset.
- have eqQ_prop_eqP : ({eq P} `<` {eq Q})%fset by apply/active_proper.
  move/fproperP: (eqQ_prop_eqP) => [_ [i i_in_eqQ i_notin_eqP]].
  have i_in_base: (i \in base) by move: (i) i_in_eqQ; apply/fsubsetP: (valP {eq Q}).
  set S := 'P^=(base; [fset i])%:poly_base => dim_lt.
  have Q_prop_S : Q `<` S :> 'poly_n.
  + rewrite dim_proper ?activeP ?fsub1set ?i_in_eqQ //.
    by move: dim_lt; rewrite (dim_facet _ _ _ i_notin_eqP).
  have S_prop_P : S `<` P :> 'poly_n.
  + rewrite lt_neqAle andbC; apply/andP; split.
    * by rewrite /= -polyEq0; apply: polyEq_antimono.
    * move: i_notin_eqP; apply: contraNneq => /pval_inj <-.
      rewrite -fsub1set; exact: active_polyEq.
  exists (pval S).
  + apply/(fsubsetP (face_setS P_face)).
    by rewrite face_setE ltW.
  + by apply/andP; split.
Qed.

Lemma dimfs0 P : \pdim (val (0%O : face_set P)) = 0%N.
Proof. by rewrite dim0. Qed.

Lemma homo_dim P (x y : face_set P) :
  x < y -> (\pdim (val x) < \pdim (val y))%N.
Proof.
by apply: (face_dim_lt (valP _) (valP _)).
Qed.

Lemma dim_graded P (x y : face_set P) :
  x <= y -> ((\pdim (val x)).+1 < \pdim (val y))%N -> exists z, x < z < y.
Proof.
rewrite leEfaces => /(graded (valP _) (valP _)) h /h => [[F] F_in F_lt].
by exists ([` F_in]%fset); rewrite !ltEfaces.
Qed.

Definition face_set_gradedFinLatticeMixin P :=
  GradedFinLatticeMixin (dimfs0 P) (@homo_dim P) (@dim_graded P).
Canonical face_set_gradedFinLatticeType P :=
  Eval hnf in GradedFinLatticeType (face_set P) (face_set_gradedFinLatticeMixin P).

Lemma atom_faceP (P : 'pointed[R]_n) (F : face_set P) :
  reflect
    (exists2 x : 'cV_n, x \in vertex_set P & val F = [pt x]%:PH)
    (atom F).
Proof.
rewrite atomE /rank /=; apply: (iffP eqP).
+ by move/face_dim1 => /(_ _ (fsvalP _)) [x ->]; exists x.
+ by case=> x xP ->; rewrite dim_pt.
Qed.

End FaceSetGraded.

Section Minkowski.

Context {R : realFieldType} {n : nat}.

Theorem conv_vertex_set (P : 'poly[R]_n) :
  compact P -> P = conv (vertex_set P).
Proof.
case: (emptyP P) => [-> _| P_prop0 P_compact].
- by rewrite vertex_set0 conv0.
- apply/poly_eqP => x; apply/idP/idP.
  + apply/contraTT.
    move/separation => [e x_notin_hs conv_sub].
    have e_bounded : bounded P e.1 by apply/compactP.
    move/compact_pointed/opt_vertex: P_compact.
    move/(_ _ e_bounded) => [y].
    move/in_conv/(poly_leP conv_sub) => y_in_e y_in_argmin.
    move: x_notin_hs; apply/contraNN => x_in_P.
    rewrite !in_hs in y_in_e *; apply/(le_trans y_in_e).
    by apply/(argmin_lower_bound y_in_argmin).
  + apply/poly_leP/conv_subset.
    exact: vertex_set_subset.
Qed.

Lemma face_atomistic (P : 'compact[R]_n) (F : face_set P) : atomistic F.
Proof.
pose S := vertex_set (val F).
have h x : x \in S -> [pt x]%:PH \in face_set P.
+ move=> xS; rewrite -in_vertex_setP.
  by apply/fsubsetP/vertex_setS/valP: x xS.
apply/atomisticP => /=; exists [set [` h _ (valP x)]%fset | x : S].
+ move=> F' /imsetP[/= x xS -> /=]; apply/atom_faceP.
  case: x xS => /= x xS vxS; exists x => //.
  by rewrite in_vertex_setP h.
rewrite (rwP eqP) eq_le -(rwP andP); split; last first.
+ apply/joinsP=> /= F' /imsetP[/= x xS ->].
  rewrite leEfaces pt_subset.
  by apply: vertex_set_subset.
rewrite leEfaces [val F]conv_vertex_set; last first.
+ by apply/(subset_compact (valP P))/(lex1 F).
apply: conv_subset => /= c cF.
have: c \in fsval [` h _ cF]%fset by rewrite in_pt.
apply: poly_leP; rewrite -leEfaces join_sup //.
by apply/imsetP; exists [` cF]%fset => //; apply: val_inj.
Qed.

Lemma card_vertex_set (P : 'poly[R]_n):
  compact P -> (\pdim P > n)%N -> (#|` vertex_set P | > n)%N.
Proof.
move => P_compact dimP.
have P_prop0: P `>` [poly0] by rewrite dimN0; apply/leq_trans: dimP.
move: dimP; apply: contraTT; rewrite -2!leqNgt => card_vtx.
have {card_vtx}: (0 < #|` vertex_set P | <= n)%N.
- rewrite card_vtx andbT.
  by rewrite cardfs_gt0 vertex_setN0 ?compact_pointed.
move/subset_hp => [e /negbTE e_neq0 vtx_sub].
have: (conv (vertex_set P) `<=` [hp e]%:PH).
- apply/conv_subset => ?; rewrite inE; apply/vtx_sub.
rewrite {vtx_sub} -conv_vertex_set // => sub.
move/dimS: (sub); rewrite hull_affine adim_hp ?e_neq0 //.
rewrite -aff_lt0x; by apply/lt_le_trans: sub.
Qed.

End Minkowski.

Section Coatomistic.

Context {R : realFieldType} {n : nat}.

Lemma card_vertex_set_gt1 (P : 'poly[R]_n) :
  compact P -> (\pdim P > 1)%N -> (#|` vertex_set P | > 1)%N.
Proof.
move => P_compact.
apply/contraTT; rewrite -2!ltnNge !ltnS.
case: (emptyP P) => [->| P_prop0 card_le1]; first by rewrite dim0.
have /eqP/cardfs1P [v]: #|` vertex_set P| = 1%N.
- apply/anti_leq/andP; split => //.
  by rewrite cardfs_gt0 vertex_setN0 ?compact_pointed.
rewrite {2}[P]conv_vertex_set // => ->.
by rewrite conv_pt dim_pt.
Qed.

Lemma polyEqT_poly0 (base : base_t[R,n]) (P : {poly base}) :
  compact P -> (\pdim P > 1)%N -> 'P^=(base; base) = [poly0].
Proof.
move/card_vertex_set_gt1 => h /h card_gt1.
have: (0 < #|` vertex_set P|)%N by apply/ltn_trans: card_gt1.
rewrite cardfs_gt0 => /fset0Pn [v v_in].
have: (0 < #|` (vertex_set P `\  v)%fset |)%N
  by rewrite (@cardfsD1 _ v) v_in ltnS in card_gt1.
rewrite cardfs_gt0 => /fset0Pn [w w_in].
apply/eqP; rewrite -lex0.
have <-: [pt v]%:PH `&` [pt w]%:PH = 0%O.
- apply/poly_eqP => x; rewrite in_polyI !in_pt inE.
  apply/negbTE/negP; move/andP => [/eqP -> /eqP v_eq_w].
  by move: w_in; rewrite v_eq_w !inE eq_refl.
move: v_in (pt_proper0 v); rewrite in_vertex_setP.
case/face_setP => Q Q_sub Q_prop0.
move: w_in (pt_proper0 w); rewrite inE => /andP[_].
rewrite in_vertex_setP; case/face_setP => Q' Q'_sub Q'_prop0.
rewrite [Q]repr_active // [Q']repr_active //.
rewrite polyEq_polyI polyEq_antimono //.
by apply/fsubset_subP.
Qed.

Lemma face_coatomistic (P : 'compact[R]_n) (F : face_set P) :
  coatomistic F.
Proof.
case: P F; case.
elim/non_redundant_baseW => base non_redundant P_pointed P_compact /=.
set P := Pointed P_pointed => F.
set L := [gradedFinLatticeType of face_set P].
case/altP: (F =P 0)%O => [-> | F_neq0]; last first.
apply/coatomisticP.
case/altP: (F =P 1)%O => [-> | F_neq_P].
- exists set0; first by move => x; rewrite inE.
  by rewrite big_pred0 //; move => x; rewrite inE.
- pose F' := insubd (val P)%:poly_base (val F).
  have F'_eq: F' = val F :> 'poly_n.
  + by rewrite /F' /insubd insubT //= (face_set_has_base (valP F)).
  have F'_prop_P : F' `<` P :> 'poly_n.
  + rewrite lt_neqAle andbC poly_base_subset /=.
    by move: F_neq_P; apply/contra_neq => ?; apply/val_inj => /=; rewrite -F'_eq.
  have F'_prop0 : F' `>` [poly0].
  + rewrite lt0x.
    by move: F_neq0; apply/contra_neq => ?; apply/val_inj => /=; rewrite -F'_eq.
  have h i : i \in base -> 'P^=(base; [fset i]) \in face_set P.
  + by move => ?; rewrite face_setE /= polyEq_antimono0.
  pose S := [set [` h _ (valP i)]%fset |
    i : base & (val i \in ({eq F'} `\` {eq (val P)%:poly_base})%fset) ].
  exists S; last first.
  + apply/le_anti/andP; split.
    * apply/meetsP => i /imsetP [{}i i_in -> /=].
      rewrite leEfaces -F'_eq /=.
      move: (fsvalP i) => ?; rewrite activeP /= fsub1set.
      by move: i_in; rewrite in_set in_fsetD => /andP[].
    * rewrite leEfaces -F'_eq polyI_facet //.
      - apply/meetsP => i _.
        + have i_in_base : val i \in base.
          * move: (valP i); rewrite in_fsetD => /andP[_].
            by apply/fsubsetP/fsubset_subP.
        suff: (\meet_(x in S) x <= [` h _ i_in_base]%fset)%O.
          rewrite leEfaces; apply: le_trans.
          by apply: lexx.
        apply/meets_inf/imsetP; exists [` i_in_base]%fset => //.
        + by rewrite in_set /= fsvalP.
        + by apply/val_inj => /=.
  +  move => Q; case/imsetP => i; rewrite in_set inE => /andP [i_notin _ ->].
     rewrite (@coatomE _ L).
     rewrite /rank /= -(rwP eqP) (dim_facet _ _ _ i_notin) ?fsvalP //.
       by apply/lt_trans: F'_prop_P.
apply/coatomisticP.
case: {2}(\pdim 'P(base)) (erefl (\pdim 'P(base))) => [dimP0|].
- exists set0; first by move => ?; rewrite in_set0.
  rewrite big_pred0; last by move => ?; rewrite in_set0.
  symmetry; apply/eqP.
  by rewrite -(@rank_eq0 _ L) /rank /= dimP0.
- case => [dimP1 |k dimP].
  + exists [set 0%O].
    * move => ?; rewrite in_set1 => /eqP ->.
      by rewrite (@coatomE _ L) !/rank /= dimP1 dim0.
    * by rewrite (big_pred1 0%O) // => ?; rewrite !inE.
  + move: (leq_addr k 2); rewrite add2n -{}dimP => dimP_gt1.
    have h i : i \in base -> 'P^=(base; [fset i]) \in face_set P.
    * by move => ?; rewrite face_setE /= polyEq_antimono0.
    have P_prop0: 'P(base) `>` [poly0] by move: dimP_gt1; rewrite dimN0; apply/ltn_trans.
    pose E := {eq ('P(base))%:poly_base} : {fset _}.
    have E_prop : (E `<` base)%fset.
    * rewrite /E fsubset_properT; move: (P_prop0); apply/contraTneq.
      have {2}->: 'P(base) = 'P(base)%:poly_base by [].
      rewrite {2}['P(base)%:poly_base]repr_active //= => ->.
      by rewrite (polyEqT_poly0 P_compact) ?ltxx.
    pose S := [set [` h _ (valP i)]%fset | i : base & (val i \notin E) ].
    exists S; last first.
    - apply/le_anti/andP; split; first by apply/le0x.
      rewrite leEfaces.
      have ->: val (0%O : face_set P) = [poly0] by [].
      rewrite -(polyEqT_poly0 P_compact) //.
      suff ->: 'P^=(base; base) =
        \meet_(i : base | (val i) \notin E) 'P^=(base; [fset (val i)]).
      + apply/meetsP => i i_notin.
        suff: (\meet_(x in S) x <= [` h _ (valP i)]%fset)%O.
          by rewrite leEfaces /=; apply/le_trans.
        apply/meets_inf/imsetP; exists i => //; by rewrite in_set i_notin.
      + rewrite polyEq_big_polyI;
        last by apply/pred0Pn; move/fproperP: E_prop => [_] [e e_in ?]; exists [` e_in]%fset.
        have ->: 'P^=(base; base) = 'P^=(base; (base `\` E) `|` E).
        * apply/congr1; apply/fsetP => e; rewrite in_fsetU.
          apply/idP/idP.
          - rewrite in_fsetD => ->; rewrite andbT; by case: (e \in E).
          - case/orP.
            by rewrite in_fsetD => /andP [].
            rewrite /E; apply/fsubsetP/fsubset_subP.
        rewrite -polyEq_polyI {3}/E.
        move: (@repr_active _ _ _ 'P(base)%:poly_base) => /(_ P_prop0)/(congr1 val) //= <-.
        have /meet_l ->: 'P^=(base; base `\` E) `<=` 'P(base) by apply/polyEq_antimono0.
        apply/congr1/fsetP => e; apply/idP/idP.
        - rewrite in_fsetD => /andP [e_notin e_in].
          apply/bigfcupP; exists ([`e_in]%fset) => //.
          * by rewrite /index_enum unlock -enumT mem_enum /=.
          * by rewrite in_fset1.
        - case/bigfcupP => e'; rewrite in_fset1 => /andP [_ e'_not_in] /eqP ->.
          by rewrite in_fsetD e'_not_in /= fsvalP.
    - move => Q; case/imsetP => i; rewrite in_set => i_notin ->.
      rewrite (@coatomE _ L).
      by rewrite /rank /= -(rwP eqP) (dim_facet _ _ _ i_notin) ?fsvalP //.
Qed.

End Coatomistic.

Section SeparationVertex.

Context {R : realFieldType} {n : nat}.

Lemma sep_vertex (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P -> v \notin conv (vertex_set P `\ v)%fset.
Proof.
move => P_compact.
rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) [c c_bounded pt_eq].
pose S := [seq '[c,x] | x <- (vertex_set P `\ v)%fset].
pose α := min_seq S ('[c,v]+1%R).
have v_notin: v \notin [hs [<c, α>]].
- rewrite /α; case: min_seqP => [| ? [/mapP [z] z_in -> _]].
  + by rewrite in_hs -ltNge cpr_add ltr01.
  + move: z_in; rewrite 2!inE => /andP [z_neq_v /vertex_set_subset z_in].
    have /(notin_argmin c_bounded z_in): z \notin argmin P c
      by rewrite -pt_eq in_pt.
    rewrite in_hsN in_hs /=.
    suff ->: '[c,v] = opt_value c_bounded by [].
    move: (argmin_opt_value c_bounded).
    rewrite -pt_eq => /poly_leP/(_ v).
    by rewrite in_pt_self in_hp => /(_ isT)/eqP ->.
- suff: conv (vertex_set P `\ v)%fset `<=` [hs [<c,α >]].
  + by apply/contraL => v_in; apply/poly_lePn; exists v.
  + apply/conv_subset => w w_in.
    by rewrite in_hs /= /α; apply/min_seq_ler/mapP; exists w.
Qed.

Lemma vertex_set_conv_subset (V : {fset 'cV[R]_n}) :
  (vertex_set (conv V) `<=` V)%fset.
Proof.
set P := conv V.
apply/fsubsetP => v v_vtx.
move/vertex_set_subset: (v_vtx) => v_in.
move: v_vtx;
  rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) [c] c_bounded.
move/in_convP: v_in => {v} [w w_supp ->].
set v := combine w => eq_argmin.
have /forallPn [x]:
  ~~ [forall v : V, val v \notin [hs -[<c, opt_value c_bounded>]]].
- move: (in_pt_self v); rewrite eq_argmin argmin_polyIN in_polyI => /andP [_].
  apply/contraL; move/forallP => h.
  suff: v \in [predC [hs -[<c, opt_value c_bounded>]]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => x /(fsubsetP w_supp) x_in.
  have ->: x = val [` x_in]%fset by [].
  by apply/h.
rewrite negbK => x_in.
have {x_in}: val x \in argmin P c
  by rewrite argmin_polyIN inE x_in andbT in_conv ?fsvalP.
rewrite -eq_argmin in_pt => /eqP <-; exact: fsvalP.
Qed.

Definition sep_hp (e : lrel[R]_n) (V : {fset 'cV_n}) (x : 'cV_n) :=
  (x \notin [hs e]) && [forall v : V, (val v) \notin [hs -e]].

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : polyh_scope.

Lemma sep_hpP {e : lrel[R]_n} {V : {fset 'cV_n}} {x : 'cV_n} :
  reflect ((x \notin [hs e]) /\ (forall y, y \in conv V -> y \notin [hs -e]))
          ([e separates x from V]).
Proof.
apply: (iffP andP) => [[? /forallP h] | [? h]]; split => //.
- move => y /in_convP [w w_supp ->].
  suff: combine w \in [predC [hs -e]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => v /(fsubsetP w_supp) v_in.
  have ->: v = val [` v_in]%fset by []; apply/h.
- by apply/forallP => v; apply/h/in_conv/fsvalP.
Qed.

Lemma conv_sep_hp (V : {fset 'cV_n}) (x : 'cV_n) :
  x \notin conv V -> exists e : lrel, [e separates x from V].
Proof.
move/separation => [e x_notin /poly_leP sub].
rewrite in_hs -ltNge in x_notin.
pose e' := [<e.1, ('[e.1,x]+e.2)/2%:R >].
exists e'; apply/andP; split.
- by rewrite in_hs -ltNge /e' /= midf_lt.
- apply/forallP => v; rewrite in_hsN -ltNge /e' /=.
  move/in_conv/sub: (fsvalP v); rewrite in_hs.
  by apply/lt_le_trans; rewrite midf_lt.
Qed.

End SeparationVertex.

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : polyh_scope.

Section FaceSegment.

Context {R : realFieldType} {n : nat} .

Lemma vertex_set_segm (v v' : 'cV[R]_n) :
  vertex_set [segm v & v'] = [fset v; v']%fset.
Proof.
set V := [fset _; _]%fset; set S := conv _.
have sub: (vertex_set S `<=` V)%fset by apply/vertex_set_conv_subset.
apply/eqP; rewrite eqEfcard sub /=.
move: (conv_vertex_set (compact_conv [fset v; v']%fset)); rewrite -/S.
apply/contra_eqT => /=; rewrite -ltnNge cardfs2 ltnS.
case/altP: (#|` vertex_set S| =P 0%N) => /= [ /cardfs0_eq -> _|].
- by rewrite conv0 -lt0x segm_prop0.
- rewrite -lt0n => card_gt0.
  case/altP: (v =P v') => /= [_| neq card_le1].
  + by rewrite leqn0 => /eqP card_eq0; rewrite card_eq0 in card_gt0.
  + have {card_gt0} {card_le1} /eqP/cardfs1P [x ->]: #|` vertex_set S| = 1%N by apply/anti_leq/andP; split.
    apply/eqP; move/(congr1 (fun P => \pdim P)).
    by rewrite conv_pt dim_pt dim_segm neq.
Qed.

Lemma face_set_segm (v v' : 'cV[R]_n) :
  face_set [segm v & v'] = [fset [poly0]; [pt v]%:PH; [pt v']%:PH; [segm v & v']]%fset.
Proof.
set S := conv _.
apply/eqP; rewrite eqEfsubset; apply/andP; split; last first.
- apply/fsubsetP => F; rewrite !inE -!orbA; move/or4P.
  case; move/eqP ->;
    by rewrite ?poly0_face_set ?face_set_self -?in_vertex_setP ?vertex_set_segm ?inE ?eq_refl ?orbT.
- apply/fsubsetP => F F_face; rewrite !inE -!orbA.
  case: {2}(\pdim F) (erefl (\pdim F)).
  + by move/dim_eq0 ->; rewrite eq_refl.
  + case. move/(face_dim1 F_face) => [x ->].
    by rewrite vertex_set_segm !inE => /orP; case => /eqP ->; rewrite eq_refl /= ?orbT.
  + case. move => dimF2.
    have /(face_dim_geq F_face) ->: (\pdim F >= \pdim S)%N.
    * by rewrite dimF2 dim_segm; apply/(leq_ltn_trans (leq_b1 _)).
    * by rewrite eq_refl !orbT.
  + move => k dimF_eq; move: (face_dim_leqif_eq F_face).1; rewrite dim_segm dimF_eq ltnS.
    by move/leq_trans/(_ (leq_b1 _)); rewrite -ltn_predRL /= ltn0.
Qed.

End FaceSegment.

Section VertexFigureHyp.

Context {R : realFieldType} {n : nat}.

Definition vf_hyp (P : 'poly[R]_n) (v : 'cV[R]_n) (e : lrel[R]_n) :=
  ((v \in vertex_set P) * [e separates v from ((vertex_set P) `\ v)%fset])%type.

End VertexFigureHyp.

Module VertexFigurePolyBase.
Section VertexFigurePolyBase.

Context {R : realFieldType} {n : nat}.

Variable (base : base_t[R,n]) (P : {poly base}) (v : 'cV[R]_n) (e0 : lrel[R]_n).
Hypothesis P_compact : compact P.
Hypothesis hyp : vf_hyp P v e0.
Let v_vtx := hyp.1.
Let sep_v := (sep_hpP hyp.2).1.
Let sep_other := (sep_hpP hyp.2).2.

Let L := [fset F in face_set P | v \in F]%fset.
Let Φ := (slice e0).

Lemma vf_vtx (F : 'poly[R]_n) :
  F \in L -> v \in vertex_set F.
Proof.
rewrite !inE /= => /andP [F_face ?].
by rewrite (vertex_set_face F_face) !inE v_vtx.
Qed.

Lemma vf_L_v_in (F : 'poly[R]_n) :
  F \in L -> v \in F.
by rewrite !inE /= => /andP [??].
Qed.

Lemma vf_L_prop0 (F : 'poly[R]_n) :
  F \in L -> F `>` [poly0].
by move/vf_L_v_in => ?; apply/proper0P; exists v.
Qed.

Lemma vf_L_face (F : 'poly[R]_n) :
  F \in L -> F \in face_set P.
by rewrite !inE /= => /andP [??].
Qed.

Lemma vf_L_other_pt (F : 'poly[R]_n) :
  F \in L -> (\pdim F > 1)%N -> exists2 x, x \in F & x \notin [hs -e0].
Proof.
move => F_in_L dimF_gt1.
rewrite [F]conv_vertex_set ?(face_compact P_compact) ?vf_L_face // in dimF_gt1.
suff /fsubsetPn [w w_vtx w_neq] : ~~ (vertex_set F `<=` [fset v])%fset.
- exists w; first by move: w_vtx => /vertex_set_subset w_in_F.
  apply/sep_other/in_conv; rewrite inE w_neq /=.
  by move: w_vtx; apply/fsubsetP/vertex_setS/vf_L_face.
- move: dimF_gt1; apply: contraTN => sub.
  suff ->: vertex_set F = [fset v]%fset by rewrite conv_pt dim_pt.
  by apply/eqP; rewrite eqEfsubset fsub1set ?vf_vtx ?andbT.
Qed.

Lemma vf_prop0 (F : 'poly[R]_n) :
  F \in L -> (\pdim F > 1)%N -> (Φ F) `>` [poly0].
Proof.
move => F_in_L dimF_gt1.
move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
have w_in_hs : w \in [hs e0] by apply/hsN_subset/w_notin.
move: (hp_itv w_in_hs sep_v) => [α /ltW_le α01].
set x := _ + _ => x_in_hp; apply/proper0P; exists x.
by rewrite in_slice x_in_hp mem_poly_convex ?vf_L_v_in.
Qed.

Lemma vf_eq (F : {poly base}) :
  (pval F) \in L -> (\pdim F > 1)%N -> {eq (Φ F)%:poly_base} = (e0 +|` {eq F})%:fsub.
Proof.
move => F_in_L dimF_gt1.
apply/fsubset_inj/eqP; rewrite eq_sym eqEfsubset active_slice.
apply/fsubset_fsubsetP => i; rewrite inE.
move/orP; case => [| i_in_base];
  first by rewrite in_fset1 => /eqP -> _; rewrite inE in_fset1 eq_refl.
apply/contraTT; rewrite inE negb_or => /andP [_].
rewrite in_active // => /poly_lePn => [[x] x_in_F x_notin_hp].
case: (boolP (x \in [hs -e0])) => [x_in | /hsN_subset x_in].
- move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
  move: (hp_itv x_in w_notin) => [α α01].
    set y := _ + _; rewrite hpN => y_in_hp.
    rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_lePn; exists y.
    + by rewrite in_slice y_in_hp; apply/mem_poly_convex => //; apply/ltW_le.
      move: x_notin_hp; rewrite !inE; apply/contraNN/hp_extremeL => //.
      by apply/(poly_leP (poly_base_subset_hs _ _)) : x_in_F.
      by apply/(poly_leP (poly_base_subset_hs _ _)) : w_in_F.
- move: (hp_itv x_in sep_v) => [α α01].
  set y := _ + _ => y_in_hp.
  rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_lePn; exists y.
  + by rewrite in_slice y_in_hp mem_poly_convex ?vf_L_v_in ?ltW_le.
  + move: x_notin_hp; rewrite !inE; apply/contraNN/hp_extremeL => //.
    by apply/(poly_leP (poly_base_subset_hs _ _)) : x_in_F.
    by move/vf_L_v_in: F_in_L; apply/(poly_leP (poly_base_subset_hs _ _)).
Qed.

Lemma vf_slice_pt : Φ ([pt v]%:PH) = [poly0].
Proof.
apply/le_anti; apply/andP; split; last exact: le0x.
apply/poly_leP => x; rewrite in_slice in_pt in_poly0 andbC.
move/andP => [/eqP -> /hp_subset_hs].
by move/negbTE: sep_v ->.
Qed.

Lemma vf_dim1 (F : 'poly[R]_n) :
  F \in L -> (\pdim F <= 1)%N -> F = ([pt v]%:PH) :> 'poly_n.
Proof.
move => F_in_L dim_le1; apply/eqP.
rewrite eq_sym -(geq_leqif (face_dim_leqif_eq _)) ?dim_pt //.
by rewrite -in_vertex_setP vf_vtx.
Qed.

Lemma vf_im (F : 'poly[R]_n) :
  F \in L -> (Φ F) \in face_set (Φ P).
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L.
case/face_setP => {}F F_sub_P F_in_L.
case: (ltnP 1 (\pdim F)) => [dim_gt1 | ?].
- by rewrite face_setE sliceS.
- by rewrite [pval F]vf_dim1 ?vf_slice_pt ?poly0_face_set.
Qed.

Lemma vf_e0_notin_eq (F : {poly base}) :
  pval F \in L -> e0 \notin ({eq F} : {fset _}).
Proof.
apply: contraL => /poly_base_subset_hp/poly_leP sub.
move: sep_v; apply/contraNN => /vf_L_v_in/sub.
by rewrite inE; apply/hp_subset_hs.
Qed.

Lemma vf_inj : {in L &, injective Φ}.
Proof.
move => F F'.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/face_setP => {}F F_sub_P F_in_L.
move => F'_in_L; move: (F'_in_L); move/vf_L_face: F'_in_L; case/face_setP => {}F' F'_sub_P F'_in_L.
case: (ltnP 1 (\pdim F)) => [dimF_gt1 | ?]; case: (ltnP 1 (\pdim F')) => [dimF'_gt1 | ?]; last first.
- by rewrite [pval F]vf_dim1 1?[pval F']vf_dim1.
- rewrite [pval F]vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F'_in_L dimF'_gt1); rewrite -eq ltxx.
- rewrite [pval F']vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F_in_L dimF_gt1); rewrite eq ltxx.
- move/pval_inj/(congr1 active); rewrite ?vf_eq //=.
  rewrite {3}[F]repr_active 1?{3}[F']repr_active ?vf_L_prop0 //.
  move/(congr1 (fun (x : {fsubset _}) => (x `|- e0))) => /=.
  by rewrite !/funslice !/fslice !fsetU1K ?vf_e0_notin_eq // => ->.
Qed.

Lemma vf_mem_v (F : 'poly[R]_n) :
  F \in face_set P -> Φ F `>` ([poly0]) -> v \in F.
Proof.
move => F_face PhiF_prop0; apply/vertex_set_subset; move: PhiF_prop0.
apply/contraTT; rewrite lt0x => v_notin; rewrite negbK.
apply/eqP; apply/le_anti; apply/andP; split; last exact: le0x.
rewrite [F]conv_vertex_set ?(face_compact P_compact) //.
apply/poly_leP => x; rewrite in_slice andbC => /andP [/in_convP [y /fsubsetP y_supp ->] in_e0].
have: combine y \in [predC [hs -e0]].
- apply/convexW; first exact: hsC_convex.
  move => w /y_supp w_vtx; rewrite inE.
  apply/sep_other/in_conv; rewrite !inE.
  apply/andP; split; move: w_vtx.
  + by apply/contraTneq => ->.
  + by apply/fsubsetP/vertex_setS.
rewrite !inE in_hsN in_hp in in_e0 *.
by move/eqP: in_e0 ->; rewrite lexx.
Qed.

Lemma vf_P_in_L : pval P \in L.
Proof.
by rewrite !inE; rewrite ?face_set_self ?vertex_set_subset.
Qed.

Lemma vf_surj (F : 'poly[R]_n) :
  F \in face_set (Φ P) -> exists2 F', F' \in L & F = Φ F'.
Proof.
move => F_face.
case: (emptyP F) => [->| F_prop0].
- exists ([pt v]%:PH); rewrite ?vf_slice_pt //.
  by rewrite !inE -in_vertex_setP in_pt eq_refl andbT.
- move: F_face F_prop0; case/face_setP => {}F F_sub F_prop0.
  set F' := 'P^=(base; ({eq F} `|- e0))%:poly_base.
  have F_eq : F = (Φ F') :> 'poly_n.
  + rewrite {1}[F]repr_active //= /Φ slice_polyEq /fslice fsetD1K //.
    rewrite in_active ?inE ?eq_refl //.
    by apply/(le_trans F_sub)/leIl.
  rewrite F_eq; exists (pval F') => //.
  suff F'_face: pval F' \in face_set P by rewrite 2!inE vf_mem_v ?andbT ?F'_face -?F_eq.
  rewrite face_setE [P]repr_active ?vf_L_prop0 ?vf_P_in_L ?polyEq_antimono //.
  move/activeS/(fsubset_trans (active_slice _ _))/(fsetSD [fset e0]%fset): F_sub.
  by rewrite fsetU1K ?vf_e0_notin_eq ?vf_P_in_L.
Qed.

Lemma vf_dim (F : 'poly[R]_n) :
  F \in L -> (\pdim F = (\pdim (Φ F)).+1)%N.
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/face_setP => {}F F_sub_P F_in_L.
case: (ltnP 1 (\pdim F)) => [dim_gt1 | ?]; last first.
- by rewrite [pval _]vf_dim1 // dim_pt vf_slice_pt dim0.
- have hull_PhiF : hull (Φ F) = (hull F) `&` [hp e0].
  + rewrite !hullN0_eq ?vf_prop0 ?vf_eq //.
    * by rewrite span_fsetU span_fset1 affine_addv meetC.
    * by rewrite dimN0; apply/ltn_trans: dim_gt1.
  rewrite dim_hull [in RHS]dim_hull hull_PhiF !hull_affine .
  apply/dim_affineI; last by rewrite -hull_PhiF -hullN0 vf_prop0.
  rewrite -hullP.
  apply/poly_lePn; exists v; first by rewrite vf_L_v_in.
  by move: sep_v; apply/contraNN; rewrite affE; apply/hp_subset_hs.
Qed.

End VertexFigurePolyBase.
End VertexFigurePolyBase.

Section VertexFigure.

Context {R : realFieldType} {n : nat}.

Definition face_set_itv (P : 'poly[R]_n) F F' :=
  [fset Q in face_set P | F `<=` Q `<=` F']%fset.

Lemma face_set_itv_vtx (P : 'poly[R]_n) (v : 'cV[R]_n) :
  v \in vertex_set P ->
  [fset Q in face_set P | v \in Q]%fset = face_set_itv P ([pt v]%:PH) P.
Proof.
move=> vP; apply/fsetP=> /= x; apply/idP/idP.
+ case/imfsetP=> /= {}Q /andP[QP vQ] ->; apply/imfsetP => /=.
  exists Q => //=; rewrite !inE QP /= pt_subset vQ /=.
  by apply: face_subset.
+ case/imfsetP=> /= Q /andP[QP /andP[vQ _]] ->; apply/imfsetP => /=.
  by exists Q => //; rewrite !inE QP /=; rewrite -pt_subset.
Qed.

Lemma vf_im (P : 'compact[R]_n) v e F :
  vf_hyp P v e ->
    F \in face_set_itv P ([pt v]%:PH) P -> (slice e F) \in face_set (slice e P).
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp F_in.
by apply/(VertexFigurePolyBase.vf_im hyp); rewrite face_set_itv_vtx ?hyp.1.
Qed.

Lemma vf_dim (P : 'compact[R]_n) v e F :
  vf_hyp P v e -> F \in face_set_itv P ([pt v]%:PH) P ->
                       \pdim F = (\pdim (slice e F)).+1.
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp F_in.
by apply/(VertexFigurePolyBase.vf_dim P_compact hyp); rewrite face_set_itv_vtx ?hyp.1.
Qed.

Lemma vf_inj (P : 'compact[R]_n) v e :
  vf_hyp P v e -> {in face_set_itv P ([pt v]%:PH) P &, injective (slice e)}.
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp Q Q' Q_in Q'_in ?.
by apply/(VertexFigurePolyBase.vf_inj P_compact hyp); rewrite ?face_set_itv_vtx ?hyp.1.
Qed.

Lemma vf_surj (P : 'compact[R]_n) v e F :
  vf_hyp P v e ->
  F \in face_set (slice e P) -> exists2 F', F' \in face_set_itv P ([pt v]%:PH) P & F = slice e F'.
Proof.
case: P => [[]]; elim/polybW => base P ? P_compact /= hyp.
move/(VertexFigurePolyBase.vf_surj P_compact hyp) => [F' F'_in eq_slice].
by exists F'; rewrite -?face_set_itv_vtx ?hyp.1.
Qed.

Lemma face_intervalE (P : 'pointed[R]_n) (F F' Q : face_set P) :
  (Q \in interval F F') = (val Q \in face_set_itv P (val F) (val F')).
Proof.
apply/intervalP/idP => [[le_FQ le_QF']|].
+ apply/imfsetP=> /=; exists (val Q) => //; rewrite !inE.
  by rewrite -!leEfaces le_FQ le_QF' (valP Q).
+ case/imfsetP=> /= Q' /andP[Q'P /andP[le_FQ' le_Q'F']] /esym Q'E.
  by rewrite !leEfaces /= -Q'E le_FQ' le_Q'F'.
Qed.

Lemma face_of_vtxP (P : 'poly[R]_n) (v : vertex_set P) :
  [pt (val v)]%:PH \in face_set P.
Proof.
by rewrite -in_vertex_setP (valP v).
Qed.

Definition face_of_vtx (P : 'poly[R]_n) (v : vertex_set P) :=
  [` face_of_vtxP v]%fset : face_set P.

Lemma vtx_of_atomP (P : 'pointed[R]_n) (F : face_set P) :
  atom F -> exists (v : vertex_set P), val F == [pt (val v)]%:PH.
Proof.
by move/atom_faceP => [x x_in ->]; exists [` x_in]%fset.
Qed.

Definition vtx_of_atom (P : 'pointed[R]_n) (F : face_set P) (F_atom : atom F) :=
  xchoose (vtx_of_atomP F_atom).

Lemma vtx_of_atomE (P : 'pointed[R]_n) (F : face_set P) (F_atom : atom F) :
  [pt (val (vtx_of_atom F_atom))]%:PH = val F.
Proof.
rewrite /vtx_of_atom; set s := (X in xchoose X).
by move: (xchooseP s) => /eqP <-.
Qed.

Section LiftSlice.

Variable (P : 'compact[R]_n) (Fv : face_set P).
Hypothesis Fv_atom : atom Fv.
Let v := vtx_of_atom Fv_atom.
Let e := xchoose (conv_sep_hp (sep_vertex (valP P) (valP v))).

Local Lemma hyp : vf_hyp P (val v) e.
split; first apply/valP.
by apply: (xchooseP (conv_sep_hp (sep_vertex (valP P) (valP v)))).
Qed.

Lemma lift_sliceP (F : face_set P) :
  F \in interval Fv 1%O -> slice e (val F) \in face_set (slice e P).
Proof.
by rewrite face_intervalE /= => ?; apply/(vf_im hyp); rewrite vtx_of_atomE.
Qed.

Definition lift_slice (F : '[< Fv; 1%O >]) := [` lift_sliceP (valP F) ]%fset.

Lemma lift_slice_inj : injective lift_slice.
Proof.
move => F F' lift_eq.
apply/val_inj/val_inj/(vf_inj hyp) => //.
- by rewrite vtx_of_atomE; move: (valP F); rewrite face_intervalE /=.
- by rewrite vtx_of_atomE; move: (valP F'); rewrite face_intervalE /=.
- by move/(congr1 val): lift_eq.
Qed.

Lemma lift_slice_surj (F : face_set (slice e P)) : exists F', F = lift_slice F'.
Proof.
move: (vf_surj hyp (valP F)) => [F0].
rewrite !inE /= => /andP [F_face v_in F_eq].
rewrite vtx_of_atomE in v_in.
exists (insubd (0 : '[<Fv; 1>])%O [` F_face]%fset ).
by apply/val_inj => /=; rewrite F_eq /insubd insubT //=.
Qed.

End LiftSlice.

Lemma inj_surj_bij (T1 T2: finType) (f : T1 -> T2) :
  injective f -> (forall y, exists x, y = f x) -> bijective f.
Proof.
move => f_inj f_surj.
have f_surj': forall y, exists x, y == f x by move => y; move: (f_surj y) => [x ->]; exists x.
pose g y := xchoose (f_surj' y); exists g.
- by move => x; apply/f_inj/eqP; rewrite eq_sym (xchooseP (f_surj' (f x))).
- by move => y; apply/eqP; rewrite eq_sym (xchooseP (f_surj' y)).
Qed.

(*
Lemma fin_joinE (disp : unit) (L : finLatticeType disp) (x y : L) :
  (x `|` y = \meet_(z : L | (z >= x) && (z >= y)) z)%O.
Proof.
apply/le_anti/andP; split.
- by apply/meetsP => z; rewrite leUx.
- by apply/meets_inf; rewrite leUl leUr.
Qed.*)

Lemma inj_mono (disp : unit)  (L L' : latticeType disp) (f : L -> L') :
  injective f -> {morph f : x y / (x `&` y)%O >-> (x `&` y)%O} -> {mono f : x y / x <= y}%O.
Proof.
move => f_inj f_meet x y.
by rewrite !leEmeet -f_meet (inj_eq f_inj).
Qed.

(*
Lemma bij_on_bij (I J : Type) (f : I -> J) (P : pred J) :
  bijective f -> {on P, bijective f}.
Proof.
by move => [g fgK gfK]; exists g => ??; [ apply/fgK | apply/gfK ].*)

Lemma bij_omorphism (disp : unit) (L L' : finLatticeType disp) (f : L -> L') :
  bijective f -> {morph f : x y / (x `&` y)%O >-> (x `&` y)%O} -> omorphism f.
Proof.
case => g fgK gfK f_meet; split => //.
have f_mono := (inj_mono (can_inj fgK) f_meet).
move => x y; apply/le_anti/andP; split.
- by rewrite -[X in (_ <= X)%O]gfK f_mono leUx -!f_mono gfK leUl leUr.
- by rewrite leUx !f_mono leUl leUr.
Qed.

Lemma vertex_figure (P : 'compact[R]_n) (x : face_set P) : atom x ->
  exists Q : 'compact[R]_n,
  exists f : {omorphism '[< x; 1 >] -> face_set Q}%O, bijective f.
Proof.
move => x_atom.
pose v := vtx_of_atom x_atom.
pose e := xchoose (conv_sep_hp (sep_vertex (valP P) (valP v))).
pose Q := Compact (compact_slice e (valP P)); exists Q.
pose f := lift_slice x_atom.
have f_bij : bijective f.
- apply/inj_surj_bij; by [apply/lift_slice_inj | apply/lift_slice_surj].
have f_omorph : omorphism f.
- apply/bij_omorphism => //.
  move => y z; apply/val_inj => /=; rewrite -/e.
  by apply/poly_eqP => u; rewrite !inE andbACA andbb.
by exists (OMorphism f_omorph).
Qed.

End VertexFigure.

(* -------------------------------------------------------------------- *)
Local Open Scope order_scope.

Section ClosednessByInterval.
Context (R : realFieldType) (n : nat) (P : 'compact[R]_n).

Lemma closed_by_interval_r (x : face_set P) :
   exists Q : 'compact[R]_n,
   exists2 f : {omorphism '[< x; 1 >] -> face_set Q},
     bijective f & \pdim P = (\pdim Q + rank x)%N.
Proof.
elim/rank_ind: x => /= x; case: (x =P 0) => [-> _|/eqP nz_x ih].
+ pose h := omorph_full_intv_val [tbLatticeType of face_set P].
  exists P, (TBOMorphism h); first by apply: bij_full_intv_val.
  by rewrite rank0 addn0.
case: (graded_rankS (x := x)); first by rewrite rank_gt0 lt0x.
move=> y lt_y_x /esym rkxE; case: (ih y _); first by rewrite rkxE.
move=> Q [f bij_f rkPE]; set I := '[< f x%:I; 1 >].
case: (@vertex_figure R n Q (f x%:I)).
+ rewrite atomE.
  set L := [gradedFinLatticeType of '[<y;1>]].
  rewrite (@rank_morph_bij _ _ L) //; last by case: {+}f.
  by rewrite intv_rankE /= rkxE subSn // subnn.
move=> T [g bij_g]; exists T.
set h : _ -> face_set Q := fun (z : '[<x; 1>]) => f (z%:I_[< <~ y ; >]).
have hcodom z : h z \in interval (f x%:I) 1.
+ rewrite intervalE lex1 andbT /h; apply: omorph_homo.
  by rewrite leEsub /= (intervalPL (valP z)).
pose k (z : '[<x; 1>]) : face_set T := g (Interval (hcodom z)).
have morph_k: omorphism k; first apply/omorphismP=> z1 z2.
+ rewrite -omorphI; congr (g _); apply: val_inj => /=.
  by rewrite /h omorphI /= -omorphI; congr (f _); apply/val_inj.
+ rewrite -omorphU; congr (g _); apply: val_inj => /=.
  by rewrite /h omorphU /= -omorphU; congr (f _); apply/val_inj.
+ have bij_k: bijective k.
  apply: bij_comp => //; case: (bij_f) => fI fK Kf.
  set hI := fun (z : '[<f x%:I; 1>]) => fI (val z).
  have hcodomI z : val (hI z) \in interval x 1.
  * rewrite intervalE lex1 andbT /hI.
    apply: (le_trans (y := (val x%:I_[< y; 1 >]))) => //.
    rewrite -leEsub -(omorph_mono (bij_inj bij_f)).
    by rewrite Kf (intervalPL (valP z)).
  exists (fun z => Interval (hcodomI z)).
  * by move=> z; apply: val_inj => /=; rewrite /hI /h /= fK.
  * case=> /= [z hz] /=; apply: val_inj; rewrite /h /=.
    rewrite [X in f X](_ : _ = hI (Interval hz)) ?Kf //=.
    by apply: val_inj.
exists (OMorphism morph_k) => //=; rewrite rkxE -addSnnS.
have ->: \pdim T = rank (k 1).
+ set ok := bij_omorphism_tbomorphism bij_k morph_k.
  by have /= -> := omorph1 (TBOMorphism ok).
rewrite rank_morph_bij // {1}/rank /= /vrank /=.
by rewrite addSnnS -rkxE subnK //; apply/le_homo_rank/lex1.
Qed.

Lemma closed_by_interval (x y : face_set P) : (x <= y)%O ->
   exists Q : 'compact[R]_n,
   exists2 f : {omorphism '[< x; y >] -> face_set Q},
     bijective f & rank y = (\pdim Q + rank x)%N.
Proof.
case: (closed_by_interval_r x) => Q [f bij_f dimPE] le_xy.
set I : face_set Q := f y%:I; have cI: compact (val I).
+ by apply/(face_compact (valP Q))/valP.
have gI (z : '[<x; y>]) : val (f z%:I_[< ; 1%O ~> >]) \in face_set (val I).
+ rewrite (face_set_of_face (valP (f y%:I))).
  set zc := _%:I_[< ; 1 ~> >]; have le_zy: zc <= y%:I.
  - by rewrite leEsub /= (intervalPR (valP z)).
  rewrite 2!inE /=; apply/andP; split; first by apply: valP.
  by have := omorph_homo f le_zy; rewrite leEfaces.
pose g (z : '[<x; y>]) := [` gI z]%fset.
+ have bij_g: bijective g.
  case: bij_f => /= fI fK Kf.
  have hgK (z : face_set (val I)) : val z \in face_set Q.
  * by have /fsubsetP := face_setS (valP I); apply; apply/valP.
  pose gK (z : face_set (val I)) := fI [` hgK z ]%fset.
  have h z: x <= val (gK z) <= y.
  * rewrite (intervalPL (valP _)) /gK /=.
    set qy := y%:I_[< x; 1 >]; suff: fI [`hgK z]%fset <= qy by [].
    rewrite -(omorph_mono (can_inj fK)) Kf leEfaces /qy /=.
    by apply: face_subset.
  exists (fun z => Interval (h z)).
  * case=> z hz /=; rewrite /gK /=; apply: val_inj=> /=.
    set c := (X in fI {| fsval := fsval X |}).
    rewrite [X in fI X](_ : _ = c) //; first by rewrite /c fK.
    by apply: val_inj.
  * case=> /= z hz /=; apply: val_inj; rewrite /g /=.
    rewrite [_%:I_[< ; 1 ~> >]](_ : _ = gK [`hz]%fset).
    - by rewrite Kf. - by apply: val_inj.
have morph_g: omorphism g.
+ apply/bij_omorphism => // z1 z2; rewrite /g /=.
  by apply: val_inj => /=; rewrite widdenRI omorphI.
exists (Compact cI), (OMorphism morph_g) => //=.
pose J : 'pointed[R]_n := Pointed (compact_pointed cI).
pose JL := [gradedFinLatticeType of face_set J].
have ->: \pdim (fsval I) = rank (g 1 : JL).
+ set og := bij_omorphism_tbomorphism bij_g morph_g.
  by have /= -> := omorph1 (TBOMorphism og).
rewrite rank_morph_bij // {2}/rank /= /vrank /=.
by rewrite subnK //; apply/le_homo_rank.
Qed.
End ClosednessByInterval.

(* -------------------------------------------------------------------- *)
Global Instance expose_lexx (disp : unit) (L : porderType disp) (x : L) :
  expose (x <= x)%O := Expose (lexx x).

(* -------------------------------------------------------------------- *)
Section DiamondProperty.
Context (R : realFieldType) (n : nat) (P : 'compact[R]_n).

Theorem diamond (x y : face_set P) :
  rank y = (rank x).+2 -> x <= y ->
  exists z1 z2 : face_set P,
    [/\ forall z : '[<x; y>], val z \in [:: x; y; z1; z2]
      , rank z1 = (rank x).+1
      , rank z2 = (rank x).+1
      , x <= z1 <= y & x <= z2 <= y].
Proof.
move=> rkyE le_xy; case: (closed_by_interval le_xy)=> [Q] [f bij_f].
rewrite {}rkyE -addn2 addnC => /addIn /esym.
case/dim2P => [|/= z1 [z2] QE ne_z]; first by case: {+}Q.
have hz1: [pt z1]%:PH \in face_set Q.
+ by rewrite QE face_set_segm !inE eqxx !(orbT, orTb).
have hz2: [pt z2]%:PH \in face_set Q.
+ by rewrite QE face_set_segm !inE eqxx !(orbT, orTb).
case: (bij_f) => /= fI fK Kf.
pose y1 := fI [` hz1]%fset; pose y2 := fI [` hz2]%fset.
exists (val y1), (val y2); split; first move=> z.
+ rewrite [in X in _ \in [:: X, _ & _]](_ : x = val x%:I_[< x; y >]) //.
  rewrite [in X in _ \in [:: _, X & _]](_ : y = val y%:I_[< x; y >]) //.
  set s := [:: x%:I; y%:I; y1; y2]; set s' := (X in _ \in X).
  have ->: s' = map val s by [].
  rewrite {s'}/s; rewrite mem_map; last by apply: val_inj.
  rewrite -(mem_map (f := val \o f)); last first.
  * by apply/inj_comp; [apply/val_inj | apply/(can_inj fK)].
  have /= := valP (f z); rewrite [in X in _ \in X -> _]QE.
  rewrite face_set_segm ![in X in X -> _]inE -!orbA.
  rewrite mem_seq4 -[X in _ -> X](rwP or4P) => /or4P[] /eqP->.
  * constructor 1; have ->: x%:I_[<x; y>] = 0 by apply: val_inj.
    case: {+}f bij_f => /= g morph_g bij_g.
    set h := bij_omorphism_tbomorphism bij_g morph_g.
    by have /= -> := (omorph0 (TBOMorphism h)).
  * by constructor 3; rewrite Kf.
  * by constructor 4; rewrite Kf.
  * constructor 2; have ->: y%:I_[<x; y>] = 1 by apply: val_inj.
    case: {+}f bij_f => /= g morph_g bij_g.
    set h := bij_omorphism_tbomorphism bij_g morph_g.
    by have /= -> := (omorph1 (TBOMorphism h)); rewrite -QE.
+ have: rank y1 = (rank x%:I_[<x; y>]).+1; last first.
  * rewrite {1 2}/rank /= /vrank /= subnn -[in X in _ -> X]addn1 => <-.
    rewrite subnKC //; apply/le_homo_rank/(intervalPL (valP y1)).
  rewrite (_ : x%:I = 0) ?rank0 /y1; last by apply: val_inj.
  (rewrite rank_morph_bij; last by exists f); last first.
  * by apply: (inv_is_omorphism fK Kf); case: {+}(f).
  by rewrite /rank /= dim_pt.
+ have: rank y2 = (rank x%:I_[<x; y>]).+1; last first.
  * rewrite {1 2}/rank /= /vrank /= subnn -[in X in _ -> X]addn1 => <-.
    rewrite subnKC //; apply/le_homo_rank/(intervalPL (valP y2)).
  rewrite (_ : x%:I = 0) ?rank0 /y1; last by apply: val_inj.
  (rewrite rank_morph_bij; last by exists f); last first.
  * by apply: (inv_is_omorphism fK Kf); case: {+}(f).
  by rewrite /rank /= dim_pt.
+ by apply: (valP y1).
+ by apply: (valP y2).
Qed.
End DiamondProperty.

Section Graph.

Context {R : realFieldType} {n : nat}.

Definition adj P :=
  [rel v w : 'cV[R]_n | (v != w) && ([segm v & w] \in face_set P)].

Lemma adj_sym P v w : adj P v w = adj P w v. (*symmetric adj.*)
Proof. by rewrite /= eq_sym fsetUC. Qed.

Lemma adj_vtxl P (v w : 'cV[R]_n) : adj P v w -> v \in vertex_set P.
Proof.
by move/andP => [_] segm_face; apply/(fsubsetP (vertex_setS segm_face));
   rewrite vertex_set_segm; rewrite !inE eq_refl.
Qed.
Lemma adj_vtxr P (v w : 'cV[R]_n) : adj P v w -> w \in vertex_set P.
Proof. by rewrite adj_sym; apply/adj_vtxl. Qed.

Lemma sub_adj P F : F \in face_set P -> subrel (adj F) (adj P).
Proof.
move=> F_face x y /= /andP [->] /=.
by apply/fsubsetP/(face_setS F_face).
Qed.

Lemma path_adj P p : forall v, v \in vertex_set P -> path (adj P) v p -> {subset p <= (vertex_set P)}.
Proof.
elim: p => // [a p] ind v v_vtx /= /andP [/adj_vtxr a_vtx p_path] x.
rewrite in_cons=> /orP; case => [/eqP-> //|].
by apply/(ind a a_vtx).
Qed.

Lemma vertex_set_slice_dim (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       forall F, F \in face_set P -> (v \in F) -> \pdim F = (\pdim (slice e F)).+1%N.
Proof.
  elim/polybW: P => base P P_compact v_vtx e e_sep F F_face v_in_F.
rewrite (VertexFigurePolyBase.vf_dim P_compact (v_vtx, e_sep)) //.
by rewrite inE /=; apply/andP.
Qed.

Lemma vertex_set_slice (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       vertex_set (slice e P) =
       [fset ppick (slice e F) | F in face_set P & ((v \in F) && (\pdim F == 2%N))]%fset.
Proof.
elim/polybW: P => base P P_compact v_vtx e e_sep.
apply/fsetP => ?; apply/imfsetP/imfsetP =>
  [[F] /= /andP [F_face dimF1] -> | [F] /= /and3P [F_face v_in_F dimF2] ->].
+ case/(VertexFigurePolyBase.vf_surj P_compact (v_vtx, e_sep)): F_face => F'.
  rewrite inE=> /andP [F'_face v_in_F'] F'_eq.
  exists F'; rewrite ?F'_eq ?inE //; apply/and3P; split=> //.
  by rewrite (vertex_set_slice_dim P_compact v_vtx e_sep) // -F'_eq eqSS.
+ exists (slice e F) => //; rewrite inE /=; apply/andP; split.
  - by apply/(VertexFigurePolyBase.vf_im (v_vtx, e_sep)); rewrite inE; apply/andP.
  - by move: dimF2; rewrite (vertex_set_slice_dim P_compact v_vtx e_sep).
Qed.

Variable (P : 'poly[R]_n).

Hypothesis (P_compact : compact P).

Lemma adj_argmin (c v : 'cV[R]_n) :
  v \in vertex_set P -> (forall w, adj P v w -> '[c,v] <= '[c,w]) -> v \in argmin P c.
Proof.
move=> v_vtx neigh_v.
rewrite in_argmin vertex_set_subset //=.
have P_prop0 : P `>` [poly0] by apply/proper0P; exists v; apply/vertex_set_subset.
pose sep := conv_sep_hp (sep_vertex P_compact v_vtx).
pose e := xchoose sep.
pose sep_v := (sep_hpP (xchooseP sep)).1.
pose sep_other := (sep_hpP (xchooseP sep)).2.
suff slice_sub: (slice e P `<=` [hs [<c, '[ c, v]>]]).
- rewrite [P]conv_vertex_set //; apply/conv_subset.
  move => w; case/altP : (w =P v) => [-> _| w_neq_v w_vtx]; first by rewrite in_hs.
  have w_in_hs : w \in [hs e].
    by apply/hsN_subset/sep_other/in_conv; rewrite !inE w_neq_v /=.
  move: (hp_itv w_in_hs sep_v) => [α α01].
  set x := _ + _ => /= x_in_hp.
  have {x_in_hp} /(poly_leP slice_sub) : x \in slice e P.
  - rewrite in_polyI /=; apply/andP; split; first by rewrite affE.
    by rewrite mem_poly_convex ?ltW_le ?vertex_set_subset.
  rewrite !in_hs /= /x combine2C combine2_line vdotDr ler_addl.
  rewrite vdotZr vdotBr pmulr_rge0 ?subr_ge0 //.
  by rewrite subr_cp0; move/andP: α01=> [].
- rewrite [slice _ _]conv_vertex_set ?compact_slice //; apply/conv_subset=> z.
  rewrite (vertex_set_slice P_compact v_vtx) ?(xchooseP sep) //.
  move/imfsetP => [F /and3P [F_face v_in_F /eqP dimF2] ->].
  have slice_prop0 : slice e F `>` [poly0].
  + rewrite (vertex_set_slice_dim P_compact v_vtx (xchooseP sep)) // in dimF2.
    by move/succn_inj: dimF2; rewrite dimN0 => ->.
  have: v \in vertex_set F by rewrite (vertex_set_face F_face) in_imfset // inE ?v_vtx.
  move: (F_face) slice_prop0.
  move/(dim2P (face_compact P_compact F_face)): dimF2 => [y [y' -> y_neq_y' yy'_face yy'_prop0]].
  have adj_y_y': adj P y y' by rewrite inE yy'_face y_neq_y'.
  move/vertex_setS: (yy'_face); rewrite vertex_set_segm => /fsubsetP sub_vtx v_in.
  suff: slice e [segm y & y'] `<=` [hs [<c, '[ c, v]>]].
    by move/poly_leP/(_ _ (ppickP yy'_prop0)).
  apply/(le_trans (leIr _ _))/conv_subset.
  move: v_in adj_y_y' => /fset2P; case=> <-;
    by move => adj_v u /fset2P; case=> ->; rewrite in_hs //= neigh_v // adj_sym.
Qed.

Variable (c : 'cV[R]_n).

Definition improve :=
  [rel v w | (adj P v w) && ('[c,w] < '[c,v])].

Lemma sub_improve_adj : subrel improve (adj P).
by move => ??/andP []. Qed.

Lemma argminN_improve (v : 'cV[R]_n) :
  v \in vertex_set P -> v \notin argmin P c -> exists w, improve v w.
Proof.
move => v_vtx v_notin.
suff /existsP: [exists w : vertex_set P, adj P v (fsval w) &&  ('[c,fsval w] < '[c,v])]
  by move => [w ?]; exists (fsval w).
move: v_notin; apply/contraR; rewrite negb_exists => /forallP neigh_v.
apply/adj_argmin => // w /[dup] w_adj /adj_vtxr w_vtx.
by move/(_ [` w_vtx]%fset): neigh_v; rewrite w_adj /= leNgt.
Qed.

Definition height (v : 'cV[R]_n) :=
  #|` [fset w in vertex_set P | '[c,w] < '[c,v]] |%fset.

Lemma heightP v :
  v \in P -> ((v \in argmin P c) = (height v == 0%N)).
Proof.
move=> v_in; rewrite in_argmin {}v_in /=.
apply/idP/eqP.
- move/poly_leP=> sub.
  apply/eqP; rewrite cardfs_eq0.
  apply/contraT; case/fset0Pn=> w.
  rewrite !inE=> /andP [/vertex_set_subset/sub].
  by rewrite in_hs /= => /le_lt_trans/[apply]; rewrite ltxx.
- move=> h0.
  rewrite [P]conv_vertex_set //; apply/conv_subset=> w.
  rewrite in_hs /= => w_vtx; move: h0; apply/contra_eqT.
  rewrite -ltNge cardfs_eq0 => c_w_v.
  by apply/fset0Pn; exists w; rewrite !inE; apply/andP.
Qed.

Lemma improve_path {v : 'cV[R]_n} :
  v \in vertex_set P ->
        exists2 p, path improve v p & last v p \in vertex_set (argmin P c).
Proof.
move: v {-1}(height v) (erefl (height v)) => /[swap] k.
elim: k {-2}k (leqnn k).
- move=> ?; rewrite leqn0=> /eqP ->.
  move=> v /[swap] v_vtx /eqP; rewrite -heightP => [v_in|]; last exact: vertex_set_subset.
  exists [::] => //=.
  rewrite (vertex_set_face (P := P)).
  + by rewrite !inE; apply/andP.
  + apply/argmin_in_face_set/compactP=> //.
    by apply/proper0P; exists v; apply/vertex_set_subset.
- move=> m ind k; rewrite leq_eqVlt ltnS.
  move/orP=> [/eqP -> v h_v v_vtx|]; last by apply: ind.
  have: v \notin argmin P c
    by rewrite heightP ?vertex_set_subset // h_v.
  case/(argminN_improve v_vtx)=> w /[dup] imp_v_w /andP [/adj_vtxr w_vtx w_lt_v].
  have h_w: (height w <= m)%N.
  + rewrite -ltnS -h_v.
    apply/fproper_ltn_card/fproperP; split.
    * move => x; rewrite !inE /= => /andP [-> /=].
      by move/lt_trans/(_ w_lt_v).
  * by exists w; rewrite !inE w_vtx //= ltxx.
  case: (ind _ h_w _ (erefl _) w_vtx) => p p_path last_in.
  by exists (w :: p) => //; apply/andP.
Qed.

End Graph.

Section Connectness.

Context {R : realFieldType} {n : nat}.

Theorem connected_graph (P: 'poly[R]_n) v w :
  compact P -> v \in vertex_set P -> w \in vertex_set P ->
    exists2 p, (path (adj P) v p) & w = last v p.
Proof.
move=> P_compact v_vtx; rewrite in_vertex_setP.
move/face_argmin/(_ (pt_proper0 _)) => [c c_bouned argmin_eq].
case: (improve_path P_compact c v_vtx) => p.
move/(sub_path (sub_improve_adj (c := c)))=> p_path.
rewrite -argmin_eq vertex_set1 inE=> /eqP <-.
by exists p.
Qed.

Lemma improve_path_lt (P : 'poly[R]_n) c p x v :
  path (improve P c) v p -> x \in p -> '[c,x] < '[c,v].
Proof.
move: v; elim: p => // [a p] ind.
move=> v p_path.
have a_lt_v: '[c,a] < '[c,v] by case/andP: p_path => /andP [_].
rewrite inE; move/orP; case=> [/eqP ->// | x_in_p].
apply/lt_trans: a_lt_v; apply/ind=> //.
by case/andP: p_path.
Qed.

Hypothesis (n_gt0 : n > 0).

Theorem balinski (P : 'poly[R]_n) (V : {fset 'cV[R]_n}) v w :
  compact P -> \pdim P = n.+1 -> (V `<=` vertex_set P)%fset -> #|` V | = n.-1 ->
    v \in (vertex_set P `\` V)%fset -> w \in (vertex_set P `\` V)%fset ->
      exists p, [/\ (path (adj P) v p), w = last v p & all [predC V] p].
Proof.
set S := (_ `\` _)%fset.
move=> P_compact dimP V_sub V_card v_in_S w_in_S.
have S_sub: (S `<=` vertex_set P)%fset by apply/fsubsetDl.
have v_vtx := (fsubsetP S_sub _ v_in_S).
have w_vtx := (fsubsetP S_sub _ w_in_S).
have P_prop0: (P `>` [poly0]).
  by apply/proper0P; exists v; apply/vertex_set_subset.
pose V' := (v |` V)%fset.
suff [e [z] [V'_sub z_in_P e_z e_w]]:
  exists e, exists z,
        [/\ {subset V' <= [hp e]}, z \in P, z \notin [hs e] & w \in [hs (-e)]].
- set c := e.1; set α := e.2.
  set F := argmin P c.
  have c_bounded : bounded P c by apply/compactP.
  have F_face : F \in face_set P by apply/argmin_in_face_set.
  have F_compact : compact F by apply/(face_compact P_compact).
  have c_F : forall x, x \in F -> '[c,x] < α.
  + move=> x /(poly_leP (argmin_opt_value c_bounded)).
    rewrite in_hp /= => /eqP ->.
    suff: '[c,z] < α.
    * apply/le_lt_trans.
      by rewrite -in_hs; apply/(poly_leP (opt_value_lower_bound c_bounded)).
    * by rewrite in_hs -ltNge in e_z.
  have c_v : '[c,v] = α.
  - by apply/eqP; rewrite -in_hp beE; apply/V'_sub/fset1U1.
  have c_V : forall x, x \in V -> '[c,x] = α.
  - move=> x xV; apply/eqP; rewrite -in_hp beE.
    by apply/V'_sub/fset1Ur.
  have c_w : '[c,w] <= α by rewrite in_hsN in e_w.
  case: (improve_path P_compact c v_vtx)
    => p1 /[swap] last_p1 /[dup] /(sub_path (sub_improve_adj (c := c))) p1_path
         /improve_path_lt cp1.
  case: (improve_path P_compact c w_vtx)
    => p2 /[swap] last_p2 /[dup] /(sub_path (sub_improve_adj (c := c))) p2_path
         /improve_path_lt cp2.
  case: (connected_graph F_compact last_p1 last_p2) => p3 p3_path last_p3.
  exists (p1 ++ p3 ++ (rev (belast w p2))); split.
  + rewrite !cat_path; apply/and3P; split=> //.
    * by move: p3_path; apply/(sub_path (sub_adj _)).
    * by rewrite -last_p3 rev_path -(eq_path (adj_sym P)).
  + rewrite !last_cat -last_p3.
    by case: (p2) => //= ??; rewrite rev_cons /= last_rcons.
  + rewrite !all_cat; apply/and3P; split.
    * apply/allP => x /cp1.
      by apply/contraL=> /c_V ->; rewrite c_v ltxx.
    * apply/allP=> x /(path_adj last_p1 p3_path)/vertex_set_subset/c_F.
      by apply/contraL=> /c_V ->; rewrite ltxx.
    * rewrite all_rev; apply/allP=> x /mem_belast.
      rewrite inE=> /orP [/eqP ->|/cp2 ].
      - by move: w_in_S; rewrite inE => /andP [].
      - by apply/contraL=> /c_V ->; rewrite -leNgt.
- have: (0 < #|` V' | <= n)%N.
  + apply/andP; split.
    * rewrite cardfs_gt0; apply/fset0Pn; exists v; apply/fset1U1.
    * rewrite cardfsU1 V_card addnC.
      by case: (boolP (v \notin V)) => [_|_] /=;
         rewrite ?addn1 ?ltn_predL ?addn0 ?leq_pred.
  move/subset_hp=> [e] e1_neq0 V'_sub_hp.
  case: (boolP (w \in [hp e])) => [w_in_hp | w_notin_hp].
  + have /poly_lePn [z z_in_P z_notin_hp]: ~~ (P `<=` [hp e]%:PH).
    * move: dimP; apply/contra_eqN.
      move/dimS; rewrite dim_hp; last first.
      - by apply/proper0P; exists w; rewrite affE.
      move/negbTE: e1_neq0 ->; rewrite /= add0n.
      by apply/contraTneq => ->; rewrite ltnn.
    case: (boolP (z \in [hs e])) => [z_in_hs | z_notin_hs].
    * exists (-e); exists z; rewrite hpN; split=> //.
      - move: z_notin_hp; apply: contraNN.
        by  rewrite hpE in_polyI z_in_hs.
      - by have := hp_subset_hs w_in_hp; apply/poly_leP; rewrite opprK.
    * exists e; exists z; split=> //.
      by move: w_in_hp; rewrite -affE hpE in_polyI => /andP[].
  + case: (boolP (w \in [hs e])) => [w_in | w_notin].
    * exists (-e); exists w; rewrite hpN opprK; split=> //.
      - by apply/vertex_set_subset/(fsubsetP S_sub).
      - move: w_notin_hp; apply: contraNN => wNe.
        by rewrite -affE hpE in_polyI w_in.
    * exists e; exists w; split=> //.
      - by apply/vertex_set_subset/(fsubsetP S_sub).
      - by apply/hsN_subset; rewrite opprK.
Qed.

End Connectness.

(* TODO : rename of delete section*)
Section Extra.

Context {R : realFieldType} {n : nat}.

(*TODO : move these lemmas somewhere else*)
Lemma imfset_mem {T T': choiceType} (S : {fset T}) (f : T -> T')  (x : S) :
  (f (fsval x) \in (f @` S))%fset.
Proof. exact/in_imfset/fsvalP. Qed.

Lemma sum_lin_vect {T T' : choiceType} (S : {fset T}) (vT : vectType R) (f : T -> T')
  (K : (f @` S)%fset -> vT) (K' : S -> vT) :
  (exists lambda : S -> R, forall i, (lambda i) *: (K' i) = K [` imfset_mem f i]%fset) ->
  exists mu: S -> R, \sum_i (K i) = \sum_i ((mu i) *: K' i).
Proof.
case=> lambda lambda_def.
exists (fun i => (lambda i) / (#|` [fset j : S | f (fsval j) == f (fsval i)] |%fset)%:R).
rewrite [RHS](partition_big (fun i => [`imfset_mem f i]%fset) predT) //=.
apply: eq_bigr=> i _.
have ->: K i = \sum_(i0 | [` imfset_mem f i0]%fset == i)
  ((#|` [fset j : S | f (fsval j) == (fsval i)] |%fset)%:R)^-1 *: (K i).
- rewrite -scaler_sumr sumr_const -scaler_nat scalerA /=.
  rewrite -[LHS]scale1r; congr (_ *: _).
  set y:= (X in _ * X); set x := (X in X ^-1 * _).
  suff ->: x = y.
  + rewrite mulVr // unitfE pnatr_eq0.
    apply/lt0n_neq0/card_gt0P=> /=.
    case/imfsetP: (fsvalP i)=> /= i' i'S ->.
    by exists [` i'S]%fset; rewrite unfold_in /= -eqE.
  congr (_ %:R).
  rewrite card_imfset //= cardE.
  apply/perm_size/uniq_perm; rewrite ?filter_uniq -?enumT ?enum_uniq //.
  by move=> z; rewrite mem_filter !mem_enum !unfold_in -eqE andbT.
apply: eq_bigr=> i' /eqP <- /=.
by rewrite -lambda_def scalerA mulrC.
Qed.

Lemma active_span_fst_eq (I J : base_t[R,n]) x :
  {subset J <= I} -> (<<(befst @` J)%fset>> = <<(befst @` I)%fset>>)%VS ->
  (forall e, e \in I -> x \in [hp e]) -> (<<I>> = <<J>>)%VS.
Proof.
move=> sub_IJ span1_IJ x_feas.
apply/eqP; rewrite eqEsubv [X in _ && X]sub_span ?andbT //.
apply/span_subvP=> e eI.
have: e.1 \in <<(befst @` I)%fset>>%VS by apply/memv_span/imfsetP=> /=; exists e; rewrite ?lfunE.
rewrite -span1_IJ span_def big_seq_fsetE /=.
case/memv_sumP=> J1_ J1_def e1_eq.
rewrite span_def big_seq_fsetE /=; apply/memv_sumP.
have foo: forall j: J, exists lambda, J1_ [`imfset_mem befst j]%fset == lambda *: befst (fsval j).
- move=> j; move/(_ isT): (J1_def [` imfset_mem befst j]%fset)=> /=.
  by case/vlineP=> lambda ->; exists lambda.
have [lambda e1_eq2]: exists lambda : J -> R, e.1 = \sum_j (lambda j) *: ((fsval j).1).
- rewrite e1_eq; apply/sum_lin_vect.
  pose sol := fun j => (xchoose (foo j)).
  exists sol; move=> i; move/eqP: (xchooseP (foo i)) => ->.
  by rewrite {3}lfunE.
exists (fun j => (lambda j) *: (fsval j)).
  by move=> i _; apply/memvZ/memv_line.
rewrite -[e]beE e1_eq2.
move: (x_feas _ eI); rewrite in_hp e1_eq2 vdot_sumDl; move/eqP=> <-.
apply/eqP/be_eqP=> /=; rewrite sum_lrel_fst_gen sum_lrel_snd_gen.
split=> //; apply/eq_big=> // i _; rewrite vdotZl /=.
move: (x_feas (fsval i))=> /(_ (sub_IJ _ (fsvalP i))).
by rewrite in_hp=> /eqP ->.
Qed.


Lemma in_polyEq_span (base I: base_t[R,n]) x :
  reflect (x \in 'P(base) /\ (forall e, e \in <<I>>%VS -> x \in [hp e])) 
  (x \in 'P^=(base; I)).
Proof.
apply/(iffP idP).
- case/in_polyEqP=> x_rel ->; split=> // e.
  have I_eq: enum_fset I =i [tuple of I] by done.
  rewrite (eq_span I_eq)=> /coord_span /= ->.
  rewrite in_hp sum_lrel_fst sum_lrel_snd vdot_sumDl.
  apply/eqP/eq_big_seq=> /= i _; rewrite vdotZl.
  congr (_ * _); move: (x_rel I`_i); rewrite mem_nth //.
  by move/(_ isT); rewrite in_hp; move/eqP.
- by case=> x_base x_hp; apply/in_polyEqP; split=> // e /memv_span /(x_hp).
Qed.

Lemma face_active_free_fset (base : base_t[R,n]) F :
  F `>` [poly0] ->
  reflect 
  (exists I, [/\ (I `<=` base)%fset, F = 'P^=(base;I),
    #|`(befst @` I)%fset| = (n.+1 - \pdim F)%N & free (befst  @` I)%fset ])
  ((F \in face_set 'P(base))).
Proof.
move=> F_n0.
apply/(iffP idP).
- move: F_n0=> /[swap] /face_setP [F'] F'_face F'_n0.
  move: (F'_n0); rewrite (repr_active F'_n0) /=.
  set I:= {eq F'}; move=> PF_n0.
  case/proper0P: (PF_n0)=> p p_feas.
  pose I' := ((befst \o val) @` I)%fset.
  pose I'' := span_gen I'.
  pose J := [fsetval e in I| (befst (val e)) \in I'']%fset.
  have subJI: {subset J <= I : {fset _}} by
    move=> x /imfsetP /= [? _ ->]; exact: fsvalP.
  have basis1_IJ: basis_of <<I'>>%VS (befst @` J)%fset.
  + rewrite (perm_basis (Y:=I'')) ?span_gen_basis //.
    apply/uniq_perm; rewrite ?span_gen_uniq ?fset_uniq //.
    move=> z; apply/idP/idP.
      + by case/imfsetP=> /= e /imfsetP /= [e']; rewrite inE=>  ? -> ->.
      + move=> zI''; move/(_ _ zI''): (mem_subseq (span_gen_sub I')).
        case/imfsetP=> /= e eI z_eq; rewrite z_eq; apply/in_imfset=> /=.
        by apply/imfsetP; exists e=> //=; rewrite inE -z_eq.
  have span_IJ: <<I>>%VS = <<J>>%VS. apply:(active_span_fst_eq (x:=p)) => //.
    + rewrite (span_basis basis1_IJ) ; apply/eq_span=> z.
      apply/idP/idP; case/imfsetP=> /= e eI ->.
      * exact/in_imfset/fsvalP.
      * by apply/imfsetP=> /=; exists [` eI]%fset.
    + by case/in_polyEqP: p_feas. 
  exists J; split.
  + apply/fsubsetP=> e /subJI.
    by apply: (@fsubset_incl _ _ I).
  + apply/le_anti/andP; split.
    * apply/polyEq_antimono/fsubsetP=> e.
      by case/imfsetP=> /= e' _ ->.
    * apply/poly_leP=> z /in_polyEq_span [z_base z_span].
      apply/in_polyEq_span; split=> // e.
      rewrite span_IJ; exact: z_span.
  + have ->: 'P^=(base; I) = F' by rewrite (repr_active F'_n0).
    rewrite (dimN0_eq F'_n0) (dir_hull F'_n0) dim_orthv.
    rewrite -subSn ?dim_cVn // subKn ?leqW ?dim_cVn // span_IJ.
    rewrite limg_span (eq_span (Y:=(befst @` J)%fset)); last (move=> z; apply/idP/idP).
    * apply: anti_leq; rewrite dim_span andbT (span_basis basis1_IJ).
      by move: (basis1_IJ); rewrite basisEdim; case/andP.
    * case/mapP=> z' z'J ->; exact/in_imfset.
    * case/imfsetP=> z' z'J ->; exact/map_f.
  + exact: (basis_free basis1_IJ).
- move: F_n0=> /[swap]; case=> I [I_base -> cardI freeI] F_n0.
  (* + by rewrite (face_setE 'P(base)%:poly_base) /= polyEq_antimono0. *)
  + by move/polyEq_baseP: (I_base)=> ?; rewrite face_setE /= polyEq_antimono0.
Qed.

Lemma segm_in_poly (P : 'poly[R]_n) x y :
  x \in vertex_set P -> y \in vertex_set P -> [segm x & y] `<=` P.
Proof.
move=> x_vtx y_vtx; apply: conv_subset=> z.
rewrite in_fset2=> h; apply/vertex_set_subset.
by case/pred2P: h=> ->.
Qed.

Lemma vertex_set_of_face (P Q: 'poly[R]_n) x: 
  x \in vertex_set P -> Q \in face_set P -> x \in Q -> x \in vertex_set Q.
Proof.
move=> x_vtx Q_face xQ; rewrite in_vertex_setP.
move/face_set_of_face: Q_face=> ->; rewrite !inE -in_vertex_setP x_vtx /=.
by apply/poly_leP=> z; rewrite in_pt=> /eqP ->.
Qed.


End Extra.

Section Facets.

Context {R : realFieldType} {n : nat}.

Definition facets (P : 'poly[R]_n):= 
  [fset F in face_set P | [poly0] < F & \pdim P == (\pdim F).+1]%fset.

Lemma facets0:
  facets [ poly0 ] = fset0.
Proof.
apply/eqP; rewrite -fsubset0; apply/fsubsetP=> F.
case/imfsetP=> /= F'; rewrite !inE face_set0 !inE.
by case/and3P=> /eqP ->; rewrite ltxx.
Qed.

Lemma facets_foo {base : base_t[R,n]}:
  non_redundant_base base ->
  [ poly0 ] `<` ('P(base)) %:poly_base ->
  (facets 'P(base) `<=` [fset 'P^=(base; [fset val i]) | i : base])%fset.
Proof.
move=> nrb_base base_prop0; apply/fsubsetP=> x.
case/imfsetP=> F /=; rewrite !inE /=.
case/and3P=> /face_setP [F'] /= F'_in F'_prop0 /eqP F'_dim ->.
move: (facetP nrb_base base_prop0 F'_prop0 F'_dim).
case=> i [i_base] _ ->; apply/imfsetP=> /=.
by exists [`i_base]%fset.
Qed.


Lemma facets_le {base : base_t[R,n]}:
  (#|` facets 'P(base) | <= #|` base|)%nat.
Proof.
rewrite -poly_of_non_redundant_base.
apply/(leq_trans (n:=#|` mk_non_redundant_base base|)).
- case: (emptyP 'P(mk_non_redundant_base base)).
    by move=> ->; rewrite facets0 cardfs0 leq0n.
  move: (mk_non_redundant_baseP base)=> /[swap].
  move/facets_foo=> /[apply] /fsubset_leq_card.
  move/leq_trans; apply.
  apply/(leq_trans (leq_imfset_card _ _ _))=> /=.
  by rewrite -cardE cardfE.
- apply/fsubset_leq_card/fsubsetP=> ? /imfsetP [/= x + ->].
  move/MkNonRedundantBase.mk_nonredundant_base_subset.
  by rewrite cats0.
Qed.


End Facets.

