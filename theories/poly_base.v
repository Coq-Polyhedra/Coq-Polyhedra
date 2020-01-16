(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx.
Require Import hpolyhedron polyhedron barycenter.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

Section PolyBase.

Variable (R : realFieldType) (n : nat).

Section FixedBase.

Definition has_base (base : base_t[R,n]) (P : 'poly[R]_n) & (phantom _ P):=
  (P `>` `[poly0]) ==>
    [exists I : {fsubset base}, P == 'P^=(base; I)].

Notation "'[' P 'has' '\base' base ']'" := (has_base base (Phantom 'poly[R]_n P)) : poly_scope.

Context {base : base_t[R,n]}.

Lemma has_baseP {P : 'poly[R]_n} :
  reflect ((P `>` `[poly0]) -> exists I : {fsubset base}, P = 'P^=(base; I)) [P has \base base].
Proof.
by apply/(iffP implyP) => [H /H /exists_eqP [I ->]| H /H [I ->]];
  [|apply/exists_eqP]; exists I.
Qed.

Inductive poly_base := PolyBase { pval :> 'poly[R]_n ; _ : [pval has \base base]}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin := Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType := Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin := Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType := Eval hnf in ChoiceType poly_base poly_base_choiceMixin.

Lemma poly_base_base (P : poly_base) : [pval P has \base base].
Proof.
(*exact: valP.*)
by case : P.
Qed.

Lemma poly0_baseP : [ `[poly0] has \base base].
Proof.
by rewrite /has_base poly_properxx.
Qed.
Canonical poly0_base := PolyBase poly0_baseP.

End FixedBase.

Notation "'[' P 'has' '\base' base ']'" := (has_base base (Phantom _ P)) : poly_scope.
Notation "'{poly'  base '}'" := (@poly_base base) : poly_scope.
Definition poly_base_of base (x : {poly base}) & (phantom 'poly[R]_n x) : {poly base} := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

Lemma polyEq_baseP base I :
  (I `<=` base)%fset -> [('P^=(base; I)) has \base base].
Proof.
move => Isub.
by apply/implyP => _; apply/exists_eqP => /=; exists (I %:fsub).
Qed.

Canonical polyEq_base base I (H : expose (I `<=` base)%fset) := PolyBase (polyEq_baseP H).

(*
Section Test.
Variable (base I : base_t[R,n]) (I' : {fsubset base}).
Hypothesis Isub : (I `<=` base)%fset.
Check ('P^=(base; I)%:poly_base) : {poly base}.
Check ('P^=(base; I')%:poly_base) : {poly base}.
End Test.
 *)

Variable base : base_t[R,n].

Variant poly_base_spec (P : {poly base}) : Prop :=
| PolyBase0 of (P = (`[poly0])%:poly_base) : poly_base_spec P
| PolyBaseN0 (I : {fsubset base}) of (P = 'P^=(base; I)%:poly_base /\ P `>` `[poly0]) : poly_base_spec P.

Lemma poly_baseP (P : {poly base}) : poly_base_spec P.
Proof.
case: (emptyP P) => [/val_inj -> | P_prop0]; first by constructor.
move/implyP/(_ P_prop0)/exists_eqP: (poly_base_base P) => [I ?].
constructor 2 with I.
split; [exact: val_inj | done].
Qed.

(*
Section Test.
Variable P Q : {poly base}.
Goal P = Q.
case/poly_baseP: P.
Abort.

End Test.
*)

Lemma poly_base_subset (P : {poly base}) :
  P `<=` 'P(base).
Proof.
case/poly_baseP : (P) => [->| I [-> _]];
  [ exact: poly0_subset | exact: polyEq_antimono0].
Qed.

Lemma poly_base_subset_hs (P : {poly base}) e :
  e \in base -> P `<=` `[hs e].
Proof.
move => ?; apply/(poly_subset_trans (poly_base_subset _)).
exact: poly_of_base_subset_hs.
Qed.

Definition set_of_poly_base (P : {poly base}) : option {fsubset base} :=
  if @idP (P `>` (`[poly0])) is ReflectT H then
    let I := xchoose (existsP (implyP (poly_base_base P) H)) in
    Some I
  else
    None.

Definition set_of_poly_base_pinv (I : option {fsubset base}) : {poly base} :=
  match I with
  | Some I' =>
    let P := 'P^=(base; I')%:poly_base in
    if set_of_poly_base P == Some I' then P else `[poly0]%:poly_base
  | None => `[poly0]%:poly_base
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
- rewrite proper0N_equiv in h.
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
suff ->: 'P(base) = 'P^=(base; fset0)%:poly_base by exact: poly_base_base.
by rewrite /= polyEq0.
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

Lemma polyI_baseP (P Q : {poly base}) & (phantom _ P) & (phantom _ Q):
  [(P `&` Q) has \base base].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= poly0I (valP (`[poly0]%:poly_base)).
case: (poly_baseP Q) => [->| I' [-> _]]; first by rewrite /= polyI0 (valP (`[poly0]%:poly_base)).
apply/has_baseP => _; exists (I `|` I')%fset%:fsub; by rewrite polyEq_polyI.
Qed.
Canonical polyI_base P Q := PolyBase (polyI_baseP (Phantom _ P) (Phantom _ Q)).

Lemma slice_baseP (e : base_elt) (P : {poly base}) :
  [(slice e P) has \base (e +|` base)].
Proof.
case: (poly_baseP P) => [->| I [-> _]]; first by rewrite /= slice0 (valP (`[poly0]%:poly_base)).
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
  have: x \in `[hp (combine w)] : 'poly[R]_n.
  - by rewrite inE w_comb /=; apply/eqP.
  move/(compl_slack_cond w_ge0 x_in_P0) => x_in_P0I.
  have ->: c = (combine w).1 by rewrite w_comb.
  apply/dual_sol_argmin; try by done.
  by apply/proper0P; exists x.
Qed.
Canonical argmin_base (P : {poly base}) c := PolyBase (argmin_baseP P c).

Lemma affine_base : [affine << base >> has \base base].
Proof.
by rewrite -polyEqT_affine; rewrite (valP ('P^=(_; _))%:poly_base).
Qed.
Canonical affine_baseP := PolyBase affine_base.

End PolyBase.

Notation "'{poly'  base '}'" := (@poly_base _ _ base) : poly_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base (Phantom _ P)) : poly_scope.

(*
Section Test.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Variables (P Q : {poly base}) (Q' : 'poly[R]_n) (x : 'cV[R]_n).

Set Printing Coercions.

Check (P `&` Q : 'poly[R]_n).
Check (x \in P).

Goal P `<=` Q' -> forall x, x \in P -> x \in Q'.
move/poly_subsetP => H z z_in_P.
by move/H: z_in_P.
Qed.

Goal (P = Q' :> 'poly[R]_n) -> x \in P -> x \in Q'.
move <-.
done.
Qed.

Unset Printing Coercions.

End Test.
*)

Section Active.

Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.

Fact active_key : unit. by []. Qed.

Definition active (P : {poly base}) := (* TODO: fix broken notation *)
  locked_with active_key
    ((\big[@fsetU _/fset0]_(I : {fsubset base} | (P `<=` 'P^=(base; I))) I)%:fsub).

Notation "'{eq'  P }" := (active P) : poly_scope.

(*
Section Test.
Variable (P : {poly base}).
Check {eq P}.
Goal {eq P} = fset0%:fsub :> {fsubset base}.
Set Printing Coercions.
apply/fsubset_inj => /=.
Abort.
Check 'P^=(base; {eq P}) : 'poly[R]_n.
Check 'P^=(base; {eq P})%:poly_base : {poly base}.
End Test.
 *)

Lemma repr_active (P : {poly base}) :
  P `>` (`[poly0]) -> P = ('P^=(base; {eq P}))%:poly_base.
Proof.
case/poly_baseP: (P) => [->|]; first by rewrite poly_properxx.
move => I [P_eq _] Pprop0; apply: val_inj => /=.
suff ->: 'P^=(base; {eq P}) =
  \polyI_(I : {fsubset base} | P `<=` 'P^=(base; I)) 'P^= (base; I) :> 'poly[R]_n.
- apply/poly_equivP/andP; split.
  + by apply/big_polyIsP.
  + rewrite P_eq; apply/big_poly_inf; exact: poly_subset_refl.
- rewrite polyEq_big_polyI /active; first by rewrite unlock_with.
  apply/pred0Pn; rewrite P_eq /=; exists I.
  exact: poly_subset_refl.
Qed.

Lemma activeP (P : {poly base}) (I : {fsubset base}) :
  (P `<=` 'P^=(base; I)) = (I `<=` {eq P})%fset.
Proof.
apply/idP/idP.
- by move => Psub; rewrite /active unlock_with; apply/bigfcup_sup.
- case: (emptyP P) => [-> _|]; first exact: poly0_subset.
  move/repr_active => {2}-> /=.
  exact: polyEq_antimono.
Qed.

Lemma subset_repr_active {P : {poly base}} :
  P `<=` 'P^=(base; {eq P}).
apply/poly_subsetP => x x_in_P.
have h: P `>` (`[poly0]) by apply/proper0P; exists x.
by rewrite [P]repr_active in x_in_P.
Qed.

Lemma active0 :
  {eq (`[poly0]%:poly_base : {poly base})} = base%:fsub.
Proof.
set A := {eq _}.
apply/val_inj/FSubset.untag_inj => /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; first exact: fsubset_subP.
- rewrite -activeP => /=; exact: poly0_subset.
Qed.

Lemma active_polyEq (I : {fsubset base}) :
  (I `<=` {eq 'P^=(base; I)%:poly_base})%fset.
Proof.
rewrite -activeP; exact: poly_subset_refl.
Qed.

Lemma poly_base_subset_hp {P : {poly base}} {e} :
  (e \in ({eq P} : {fset _})) -> (P `<=` `[hp e]).
Proof.
move => h.
have e_in_base : ([fset e] `<=` base)%fset.
- rewrite fsub1set.
  by apply/(fsubsetP (valP {eq P})).
set se := [fset e]%:fsub%fset : {fsubset base}.
have: (se `<=` {eq P})%fset by  rewrite fsub1set.
rewrite -activeP polyEq1 => P_sub.
apply: (poly_subset_trans P_sub); exact: poly_subsetIr.
Qed.

Lemma in_active {P : {poly base}} {e} :
  e \in base -> (e \in ({eq P} : {fset _})) = (P `<=` `[hp e]).
Proof.
move => e_in_base.
apply/idP/idP; first exact: poly_base_subset_hp.
set se := [fset e]%:fsub%fset : {fsubset base}.
move => P_sub.
suff: (se `<=` {eq P})%fset by  rewrite fsub1set.
rewrite -activeP polyEq1.
by apply/poly_subsetIP; split; try exact: poly_base_subset.
Qed.

Lemma activeS :
  {homo active : P Q / (P `<=` Q) >-> (Q `<=` P)%fset}.
Proof.
move => P Q; case: (poly_baseP P) => [-> | ? [_ P_prop0]].
- rewrite active0 poly0_subset => _; exact: fsubset_subP.
- case: (poly_baseP Q) => [-> | ? [_ Q_prop0]].
  + rewrite -subset0N_proper in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma activeI (P Q : {poly base}) :
  ({eq P} `|` {eq Q} `<=` {eq ((P `&` Q)%PH)%:poly_base})%fset.
Proof.
rewrite -activeP -polyEq_polyI.
by apply: polyISS; rewrite activeP.
Qed.

Lemma poly_base_proper (P Q : {poly base}) :
  ({eq Q} `<` {eq P})%fset -> P `<` Q.
Proof.
case: (poly_baseP Q) => [->| J [Q_eq Q_prop0]]; first by rewrite active0 fsubsetT_proper.
case: (poly_baseP P) => [->| I [P_eq P_prop0]]; first by [].
rewrite {2}[Q]repr_active // => /fproperP [/fsubsetP eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; first exact: polyEq_antimono.
apply/poly_subsetPn.
move: i_notin; rewrite in_active.
- move/poly_subsetPn => [x x_in_Q x_notin].
  exists x; first by move/(poly_subsetP subset_repr_active): x_in_Q.
  move: x_notin; apply: contra => x_in; exact: (polyEq_eq x_in).
- move: i_in; apply/fsubsetP; exact: fsubset_subP.
Qed.

Lemma active_proper (P Q : {poly base}) :
  `[poly0] `<` P -> P `<` Q -> ({eq Q} `<` {eq P})%fset.
Proof.
move => P_prop0 P_prop_Q; rewrite fproperEneq.
have Q_prop0: Q `>` `[poly0] by apply/poly_proper_trans: P_prop_Q.
move/poly_properW/activeS: (P_prop_Q) ->.
rewrite andbT; move: P_prop_Q; apply: contraTneq.
rewrite {2}[P]repr_active // {2}[Q]repr_active // /val_inj /= => ->.
by rewrite poly_properxx.
Qed.

Lemma active_affine :
  {eq (affine <<base>>)%:poly_base} = base%:fsub.
Proof.
apply/fsubset_inj/eqP; rewrite eqEfsubset.
rewrite fsubset_subP //=.
apply/fsubsetP => i ?; rewrite in_active //=.
by apply/affineS1/memv_span.
Qed.

End Active.

Notation "'{eq'  P }" := (active P) : poly_scope.

Section ActiveSlice.

Variable (R : realFieldType) (n : nat).

Lemma active_slice e (base : base_t[R,n]) (P : {poly base}) :
  ((e +|` {eq P}) `<=` {eq (slice e P)%:poly_base})%fset.
Proof.
rewrite -activeP -slice_polyEq.
case: (poly_baseP P) => [-> /= | ? [_ P_prop0] /=].
- rewrite {1}(slice0 _); exact: poly0_subset.
- move/repr_active: P_prop0 => {1}->.
  exact: poly_subset_refl.
Qed.

End ActiveSlice.

Module BaseQuotient.
Section BaseQuotient.

Variable (R : realFieldType) (n : nat).

Lemma poly_has_base P :
  exists (x : { base : base_t[R,n] & {poly base}}),
    P == (tagged x) :> 'poly[R]_n.
Proof.
move: (is_poly_of_base P) => [base ->].
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
rewrite -{-1}[P]reprK unlock; exact: poly_base_base.
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

Lemma reprK (P : 'poly[R]_n) : \repr P = P :> 'poly[R]_n.
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
move: (is_poly_of_base P) => [base ->].
rewrite -poly_of_non_redundant_base.
have ->: 'P(mk_non_redundant_base base) = 'P(mk_non_redundant_base base)%:poly_base by [].
by apply/h/mk_non_redundant_baseP.
Qed.

End BaseQuotientAux.

Section PolyBaseFace.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition pb_face_set (P : {poly base}) : {set {poly base}} :=
  [set Q : {poly base} | Q `<=` P].

Notation "\face_set P" := (pb_face_set P) (at level 40).

CoInductive pb_face_spec (P : {poly base}) : {poly base} -> Prop :=
| PbEmptyFace : pb_face_spec P (`[poly0])%:poly_base
| PbArgMin c of (bounded P c) : pb_face_spec P (argmin P c)%:poly_base.

Lemma pb_faceP (P Q : {poly base}) :
  Q \in \face_set P -> pb_face_spec P Q.
Proof.
case: (emptyP ('P(base) : 'poly[R]_n))
  => [base_eq0 | base_prop0].
- suff ->: (P = (`[poly0]%:poly_base)).
  + rewrite inE subset0_equiv => /eqP.
    move/val_inj ->; constructor.
    move: (poly_base_subset P); rewrite base_eq0 //=.
      by rewrite subset0_equiv => /eqP/val_inj.
- case: (poly_baseP Q) => [-> | ]; first constructor.
  move => I [Q_eq Q_prop0].
  rewrite inE; move => Q_sub_P.
  pose w : {conic base_elt ~> R} := (fconicu I).
  pose c := (combine w).1.
  have c_bounded : bounded ('P(base) : 'poly[R]_n) c.
  + apply: dual_sol_bounded => //; rewrite finsupp_fconicu; exact: fsubset_subP.
  have c_bounded_P : (bounded P c).
  + apply: (bounded_mono1 c_bounded); apply/andP; split;
      [ exact: (poly_proper_subset Q_prop0) | exact: poly_base_subset ].
  have c_argmin: argmin 'P(base) c = Q.
  + rewrite Q_eq in Q_prop0 *.
    rewrite dual_sol_argmin /=; rewrite ?/w ?finsupp_fconicu //.
    exact: fsubset_subP.
  suff <- : (argmin P c)%:poly_base = Q by constructor.
  apply: val_inj => /=. rewrite -c_argmin.
  apply/subset_argmin; first by done.
  apply/andP; split; [ by rewrite c_argmin | exact: poly_base_subset ].
Qed.

End PolyBaseFace.

Notation "\face_set P" := (pb_face_set P) (at level 40).

Section Face.
Variable (R : realFieldType) (n : nat).

Definition face_set (P : 'poly[R]_n) :=
  [fset pval x | x in \face_set (\repr P)]%fset.

Lemma face_set_mono (base : base_t[R,n]) (P : {poly base}) :
  face_set P = [fset pval x | x in \face_set P]%fset.
Proof.
suff H: forall base1 base2 (P1 : {poly base1}) (P2 : {poly base2}),
    P1 = P2 :> 'poly[R]_n ->
    ([fset pval x | x in \face_set P1] `<=` [fset pval x | x in \face_set P2])%fset.
- by apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/H; rewrite reprK.
- move => base1 base2 P1 P2 eq_P12.
  apply/fsubsetP => F /imfsetP [F' /= F'_in ->].
  case/pb_faceP : F'_in.
  + apply/imfsetP; exists (`[poly0]%:poly_base) => //=.
    rewrite inE; exact: poly0_subset.
  + move => c c_bounded.
    apply/imfsetP; exists ((argmin P2 c)%:poly_base) => /=.
    rewrite inE; exact: argmin_subset.
    by rewrite eq_P12.
Qed.

Lemma face_set_has_base (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) :
  Q \in face_set P -> [Q has \base base].
Proof.
rewrite face_set_mono => /imfsetP [{}Q _ ->].
exact: poly_base_base.
Qed.

(*Canonical face_set_has_baseP (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n) (H : expose (Q \in face_set P)) :=
  PolyBase (face_set_has_base H).

Parameter (base : base_t[R,n]) (P : {poly base}) (Q : 'poly[R]_n).
Hypothesis H : (Q \in face_set P).
Check (Q%:poly_base) : {poly base}.*)

Lemma face_setE (base : base_t[R,n]) (P : {poly base}) :
    (forall F : {poly base}, (pval F \in face_set P) = (F `<=` P))
    * (forall F : 'poly[R]_n, forall H : [F has \base base], (F \in face_set P) = (F `<=` P)).
Proof.
set X := (X in (X * _)%type).
suff hX: X.
- split => //.
  move => F F_base; have ->: F = PolyBase F_base by []; exact: hX.
- move => F; rewrite face_set_mono.
  apply/imfsetP/idP => [[{}F H ->]| F_sub_P]; first by rewrite inE in H.
  by exists F; rewrite ?inE.
Qed.

Lemma face_set_self (P : 'poly[R]_n) : P \in (face_set P).
Proof.
elim/polybW: P => base P.
rewrite face_setE; exact: poly_subset_refl.
Qed.

(*
Lemma in_face_setP (base : base_t[R,n]) (F : 'poly[R]_n) (P : {poly base}) & (F \in face_set P) :
  F%:poly_base `<=` P.
Proof.
by rewrite -face_setE.
Qed.*)

Variant face_set_spec (base : base_t[R, n]) (P : {poly base}) : 'poly[R]_n -> Type :=
| FaceSetSpec (Q : {poly base}) of (Q `<=` P) : face_set_spec P Q.

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
  exact: (poly_subset_trans Q'_sub_Q).
- rewrite mem_imfset => //= /andP[].
  case/face_setP => {}Q' _.
  by rewrite face_setE.
Qed.

Corollary subset_face_set (P Q : 'poly[R]_n) :
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

Lemma poly0_face_set (P : 'poly[R]_n) : `[poly0] \in face_set P.
Proof.
elim/polybW: P => base P.
by rewrite face_setE ?poly0_subset ?(valP (`[poly0]%:poly_base)).
Qed.

Lemma face_set0 : face_set (`[poly0]) = [fset `[poly0]]%fset.
Proof.
apply/fsetP => P; rewrite !inE /=; apply/idP/idP.
- by move/face_subset; rewrite subset0_equiv.
- move/eqP ->; exact: face_set_self.
Qed.

Lemma face_set_polyI (P F F' : 'poly[R]_n) :
  F \in face_set P -> F' \in face_set P -> F `&` F' \in face_set P.
Proof.
elim/polybW: P => base P.
case/face_setP => {}F F_sub_P.
case/face_setP => {}F' F'_sub_P.
rewrite face_setE; first by rewrite (poly_subset_trans (poly_subsetIl _ _)).
(*apply/valP.*) (* TODO: valP doesn't work *)
exact: (valP (_ `&` _)%:poly_base).
Qed.

Lemma argmin_in_face_set (P : 'poly[R]_n) c :
  bounded P c -> argmin P c \in face_set P.
Proof.
elim/polybW: P => base P c_bounded.
have ->: (argmin P c) = (argmin P c)%:poly_base by [].
rewrite face_setE; exact: argmin_subset.
Qed.

Lemma face_argmin (P Q : 'poly[R]_n) :
  Q \in face_set P -> Q `>` (`[poly0]) -> exists2 c, bounded P c & Q = argmin P c.
Proof.
rewrite /face_set; move/imfsetP => [{}Q /= Q_face ->].
by case: (pb_faceP Q_face) => [| c]; rewrite /= ?reprK ?poly_properxx //; exists c.
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

Section SpanActive.

Context {R : realFieldType} {n : nat}.

Implicit Types (base : base_t[R,n]).

Lemma in_span_active base (P : {poly base}) e :
  (e \in << {eq P} >>%VS) -> (P `<=` `[hp e]).
Proof.
move/coord_span ->.
apply/poly_subsetP => x x_in_P; rewrite inE; apply/eqP.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : base_elt[R,n] => x.1)) //.
rewrite (big_morph (id1 := 0) (op1 := +%R) (fun x : base_elt[R,n] => x.2)) //=.
rewrite vdot_sumDl; under eq_big do [| rewrite /= vdotZl].
apply/eq_bigr => i _; apply: congr1.
apply/eqP; rewrite -in_hp; move: x_in_P; apply/poly_subsetP/poly_base_subset_hp.
by rewrite mem_nth ?size_tuple.
Qed.

Lemma in_span_activeP base (P : {poly base}) e :
  (P `>` `[poly0]) ->
  (P `<=` `[hp e]) = (e \in << {eq P} >>%VS).
Proof.
move => P_prop0; apply/idP/idP; last exact : in_span_active.
move: (erefl P); rewrite {2}[P]repr_active // => /(congr1 (@pval _ _ _)) /=.
rewrite polyEq_flatten => P_eq P_sub_hp.
move: (poly_subset_trans P_sub_hp (hp_subset_hs _)).
move: (P_prop0); rewrite P_eq; set S := {eq P}: {fset _}.
move/farkas => h /h {h} [w w_supp [e1_eq e2_le]].
suff finsupp_sub_eq: (finsupp w `<=` (S `|` -%R @` S))%fset.
- have comb_in_eqP: combine w \in << {eq P} >>%VS.
  * rewrite (combinewE finsupp_sub_eq).
    apply/memv_suml => i _; rewrite memvZ //.
    move: (valP i); rewrite inE; move/orP; case; try exact: memv_span.
      by move/imfsetP => [? /= ? ->]; rewrite memvN memv_span.
  suff <-: (combine w) = e by [].
  move/proper0P: P_prop0 => [x x_in_P].
  apply/(befst_inj (x := x)) => //.
  * by apply/poly_subsetP/in_span_active: x_in_P.
  * by move/poly_subsetP/(_ _ x_in_P): P_sub_hp.
- move: P_sub_hp; apply: contraTT.
  move/fsubsetPn => [e']; rewrite inE negb_or => e'_in /andP [e'_notin_S /negbTE e'_notin_mS].
  have {e'_notin_S e'_notin_mS} /poly_subsetPn [x x_in x_notin]: ~~ (P `<=` `[hp e']).
  + rewrite -in_active ?e'_notin_S //.
    by move/fsubsetP/(_ _ e'_in): w_supp; rewrite inE e'_notin_mS orbF.
  apply/poly_subsetPn; exists x => //.
  rewrite in_hp -e1_eq eq_sym; apply/ltr_neq.
  apply/(le_lt_trans e2_le).
  rewrite !(combinebE w_supp) /= vdot_sumDl.
  apply/sumr_ltrP.
  + move => i; rewrite vdotZl ler_wpmul2l ?ge0_fconic //.
    rewrite -in_hs; move: x_in; apply/poly_subsetP.
    rewrite P_eq; apply/poly_base_subset_hs; exact: fsvalP.
  + have e'_in_baseEq : e' \in baseEq base S by apply/(fsubsetP w_supp).
    pose e'_idx := [` e'_in_baseEq]%fset.
    exists e'_idx. rewrite vdotZl ltr_pmul2l ?gt0_fconic //.
    rewrite -notin_hp //=.
    move: x_in; apply/poly_subsetP.
    by rewrite P_eq; apply/poly_base_subset_hs.
Qed.

Lemma span_activeS base (P : {poly base}) base' (Q : {poly base'}) :
  (P `>` `[poly0]) -> P `<=` Q -> (<< {eq Q} >> <= << {eq P} >>)%VS.
Proof.
move => P_prop0 P_sub_Q; apply/subvP => e /in_span_active.
rewrite -in_span_activeP //; exact: poly_subset_trans.
Qed.

Lemma span_activeE base (P : {poly base}) base' (Q : {poly base'}) :
  (P `>` `[poly0]) -> P = Q :> 'poly[R]_n -> (<< {eq P} >> = << {eq Q} >>)%VS.
Proof.
move => P_prop0 P_eq_Q.
by apply/subv_anti; apply/andP; split; apply/span_activeS; rewrite -?P_eq_Q ?poly_subset_refl.
Qed.

End SpanActive.

Section AffineHull.

Context {R : realFieldType} {n : nat}.

Implicit Type base : base_t[R,n].

Definition pb_hull base (P : {poly base}) :=
  if P `>` `[poly0] then
    affine << {eq P} >>%VS
  else
    `[poly0].

Notation "\hull P" := (pb_hull P) (at level 40).

Definition hull (P : 'poly[R]_n) := \hull \repr P.

Lemma hullE base (P : {poly base}) :
  hull P = \hull P.
Proof.
case: (emptyP P)  => [| P_propØ].
- rewrite /hull /pb_hull => ->.
  by rewrite ifF ?reprK ?poly_properxx.
- rewrite /hull /pb_hull reprK !ifT //=.
  suff ->: (<<{eq P}>> = <<{eq \repr P}>>)%VS by [].
  by apply/span_activeE; rewrite ?reprK.
Qed.

Lemma subset_hull P : P `<=` hull P.
Proof.
case: (emptyP P) => [->| ]; rewrite ?poly0_subset //.
elim/polybW : P => base P; rewrite hullE /pb_hull => P_prop0.

  by rewrite P_prop0; rewrite {1}[P]repr_active //= polyEq_affine poly_subsetIr.
Qed.

Lemma hull0 : hull (`[poly0] : 'poly[R]_n) = `[poly0].
by rewrite /hull /pb_hull reprK ifF ?poly_properxx.
Qed.

Lemma hullN0 P : (P `>` `[poly0]) = (hull P `>` `[poly0]).
Proof.
case/emptyP : (P) => [-> | P_prop0]; first by rewrite hull0 poly_properxx.
by symmetry; apply/(poly_proper_subset P_prop0)/subset_hull.
Qed.

Lemma hullN0_eq base (P : {poly base}) :
  (P `>` `[poly0]) -> hull P = affine << {eq P} >>.
Proof.
by rewrite hullE /pb_hull => ->.
Qed.

Lemma hullP P U :
  (P `<=` affine U) = (hull P `<=` affine U).
Proof.
case: (emptyP P) => [->|]; rewrite ?hull0 //.
move => P_prop0; apply/idP/idP; last by apply/poly_subset_trans; exact: subset_hull.
elim/polybW : P P_prop0 => base P P_prop0.
rewrite hullN0_eq // => P_sub_affU; apply: affineS.
apply/subvP => e; rewrite -in_span_activeP //.
by move/affineS1; apply/poly_subset_trans.
Qed.

Lemma hull_affine U :
  hull (affine U) = affine U.
Proof.
by apply/poly_subset_anti; rewrite ?subset_hull -?hullP ?poly_subset_refl.
Qed.

Lemma hullI (P : 'poly[R]_n) : hull (hull P) = hull P.
Proof.
case: (emptyP P) => [->|]; first by rewrite !hull0.
elim/polybW: P => base P P_prop0.
by rewrite hullN0_eq // hull_affine.
Qed.

Lemma hullS : {homo hull : P Q / P `<=` Q}.
Proof.
move => P Q.
case: (emptyP Q) => [->|];
  first by rewrite subset0_equiv => /eqP ->; exact: poly_subset_refl.
elim/polybW : Q => base Q Q_prop0 P_sub_Q.
rewrite hullN0_eq // hullP hullI -hullP.
rewrite -hullN0_eq //; apply/(poly_subset_trans P_sub_Q); exact: subset_hull.
Qed.

Lemma line_subset_hull (P : 'poly[R]_n) (v v' : 'cV[R]_n) :
  v \in P -> v' \in P -> `[line (v' - v) & v] `<=` hull P.
Proof.
elim/polybW: P => base P v_in_P v'_in_P.
have P_prop0: P `>` `[poly0] by apply/proper0P; exists v.
rewrite hullN0_eq // affine_span; apply/big_polyIsP => e _.
by apply/line_subset_hp; apply/(poly_subsetP (poly_base_subset_hp (valP _))).
Qed.

Lemma hull_line (v v' : 'cV[R]_n) :
  hull (conv [fset v; v']%fset) = `[line (v' - v) & v].
Proof.
set S := conv _.
apply/poly_subset_anti; last by apply/line_subset_hull; [rewrite in_segml | rewrite in_segmr].
have eq := line_affine v (v' - v); rewrite /mk_affine in eq.
rewrite eq -hullP -eq. (* TODO: we shouldn't have to use /mk_affine *)
apply/conv_subset => x; rewrite !inE => /orP; case => /eqP ->; apply/in_lineP.
- by exists 0; rewrite scale0r addr0.
- by exists 1; rewrite scale1r addrCA addrN addr0.
Qed.

End AffineHull.

Section Dimension.

Variable (R : realFieldType) (n : nat).

Definition pb_dim (base : base_t[R,n]) (P : {poly base}) :=
  if (P `>` `[poly0]) then
    (n - \dim << {eq P} >>).+1%N
  else 0%N.

Notation "\dim P" := (pb_dim P) (at level 10, P at level 8) : poly_scope.

Definition dim (P : 'poly[R]_n) := \dim (\repr P).

Lemma dimE (base : base_t[R,n]) (P : {poly base}) :
  dim P = \dim P.
Proof.
case: (emptyP P) => [| P_propØ].
- rewrite /dim /pb_dim => ->.
  by rewrite ifF ?reprK ?poly_properxx.
- rewrite /dim /pb_dim reprK !ifT //.
  by do 3![apply/congr1]; symmetry; apply/span_activeE; rewrite ?reprK.
Qed.

Lemma dim_le_Sn (P : 'poly[R]_n) :
  (dim P <= n.+1)%N.
Proof.
elim/polybW: P => base P; rewrite dimE /pb_dim.
by case: ifP => [_|//]; apply: leq_subr.
Qed.

Lemma dim0 :
  (dim (`[poly0] : 'poly[R]_n) = 0%N)
  * (forall base, dim (`[poly0] %:poly_base : {poly base}) = 0%N).
Proof.
suff H: forall base, dim (`[poly0] %:poly_base : {poly base}) = 0%N.
- split => //.
  pose base0 := fset0 : base_t[R,n].
  have ->: `[poly0] = (`[poly0]%:poly_base : {poly base0}) by [].
  exact: H.
- by move => base; rewrite dimE /pb_dim ifF // poly_properxx.
Qed.

Lemma dimN0 (P : 'poly[R]_n) : (P `>` `[poly0]) = (dim P > 0)%N.
Proof.
case/emptyP : (P) => [-> | P_prop0]; first by rewrite dim0 ltnn.
by elim/polybW: P P_prop0 => base P P_prop0; rewrite dimE /pb_dim ifT.
Qed.

Lemma dimN0_eq (base : base_t[R,n]) (P : {poly base}) :
  (P `>` `[poly0]) -> dim P = (n - \dim << {eq P} >>).+1%N.
Proof.
by rewrite dimE /pb_dim => ->.
Qed.

Lemma dim_eq0 (P : 'poly[R]_n) :
  dim P = 0%N <-> P = `[poly0].
Proof.
split; last by move ->; rewrite dim0.
by apply/contra_eq; rewrite equiv0N_proper dimN0 lt0n.
Qed.

Lemma dim_affine (U : {vspace 'cV[R]_n}) Ω :
  (dim (`[affine U & Ω]) = (\dim U).+1)%N.
Proof.
move: (mk_affine_prop0 U Ω).
rewrite /mk_affine.
set V := (X in affine X).
set base := [fset e in ((vbasis V) : seq _)]%fset : {fset base_elt[R,n]}.
have eq: V = << base >>%VS.
- move: (vbasisP V) => /andP [/eqP <- _].
  apply/subv_anti/andP; split; apply/sub_span;
  by move => ?; rewrite inE.
rewrite eq => prop0; rewrite dimN0_eq ?active_affine //=.
by rewrite -eq dim_mk_affine_fun dim_orthv subKn ?dim_cVn.
Qed.

Variant dim_spec : 'poly[R]_n -> nat -> Prop :=
| DimEmpty : dim_spec (`[poly0]) 0%N
| DimNonEmpty (base : base_t[R,n]) (P : {poly base}) of (P `>` `[poly0]) : dim_spec P (n-\dim <<{eq P}>>).+1.

Lemma dimP P : dim_spec P (dim P).
case: (emptyP P) => [->| ]; first by rewrite dim0; constructor.
by elim/polybW: P => base P P_prop0; rewrite dimN0_eq //; constructor.
Qed.

Lemma dim_hull (P : 'poly[R]_n) :
  dim P = dim (hull P).
Proof.
case/dimP: P => [| base P P_prop0]; first by rewrite hull0 dim0.
have hull_prop0: (hull P) `>` `[poly0] by apply/(poly_proper_subset P_prop0); exact: subset_hull.
rewrite hullN0_eq // in hull_prop0 *.
have ->: affine << {eq P} >> = (affine << {eq P} >>)%:poly_base by [].
by rewrite dimN0_eq //= active_affine.
Qed.

Lemma dimS : {homo dim : P Q / (P `<=` Q) >-> (P <= Q)%N}.
Proof.
move => P Q.
case/dimP: P => [| base P P_prop0]; rewrite ?dim0 //.
case/dimP: Q => [| base' Q Q_prop0];
  first by move/(poly_proper_subset P_prop0); rewrite ?poly_properxx.
by rewrite ltnS => P_sub_Q; apply/leq_sub2l/dimvS/span_activeS.
Qed.

Lemma hull_mk_affine {P : 'poly[R]_n} {x} :
  x \in P -> exists2 U, hull P = `[affine U & x] & (\dim U = (dim P).-1)%N.
Proof.
elim/polybW: P => base P x_in_P.
have P_prop0 : P `>` `[poly0] by apply/proper0P; exists x.
set U := (befst @: <<{eq P}>>)^OC%VS.
have hullP : hull P = `[affine U & x].
- by rewrite -affine_orth -hullN0_eq //; apply/(poly_subsetP (subset_hull _)).
exists U => //; by rewrite dim_hull hullP dim_affine /=.
Qed.

Lemma dim_span_active (base : base_t[R,n]) (P : {poly base}) :
  P `>` (`[poly0]) -> (\dim << {eq P} >> <= n)%N.
Proof.
move => /proper0P [x x_in_P].
have /limg_dim_eq <-: (<<{eq P}>> :&: lker befst)%VS = 0%VS.
- apply/eqP; rewrite -subv0.
  apply/subvP => e; rewrite memv_cap memv_ker memv0 => /andP [e_in /eqP f_e_eq0].
  have e1_eq0 : e.1 = 0 by rewrite lfunE in f_e_eq0.
  apply/be_eqP => /=; split; first done.
  move/(poly_subsetP subset_repr_active): x_in_P.
  rewrite polyEq_affine in_polyI => /andP [_ /in_affine/(_ _ e_in)].
  by rewrite in_hp e1_eq0 vdot0l => /eqP.
- apply/(leq_trans (n := \dim fullv)); first by apply/dimvS/subvf.
  by rewrite dimvf /Vector.dim /= muln1.
Qed.

Lemma face_dim_leqif_eq (P Q : 'poly[R]_n) :
  (P \in face_set Q) -> (dim P <= dim Q ?= iff (P == Q))%N.
Proof.
move => P_face_Q; split; first by apply/dimS; exact: face_subset.
apply/eqP/eqP => [| -> //].
case/dimP: Q P_face_Q => [_ /dim_eq0 //| base Q Q_prop0].
case/face_setP => {}P P_sub_Q.
case: (emptyP P) => [->| P_prop0]; rewrite ?dim0 //.
rewrite dimN0_eq // => /eqP; rewrite eqSS subn_inj ?dim_span_active // => /eqP dim_eq.
suff: (<< {eq P} >> = << {eq Q} >>)%VS.
- by rewrite {2}[P]repr_active ?{2}[Q]repr_active //= ?polyEq_affine => ->.
- apply/eqP; rewrite eq_sym eqEdim {}dim_eq leqnn andbT.
  by apply/span_activeS.
Qed.

Lemma face_dim_geq (P Q : 'poly[R]_n) :
  P \in face_set Q -> (dim P >= dim Q)%N -> P = Q.
Proof.
move/face_dim_leqif_eq/geq_leqif => h dim_geq.
by rewrite dim_geq in h; move/esym/eqP: h.
Qed.

Lemma face_dim_eq (P Q : 'poly[R]_n) :
  P \in face_set Q -> dim P = dim Q -> P = Q.
Proof.
by move => ? dim_eq; apply/face_dim_geq; rewrite ?dim_eq.
Qed.

Lemma dim_pt (x : 'cV[R]_n) :
  dim (`[pt x]) = 1%N.
Proof.
by rewrite dim_affine dimv0.
Qed.

Lemma dim1P (P : 'poly[R]_n) :
  reflect (exists x, P = `[pt x]) (dim P == 1%N).
Proof.
apply/(iffP eqP) => [ dim1| [? ->]]; last exact: dim_pt.
have P_prop0: (P `>` `[poly0]) by rewrite dimN0 dim1.
move/proper0P: (P_prop0) => [x x_in_P].
exists x; apply/poly_subset_anti; rewrite ?pt_subset //.
elim/polybW : P P_prop0 x_in_P dim1 => base P P_prop0.
move/(poly_subsetP (subset_hull _)) => x_in_hullP dim1.
apply/(poly_subset_trans (subset_hull _)).
rewrite !hullN0_eq // in x_in_hullP *.
apply/poly_subsetP => y.
move: dim1; rewrite dim_hull hullN0_eq //.
by rewrite (affine_orth x_in_hullP) dim_affine => /succn_inj/eqP; rewrite dimv_eq0 => /eqP ->.
Qed.

Lemma dim_line (Ω d : 'cV[R]_n) :
  (dim (`[line d & Ω] ) = (d != 0%R).+1)%N.
Proof.
case/altP: (d =P 0) => [->|]; first by rewrite /= line0 dim_pt.
by rewrite line_affine dim_affine dim_vline => ->.
Qed.

Lemma dim_segm (v v' : 'cV[R]_n) : dim (conv [fset v; v']%fset) = (v != v').+1.
Proof.
by rewrite dim_hull hull_line dim_line subr_eq0 eq_sym.
Qed.

Lemma dim2P (P : 'poly[R]_n) :
  compact P -> dim P = 2 -> exists v, exists2 w, P = conv [fset v; w]%fset & v != w.
Proof.
elim/polybW: P => base P P_compact dimP2.
have P_prop0 : P `>` `[poly0] by rewrite dimN0 dimP2.
set U := (befst @: <<{eq P}>>)^OC%VS.
have hullP_eq : forall x, x \in P -> hull P = `[ affine U & x ].
- move => x x_in_P.
  by rewrite -affine_orth -hullN0_eq //; apply/(poly_subsetP (subset_hull _)).
pose Ω := ppick P.
have dimU1 : (\dim U = 1)%N.
- by move: dimP2; rewrite dim_hull (hullP_eq _ (ppickP _)) // dim_affine => /succn_inj.
pose d := vpick U.
have d_neq0 : d != 0 by rewrite vpick0 -dimv_eq0 dimU1.
have d_bounded : bounded P d by apply/(compactP P_prop0).
have d_bounded' : bounded P (-d) by apply/(compactP P_prop0).
set v := ppick (argmin P d); set w := ppick (argmin P (-d)).
have v_in_argmin: v \in (argmin P d) by apply/ppickP; rewrite -bounded_argminN0.
have w_in_argmin: w \in (argmin P (-d)) by apply/ppickP; rewrite -bounded_argminN0.
have d_v : '[d,v] = opt_value d_bounded.
- by move: v_in_argmin; rewrite argmin_polyI in_polyI => /andP [_]; rewrite in_hp => /eqP.
have d_w : '[d,w] = -(opt_value d_bounded').
- move: w_in_argmin; rewrite argmin_polyI in_polyI => /andP [_]; rewrite in_hp => /eqP /=.
  by rewrite vdotNl => <-; rewrite opprK.
have v_in_P : v \in P by move: v_in_argmin; apply/(poly_subsetP (argmin_subset _ _)).
have w_in_P : w \in P by move: w_in_argmin; apply/(poly_subsetP (argmin_subset _ _)).
have dv_neq_dw: '[d,v] != '[d,w].
- move: d_neq0; apply: contra_neq => dv_eq_dw.
  pose e := [< d, opt_value d_bounded >].
  have: P `<=` `[hp e].
  + apply/poly_subsetIP; split; first by apply/opt_value_lower_bound.
    rewrite beoppE /= -d_v dv_eq_dw d_w opprK.
    by apply/opt_value_lower_bound.
  rewrite in_span_activeP // => /(memv_img befst).
  rewrite lfunE /= => d_in_eq.
  have: d \in (U :&: U^OC)%VS by rewrite memv_cap orthK d_in_eq (memv_pick U).
  by rewrite direct_orthvP memv0 => /eqP.
have v_neq_w : v != w by move: dv_neq_dw; apply/contra_neq => ->.
have dv_lt_dw: '[d,v] < '[d,w].
- rewrite lt_neqAle dv_neq_dw /=.
  move/poly_subsetP/(_ _ w_in_P): (opt_value_lower_bound d_bounded).
  by rewrite in_hs -d_v /=.
exists v; exists w => //.
have U_eq: U = <[w-v]>%VS.
- apply/eqP; rewrite eq_sym eqEdim; apply/andP; split; last first.
  + by rewrite dimU1 dim_vline subr_eq0 eq_sym v_neq_w.
  + rewrite -memvE -in_mk_affine -(hullP_eq _ v_in_P).
    by apply/(poly_subsetP (subset_hull _)).
have {}hullP_eq : hull P = `[line (w-v) & v].
- by rewrite line_affine -U_eq -hullP_eq.
apply/poly_subset_anti; last first.
- by apply/conv_subset => x /fset2P; case => ->.
- apply/poly_subsetP => x x_in_P.
  move/(poly_subsetP (subset_hull _)): (x_in_P).
  rewrite hullP_eq => /in_lineP [μ x_eq].
  apply/in_segmP; exists μ; last first.
  + rewrite scalerDl scale1r addrAC scaleNr -scalerN.
    by rewrite x_eq scalerDr addrA.
  + apply/andP; split.
    * move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound d_bounded).
      rewrite inE /= -d_v x_eq vdotDr vdotZr vdotBr ler_addl.
      by rewrite pmulr_lge0 ?subr_gt0.
    * move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound d_bounded').
      rewrite inE /= vdotNl ler_oppr -d_w x_eq vdotDr vdotZr vdotBr addrC.
      by rewrite -ler_subr_addr ger_pmull ?subr_gt0.
Qed.

Lemma dim_hp (e : base_elt[R,n]) :
  (`[hp e] `>` `[poly0]) -> (dim (`[hp e]) = (e.1 == 0%R) + n)%N.
Proof.
Admitted.

(*
Lemma dimW (Pt : 'poly[R]_n -> Prop) :
  Pt (`[poly0]) -> (forall k, forall Q : 'poly[R]_n, (dim Q = k.+1)%N -> Pt Q) -> (forall P : 'poly[R]_n, Pt P).
Admitted.
 *)

(*
Lemma hull_conv (V : {fset 'cV[R]_n}) Ω :
  Ω \in V -> hull (conv V) = `[affine << [fset (v - Ω) | v in V]%fset >>%VS & Ω].
Proof.
set P := conv V.
move => Ω_in_V.
have : Ω \in (hull P)
  by apply/(poly_subsetP (subset_hull _))/in_conv.
have : P `>` `[poly0] by admit.
elim/polybW : P => base P P_prop0.
Admitted.
*)

End Dimension.

Notation "\dim P" := (pb_dim P) (at level 10, P at level 8) : poly_scope.

Section Facet.

Context {R : realFieldType} {n : nat} (base : base_t[R,n]).
Hypothesis non_redundant : non_redundant_base base.

Let P := 'P(base)%:poly_base.
Hypothesis P_prop0 : P `>` `[poly0].

Lemma activeU1 (e : base_elt) & (e \in base) :
  {eq 'P^=(base; [fset e])%:poly_base } = ({eq P} `|` [fset e])%fset%:fsub.
Proof.
case: (boolP (e \in ({eq P} : base_t))).
- move => e_in_eqP.
  have ->: 'P^= (base; [fset e])%:poly_base = 'P(base)%:poly_base.
  + apply/val_inj => /=; rewrite polyEq1; apply/polyIidPl.
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
    apply/(contra poly_base_subset_hp)/poly_subsetPn.
    move/non_redundant_baseP/(_ _ H)/poly_subsetPn: non_redundant => [z z_in_P' z_notin_e].
    move: i_notin_eqP; rewrite in_active //.
    move/poly_subsetPn => [y y_in_P y_notin_i].
    have y_in_e : y \in `[hs e] by apply/(poly_subsetP _ _ y_in_P)/poly_of_base_subset_hs.
    move: (hp_itv y_in_e z_notin_e) => [α α01]; rewrite {y_in_e}.
    set x := _ + _ => x_in_e; exists x.
    * rewrite /= polyEq1 inE x_in_e andbT.
      apply/in_poly_of_baseP => j.
      case: (j =P e) => [-> _| /eqP j_neq_e j_in_base].
      - move: x x_in_e; apply/poly_subsetP; exact: hp_subset_hs.
      - have y_in_P' : y \in 'P(base `\ e)
          by move: y_in_P; apply/poly_subsetP/poly_of_base_antimono; exact: fsubD1set.
        have: x \in 'P(base `\ e) by apply/mem_poly_convex => //; exact: ltW_le.
        apply/poly_subsetP/poly_of_base_subset_hs.
        by rewrite !inE j_neq_e.
    * move: y_notin_i; apply/contraNN/hp_extremeL => //.
      - by move: y_in_P; apply/poly_subsetP/poly_of_base_subset_hs.
      - move: z_in_P'; apply/poly_subsetP/poly_of_base_subset_hs.
        by rewrite !inE i_neq_e.
Qed.

Lemma facet_proper (i : base_elt) & (i \in base) :
  i \notin ({eq P} : {fset _}) -> 'P^=(base; [fset i])%:poly_base `<` P.
Proof.
move => i_notin_eqP.
rewrite poly_properEneq; apply/andP; split.
- by rewrite /= -polyEq0; apply: polyEq_antimono.
- move: i_notin_eqP; apply: contraNneq => /val_inj <-.
  rewrite -fsub1set; exact: active_polyEq.
Qed.

Lemma facet_proper0 (i : base_elt) & (i \in base) : (* A LOT IN COMMON WITH activeU1 *)
  i \notin ({eq P} : {fset _}) -> 'P^=(base; [fset i])%:poly_base `>` `[poly0].
Proof.
move => i_notin_eqP.
move/non_redundant_baseP/(_ _ H)/poly_subsetPn: non_redundant => [y y_in_P' y_notin_i].
move/proper0P: (P_prop0) => [x x_in_P].
have x_in_i : x \in `[hs i] by move: x_in_P; apply/poly_subsetP/poly_of_base_subset_hs.
move: (hp_itv x_in_i y_notin_i) => [α α01].
set z := _ + _ => z_in_i; apply/proper0P; exists z.
rewrite /= polyEq1 inE z_in_i andbT.
apply/in_poly_of_baseP => j.
case: (j =P i) => [-> _| /eqP j_neq_i j_in_base].
- move: z z_in_i; apply/poly_subsetP; exact: hp_subset_hs.
- have x_in_P' : x \in 'P(base `\ i)
    by move: x_in_P; apply/poly_subsetP/poly_of_base_antimono; exact: fsubD1set.
  have: z \in 'P(base `\ i) by apply/mem_poly_convex => //; exact: ltW_le.
  by apply/poly_subsetP/poly_of_base_subset_hs; rewrite !inE j_neq_i.
Qed.

Lemma poly_dim_facet (i : base_elt) & (i \in base) :
  i \notin ({eq P} : {fset _}) -> dim P = (dim 'P^=(base; [fset i])%:poly_base).+1%N.
Proof.
set S := 'P^=(_; _)%:poly_base.
move => i_notin_eqP.
move/(facet_proper H): (i_notin_eqP) => S_prop_P.
have i_not_in_affP: i \notin << {eq P} >>%VS.
- move: S_prop_P; apply/contraTN; move/in_span_active.
  by rewrite /= polyEq1 => /polyIidPl ->; rewrite poly_properxx.
rewrite !dimN0_eq ?facet_proper0 //; apply: congr1.
rewrite activeU1 span_fsetU span_fset1 ?dim_add_line ?subnSK //=.
suff: (dim P > 1)%N by rewrite dimN0_eq // ltnS subn_gt0.
have S_face : pval S \in face_set P by rewrite face_setE; exact: poly_properW.
move/contra_neqN/(_ (poly_proper_neq S_prop_P)): (face_dim_geq S_face).
by rewrite -ltnNge; apply/leq_ltn_trans; rewrite -dimN0 facet_proper0.
Qed.

End Facet.

Section PointedFacet.

Context {R : realFieldType} {n : nat}.

Lemma pointed_facet (P : 'poly[R]_n) :
  P `>` (`[poly0]) -> pointed P -> exists2 F, F \in face_set P & dim P = (dim F).+1.
Proof.
elim/non_redundant_baseW: P => base non_redundant.
set P := 'P(base)%:poly_base => P_prop0 P_pointed.
case: (leqP (dim P) 1%N) => [dimP_le1 | dimP_gt1].
- rewrite dimN0 in P_prop0.
  have ->: dim P = 1%N by apply/anti_leq/andP; split.
  exists (pval ((`[poly0]%:poly_base) : {poly base})).
  + by rewrite face_setE poly0_subset.
  + by rewrite dim0.
- suff: ({eq P} `<` base)%fset.
  + move/fproperP => [_ [i i_base i_notin_eqP]].
    set F := 'P^=(base; [fset i]%fset)%:poly_base.
    exists (pval F); last exact: poly_dim_facet.
    by rewrite face_setE poly_properW ?facet_proper.
  + move: P_pointed; apply: contraTT; rewrite fsubset_properT negbK => /eqP eqP_eq_base.
    move: (P_prop0) dimP_gt1; rewrite [P]repr_active //=.
    rewrite eqP_eq_base polyEqT_affine => /proper0P [x x_in_aff].
    by rewrite (affine_orth x_in_aff) pointed_affine dim_affine ltnS lt0n dimv_eq0.
Qed.

End PointedFacet.

Section VertexSet.

Context {R : realFieldType} {n : nat}.

Definition vertex_set (P : 'poly[R]_n) :=
  [fset ppick F | F in face_set P & dim F == 1%N]%fset.

Lemma in_vertex_setP (P : 'poly[R]_n) x :
  (x \in vertex_set P) = (`[pt x] \in face_set P).
Proof.
apply/imfsetP/idP => /=.
- move => [F] /andP [F_face /dim1P [y F_eq]].
  move: F_face; rewrite {}F_eq => ?.
  by rewrite ppick_pt => ->.
- move => pt_x_face.
  exists (`[pt x]); rewrite ?ppick_pt //=.
  by apply/andP; split; rewrite ?dim_pt.
Qed.

Lemma dim1_pt_ppick (P : 'poly[R]_n) :
  dim P = 1%N -> P = `[pt (ppick P)].
Proof.
by move/eqP/dim1P => [? ->]; rewrite ppick_pt.
Qed.

Lemma face_dim1 (P Q : 'poly[R]_n) :
  Q \in face_set P -> dim Q = 1%N -> exists2 x, Q = `[pt x] & x \in vertex_set P.
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
apply/fsubsetP; exact: subset_face_set.
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

Lemma vertex_set0 : (vertex_set (`[poly0])) = fset0.
Proof.
apply/fsetP => x; rewrite in_vertex_setP.
by rewrite face_set0 !inE -proper0N_equiv pt_proper0.
Qed.

Lemma vertex_set1 (v : 'cV[R]_n) : (vertex_set (`[pt v])) = [fset v]%fset.
Proof.
apply/fsetP => x; apply/idP/idP.
- by move/vertex_set_subset; rewrite in_pt => /eqP ->; rewrite inE.
- rewrite inE => /eqP ->.
  by rewrite in_vertex_setP face_set_self.
Qed.

Lemma vertex_setN0 (P : 'poly[R]_n) :
  P `>` (`[poly0]) -> pointed P -> vertex_set P != fset0.
Proof.
pose H k :=
  forall (P : 'poly[R]_n), dim P = k -> P `>` (`[poly0]) -> pointed P -> vertex_set P != fset0.
suff: forall k, H k by move/(_ (dim P) P (erefl _)).
elim => [ Q | k IHk Q ].
- by rewrite dimN0 => ->.
- case: (posnP k) => [-> dimQ1 _ _ | k_gt0 dimQ _ Q_pointed].
  + apply/fset0Pn; exists (ppick Q).
    by rewrite [Q]dim1_pt_ppick ?ppick_pt ?vertex_set1 ?inE.
  + have : Q `>` `[poly0] by rewrite dimN0 dimQ.
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
have F_prop0 : F `>` `[poly0] by rewrite -bounded_argminN0.
move/(vertex_setN0 F_prop0)/fset0Pn: F_pointed => [x x_vtx_F].
exists x.
- by apply/(fsubsetP (vertex_setS _)): x_vtx_F.
- by apply/vertex_set_subset.
Qed.

End VertexSet.

Section Graded.

Context {R : realFieldType} {n : nat}.

Lemma graded (P Q : 'poly[R]_n) :
  pointed P -> Q \in face_set P -> Q != P -> ~~ [exists S : face_set P, (Q `<` (val S) `<` P)] -> dim P = (dim Q).+1%N.
Proof.
elim/non_redundant_baseW : P => base non_redundant.
set P := 'P(base)%:poly_base => P_pointed.
case/face_setP => {}Q Q_sub_P Q_neq_P.
have {Q_sub_P Q_neq_P} Q_prop_P : Q `<` P by rewrite poly_properEneq Q_sub_P.
have P_prop0 : P `>` `[poly0] by apply/(poly_subset_proper (poly0_subset Q)).
case: (emptyP Q) => [ -> P_cover0 | Q_prop0 P_cover_Q ].
- suff: (dim P <= 1)%N.
  + move: P_prop0; rewrite dim0 dimN0 => ??.
    by apply/anti_leq/andP; split.
  + move: P_cover0; apply: contraR.
    rewrite -ltnNge => dim_lt1.
    move/fset0Pn: (vertex_setN0 P_prop0 P_pointed) => [x].
    rewrite in_vertex_setP => x_vtx.
    apply/existsP; exists [` x_vtx]%fset; apply/andP; split.
    * by rewrite dimN0 /= dim_pt.
    * rewrite poly_properEneq /= face_subset //=.
      by move: dim_lt1; apply: contraTneq => /= <-; rewrite dim_pt.
- have eqQ_prop_eqP : ({eq P} `<` {eq Q})%fset by apply/active_proper.
  move/fproperP: (eqQ_prop_eqP) => [_ [i i_in_eqQ i_notin_eqP]].
  have i_in_base: (i \in base) by move: (i) i_in_eqQ; apply/fsubsetP: (valP {eq Q}).
  set S := 'P^=(base; [fset i])%:poly_base.
  have Q_sub_S : Q `<=` S by rewrite activeP fsub1set.
  have S_prop_P : S `<` P.
  + rewrite poly_properEneq; apply/andP; split.
    * by rewrite /= -polyEq0; apply: polyEq_antimono.
    * move: i_notin_eqP; apply: contraNneq => /val_inj <-.
      rewrite -fsub1set; exact: active_polyEq.
  have -> : Q = S.
  + have S_face: (pval S \in (face_set P)) by rewrite face_setE poly_properW.
    move/existsPn/(_ [` S_face]%fset): P_cover_Q.
    rewrite S_prop_P andbT.
    by apply: contraNeq; rewrite poly_properEneq => ->; rewrite andbT.
  exact: poly_dim_facet.
Qed.

End Graded.

Section Minkowski.

Context {R : realFieldType} {n : nat}.

Lemma conv_vertex_set (P : 'poly[R]_n) :
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
    move/in_conv/(poly_subsetP conv_sub) => y_in_e y_in_argmin.
    move: x_notin_hs; apply/contraNN => x_in_P.
    rewrite !in_hs in y_in_e *; apply/(le_trans y_in_e).
    by apply/(argmin_lower_bound y_in_argmin).
  + apply/poly_subsetP/conv_subset.
    exact: vertex_set_subset.
Qed.

Lemma subset_hp (V : {fset 'cV[R]_n}) :
  (#|` V | <= n)%N -> exists2 e : base_elt[R,n], (e.1 != 0) & {subset V <= `[hp e]}.
Admitted.

Lemma card_vertex_set (P : 'poly[R]_n):
  compact P -> (dim P > n)%N -> (#|` vertex_set P | > n)%N.
Proof.
move => P_compact dimP.
have P_prop0: P `>` `[poly0] by rewrite dimN0; apply/leq_trans: dimP.
move: dimP; apply: contraTT; rewrite -2!leqNgt.
move/subset_hp => [e /negbTE e_neq0 /conv_subset].
rewrite -conv_vertex_set // => sub.
move/dimS: (sub); rewrite dim_hp ?e_neq0 //.
by apply/poly_proper_subset: sub.
Qed.

End Minkowski.

Section SeparationVertex.

Context {R : realFieldType} {n : nat}.

Lemma sep_vertex (P : 'poly[R]_n) v :
  compact P -> v \in vertex_set P -> v \notin conv (vertex_set P `\ v)%fset.
Proof.
move => P_compact.
rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) [c c_bounded pt_eq].
pose S := [seq '[c,x] | x <- (vertex_set P `\ v)%fset].
pose α := min_seq S ('[c,v]+1%R).
have v_notin: v \notin (`[ hs [<c, α>] ]).
- rewrite /α; case: min_seqP => [| ? [/mapP [z] z_in -> _]].
  + by rewrite in_hs -ltNge cpr_add ltr01.
  + move: z_in; rewrite 2!inE => /andP [z_neq_v /vertex_set_subset z_in].
    have /(notin_argmin c_bounded z_in): z \notin argmin P c by rewrite -pt_eq in_pt.
    rewrite in_hsN in_hs /=.
    suff ->: '[c,v] = opt_value c_bounded by [].
    move: (argmin_opt_value c_bounded).
    rewrite -pt_eq => /poly_subsetP/(_ _ (in_pt_self _)).
    by rewrite inE /= => /eqP ->.
- suff: conv (vertex_set P `\ v)%fset `<=` `[hs [<c,α >]].
  + by apply/contraL => v_in; apply/poly_subsetPn; exists v.
  + apply/conv_subset => w w_in.
    by rewrite inE /= /α; apply/min_seq_ler/mapP; exists w.
Qed.

Lemma vertex_set_conv_subset (V : {fset 'cV[R]_n}) : (vertex_set (conv V) `<=` V)%fset.
Proof.
set P := conv V.
apply/fsubsetP => v v_vtx.
move/vertex_set_subset: (v_vtx) => v_in.
move: v_vtx; rewrite in_vertex_setP => /face_argmin/(_ (pt_proper0 _)) => [[c] c_bounded].
move/in_convP: v_in => {v} [w w_supp ->].
set v := combine w => eq_argmin.
have /forallPn [x]: ~~ [forall v : V, val v \notin `[hs -[<c, opt_value c_bounded>]]].
- move: (in_pt_self v); rewrite eq_argmin argmin_polyIN in_polyI => /andP [_].
  apply/contraL; move/forallP => h.
  suff: v \in [predC `[hs -[<c, opt_value c_bounded>]]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => x /(fsubsetP w_supp) x_in.
  have ->: x = val [` x_in]%fset by [].
  by apply/h.
rewrite negbK => x_in.
have {x_in}: val x \in argmin P c by rewrite argmin_polyIN inE x_in andbT in_conv ?fsvalP.
rewrite -eq_argmin in_pt => /eqP <-; exact: fsvalP.
Qed.

Definition sep_hp (e : base_elt[R,n]) (V : {fset 'cV_n}) (x : 'cV_n) :=
  (x \notin `[hs e]) && [forall v : V, (val v) \notin `[hs -e]].

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : poly_scope.

Lemma sep_hpP {e : base_elt[R,n]} {V : {fset 'cV_n}} {x : 'cV_n} :
  reflect ((x \notin `[hs e]) /\ (forall y, y \in conv V -> y \notin `[hs -e]))
          ([e separates x from V]).
Proof.
apply: (iffP andP) => [[? /forallP h] | [? h]]; split => //.
- move => y /in_convP [w w_supp ->].
  suff: combine w \in [predC `[hs -e]] by rewrite !inE.
  apply/convexW; first exact: hsC_convex.
  move => v /(fsubsetP w_supp) v_in.
  have ->: v = val [` v_in]%fset by []; apply/h.
- by apply/forallP => v; apply/h/in_conv/fsvalP.
Qed.

Lemma conv_sep_hp (V : {fset 'cV_n}) (x : 'cV_n) :
  x \notin conv V -> exists e : base_elt, [e separates x from V].
Proof.
move/separation => [e x_notin /poly_subsetP sub].
rewrite in_hs -ltNge in x_notin.
pose e' := [<e.1, ('[e.1,x]+e.2)/2%:R >].
exists e'; apply/andP; split.
- by rewrite in_hs -ltNge /e' /= midf_lt.
- apply/forallP => v; rewrite in_hsN -ltNge /e' /=.
  move/in_conv/sub: (fsvalP v); rewrite in_hs.
  by apply/lt_le_trans; rewrite midf_lt.
Qed.

End SeparationVertex.

Notation "[ e 'separates' x 'from' V ]" := (sep_hp e V x) : poly_scope.

Section FaceSegment.

Context {R : realFieldType} {n : nat} .

Lemma vertex_set_segm (v v' : 'cV[R]_n) :
  vertex_set (conv [fset v; v']%fset) = [fset v; v']%fset.
Proof.
set V := [fset _; _]%fset; set S := conv _.
have sub: (vertex_set S `<=` V)%fset by apply/vertex_set_conv_subset.
apply/eqP; rewrite eqEfcard sub /=.
move: (conv_vertex_set (compact_conv [fset v; v']%fset)); rewrite -/S.
apply/contra_eqT => /=; rewrite -ltnNge cardfs2 ltnS.
case/altP: (#|` vertex_set S| =P 0%N) => /= [ /cardfs0_eq -> _|].
- by rewrite conv0 equiv0N_proper segm_prop0.
- rewrite -lt0n => card_gt0.
  case/altP: (v =P v') => /= [_| neq card_le1].
  + by rewrite leqn0 => /eqP card_eq0; rewrite card_eq0 in card_gt0.
  + have {card_gt0} {card_le1} /eqP/cardfs1P [x ->]: #|` vertex_set S| = 1%N by apply/anti_leq/andP; split.
    apply/eqP; move/(congr1 (@dim R n)).
    by rewrite conv_pt dim_pt dim_segm neq.
Qed.

Lemma face_set_segm (v v' : 'cV[R]_n) :
  face_set (conv [fset v; v']%fset) = [fset `[poly0]; `[pt v]; `[pt v']; (conv [fset v; v']%fset)]%fset.
Proof.
set S := conv _.
apply/eqP; rewrite eqEfsubset; apply/andP; split; last first.
- apply/fsubsetP => F; rewrite !inE -!orbA; move/or4P.
  case; move/eqP ->;
    by rewrite ?poly0_face_set ?face_set_self -?in_vertex_setP ?vertex_set_segm ?inE ?eq_refl ?orbT.
- apply/fsubsetP => F F_face; rewrite !inE -!orbA.
  case: {2}(dim F) (erefl (dim F)).
  + by move/dim_eq0 ->; rewrite eq_refl.
  + case. move/(face_dim1 F_face) => [x ->].
    by rewrite vertex_set_segm !inE => /orP; case => /eqP ->; rewrite eq_refl /= ?orbT.
  + case. move => dimF2.
    have /(face_dim_geq F_face) ->: (dim F >= dim S)%N.
    * by rewrite dimF2 dim_segm; apply/(leq_ltn_trans (leq_b1 _)).
    * by rewrite eq_refl !orbT.
  + move => k dimF_eq; move: (face_dim_leqif_eq F_face).1; rewrite dim_segm dimF_eq ltnS.
    by move/leq_trans/(_ (leq_b1 _)); rewrite -ltn_predRL /= ltn0.
Qed.

End FaceSegment.

Section VertexFigure.

Context {R : realFieldType} {n : nat}.

Variable (base : base_t[R,n]) (P : {poly base}) (v : 'cV[R]_n) (e0 : base_elt[R,n]).
Hypothesis P_compact : compact P.
Hypothesis v_vtx : v \in vertex_set P.
Hypothesis sep : [e0 separates v from ((vertex_set P) `\ v)%fset].
Let sep_v := (sep_hpP sep).1.
Let sep_other := (sep_hpP sep).2.

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
  F \in L -> F `>` `[poly0].
by move/vf_L_v_in => ?; apply/proper0P; exists v.
Qed.

Lemma vf_L_face (F : 'poly[R]_n) :
  F \in L -> F \in face_set P.
by rewrite !inE /= => /andP [??].
Qed.

Lemma vf_L_other_pt (F : 'poly[R]_n) :
  F \in L -> (dim F > 1)%N -> exists2 x, x \in F & x \notin `[hs -e0].
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
  F \in L -> (dim F > 1)%N -> (Φ F) `>` `[poly0].
Proof.
move => F_in_L dimF_gt1.
move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
have w_in_hs : w \in `[hs e0] by apply/hsN_subset/w_notin.
move: (hp_itv w_in_hs sep_v) => [α /ltW_le α01].
set x := _ + _ => x_in_hp; apply/proper0P; exists x.
by rewrite in_slice x_in_hp mem_poly_convex ?vf_L_v_in.
Qed.

Lemma vf_eq (F : {poly base}) :
  (pval F) \in L -> (dim F > 1)%N -> {eq (Φ F)%:poly_base} = (e0 +|` {eq F})%:fsub.
Proof.
move => F_in_L dimF_gt1.
apply/fsubset_inj/eqP; rewrite eq_sym eqEfsubset active_slice.
apply/fsubset_fsubsetP => i; rewrite inE.
move/orP; case => [| i_in_base];
  first by rewrite in_fset1 => /eqP -> _; rewrite inE in_fset1 eq_refl.
apply/contraTT; rewrite inE negb_or => /andP [_].
rewrite in_active // => /poly_subsetPn => [[x] x_in_F x_notin_hp].
(* TODO : remove code duplication by introducing the right suff *)
case: (boolP (x \in `[hs -e0])) => [x_in | /hsN_subset x_in].
- move: (vf_L_other_pt F_in_L dimF_gt1) => [w w_in_F w_notin].
  move: (hp_itv x_in w_notin) => [α α01].
    set y := _ + _; rewrite hpN => y_in_hp.
    rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_subsetPn; exists y.
    + by rewrite in_slice y_in_hp; apply/mem_poly_convex => //; apply/ltW_le.
      move: x_notin_hp; apply/contraNN/hp_extremeL => //.
      by apply/(poly_subsetP (poly_base_subset_hs _ _)) : x_in_F.
      by apply/(poly_subsetP (poly_base_subset_hs _ _)) : w_in_F.
- move: (hp_itv x_in sep_v) => [α α01].
  set y := _ + _ => y_in_hp.
  rewrite in_active ?inE ?i_in_base ?orbT //; apply/poly_subsetPn; exists y.
  + by rewrite in_slice y_in_hp mem_poly_convex ?vf_L_v_in ?ltW_le.
  + move: x_notin_hp; apply/contraNN/hp_extremeL => //.
    by apply/(poly_subsetP (poly_base_subset_hs _ _)) : x_in_F.
    by move/vf_L_v_in: F_in_L; apply/(poly_subsetP (poly_base_subset_hs _ _)).
Qed.

Lemma vf_slice_pt : Φ (`[pt v]) = `[poly0].
Proof.
apply/poly_subset_anti; last exact: poly0_subset.
apply/poly_subsetP => x; rewrite in_slice in_pt in_poly0 andbC.
move/andP => [/eqP -> /(poly_subsetP (hp_subset_hs _))].
by move/negbTE: sep_v ->.
Qed.

Lemma vf_dim1 (F : 'poly[R]_n) :
  F \in L -> (dim F <= 1)%N -> F = (`[pt v]) :> 'poly[R]_n.
Proof.
move => F_in_L dim_le1.
apply/eqP; rewrite eq_sym -(geq_leqif (face_dim_leqif_eq _)) ?dim_pt //.
by rewrite -in_vertex_setP vf_vtx.
Qed.

Lemma vf_face' (F : 'poly[R]_n) :
  F \in L -> (Φ F) \in face_set (Φ P).
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L.
case/face_setP => {}F F_sub_P F_in_L.
case: (ltnP 1 (dim F)) => [dim_gt1 | ?].
- have ->: Φ F = (Φ F)%:poly_base by [].
  by rewrite face_setE sliceS.
- by rewrite [pval F]vf_dim1 ?vf_slice_pt ?poly0_face_set.
Qed.

Lemma vf_e0_notin_eq (F : {poly base}) :
  pval F \in L -> e0 \notin ({eq F} : {fset _}).
Proof.
apply: contraL => /poly_base_subset_hp/poly_subsetP sub.
by move: sep_v; apply/contraNN; move/vf_L_v_in/sub; apply/(poly_subsetP (hp_subset_hs _)).
Qed.

Lemma vf_inj : {in L &, injective Φ}.
Proof.
move => F F'.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/face_setP => {}F F_sub_P F_in_L.
move => F'_in_L; move: (F'_in_L); move/vf_L_face: F'_in_L; case/face_setP => {}F' F'_sub_P F'_in_L.
case: (ltnP 1 (dim F)) => [dimF_gt1 | ?]; case: (ltnP 1 (dim F')) => [dimF'_gt1 | ?]; last first.
- by rewrite [pval F]vf_dim1 1?[pval F']vf_dim1.
- rewrite [pval F]vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F'_in_L dimF'_gt1); rewrite -eq poly_properxx.
- rewrite [pval F']vf_dim1 ?vf_slice_pt // => eq.
  by move: (vf_prop0 F_in_L dimF_gt1); rewrite eq poly_properxx.
- have ->: (Φ F = (Φ F)%:poly_base) by [].
  have ->: (Φ F' = (Φ F')%:poly_base) by [].
  move/val_inj/(congr1 active); rewrite ?vf_eq //=.
  rewrite {3}[F]repr_active 1?{3}[F']repr_active ?vf_L_prop0 //.
  move/(congr1 (fun (x : {fsubset _}) => (x `|- e0))) => /=.
  by rewrite !/funslice !/fslice !fsetU1K ?vf_e0_notin_eq // => ->.
Qed.

Lemma vf_dim (F : 'poly[R]_n) :
  F \in L -> (dim F = (dim (Φ F)).+1)%N.
Proof.
move => F_in_L; move: (F_in_L); move/vf_L_face: F_in_L; case/face_setP => {}F F_sub_P F_in_L.
case: (ltnP 1 (dim F)) => [dim_gt1 | ?].
- rewrite ?dimN0_eq ?vf_prop0 ?vf_L_prop0 //.
  apply/congr1; rewrite vf_eq //=.
  rewrite span_fsetU span_fset1 addvC dim_add_line ?subnSK //=.
  + by rewrite dimN0_eq ?ltnS ?subn_gt0 ?vf_L_prop0 in dim_gt1.
  + rewrite -in_span_activeP ?vf_L_prop0 //.
    apply/poly_subsetPn; exists v; first by rewrite vf_L_v_in.
    by move: sep_v; apply/contraNN/poly_subsetP/hp_subset_hs.
- by rewrite [pval _]vf_dim1 // dim_pt vf_slice_pt dim0.
Qed.

Lemma vf_mem_v (F : 'poly[R]_n) :
  F \in face_set P -> Φ F `>` (`[poly0]) -> v \in F.
Proof.
move => F_face PhiF_prop0; apply/vertex_set_subset; move: PhiF_prop0.
apply/contraTT; rewrite proper0N_equiv => v_notin.
apply/eqP; apply/poly_subset_anti; last exact: poly0_subset.
rewrite [F]conv_vertex_set ?(face_compact P_compact) //.
apply/poly_subsetP => x; rewrite in_slice andbC => /andP [/in_convP [y /fsubsetP y_supp ->] in_hp].
have: combine y \in [predC `[hs -e0]].
- apply/convexW; first exact: hsC_convex.
  move => w /y_supp w_vtx; rewrite inE.
  apply/sep_other/in_conv; rewrite !inE.
  apply/andP; split; move: w_vtx.
  + by apply/contraTneq => ->.
  + by apply/fsubsetP/vertex_setS.
rewrite !inE /= vdotNl in in_hp *.
by move/eqP: in_hp ->; rewrite lexx.
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
- exists (`[pt v]); rewrite ?vf_slice_pt //.
  by rewrite !inE -in_vertex_setP in_pt eq_refl andbT.
- move: F_face F_prop0; case/face_setP => {}F F_sub F_prop0.
  set F' := 'P^=(base; ({eq F} `|- e0))%:poly_base.
  have F_eq : F = (Φ F') :> 'poly[R]_n.
  + rewrite {1}[F]repr_active //= /Φ slice_polyEq /fslice fsetD1K //.
    rewrite in_active ?inE ?eq_refl //.
    by apply/(poly_subset_trans F_sub)/poly_subsetIl.
  rewrite F_eq; exists (pval F') => //.
  suff F'_face: pval F' \in face_set P by rewrite 2!inE vf_mem_v ?andbT ?F'_face -?F_eq.
  rewrite face_setE [P]repr_active ?vf_L_prop0 ?vf_P_in_L ?polyEq_antimono //.
  move/activeS/(fsubset_trans (active_slice _ _))/(fsetSD [fset e0]%fset): F_sub.
  by rewrite fsetU1K ?vf_e0_notin_eq ?vf_P_in_L.
Qed.

(*
Definition vf_inv (F : {poly (e0 +|` base)}) :=
  if F == (`[poly0]) :> 'poly[R]_n then
    `[pt v]
  else
    ('P^=(base; ({eq F} `|- e0)%fset))%:poly_base.

(* the part below should follow more generally from injectivity and surjectivity of functions between finTypes *)
Lemma in_vf_inv (F : {poly (e0 +|` base)}) :
  pval F \in face_set (Φ P) -> v \in (vf_inv F).
Proof.
move => F_face.
rewrite /vf_inv; case: ifP => [_ | /negbT F_prop0].
- by rewrite in_pt.
- rewrite equiv0N_proper in F_prop0.
  by apply/vf_mem_v; rewrite -vf_surj.
Qed.

Lemma vf_invK (F : {poly base}) : v \in F -> vf_inv ((Φ F)%:poly_base) = F.
Proof.
move => v_in_F.
rewrite /vf_inv; case: ifP => [/eqP PhiF_eq0 | /negbT PhiF_prop0].
- case: (ltnP 1 (dim F)) => [/(vf_prop0 v_in_F) | ?].
  + by rewrite /Φ PhiF_eq0 poly_properxx.
  + by rewrite vf_dim1.
- rewrite equiv0N_proper in PhiF_prop0.
  rewrite vertex_fig_eq //=.
  + rewrite /funslice /fslice fsetU1K.
    * by rewrite [F in RHS]repr_active //=; apply/proper0P; exists v.
    * move: v_in_F; apply: contraL => /in_active/poly_subsetP sub.
      by move: sep_v; apply/contraNN; move/sub; apply/(poly_subsetP (hp_subset_hs _)).
  + move: PhiF_prop0; apply/contraTT.
    rewrite -leqNgt proper0N_equiv /= => ?.
    by rewrite -/Φ vf_dim1 ?vf_slice_pt.
Qed.

Lemma vfK (F : {poly e0 +|` base}) :
  pval F \in face_set (Φ P) -> Φ (vf_inv F) = F.
Proof.
move => F_face.
rewrite /vf_inv; case: ifP => [/eqP -> | /negbT]; first by rewrite vf_slice_pt.
rewrite equiv0N_proper => F_prop0.
by rewrite [F in RHS]repr_active -?vf_surj 1?[F in LHS]repr_active.
Qed.
 *)

End VertexFigure.

Section Graph.

Context {R : realFieldType} {n : nat} (P : 'poly[R]_n).

Definition adj :=
  [rel v w : 'cV[R]_n | (v != w) && (conv [fset v; w]%fset \in face_set P)].

Lemma adj_sym v w : adj v w = adj w v. (*symmetric adj.*)
Proof.
by rewrite /= eq_sym fsetUC.
Qed.

Lemma adj_vtxl (v w : 'cV[R]_n) : adj v w -> v \in vertex_set P.
Proof.
by move/andP => [_] segm_face; apply/(fsubsetP (vertex_setS segm_face));
   rewrite vertex_set_segm; rewrite !inE eq_refl.
Qed.

Lemma adj_vtxr (v w : 'cV[R]_n) : adj v w -> w \in vertex_set P.
Proof.
by rewrite adj_sym; apply/adj_vtxl.
Qed.

Hypothesis P_compact : compact P.

Lemma vertex_set_slice_dim1 v : v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       forall F, F \in face_set P -> (v \in F) -> (dim F >= 1)%N -> (slice e F `>` `[poly0]).
Admitted.

Lemma vertex_set_slice v : v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       vertex_set (slice e P) =
       [fset ppick (slice e F) | F in face_set P & ((v \in F) && (dim F == 2%N))]%fset.
Admitted.

Definition improve c :=
  [rel v w | (adj v w) && ('[c,w] < '[c,v])].

Lemma sub_improve_adj c: subrel (improve c) adj.
Proof.
by move => ??/andP [].
Qed.

Lemma improving_neighbor (c v : 'cV[R]_n) :
  v \in vertex_set P -> v \notin argmin P c -> exists w, improve c v w.
Proof.
move => v_vtx v_notin.
have P_prop0 : P `>` `[poly0] by apply/proper0P; exists v; apply/vertex_set_subset.
suff /existsP: [exists w : vertex_set P, adj v (fsval w) &&  ('[c,fsval w] < '[c,v])]
  by move => [w ?]; exists (fsval w).
move: v_notin; apply/contraR; rewrite negb_exists => /forallP adj_vert.
have {}adj_vert: forall w, adj v w -> '[c,w] >= '[c,v].
- move => w adj; move/adj_vtxr: (adj) => w_vtx.
  by move/(_ [` w_vtx]%fset): adj_vert; rewrite adj /= leNgt.
have c_bounded : bounded P c by apply/compactP.
rewrite in_argmin vertex_set_subset //=.
rewrite [P]conv_vertex_set //; apply/conv_subset.
move => w; case/altP : (w =P v) => [ -> _| w_neq_v w_vtx]; first by rewrite in_hs.
pose sep := conv_sep_hp (sep_vertex P_compact v_vtx).
pose e := xchoose sep.
pose sep_v := (sep_hpP (xchooseP sep)).1.
pose sep_other := (sep_hpP (xchooseP sep)).2.
have w_in_hs : w \in `[hs e].
  by apply/hsN_subset/sep_other/in_conv; rewrite !inE w_neq_v /=.
move: (hp_itv w_in_hs sep_v) => [α α01].
set x := _ + _ => x_in_hp.
have {x_in_hp} x_in_slice : x \in slice e P
  by rewrite in_polyI x_in_hp /= mem_poly_convex ?ltW_le ?vertex_set_subset.
suff: x \in (`[ hs [<c, '[ c, v]>] ]).
- rewrite !in_hs /= /x combine2C combine2_line vdotDr ler_addl.
  rewrite vdotZr vdotBr pmulr_rge0 ?subr_ge0 //.
  by rewrite subr_cp0; move/andP: α01 => [].
- move: x_in_slice; rewrite [slice _ _]conv_vertex_set;
    last by apply/(subset_compact P_compact)/poly_subsetIr.
  rewrite (vertex_set_slice v_vtx) ?(xchooseP sep) // => /in_convP [ω ω_supp ->].
  apply/convexW; first apply/mem_poly_convex.
  move => z /(fsubsetP ω_supp)/imfsetP => [[F] /and3P [F_face v_in_F /eqP dimF2] ->].
  have : v \in vertex_set F by rewrite (vertex_set_face F_face) in_imfset // inE ?v_vtx.
  move: (F_face).
  move/(dim2P (face_compact P_compact F_face)): dimF2 => [y [y' -> y_neq_y' yy'_face]].
  have adj_y_y': adj y y' by rewrite inE yy'_face y_neq_y'.
  move/vertex_setS: (yy'_face); rewrite vertex_set_segm => /fsubsetP sub_vtx v_in.
  have slice_prop0 : slice e (conv [fset y; y']%fset) `>` `[poly0].
  - apply/(vertex_set_slice_dim1 v_vtx) => //; first by apply/(xchooseP sep).
    + by apply/in_conv.
    + by rewrite dim_segm y_neq_y'.
  suff: slice e (conv [fset y; y']%fset) `<=` `[ hs [<c, '[ c, v]>] ]
    by move/poly_subsetP/(_ _ (ppickP slice_prop0)).
  apply/(poly_subset_trans (poly_subsetIr _ _))/conv_subset.
  move: v_in adj_y_y' => /fset2P; case => <-;
    by move => adj_v u /fset2P; case => ->; rewrite in_hs // adj_vert // adj_sym.
Qed.

End Graph.

Section MkPath.

Context {R : realFieldType} {n : nat} (P : 'poly[R]_n).
Hypothesis P_compact : compact P.

Variable c : 'cV[R]_n.

Definition height (v : 'cV[R]_n) :=
  #|` [fset w in vertex_set P | '[c,w] <= '[c,v]] |%fset.

Definition mk_improve (v : 'cV[R]_n) :=
  match @idP (v \in vertex_set P) with
  | ReflectT v_vtx =>
    match @idPn (v \in argmin P c) with
    | ReflectT v_notin => xchoose (improving_neighbor P_compact v_vtx v_notin)
    | _ => v
    end
  | _ => v
  end.

Lemma mk_improveE (v : 'cV[R]_n) (v_vtx : v \in vertex_set P) (v_notin : v \notin argmin P c) :
  let w := mk_improve v in improve P c v w.
Proof.
rewrite /mk_improve.
case: {-}_/idP => [h|]; rewrite ?v_vtx //.
case: {-}_/idPn => [h'|]; rewrite ?v_notin //.
by apply/(xchooseP (improving_neighbor _ _ _)).
Qed.

Lemma mk_improve_in_vertex_set (v : 'cV[R]_n) :
  v \in vertex_set P -> mk_improve v \in vertex_set P.
Proof.
move => v_vtx; rewrite /mk_improve.
case: {-}_/idP => [h|]; rewrite ?v_vtx //.
case: {-}_/idPn => [h'| //].
by move: (xchooseP (improving_neighbor P_compact h h')) => /andP [/adj_vtxr ? _].
Qed.

Function mk_path (v : 'cV[R]_n) {measure height v} :=
  if (v \in vertex_set P) && (v \notin argmin P c) then
    let w := mk_improve v in
    w :: mk_path w
  else [::].
Proof.
move => v /andP [v_vtx v_notin].
set w := mk_improve v; apply/ssrnat.leP.
suff w_lt_v: '[c,w] < '[c,v].
- rewrite /height.
  set S_w := [fset _ | _ in _ & _]%fset; set S_v := [fset _ | _ in _ & _]%fset.
  apply/fproper_ltn_card/fproperP; split.
  + move => x; rewrite !inE /= => /andP [-> /=].
    by move/le_lt_trans/(_ w_lt_v)/ltW.
  + by exists v; rewrite !inE v_vtx //= -?ltNge.
- by rewrite /w; move/andP : (mk_improveE v_vtx v_notin) => [_].
Qed.

Lemma mk_pathP :
  forall v, path (improve P c) v (mk_path v).
Proof.
apply/(@mk_path_rect (path (improve P c))) => [v /andP [v_vtx v_notin] w | //=].
suff: improve P c v w by rewrite /= => -> ->.
by rewrite /w; apply: mk_improveE.
Qed.

Lemma mk_path_argmin :
  forall v, v \in vertex_set P -> (last v (mk_path v)) \in argmin P c.
Proof.
pose P' v s := v \in vertex_set P -> (last v s) \in argmin P c.
apply/(@mk_path_rect P') => [v _| v ? <-].
- by rewrite /P' /= => h ?; apply/h/mk_improve_in_vertex_set.
- case: ifP => [// | /negbT]; rewrite negb_and => /orP; case; rewrite /P' /=.
  + by move/negP.
  + by rewrite negbK.
Qed.

End MkPath.

Section Connectness.

Context {R : realFieldType} {n : nat}.

Lemma connected_graph (P: 'poly[R]_n) v w :
  compact P -> v \in vertex_set P -> w \in vertex_set P ->
    exists2 p, (path (adj P) v p) & w = last v p.
Proof.
move => P_compact v_vtx; rewrite in_vertex_setP.
move/face_argmin/(_ (pt_proper0 _)) => [c c_bouned argmin_eq].
exists (mk_path P_compact c v); first by apply/(sub_path (@sub_improve_adj _ _ _ _))/mk_pathP.
by move: (mk_path_argmin P_compact c v_vtx); rewrite -argmin_eq in_pt => /eqP.
Qed.

Hypothesis n_gt0 : (n > 0)%N.

Definition disjoint_path (V : {fset 'cV[R]_n}) (p : seq 'cV[R]_n) := [forall v : V, fsval v \notin p].

Lemma disjoint_pathP V p :
  reflect (forall v, v \in V -> v \notin p) (disjoint_path V p).
Admitted.

Lemma foo (P : 'poly[R]_n) c v :
  compact P -> v \in vertex_set P -> exists p, [/\ path (adj P) v p, last v p \in argmin P c & (forall w, w \in p -> '[c,w] < '[c,v])].
Proof.
move => P_compact v_vtx; exists (mk_path P_compact c v); split.
- by apply/(sub_path (@sub_improve_adj _ _ _ _))/mk_pathP.
- exact: mk_path_argmin.
- set p := mk_path _ _ _.
Admitted.

Lemma balinski P V v w :
  compact P -> dim P = n.+1%N -> (V `<=` vertex_set P)%fset -> #|` V | = n.-1%N ->
    v \in (vertex_set P `\` V)%fset -> w \in (vertex_set P `\` V)%fset ->
      exists p, [/\ (path (adj P) v p), w = last v p & disjoint_path V p].
Proof.
set S := (_ `\` _)%fset.
move => P_compact dimP V_sub V_card v_in_S w_in_S.
have S_sub: (S `<=` vertex_set P)%fset by admit.
have v_vtx := (fsubsetP S_sub _ v_in_S).
have w_vtx := (fsubsetP S_sub _ w_in_S).
pose V' := (v |` V)%fset.
have: (#|` V' | <= n)%N by admit.
move/subset_hp => [e]; rewrite -[e]beE /=.
set c := e.1; set α := e.2 => c_neq0 sub.
case: (ltP '[c,w] α) => [c_w_lt| c_w_ge].
- set F := argmin P c.
  have c_bounded : bounded P c by admit.
  have F_compact : compact F by admit.
  pose p1 := mk_path P_compact c v.
  pose p2 := mk_path P_compact c w.
  (*pose p3 := connected_graph F_compact *)
Admitted.

(*
Lemma other_vtx : exists2 w, w \in vertex_set P & w \notin V.
Proof.
suff: (vertex_set P `\` V)%fset != fset0
  by move/fset0Pn => [w /fsetDP [??]]; exists w.
rewrite -cardfs_gt0 cardfsDS ?subn_gt0 ?card_V ?prednK //.
by apply/ltnW/card_vertex_set; rewrite ?dimP.
Qed.
*)
End Connectness.

(* -------------------------------------------------------------------- *)
Section PointedType.
Context (R : realFieldType) (n : nat).

Record pointedPoly : predArgType :=
  { pointed_poly :> 'poly[R]_n; _ : pointed pointed_poly }.

Canonical pointedPoly_subType := Eval hnf in [subType for pointed_poly].
Definition pointedPoly_eqMixin := Eval hnf in [eqMixin of pointedPoly by <:].
Canonical pointedPoly_eqType := Eval hnf in EqType pointedPoly pointedPoly_eqMixin.
Definition pointedPoly_choiceMixin := Eval hnf in [choiceMixin of pointedPoly by <:].
Canonical pointedPoly_choiceType := Eval hnf in ChoiceType pointedPoly pointedPoly_choiceMixin.

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

Canonical pointedPoly_of_subType := Eval hnf in [subType of 'pointed[R]_n].
Canonical pointedPoly_of_eqType := Eval hnf in [eqType of 'pointed[R]_n].
Canonical pointedPoly_of_choiceType := Eval hnf in [choiceType of 'pointed[R]_n].
End PointedTheory.

(* -------------------------------------------------------------------- *)
Section PolyPO.
Context (R : realFieldType) (n : nat).

Implicit Types P Q : 'poly[R]_n.

Local Lemma poly_proper_def P Q :
  (P `<` Q) = (Q != P) && (P `<=` Q).
Proof. by rewrite poly_properEneq eq_sym andbC. Qed.

Local Lemma poly_subset_anti :
  antisymmetric (@poly_subset R n).
Proof. by move=> P Q /andP[]; apply: poly_subset_anti. Qed.

Definition poly_porderMixin :=
  LePOrderMixin poly_proper_def poly_subset_refl poly_subset_anti poly_subset_trans.
Canonical poly_porderType :=
  Eval hnf in POrderType ring_display 'poly[R]_n poly_porderMixin.

Definition pointedPoly_porderMixin := [porderMixin of @pointedPoly R n by <:].
Canonical pointedPoly_porderType :=
  Eval hnf in POrderType ring_display (@pointedPoly R n) pointedPoly_porderMixin.

Definition pointedPoly_of_porderType :=
  Eval hnf in [porderType of 'pointed[R]_n].
End PolyPO.

(* -------------------------------------------------------------------- *)
Section SeqSubPOrder.
Context {disp : unit} (T : porderType disp) (s : seq T).

Definition seqsub_porderMixin :=
  [porderMixin of seq_sub s by <:].
Canonical seqsub_porderType :=
  Eval hnf in POrderType disp (seq_sub s) seqsub_porderMixin.
End SeqSubPOrder.

(* -------------------------------------------------------------------- *)
Section FacesSubType.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Variant polyFaces : predArgType := PolyFace of seq_sub (face_set P).

Definition poly_face F := let: PolyFace F := F in F.

Canonical polyFaces_subType := Eval hnf in [newType for poly_face].
Definition polyFaces_eqMixin := Eval hnf in [eqMixin of polyFaces by <:].
Canonical polyFaces_eqType := Eval hnf in EqType polyFaces polyFaces_eqMixin.
Definition polyFaces_choiceMixin := Eval hnf in [choiceMixin of polyFaces by <:].
Canonical polyFaces_choiceType := Eval hnf in ChoiceType polyFaces polyFaces_choiceMixin.
Definition polyFaces_countMixin := Eval hnf in [countMixin of polyFaces by <:].
Canonical polyFaces_countType := Eval hnf in CountType polyFaces polyFaces_countMixin.
Canonical polyFaces_subCountType := Eval hnf in [subCountType of polyFaces].
Definition polyFaces_finMixin := Eval hnf in [finMixin of polyFaces by <:].
Canonical polyFaces_finType := Eval hnf in FinType polyFaces polyFaces_finMixin.
Canonical polyFaces_subFinType := Eval hnf in [subFinType of polyFaces].
Definition polyFaces_porderMixin := Eval hnf in [porderMixin of polyFaces by <:].
Canonical polyFaces_porderType := Eval hnf in POrderType ring_display polyFaces polyFaces_porderMixin.
Canonical polyFaces_finPOrderType := Eval hnf in [finPOrderType of polyFaces].

Coercion facepoly (F : polyFaces) := val (val F).
End FacesSubType.

Bind Scope ring_scope with polyFaces.

Reserved Notation "{ 'faces' P }" (at level 8, format "{ 'faces'  P }").

Notation "{ 'faces' P }" := (@polyFaces _ _  P).

(* -------------------------------------------------------------------- *)
Section FacesSubTheory.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma facesP (F : {faces P}) : (facepoly F) \in face_set P.
Proof. by apply: valP. Qed.

Lemma facepoly_inj : injective (facepoly (P := P)).
Proof. by move=> F1 F2 /val_inj /val_inj. Qed.

Lemma PolyFaceK (F : 'poly[R]_n) (p : F \in face_set P) :
  facepoly (PolyFace (SeqSub p)) = F.
Proof. by []. Qed.

Lemma leEfaces (F1 F2 : {faces P}) :
  (F1 <= F2) = (facepoly F1 `<=` facepoly F2).
Proof. by rewrite !leEsub. Qed.

Lemma ltEfaces (F1 F2 : {faces P}) :
  (F1 < F2) = (facepoly F1 `<` facepoly F2).
Proof. by rewrite !ltEsub. Qed.

Definition lteEfaces := (leEfaces, ltEfaces).
End FacesSubTheory.

(* -------------------------------------------------------------------- *)
Import MeetBTFinMixin.Exports.

Section FacesLattice.
Context (R : realFieldType) (n : nat) (P : 'poly[R]_n).

Lemma poly0_fp : `[poly0] \in face_set P.
Proof. by apply: poly0_face_set. Qed.

Lemma polyP_fp : P \in face_set P.
Proof. by apply: face_set_self. Qed.

Let fp0 := (PolyFace (SeqSub poly0_fp)).
Let fp1 := (PolyFace (SeqSub polyP_fp)).

Definition fpI (F1 F2 : {faces P}) : {faces P} :=
  PolyFace (SeqSub (face_set_polyI (facesP F1) (facesP F2))).

Lemma fpIC : commutative fpI.
Proof.
move=> F1 F2; apply: facepoly_inj; rewrite !PolyFaceK.
by apply/poly_eqP=> x; rewrite !in_polyI andbC.
Qed.

Lemma fp_le_def (F1 F2 : {faces P}) : (F1 <= F2) = (fpI F1 F2 == F1).
Proof.
rewrite leEfaces -(inj_eq (@facepoly_inj _ _ _)) fpIC.
by apply/idP/eqP => /polyIidPr.
Qed.

Lemma fp_lt_def (F1 F2 : {faces P}) : (F1 < F2) = (F2 != F1) && (F1 <= F2).
Proof. by rewrite !lteEfaces poly_properEneq andbC eq_sym. Qed.

Lemma fpIA : associative fpI.
Proof.
move=> F1 F2 F3; apply: facepoly_inj; rewrite !PolyFaceK.
by apply/poly_eqP=> x; rewrite !in_polyI andbA.
Qed.

Lemma fpII : idempotent fpI.
Proof.
move=> F; apply: facepoly_inj; rewrite !PolyFaceK.
by apply/poly_eqP=> x; rewrite !in_polyI andbb.
Qed.

Lemma fp0I (F : {faces P}) : fp0 <= F.
Proof. by rewrite !leEsub /= /Order.le /= poly0_subset. Qed.

Lemma fpI1 (F : {faces P}) : F <= fp1.
Proof. by rewrite !leEsub /= /Order.le /=; apply/face_subset/facesP. Qed.

Definition polyFaces_latticeMixin :=
   MeetBTFinMixin fp_le_def fpIC fpIA fpII fp0I fpI1.

Canonical polyFaces_latticeType :=
  Eval hnf in LatticeType {faces P} polyFaces_latticeMixin.
Canonical polyFaces_bLatticeType :=
  Eval hnf in BLatticeType {faces P} polyFaces_latticeMixin.
Canonical polyFaces_tbLatticeType :=
  Eval hnf in TBLatticeType {faces P} polyFaces_latticeMixin.
Canonical polyFaces_finLatticeType :=
  Eval hnf in [finLatticeType of {faces P}].
End FacesLattice.

(* -------------------------------------------------------------------- *)
Section FacesGradedLattice.
Context (R : realFieldType) (n : nat) (P : 'pointed[R]_n).

Lemma foo :
  [/\ forall x y : {faces P}, x < y -> (dim x < dim y)%N
   &  forall x y : {faces P}, ((rank x).+1 < rank y)%N -> exists z, x < z < y].



End FacesGradedLattice.


(*
(* -------------------------------------------------------------------- *)
Parameter (R : realFieldType) (n : nat) (P : 'poly[R]_n).
Parameter (F1 F2 : {faces P}).

Notation I := '[<F1; F2>].

Import OMorphism.Exports.

Goal exists Q : 'poly[R]_n, exists f : {omorphism I -> {faces Q}}%O, bijective f.
*)
 
(*
 * {faces P} est (face_set P) directement
 * Gradation de {faces P}
 * intervalle TB + gradation
 * morphisme de rang
 * atomicité, co-atomicité

 * Propagation:
 * - integration de vertex figure
 * - treillis triviaux (d'un point, d'un segment, d'un polyhedre de hg 2)
 * - tout intervalle de hauteur 2 dans un face lattice est un diamant
 *)
