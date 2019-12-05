(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product vector_order row_submx.
Require Import hpolyhedron polyhedron barycenter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

Section PolyBase.

Variable (R : realFieldType) (n : nat).

Section FixedBase.

Variable (base : base_t[R,n]).

Definition has_base (P : 'poly[R]_n) :=
  (P `>` `[poly0]) ==>
    [exists I : {fsubset base}, P == 'P^=(base; I)].

Lemma has_baseP (P : 'poly[R]_n) :
  reflect ((P `>` `[poly0]) -> exists I : {fsubset base}, P = 'P^=(base; I)) (has_base P).
Proof.
by apply/(iffP implyP) => [H /H /exists_eqP [I ->]| H /H [I ->]];
  [|apply/exists_eqP]; exists I.
Qed.

Inductive poly_base := PolyBase { pval :> 'poly[R]_n ; _ : has_base pval}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin := Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType := Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin := Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType := Eval hnf in ChoiceType poly_base poly_base_choiceMixin.

Lemma poly_base_base (P : poly_base) : has_base P.
Proof.
exact: valP.
Qed.

Lemma poly0_baseP : has_base (`[poly0] : 'poly[R]_n).
Proof.
by rewrite /has_base poly_properxx.
Qed.
Canonical poly0_base := PolyBase poly0_baseP.

End FixedBase.

Notation "'{poly'  base '}'" := (poly_base base) : poly_scope.
Definition poly_base_of base (x : {poly base}) & (phantom 'poly[R]_n x) : {poly base} := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

Lemma polyEq_baseP base I :
  (I `<=` base)%fset -> has_base base 'P^=(base; I).
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

Definition set_of_poly_base (P : {poly base}) : option {fsubset base} :=
  if emptyP (P : 'poly[R]_n) is NonEmpty H then
    let I := xchoose (existsP (implyP (poly_base_base P) H)) in
    Some I
  else
    None.

Definition set_of_poly_base_pinv (I : {fsubset base})  : option (poly_base base) :=
  let P := 'P^=(base; I)%:poly_base in
  if set_of_poly_base P == Some I then Some P else None.

Lemma set_of_poly_baseK :
  pcancel set_of_poly_base (obind set_of_poly_base_pinv).
Proof.
move => P.
rewrite /set_of_poly_base.
Admitted.
(*have eq: forall P : poly_base, P `>` (`[poly0]) -> P = '['P^=(base; (set_of_poly_base P))]%:poly_base.
- move => P; apply/val_inj => /=; apply/eqP.
  exact: (xchooseP (existsP (poly_base_base P))).
move => P; rewrite /set_of_poly_base_pinv.
case: ifP; last first.
- move/negbT/negP; by rewrite -eq.
- by move/eqP ->; rewrite -2!eq.
Qed.*)

Definition poly_base_countMixin := PcanCountMixin set_of_poly_baseK.
Canonical poly_base_countType := Eval hnf in CountType (poly_base base) poly_base_countMixin.
Definition poly_base_finMixin := PcanFinMixin set_of_poly_baseK.
Canonical poly_base_finType := Eval hnf in FinType (poly_base base) poly_base_finMixin.
Canonical poly_base_subFinType := [subFinType of (poly_base base)].

Lemma poly_of_baseP :
  has_base base 'P(base).
Proof.
suff ->: 'P(base) = 'P^=(base; fset0)%:poly_base by exact: poly_base_base.
by rewrite /= polyEq0.
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

Lemma polyI_baseP (P Q : {poly base}) :
  has_base base (P `&` Q).
Proof.
Admitted.
Canonical polyI_base P Q := PolyBase (polyI_baseP P Q).

Lemma slice_baseP (e : base_elt) (P : {poly base}) :
  has_base (e +|` base) (slice e P).
Proof.
Admitted.
(*case/poly_baseP: P => [ | I _]; first by rewrite (quot_equivP slice0); exact: poly0_baseP.
apply/has_baseP => _.
by exists (slice_set I); rewrite -(quot_equivP slice_polyEq).*)

Canonical slice_base e P := PolyBase (slice_baseP e P).

Lemma argmin_baseP (P : {poly base}) c :
  has_base base (argmin P c).
Proof.
(* we first suppose that flat_prop holds, ie this is the situation in which
 * P (here quantified as Q) would play the role of the base *)
suff flat_prop: forall base0, bounded ('P(base0) : 'poly[R]_n) c -> has_base base0 (argmin ('P(base0) : 'poly[R]_n) c).
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

End PolyBase.

Notation "'{poly'  base '}'" := (@poly_base _ _ base) : poly_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.

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

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition active (P : {poly base}) := (* TODO: fix broken notation *)
  (\big[@fsetU _/fset0]_(I : {fsubset base} | (P `<=` 'P^=(base; I))) I)%:fsub.

Notation "'{eq'  P }" := (active P) : poly_scope.

(*
Section Test.
Variable (P : {poly base}).
Check ({eq P} : {fsubset base}).
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
- symmetry; apply: polyEq_big_polyI.
  apply/pred0Pn; rewrite P_eq /=; exists I.
  exact: poly_subset_refl.
Qed.

Lemma mem_repr_active (P : {poly base}) x :
  (x \in P) -> (x \in ('P^=(base; {eq P}))%:poly_base).
Proof.
move => x_in_P.
have h: P `>` (`[poly0]) by apply/proper0P; exists x.
by rewrite [P]repr_active in x_in_P.
Qed.

Lemma activeP (P : {poly base}) (I : {fsubset base}) :
  (P `<=` 'P^=(base; I)) = (I `<=` {eq P})%fset.
Proof.
apply/idP/idP.
- by move => Psub; apply/bigfcup_sup.
- case: (emptyP P) => [-> _|]; first exact: poly0_subset.
  move/repr_active => {2}-> /=.
  exact: polyEq_antimono.
Qed.

Lemma repr_active_supset {P : {poly base}} :
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

Lemma in_active (P : {poly base}) e :
  e \in base -> (e \in ({eq P} : {fset _})) = (P `<=` `[hp e]).
Proof.
rewrite -!fsub1set.
have ->: (P `<=` (`[ hp e ])) = (P `<=` 'P^=(base; [fset e]%fset)).
- rewrite polyEq1.
  apply/idP/poly_subsetIP => [? | [_ ?]]; last done.
  by split; first exact: poly_base_subset.
move => e_in_base.
have ->: ([fset e] = [fset e]%:fsub)%fset by done.
by rewrite activeP.
Qed.

Lemma poly_base_subset_eq (P Q : {poly base}) :
    (P `<=` Q) -> (({eq Q} : {fset _}) `<=` {eq P})%fset.
Proof.
case: (poly_baseP P) => [-> | ? [_ P_prop0]].
- rewrite active0 poly0_subset => _; exact: fsubset_subP.
- case: (poly_baseP Q) => [-> | ? [_ Q_prop0]].
  + rewrite -subset0N_proper in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma polyI_eq (P Q : {poly base}) :
  ({eq P} `|` {eq Q} `<=` {eq ((P `&` Q)%PH)%:poly_base})%fset.
Proof.
rewrite -activeP -polyEq_polyI.
by apply: polyISS; rewrite activeP.
Qed.

Lemma poly_base_proper (P Q : {poly base}) :
  ({eq Q} `<` {eq P})%fset -> P `<` Q.
Proof.
case: (poly_baseP Q) => [->| J [Q_eq Q_prop0]]; first by rewrite active0 fsubsetT_proper.
case: (poly_baseP P) => [->| I [P_eq P_prop0]]; first done.
rewrite {2}[Q]repr_active // => /fproperP [/fsubsetP eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; first exact: polyEq_antimono.
apply/poly_subsetPn.
move: i_notin; rewrite in_active.
- move/poly_subsetPn => [x x_in_Q x_notin].
  exists x; first by move/(poly_subsetP repr_active_supset): x_in_Q.
  move: x_notin; apply: contra => x_in; exact: (polyEq_eq x_in).
- move: i_in; apply/fsubsetP; exact: fsubset_subP.
Qed.

Lemma dim_le (P : {poly base}) :
  P `>` (`[poly0]) -> (\dim << {eq P} >> <= n)%N.
Proof.
move => /proper0P [x x_in_P].
have f_linear : lmorphism (fun (v : base_elt[R,n]) => v.1) by done.
pose f := Linear f_linear.
pose linfun_f := linfun f.
have /limg_dim_eq <-: (<<{eq P}>> :&: lker linfun_f)%VS = 0%VS.
- apply/eqP; rewrite -subv0.
  apply/subvP => e; rewrite memv_cap memv_ker memv0 => /andP [e_in /eqP f_e_eq0].
  have e1_eq0 : e.1 = 0 by rewrite lfunE in f_e_eq0.
  apply/be_eqP => /=; split; first done.
  move/(poly_subsetP repr_active_supset): x_in_P.
  rewrite polyEq_affine in_polyI => /andP [_ /in_affine/(_ _ e_in)].
  by rewrite in_hp e1_eq0 vdot0l => /eqP.
- apply/(leq_trans (n := \dim fullv)); first by apply/dimvS/subvf.
  by rewrite dimvf /Vector.dim /= muln1.
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

Axiom poly_has_base :
  forall P, exists (x : { base : base_t[R,n] & {poly base}}),
    P == (tagged x) :> 'poly[R]_n.

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

Lemma repr_baseP P : has_base (repr_base P) P.
Proof. Admitted.

Canonical poly_base_repr_baseP (P : 'poly[R]_n) := PolyBase (repr_baseP P).

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
Admitted.
(*Set Printing Coercions.
rewrite /BaseQuotient.repr_poly_base.
rewrite -[P in RHS]reprK /=.
suff -> //: forall x :  { base : base_t[R,n] & {poly base} } , pval (tagged x) = \pi_('poly_n)%qT x.
done.
move => x. rewrite /=.*)

Lemma polybW (Pt : 'poly[R]_n -> Prop) :
  (forall (base : base_t[R,n]) (Q : {poly base}), Pt Q)
  -> (forall P : 'poly[R]_n, Pt P).
Proof.
by move => ? P; rewrite -[P]reprK.
Qed.

End BaseQuotientAux.

Section PolyBaseFace.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition pb_face_set (P : {poly base}) : {set {poly base}} :=
  [set Q : {poly base} | Q `<=` P].

Notation "\face_set P" := (pb_face_set P) (at level 40).

CoInductive face_spec (P : {poly base}) : {poly base} -> Prop :=
| EmptyFace : face_spec P (`[poly0])%:poly_base
| ArgMin c of (bounded P c) : face_spec P (argmin P c)%:poly_base.

Lemma faceP (P Q : {poly base}) :
  Q \in \face_set P -> face_spec P Q.
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
  case/faceP : F'_in.
  + apply/imfsetP; exists (`[poly0]%:poly_base) => //=.
    rewrite inE; exact: poly0_subset.
  + move => c c_bounded.
    apply/imfsetP; exists ((argmin P2 c)%:poly_base) => /=.
    rewrite inE; exact: argmin_subset.
    by rewrite eq_P12.
Qed.

Lemma in_face_setP (base : base_t[R,n]) (F : 'poly[R]_n) (P : {poly base}) :
  reflect (exists2 Fb : {poly base}, F = Fb & Fb \in \face_set P) (F \in face_set P).
Proof.
apply: (iffP idP).
- by rewrite face_set_mono => /imfsetP [Fb ??]; exists Fb.
- by move => [{}F ->]; rewrite face_set_mono mem_imfset; try exact: val_inj.
Qed.

Lemma face_set_self (P : 'poly[R]_n) : P \in (face_set P).
Proof.
elim/polybW: P => base P.
apply/in_face_setP; exists P; by rewrite ?inE ?poly_subset_refl.
Qed.

Lemma face_set_of_face (P Q : 'poly[R]_n) :
  Q \in face_set P -> face_set Q = [fset Q' in (face_set P) | (Q' `<=` Q)%PH]%fset.
Proof.
elim/polybW: P => base P /in_face_setP [{}Q ->].
rewrite inE => Q_sub_P; apply/fsetP => Q'.
apply/in_face_setP/idP => [[{}Q' ->]| ].
- rewrite inE => Q'_sub_Q.
  apply/imfsetP; exists (Q' : 'poly[R]_n) => //.
  rewrite inE; apply/andP; split; try by done.
  apply/in_face_setP; exists Q'; rewrite ?inE //=.
  exact: (poly_subset_trans Q'_sub_Q).
- move/imfsetP => [{}Q' /andP [/in_face_setP [{}Q' -> _] ?] ->].
  by exists Q' => //; rewrite inE.
Qed.

Corollary subset_face_set (P Q : 'poly[R]_n) :
  Q \in face_set P -> (face_set Q `<=` face_set P)%fset.
Proof.
move/face_set_of_face ->; apply/fsubsetP => Q'.
by rewrite mem_imfset // => /andP[].
Qed.

Lemma face_set_subset (F : 'poly[R]_n) (P : 'poly[R]_n)  :
  F \in face_set P -> F `<=` P.
Proof.
elim/polybW: P => base P /in_face_setP[{F}F ->].
by rewrite inE.
Qed.

Lemma face_set0 : face_set (`[poly0]) = [fset `[poly0]]%fset.
Proof.
apply/fsetP => P; rewrite !inE /=; apply/idP/idP.
- by move/face_set_subset; rewrite subset0_equiv.
- move/eqP ->; exact: face_set_self.
Qed.

(*Variant face_set2_spec
  (base : base_t[R, n]) (Fb : {poly base})
  : 'poly[R]_n -> bool -> Type :=
| FaceSet2Spec (F' : {poly base}) :
    face_set2_spec Fb F' (F' \in face_set Fb).

Lemma face_set2P (base : base_t[R, n]) (Fb : {poly base}) (F : 'poly[R]_n) :
  @face_set2_spec base Fb F (F \in face_set2 Fb).
Proof. Admitted.

Lemma foo2 (F : 'poly[R]_n) (P : 'poly[R]_n)  :
  F \in face_set2 P -> F `<=` P.
Proof.
elim/polybW: P => base Q.
 case: face_set2P => {F}F.
Admitted.*)

End Face.

Section Dimension.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition poly_dim (P : {poly base}) :=
  if (P `>` `[poly0]) then
    (n-\dim << {eq P} >>%VS).+1%N
  else 0%N.

Lemma dim_poly0 : poly_dim (`[poly0]%:poly_base) = 0%N.
Proof.
by rewrite /poly_dim ifF // poly_properxx.
Qed.

Lemma poly_dimN0 (P : {poly base}) : (P `>` `[poly0]) = (poly_dim P > 0)%N.
Proof.
case/emptyP : (P) => [/val_inj -> | ? ]; first by rewrite dim_poly0 ltnn.
by rewrite /poly_dim ifT.
Qed.

Variant poly_dim_spec (P : {poly base}) : nat -> bool -> Prop :=
| PolyDimEmpty of (P = `[poly0]%:poly_base) : poly_dim_spec P 0 false
| PolyDimNonEmpty of (P `>` `[poly0]) : poly_dim_spec P (n - \dim << {eq P} >>%VS).+1%N true.

Lemma poly_dimP P : poly_dim_spec P (poly_dim P) (poly_dim P > 0)%N.
Proof.
case: (poly_baseP P) => [->| I /= [-> P_prop0]].
- by rewrite dim_poly0 ltnn; constructor.
- rewrite -poly_dimN0 P_prop0.
  by rewrite /poly_dim ifT //; constructor.
Qed.

Lemma poly_dim0 (P : {poly base}) : poly_dim P = 0%N -> P = `[poly0]%:poly_base.
Proof.
by case: (poly_dimP P).
Qed.

Lemma poly_dimS (P Q : {poly base}) : P `<=` Q -> (poly_dim P <= poly_dim Q)%N.
Proof.
case: (poly_dimP Q) => [-> | Q_prop0 P_sub_Q ].
- by rewrite subset0_equiv => /eqP /val_inj ->; rewrite dim_poly0.
- case: (poly_dimP P) => [//= | P_prop0].
  rewrite ltnS; move/poly_base_subset_eq/base_vect_subset/dimvS: P_sub_Q.
  exact: leq_sub2l.
Qed.

Lemma poly_dim_leqif_eq (P Q : {poly base}) :
  (P `<=` Q)%VS -> (poly_dim P <= poly_dim Q ?= iff (P == Q))%N.
Proof. move => P_sub_Q; split; first exact: poly_dimS.
apply/eqP/eqP; last by move => ->.
case: (poly_dimP Q) P_sub_Q => [-> | Q_prop0 P_sub_Q ].
- by rewrite subset0_equiv => /eqP /val_inj ->.
- case: (poly_dimP P) => [//= | P_prop0].
  move/succn_inj/(congr1 (addn^~ (\dim <<{eq P}>>%VS))).
  rewrite subnK; last exact: dim_le.
  rewrite addnC; move/(congr1 (addn^~ (\dim <<{eq Q}>>%VS))).
  rewrite -addnA subnK; last exact: dim_le.
  rewrite addnC; move/addIn => dimP_eq_dimQ.
  suff eq_eq: <<{eq P}>>%VS = <<{eq Q}>>%VS.
  + rewrite [P]repr_active // [Q]repr_active //.
    apply/val_inj => /=.
    by rewrite !polyEq_affine eq_eq.
  + symmetry; apply/eqP; rewrite -(geq_leqif (dimv_leqif_eq _)).
    * by rewrite dimP_eq_dimQ.
    * by apply/base_vect_subset/poly_base_subset_eq.
Qed.

End Dimension.

Section Gradedness.

Context {R : realFieldType} {n : nat} (base : base_t[R,n]).

Hypothesis non_redundant : non_redundant_base base.

Local Instance foo (e : base_elt) (_ : expose (e \in base)) : expose ([fset e] `<=` base)%fset.
Proof.
by rewrite fsub1set.
Qed.

(*Variable (e : base_elt[R,n]).
Hypothesis He : e \in base.
Check ([fset e]%fset%:fsub) : {fsubset base}.
Variable (P : {poly base}).
Set Typeclasses Debug.
Let S := (({eq P} `|` [fset e])%fset%:fsub) : {fsubset base}.
Check S.
Check 'P^=(base; S)%:poly_base.*)

Lemma activeU1 (P : {poly base}) (e : base_elt) & (e \in base) :
  (P `>` `[poly0]) ->
  let I : {fsubset base} := ({eq P} `|` [fset e])%fset%:fsub in
  {eq 'P^=(base; I)%:poly_base } = I.
Proof.
move => P_prop0.
case: (boolP (e \in ({eq P} : base_t))).
- move => h; apply/fsubset_inj.
  set I := ({eq P} `|` [fset e])%fset %:fsub.
  suff h': I = {eq P} :> base_t.
  have /= ->: 'P^= (base; I) = P by rewrite [P]repr_active // h'.
Admitted.

Lemma graded (P Q : {poly base}) :
  P `>` (`[poly0]) -> P `<` Q -> ~ (exists S, (P `<` S `<` Q)) -> poly_dim Q = (poly_dim P).+1%N.
Proof.
move => P_prop0 P_prop_Q P_cover_Q.
have Q_prop0 : Q `>` `[poly0] by apply: (poly_proper_trans P_prop0).
have eqP_prop_eqQ : ({eq Q} `<` {eq P})%fset by admit.
move/fproperP: (eqP_prop_eqQ) => [_ [i i_in_eqP i_notin_eqQ]].
have foo: ([fset i] `<=` base)%fset by admit.
set Q_U_i : {fsubset base} := (({eq Q} `|` [fset i])%fset)%:fsub.
(* TODO: I use set and not pose here because pose doesn't infer the instances *)
set S := 'P^=(base; Q_U_i)%:poly_base.
have P_sub_S : P `<=` S.
- rewrite activeP.
  apply/FSubset.fsubset_setUP; by [apply/fproper_sub | rewrite fsub1set].
Admitted.

End Gradedness.

(*
(* THE MATERIAL BELOW HAS NOT BEEN YET UPDATED *)

Section Relint.

Variable (R : realFieldType) (n : nat).

Lemma poly_base_extremeL m (base : m.-base[R,n]) (P : {poly base}) x y α :
  x \in ('P(base) : 'poly[R]_n) -> y \in ('P(base) : 'poly[R]_n) ->
    0 <= α < 1 -> (1-α) *: x + α *: y \in P -> x \in P.
Proof.
case: base P x y α => [A b] P x y α.
set z : 'cV_n := _ + _.
move => x_in_P y_in_P α_01 z_in_P.
have P_prop0 : (P `>` `[poly0]) by apply/proper0P; exists z.
rewrite [P]repr_active // in z_in_P *.
apply/in_polyEqP; split; last done.
move => j j_in_eq.
apply: (hp_extremeL (y := y) (α := α)); try by done.
- rewrite in_poly_of_base in x_in_P.
  rewrite // !inE /= row_vdot.
  by move/forallP: x_in_P.
- rewrite in_poly_of_base in y_in_P.
  rewrite // !inE /= row_vdot.
  by move/forallP: y_in_P.
by move/polyEq_eq/(_ j_in_eq) : z_in_P.
Qed.

Lemma poly_base_extremeR m (base : m.-base[R,n]) (P : {poly base}) x y α :
  x \in ('P(base) : 'poly[R]_n) -> y \in ('P(base) : 'poly[R]_n) ->
    0 < α <= 1 -> (1-α) *: x + α *: y \in P -> y \in P.
Proof.
case: base P x y α => [A b] P x y α.
set z : 'cV_n := _ + _.
move => x_in_P y_in_P α_01 z_in_P.
have P_prop0 : (P `>` `[poly0]) by apply/proper0P; exists z.
rewrite [P]repr_active // in z_in_P *.
apply/in_polyEqP; split; last done.
move => j j_in_eq.
apply: (hp_extremeR (x := x) (α := α)); try by done.
- rewrite in_poly_of_base in x_in_P.
  rewrite // !inE /= row_vdot.
  by move/forallP: x_in_P.
- rewrite in_poly_of_base in y_in_P.
  rewrite // !inE /= row_vdot.
  by move/forallP: y_in_P.
by move/polyEq_eq/(_ j_in_eq) : z_in_P.
Qed.

Definition relint m (base : m.-base[R,n]) (P : {poly base}) :=
  [predI P & [pred x | [forall Q : {poly base}, (Q `<` P) ==> (x \notin Q)]]].

Lemma in_relintP m (base : m.-base) (P : {poly base}) x :
  reflect (x \in P /\ (forall Q : {poly base}, (Q `<` P) -> x \notin Q)) (x \in relint P).
Admitted.

Lemma notin_relintP m (base : m.-base) (P Q : {poly base}) x :
  Q `<` P -> x \in Q -> x \notin relint P.
Admitted.

Lemma relint_subset m (base : m.-base) (P : {poly base}) :
  {subset (relint P) <= P}.
Admitted.

Lemma relint_activeP m (base : m.-base) (P : {poly base}) x :
  reflect (x \in P /\ (forall k, k \notin {eq P} -> x \notin (nth_hp base k : 'poly[R]_n))) (x \in relint P).
Proof.
Admitted.

Lemma relint_open_convexL m (base : m.-base) (P : {poly base}) x y α :
  x \in P -> y \in relint P -> 0 < α <= 1 -> (1-α) *: x + α *: y \in relint P.
Proof.
set z : 'cV_n := _ + _.
move => x_in_P y_in_relint α_01.
have y_in_P: y \in P by rewrite relint_subset.
apply/in_relintP; split.
have : z \in (conv ([fset x; y]%fset) : 'poly[R]_n).
- apply/in_segmP; exists α; [by apply/lt_leW | done].
  by apply/poly_subsetP/convexP2.
- move => Q Q_prop_P.
  move/in_relintP: (y_in_relint) => [_ /(_ _ Q_prop_P)].
  apply: contra.
  have Q_face : Q \in face_set P by rewrite inE poly_properW.
  move/faceP : Q_face => [Q_eq0 | c c_bounded].
  + by rewrite /= inE in Q_eq0.
  + rewrite /= argmin_polyI // inE => /andP [_ z_in_hp].
    rewrite inE y_in_P /=.
    apply: (hp_extremeR (x := x) (α := α)); try done.
    * move: (x) x_in_P; apply/poly_subsetP.
      exact: opt_value_lower_bound.
    * move: (y) y_in_P; apply/poly_subsetP.
      exact: opt_value_lower_bound.
Qed.

Lemma relint_open_convexR m (base : m.-base) (P : {poly base}) x y α :
  x \in relint P -> y \in P -> 0 <= α < 1 -> (1-α) *: x + α *: y \in relint P.
Proof.
set z : 'cV_n := _ + _.
move => x_in_relint y_in_P α_01.
have x_in_P: x \in P by rewrite relint_subset.
apply/in_relintP; split.
have : z \in (conv ([fset x; y]%fset) : 'poly[R]_n).
- apply/in_segmP; exists α; [by apply/ltW_le | done].
  by apply/poly_subsetP/convexP2.
- move => Q Q_prop_P.
  move/in_relintP: (x_in_relint) => [_ /(_ _ Q_prop_P)].
  apply: contra.
  have Q_face : Q \in face_set P by rewrite inE poly_properW.
  move/faceP : Q_face => [Q_eq0 | c c_bounded].
  + by rewrite /= inE in Q_eq0.
  + rewrite /= argmin_polyI // inE => /andP [_ z_in_hp].
    rewrite inE x_in_P /=.
    apply: (hp_extremeL (y := y) (α := α)); try done.
    * move: (x) x_in_P; apply/poly_subsetP.
      exact: opt_value_lower_bound.
    * move: (y) y_in_P; apply/poly_subsetP.
      exact: opt_value_lower_bound.
Qed.

End Relint.

Section AffineHull.

Variable (R : realFieldType) (n : nat).

Definition hull (m : nat) (base : m.-base[R,n]) (P : {poly base}) :=
  kermx (row_submx base.1 {eq P})^T.

(*
Lemma in_hullP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (P : {poly 'P(A,b)}) (d : 'cV[R]_n) :
  reflect (forall j, j \in {eq P} -> (A *m d) j 0 = 0) (d^T <= hull P)%MS.
Proof.
apply: (equivP sub_kermxP); rewrite -trmx_mul -{1}[0]trmx0; split.
- by move/trmx_inj; rewrite -row_submx_mul => /row_submx_col0P.
- by move => ?; apply/congr1; rewrite -row_submx_mul; apply/row_submx_col0P.
Qed.
 *)

Definition Sdim (m : nat) (base : m.-base[R,n]) (P : {poly base}) :=
  if (P == (`[poly0]) :> 'poly[R]_n) then 0%N else ((\rank (hull P)).+1).

(*
Fact relint_key : unit. Proof. by []. Qed.
Definition relint_pt base (P : {poly base}) : 'cV[R]_n := locked_with relint_key 0.

Lemma relint_pt_in_poly base (P : {poly base}) : relint_pt P \in P.
Admitted.

Lemma relint_pt_ineq (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (P : {poly 'P(A,b)}) i :
  i \notin {eq P} -> relint_pt P \notin (`[hp (row i A)^T & b i 0] : 'poly[R]_n).
Admitted.

Lemma hull_relintP base (P : {poly base}) d :
  reflect (exists eps, eps > 0 /\ relint_pt P + eps *: d \in P)
                             ((d^T <= hull P)%MS).
Admitted.

Lemma hullP base (P : {poly base}) d :
   reflect (exists x y, [/\ x \in P, y \in P & ((x-y)^T :=: d^T)%MS])
                              (d^T <= hull P)%MS.
Admitted.
 *)

(* TO BE FIXED : why do we need extra parenthesis for `[pt x] ? *)
Lemma Sdim1P (m : nat) (base : m.-base) (P : {poly base}) :
  reflect (exists x, (P = (`[pt x]) :> 'poly[R]_n)) (Sdim P == 1%N).
Admitted.

Lemma relint_non_empty (m : nat) (base : m.-base) (P : {poly base}) :
  reflect (exists x, x \in relint P) (Sdim P > 1)%N.
Admitted.

Lemma Sdim_homo (m : nat) (base : m.-base) :
  {homo (Sdim (base := base)) : x y / (x `<=` y) >-> (x <= y)%N }.
Admitted.

Lemma dim_homo_proper (m : nat) (base : m.-base) (P Q : {poly base}) :
  P `<` Q -> (Sdim P < Sdim Q)%N.
Admitted.

End AffineHull.

Section Vertex.

Variable (R : realFieldType) (n : nat) (m : nat) (base : m.-base[R,n]).

Definition fvertex := [set F : {poly base} | (Sdim F == 0)%N].

Definition vertex :=
  ((fun (F : {poly base}) => pick_point F) @` fvertex)%fset.

CoInductive fvertex_spec : {poly base} -> 'cV[R]_n -> Prop :=
| FVertex x (H : has_base base (`[pt x])) : fvertex_spec (PolyBase H) x.

Notation "'`[' 'pt'  x  ']%:poly_base'" := (@PolyBase _ _ _ _ (`[pt x]) _).

Lemma fvertexP (F : {poly base}) :
  F \in fvertex -> fvertex_spec F (pick_point F).
Admitted.

Lemma fvertex_baseP (F : {poly base}) :
  reflect (exists2 x, (x \in vertex) & F = (`[pt x]) :> 'poly[R]_n) (F \in fvertex).
Admitted.

(*Lemma dim_vertex x : (x \in vertex_base) ->
  Sdim (`[pt x]%:poly_base) = 0%N.
Admitted.*)

Definition fvertex_set (P : {poly base}) := [set F in fvertex | F `<=` P].
Definition vertex_set (P : {poly base}) := [fset x in vertex | x \in P]%fset.

Lemma mink (P : {poly base}) :
  P = conv (vertex_set P) :> 'poly[R]_n.
Admitted.

Lemma vertex_set_mono (P Q : {poly base}) :
  ((P `<=` Q) = (vertex_set P `<=` vertex_set Q)%fset)
* ((P `<` Q) = (vertex_set P `<` vertex_set Q)%fset).
Admitted.

Lemma vertex_set_subset (P : {poly base}) :
  {subset (vertex_set P) <= P}.
Admitted.

End Vertex.

Notation "x '%:pt'" := (pick_point x) (at level 0).

Section VertexFigure.

Variable (R : realFieldType) (n : nat).
Variable (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m).

Variable (c : 'cV[R]_n) (d : R).
Variable (v : {poly (A,b)}).
Hypothesis v_vtx : (v \in fvertex (A,b)).
Hypothesis c_v : '[c, v%:pt] < d.

Section SliceFace.

Variable P : {poly (A,b)}.
Hypothesis P_prop : v `<` P.
Hypothesis c_sep : forall w, w \in fvertex_set P -> w != v -> '[c, w%:pt] > d.

(*Fact other_vtx : exists2 w, (w \in vertex_set P) & '[c,w] > d.
Proof.
move: P_prop; rewrite vertex_set_mono => /fproperP [_] [w w_in /= w_neq_v].
rewrite vertex_set1 inE in w_neq_v.
by exists w; try exact: c_sep.
Qed.
*)

Lemma foo x y : '[c,x] < d < '[c, y] ->
                exists2 α, (0 < α < 1) & '[c, (1-α) *: x + α *: y] = d.
Admitted.

(*Lemma slice_face_proper0 : slice c d P `>` `[poly0].
Proof.
move: other_vtx => [w w_in c_w].
have [x x_in c_x] : exists2 x, (x \in (conv [fset v; w]%fset : 'poly[R]_n)) & '[c,x] = d.
- move/andP: (conj c_v c_w) => /foo [α α_0_1].
  set x : 'cV_n := (X in '[c,X] = d) => c_x; exists x; last done.
  admit.
apply/proper0P; exists x; rewrite inE; apply/andP; split; last by rewrite c_x.
move: x_in; apply/poly_subsetP; apply: convexP2;
  [ exact: pt_proper | exact: vertex_set_subset ].
Admitted.*)

Lemma active_slice_eq : slice_set {eq P} = {eq (slice c d P) %:poly_base}.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; first exact: active_slice.
apply/subsetP => i; case: (split1P i) => [_ | k].
- by rewrite inE in_set1.
- rewrite in_active nth_hp_slice => slice_sub.
  apply/setU1P; right; apply: mem_imset; move: slice_sub; apply: contraTT => k_notin_eqP.
  suff [y y_relint c_y]: exists2 y, y \in relint P & '[c,y] = d.
  + move/in_relintP : y_relint => [y_in_P].
    pose Q := ('P^=(A, b; (k |: {eq P})))%:poly_base.
    have Q_prop_P : Q `<` P.
    * admit.
    move/(_ _ Q_prop_P) => y_notin_Q.
    apply/poly_subsetPn; exists y; rewrite //=.
    by rewrite inE; apply/andP; split; rewrite ?c_y.
    Admitted.
(*
  [y /in_relintP [y_in_P /(_ _ k_notin_eqP) H] c_y]
  + apply/poly_subsetPn; exists y; rewrite //=.
    by rewrite inE; apply/andP; split; rewrite ?c_y.
  + have /relint_non_empty [x x_in] : (dim P > 0)%N.
      by move/dim_homo_proper: P_prop; rewrite dim_vertex.
    case: (ltrgtP '[c,x] d) => [c_x | c_x | ? ]; last by exists x.
    - move: other_vtx => [w w_in c_w].
      move/andP : (conj c_x c_w) => /foo [α α_0_1].
      set y : 'cV_n := (X in '[c,X] = d) => c_y; exists y; last done.
      apply: relint_open_convexR;
        [ done | exact: vertex_set_subset | exact: ltW_lt ].
    - move/andP : (conj c_v c_x) => /foo [α α_0_1].
      set y : 'cV_n := (X in '[c,X] = d) => c_y; exists y; last done.
      apply: relint_open_convexL;
        [ by move/pt_proper : P_prop | done | exact: lt_ltW ].
Qed.*)

Lemma dim_slice : Sdim (slice c d P) %:poly_base = (Sdim P - 1)%N.
Admitted.

End SliceFace.

(*
Section SliceFaceSet.

Variable P : {poly 'P(A,b)}.
Hypothesis P_prop : `[pt v]%:poly_base `<` P.
Hypothesis c_sep : forall w, w \in vertex_set P -> w != v -> '[c, w] > d.

Fact sep_face F :
  F \in face_set P -> forall w, w \in vertex_set F -> w != v -> '[c, w] > d.
Proof.
rewrite inE vertex_set_mono => [/fsubsetP vtx_sub] w ??.
by apply: c_sep; try exact: vtx_sub.
Qed.

Local Instance slice_face_proper0' F : F \in face_set P -> infer (slice c d F `>` `[poly0]).
Admitted.

Definition slice_face (F : {poly 'P(A, b)}) :
  (`[pt v]%:poly_base `<` F) -> (F \in face_set P) -> (slice c d F)%:poly_base `<=` (slice c d P)%:poly_base.


Set Printing All.
Lemma active_slice_eq.



End VertexFigure.
 *)

(*


Section VertexBase.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Inductive vertex_base := VertexBase { pt_val :> 'cV[R]_n; _ : [ `[pt pt_val] has \base base] }.
Canonical vertex_base_subType := [subType for pt_val].
Definition vertex_base_eqMixin := Eval hnf in [eqMixin of vertex_base by <:].
Canonical vertex_base_eqType := Eval hnf in EqType vertex_base vertex_base_eqMixin.
Definition vertex_base_choiceMixin := Eval hnf in [choiceMixin of vertex_base by <:].
Canonical vertex_base_choiceType := Eval hnf in ChoiceType vertex_base vertex_base_choiceMixin.

Lemma vertex_base_baseP (v : vertex_base) : [ `[pt v] has \base base].
Proof.
exact : (valP v).
Qed.

Canonical vertex_base_poly (v : vertex_base) := PolyBase (vertex_base_baseP v).

Lemma poly_base_vertexP (P : {poly base}) :
  P `>` (`[poly0]) -> (dim P == 0%N) -> [ `[pt (pick_point P)] has \base base].
Admitted.

Definition poly_base_vertex (P : {poly base}) :=
  if @idP (P `>` (`[poly0])) is ReflectT P_prop0 then
    if @idP (dim P == 0%N) is ReflectT P_dim0 then
      Some (VertexBase (poly_base_vertexP P_prop0 P_dim0))
    else None
  else None.

Lemma vertex_poly_baseK : pcancel vertex_base_poly poly_base_vertex.
Admitted.

Definition vertex_base_countMixin := PcanCountMixin vertex_poly_baseK.
Canonical vertex_base_countType := Eval hnf in CountType vertex_base vertex_base_countMixin.
Definition vertex_base_finMixin := PcanFinMixin vertex_poly_baseK.
Canonical vertex_base_finType := Eval hnf in FinType vertex_base vertex_base_finMixin.

End VertexBase.

Notation "'{vertex'  base '}'" := (vertex_base base) : poly_scope.

Section Vertex.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Definition vertex_set (P : {poly base}) := [set v : {vertex base} | (v : 'cV__) \in P].

Lemma vertexP (P : {poly base}) (v : {vertex base}) :
  (v \in vertex_set P) = (`[pt v]%:poly_base \in face_set P).
Proof.
by rewrite inE [RHS]inE pt_proper0 pt_subset.
Qed.

End Vertex.

*)

(*
Section Vertex.

Variable (R : realFieldType) (n : nat) (base : 'hpoly[R]_n).

Implicit Types (P Q F : {poly base}).

Definition fvertex_set P := [set F in face_set P | dim F == 0%N].

Definition vertex_set P :=
  ((fun (F : {poly base}) => pick_point F) @` (fvertex_set P))%fset.

Lemma vertex_has_baseP P x (H : x \in vertex_set P) : [ `[pt x] has \base base].
Proof.
move/imfsetP: H => [fx /=]; rewrite inE => /andP [fx_face].
have fx_non_empty: (fx `>` `[poly0]) by move: fx_face; rewrite inE => /andP [].
move/(dim0P fx_non_empty) => [x'] fx_eq.
rewrite fx_eq pick_point_pt => ->; rewrite -fx_eq.
exact: poly_base_base.
Qed.
Canonical vertex_poly_base P x (H : x \in vertex_set P) := PolyBase (vertex_has_baseP H).

Lemma vertex_in_face_set P x (H : x \in vertex_set P) : vertex_poly_base H \in face_set P.
Admitted.
(*Variable (P : {poly base}) (x : 'cV[R]_n).
  Check (`[pt x]%:poly_base).*)


End Vertex.
*)
End VertexFigure.
*)