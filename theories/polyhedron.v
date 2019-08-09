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
Require Import polypred. (* hpolyhedron.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

Section PolyBase.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n).

Section FixedBase.

Variable (base : base_t[R,n]).

Definition has_base (P : {quot T}) :=
  (P `>` `[poly0]) ==>
    [exists I : {fsubset base}, P == 'P^=(base; I)].


Lemma has_baseP (P : {quot T}) :
  reflect ((P `>` `[poly0]) -> exists I : {fsubset base}, P = 'P^=(base; I)) (has_base P).
Admitted.

Inductive poly_base := PolyBase { pval :> {quot T} ; _ : has_base pval}.
Canonical poly_base_subType := [subType for pval].
Definition poly_base_eqMixin := Eval hnf in [eqMixin of poly_base by <:].
Canonical poly_base_eqType := Eval hnf in EqType poly_base poly_base_eqMixin.
Definition poly_base_choiceMixin := Eval hnf in [choiceMixin of poly_base by <:].
Canonical poly_base_choiceType := Eval hnf in ChoiceType poly_base poly_base_choiceMixin.

Lemma poly_base_base (P : poly_base) : has_base P.
Proof.
exact: valP.
Qed.

Lemma poly0_baseP : has_base (`[poly0] : {quot T}).
Proof.
by rewrite /has_base poly_properxx.
Qed.
Canonical poly0_base := PolyBase poly0_baseP.

End FixedBase.

Notation "'{poly'  base '}'" := (poly_base base) : poly_scope.
Definition poly_base_of base (x : {poly base}) & (phantom {quot T} x) : {poly base} := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

Lemma polyEq_baseP base I :
  (I `<=` base)%fset -> has_base base 'P^=(base; I).
Proof.
move => Isub.
by apply/implyP => _; apply/exists_eqP => /=; exists (I %:fsub).
Qed.

Canonical polyEq_base base I (H : expose (I `<=` base)%fset) := PolyBase (polyEq_baseP H).

Section Test.
Variable (base I : base_t[R,n]) (I' : {fsubset base}).
Hypothesis Isub : (I `<=` base)%fset.
Check ('P^=(base; I)%:poly_base) : {poly base}.
Check ('P^=(base; I')%:poly_base) : {poly base}.
End Test.

Variable base : base_t[R,n].

Variant poly_base_spec (P : {poly base}) : Prop :=
| PolyBase0 of (P = (`[poly0])%:poly_base) : poly_base_spec P
| PolyBaseN0 (I : {fsubset base}) of (P = 'P^=(base; I)%:poly_base /\ P `>` `[poly0]) : poly_base_spec P.

Lemma poly_baseP (P : {poly base}) : poly_base_spec P.
Proof.
case: (emptyP P) => [/poly_equivP/quot_equivP/val_inj -> | P_prop0]; first by constructor.
move/implyP/(_ P_prop0)/exists_eqP: (poly_base_base P) => [I ?].
constructor 2 with I.
split; [exact: val_inj | done].
Qed.

Section Test.
Variable P Q : {poly base}.
Goal P = Q.
case/poly_baseP: P.
Abort.

End Test.

Lemma poly_base_subset (P : {poly base}) :
  P `<=` 'P(base).
Proof.
case/poly_baseP : (P) => [->| I [-> _]];
  [ exact: poly0_subset | exact: polyEq_antimono0].
Qed.

Definition set_of_poly_base (P : {poly base}) : option {fsubset base} :=
  if emptyP (P : {quot T}) is NonEmpty H then
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
by rewrite /= (quot_equivP polyEq0).
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

Lemma polyI_of_baseP (P Q : {poly base}) :
  has_base base (P `&` Q).
Proof.
Admitted.
Canonical polyI_of_base P Q := PolyBase (polyI_of_baseP P Q).

Lemma slice_of_baseP (e : base_elt) (P : {poly base}) :
  has_base (e +|` base) (slice e P).
Proof.
Admitted.
(*case/poly_baseP: P => [ | I _]; first by rewrite (quot_equivP slice0); exact: poly0_baseP.
apply/has_baseP => _.
by exists (slice_set I); rewrite -(quot_equivP slice_polyEq).*)

Canonical slice_of_base e P := PolyBase (slice_of_baseP e P).


Lemma argmin_baseP (P : {poly base}) c :
  has_base base (argmin P c).
Proof.
(* we first suppose that flat_prop holds, ie this is the situation in which
 * P (here quantified as Q) would play the role of the base *)
suff flat_prop: forall base0, bounded ('P(base0) : {quot T}) c -> has_base base0 (argmin ('P(base0) : {quot T}) c).
- apply/has_baseP; rewrite -bounded_argminN0.
  case/poly_baseP : (P) => [->| I [-> _]]; first by rewrite bounded_poly0.
  rewrite /= (quot_equivP (polyEq_flatten _)) => bounded_PI.
  move/flat_prop/has_baseP: (bounded_PI); rewrite -bounded_argminN0.
  move => /(_ bounded_PI) => [[J] ->].
  by move: (polyEq_of_polyEq (T := [polyPredType of {quot T}]) J)
    => [K] /quot_equivP ->; exists K. (* TODO: ugly to specify the polyPredType *)
- (* now this is the classic proof of Schrijver *)
  move => base0 c_bounded.
  move: (dual_opt_sol c_bounded) => [w w_ge0 w_comb].
  pose I := [fset e in base0 | w e > 0]%fset.
  have supp_w : forall e, (w e > 0) = (e \in I). admit.
  apply/has_baseP; exists I%:fsub.
  apply/quot_equivP.
  move: (opt_point c_bounded) => [x x_in_P0 c_x_eq_opt_val].
  have: x \in `[hp (combine base0 w)] : {quot T}.
  - by rewrite inE w_comb /=; apply/eqP.
  move/(compl_slack_cond w_ge0 supp_w x_in_P0) => x_in_P0I.
  move: (congr1 fst w_comb) => /= <-; apply/dual_sol_argmin; try by done.
  by apply/proper0P; exists x.
Admitted.
Canonical argmin_base (P : {poly base}) c := PolyBase (argmin_baseP P c).

End PolyBase.

Notation "'{poly'  T , base '}'" := (@poly_base _ _ T base) : poly_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.

Section Test.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n) (base : base_t[R,n]).

Variables (P Q : {poly T, base}) (Q' : {quot T}) (x : 'cV[R]_n).

Check (P `&` Q : {quot T}).
Check (x \in P).

Goal P `<=` Q' -> forall x, x \in P -> x \in Q'.
move/poly_subsetP => H z z_in_P.
by move/H: z_in_P.
Qed.

Goal (P = Q' :> {quot T}) -> x \in P -> x \in Q'.
move <-.
done.
Qed.

Unset Printing Coercions.

End Test.

Section Active.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n) (base : base_t[R,n]).

Definition active (P : {poly T, base}) :=
  (\big[@fsetU _/fset0]_(I : {fsubset base} | (P `<=` 'P^=(base; I))) I)%:fsub.

Notation "'{eq'  P }" := (active P) : poly_scope.

Section Test.
Variable (P : {poly T, base}).
Check ({eq P} : {fsubset base}).
Check 'P^=(base; {eq P}) : {quot T}.
Check 'P^=(base; {eq P})%:poly_base : {poly T, base}.
End Test.

Lemma repr_active (P : {poly T, base}) :
  P `>` (`[poly0]) -> P = ('P^=(base; {eq P}))%:poly_base.
Proof.
case/poly_baseP: (P) => [->|]; first by rewrite poly_properxx.
move => I [P_eq _] Pprop0; apply: val_inj => /=.
suff ->: 'P^=(base; {eq P}) =
  \polyI_(I : {fsubset base} | P `<=` 'P^=(base; I)) 'P^= (base; I) :> {quot T}.
- apply/quot_equivP/andP; split.
  + by apply/big_polyIsP.
  + rewrite P_eq; apply/big_poly_inf; exact: poly_subset_refl.
- symmetry; apply/quot_equivP.
  rewrite /active; apply: polyEq_big_polyI.
  apply/pred0Pn; rewrite P_eq /=; exists I.
  exact: poly_subset_refl.
Qed.

Lemma activeP (P : {poly T, base}) (I : {fsubset base}) :
  (P `<=` 'P^=(base; I)) = (I `<=` {eq P})%fset.
Proof.
apply/idP/idP.
- by move => Psub; apply/bigfcup_sup.
- case: (emptyP P) => [ /poly_equivP/quot_equivP -> _|]; first exact: poly0_subset.
  move/repr_active => {2}-> /=.
  exact: polyEq_antimono.
Qed.

Lemma repr_active_supset (P : {poly T, base}) :
  P `<=` 'P^=(base; {eq P}).
case: (poly_baseP P) => [-> /= | _ [_ Pprop0 /=]]; first exact: poly0_subset.
rewrite {1}[P]repr_active //=; exact: poly_subset_refl.
Qed.

Lemma repr_active0 :
  {eq (`[poly0]%:poly_base : {poly T, base})} = base%:fsub.
Proof.
set A := {eq _}.
apply/val_inj/FSubset.untag_inj => /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; first by move: (valP A).
- rewrite -activeP => /=; exact: poly0_subset.
Qed.

Lemma active_polyEq (I : {fsubset base}) :
  (I `<=` {eq 'P^=(base; I)%:poly_base})%fset.
Proof.
rewrite -activeP; exact: poly_subset_refl.
Qed.

Lemma in_active (P : {poly T, base}) e :
  e \in base -> (e \in ({eq P} : {fset _})) = (P `<=` `[hp e]).
Proof.
rewrite -!fsub1set.
have ->: (P `<=` (`[ hp e ])) = (P `<=` 'P^=(base; [fset e]%fset)).
- rewrite (quot_equivP polyEq1).
  apply/idP/poly_subsetIP => [? | [_ ?]]; last done.
  by split; first exact: poly_base_subset.
move => e_in_base.
have ->: ([fset e] = [fset e]%:fsub)%fset by done.
by rewrite activeP.
Qed.

Lemma poly_base_subset_eq (P Q : {poly T, base}) :
    (P `<=` Q) -> (({eq Q} : {fset _}) `<=` {eq P})%fset.
Proof.
case: (poly_baseP P) => [-> | ? [_ P_prop0]].
- rewrite repr_active0 poly0_subset => _; exact: (valP {eq _}).
- case: (poly_baseP Q) => [-> | ? [_ Q_prop0]].
  + rewrite -subset0N_proper in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma polyI_eq (P Q : {poly T, base}) :
  ({eq P} `|` {eq Q} `<=` {eq ((P `&` Q)%PH)%:poly_base})%fset.
Proof.
rewrite -activeP -(quot_equivP polyEq_polyI).
by apply: polyISS; rewrite activeP.
Qed.

Lemma poly_base_proper (P Q : {poly T, base}) :
  ({eq Q} `<` {eq P})%fset -> P `<` Q.
Proof.
case: (poly_baseP Q) => [->| J [Q_eq Q_prop0]]; first by rewrite repr_active0 fsubsetT_proper.
case: (poly_baseP P) => [->| I [P_eq P_prop0]]; first done.
rewrite {2}[Q]repr_active // => /fproperP [/fsubsetP eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; first exact: polyEq_antimono.
apply/poly_subsetPn.
move: i_notin; rewrite in_active.
- move/poly_subsetPn => [x x_in_Q x_notin].
  exists x; first by rewrite [Q]repr_active in x_in_Q.
  move: x_notin; apply: contra => x_in; exact: (polyEq_eq x_in).
- move: i_in; apply/fsubsetP; exact: (valP {eq _}).
Qed.

End Active.

Notation "'{eq'  P }" := (active P) : poly_scope.

Section ActiveSlice.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n).

Lemma active_slice e base (P : {poly T, base}) :
  ((e +|` {eq P}) `<=` {eq (slice e P)%:poly_base})%fset.
Proof.
rewrite -activeP -(quot_equivP slice_polyEq).
case: (poly_baseP P) => [-> /= | ? [_ P_prop0] /=].
- rewrite {1}(quot_equivP (slice0 _)); exact: poly0_subset.
- move/repr_active: P_prop0 => {1}->.
  exact: poly_subset_refl.
Qed.

End ActiveSlice.

Section Face.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n) (base : base_t[R,n]).

Definition face_set (P : {poly T, base}) : {set {poly T, base}} :=
  [set Q : {poly T, base} | Q `<=` P].

Lemma face_set_self (P : {poly T, base}) : P \in (face_set P).
Proof.
rewrite inE; exact: poly_subset_refl.
Qed.

(* TO BE FIXED : why do we need extra parenthesis for `[poly0] *)
Lemma poly0_face_set :
  face_set (`[poly0]%:poly_base) = [set `[poly0]%:poly_base] :> {set {poly T, base}}.
Proof.
apply/setP => P; rewrite !inE /=.
rewrite subset0_equiv; apply/idP/eqP => [? | -> /=].
- by apply/val_inj/quot_equivP.
- exact: poly_equiv_refl.
Qed.

CoInductive face_spec (P : {poly T, base}) : {poly T, base} -> Prop :=
| EmptyFace : face_spec P (`[poly0])%:poly_base
| ArgMin c of (bounded P c) : face_spec P (argmin P c)%:poly_base.

Lemma faceP (P Q : {poly T, base}) :
  Q \in face_set P -> face_spec P Q.
Proof.
case: (emptyP ('P(base) : {quot T}))
  => [/poly_equivP/quot_equivP base_eq0 | base_prop0].
- suff ->: (P = (`[poly0]%:poly_base)).
  + rewrite inE subset0_equiv => /quot_equivP.
    move/val_inj ->; constructor.
    move: (poly_base_subset P); rewrite base_eq0 //=.
      by rewrite subset0_equiv => /quot_equivP/val_inj.
- case: (poly_baseP Q) => [-> | ]; first constructor.
  move => I [Q_eq Q_prop0].
  rewrite inE; move => Q_sub_P.
  pose w : {fsfun base_elt[R,n] -> R for fun => 0%R} :=
    [fsfun e : I => 1 | 0]%fset.
  have w_ge0 : pweight base w.
  admit.
  (*have e_ge0 : e >=m 0.
  + apply/gev0P => i; rewrite mxE; case: ifP => _ //=; first exact: ler01.*)
  have w_supp : forall e, (w e > 0) = (e \in (I : {fset _})).
  admit.
  (*have e_gt0 : forall i, (e i 0 > 0) = (i \in I).
  + move => i; rewrite mxE; case: (i \in I); [exact: ltr01 | exact: ltrr].*)
  pose c := (combine base w).1.
  have c_bounded : bounded ('P(base) : {quot T}) c.
  + exact: dual_sol_bounded.
  have c_bounded_P : (bounded P c).
  + apply: (bounded_mono1 c_bounded); apply/andP; split;
      [ exact: (poly_proper_subset Q_prop0) | exact: poly_base_subset ].
  have c_argmin: argmin 'P(base) c = Q.
  + apply/quot_equivP; rewrite Q_eq in Q_prop0 *.
    exact: dual_sol_argmin.
  suff <- : (argmin P c)%:poly_base = Q by constructor.
  apply: val_inj => /=. rewrite -c_argmin.
  apply/quot_equivP; apply/subset_argmin; first by done.
  apply/andP; split; [ by rewrite c_argmin | exact: poly_base_subset ].
Admitted.

Lemma face_set_of_face (P Q : {poly T, base}) :
  Q \in face_set P -> face_set Q = [set Q' in face_set P | (Q' `<=` Q)].
Proof.
rewrite inE => Q_sub_P; apply/setP => Q'; rewrite !inE.
apply/idP/andP => [Q'_sub_Q | [_?]]; last by done.
by split; try exact: (poly_subset_trans Q'_sub_Q).
Qed.

Corollary face_set_subset (P Q  : {poly T, base}) :
  Q \in face_set P -> (face_set Q \subset face_set P).
Proof.
move/face_set_of_face ->; apply/subsetP => Q'.
by rewrite inE => /andP [?].
Qed.

Lemma polyI_face_set (P Q Q' : {poly T, base}) :
  Q \in face_set P -> Q' \in face_set P -> (Q `&` Q')%:poly_base \in face_set P.
Proof.
rewrite !inE => Q_sub_P Q'_sub_P.
by move: (polyISS Q_sub_P Q'_sub_P); rewrite (quot_equivP polyIxx).
Qed.
End Face.

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
