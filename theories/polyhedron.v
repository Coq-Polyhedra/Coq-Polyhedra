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

Variable (R : realFieldType) (n : nat) (T : polyPredType R n) (base : base_t[R,n]).

Definition has_base (P : {quot T}) :=
  (P `>` `[poly0]) ==>
    [exists base' : {fset base}, P == 'P^=(base; [fsetval x in base'])%fset].

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

Lemma has_baseP {P} : reflect (P `>` (`[poly0]) -> exists2 p, P = 'P^=(p) & p.1 = base) (has_base P).
Proof.
Admitted.
(*    by apply/(iffP implyP) => [H P_prop0 | H P_prop0]; move/(_ P_prop0): H => ?; apply/exists_eqP.
Qed.*)

Lemma polyEq_baseP I :
  has_base 'P^=(base; I).
Proof.
by apply/has_baseP; exists I.
Qed.
Canonical polyEq_base I := PolyBase (polyEq_baseP I).

Definition poly_base_of (x : poly_base) & (phantom 'poly[R]_n x) : poly_base := x.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

Definition set_of_poly_base (P : poly_base) : option {set 'I_m} :=
  if emptyP P is NonEmpty H then
    let I := xchoose (existsP (implyP (poly_base_base P) H)) in
    Some I
  else
    None.

Definition set_of_poly_base_pinv (I : {set 'I_m})  : option poly_base :=
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
Canonical poly_base_countType := Eval hnf in CountType poly_base poly_base_countMixin.
Definition poly_base_finMixin := PcanFinMixin set_of_poly_baseK.
Canonical poly_base_finType := Eval hnf in FinType poly_base poly_base_finMixin.
Canonical poly_base_subFinType := [subFinType of poly_base].

Lemma poly_of_baseP :
  has_base 'P(base).
Proof.
by apply/has_baseP; exists set0; rewrite (quot_equivP polyEq0).
Qed.
Canonical poly_of_base_base := PolyBase (poly_of_baseP).

End PolyBase.

Notation "'{poly'  base '}'" := (poly_base base) : poly_scope.
Notation "'[' P 'has' '\base' base ']'" := (has_base base P) : poly_scope.
Notation "P %:poly_base" := (poly_base_of (Phantom _ P)) (at level 0) : poly_scope.

(*Section Test.

Variable (R : realFieldType) (n m : nat) (base : m.-base[R,n]).

Variables (P Q : {poly base}) (Q' : 'poly[R]_n) (x : 'cV[R]_n).

Set Printing Coercions.

Check (P `&` Q).
Check (x \in P).
Check (P : 'poly[R]_n).

Goal P `<=` Q' -> forall x, x \in P -> x \in Q'.
move/poly_subsetP => H z z_in_P.
by move/H: z_in_P.
Qed.

Goal (P = Q' :> 'poly[R]_n) -> x \in P -> x \in Q'.
move <-.
done.
Qed.

Unset Printing Coercions.

End Test.*)

Section PolyhedronSpec.

Variable (R : realFieldType) (n : nat).

Variant poly_spec : 'poly[R]_n -> {m & m.-base[R,n]} -> Type :=
  PolySpec (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
    poly_spec 'P(A,b) (Tagged _ (A, b)).

Lemma polyP (P : 'poly[R]_n) :
  poly_spec P (HPolyhedron.matrix_from_hpoly (\repr P)).
Proof.
case: {2}(\repr P) (erefl (\repr P)) => [m [A b]] /= repr_eq.
suff {1}->: P = 'P(A,b) by rewrite repr_eq /=.
apply/quot_equivP/poly_equivP => x.
by rewrite inE repr_eq inE in_poly_of_base.
Qed.

Variant take_base_spec : 'poly[R]_n -> {m & m.-base[R,n]} -> Type :=
  TakeBaseSpec (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (P : {poly (A,b)}) :
    take_base_spec P (Tagged _ (A, b)).

Lemma take_baseP (P : 'poly[R]_n) :
  take_base_spec P (HPolyhedron.matrix_from_hpoly (\repr P)).
Proof.
by case: (polyP P).
Qed.

CoInductive change_base_spec (P : 'poly[R]_n) : {m' & m'.-base[R,n]} -> Type :=
  ChangeBaseSpec (m' : nat) (A : 'M[R]_(m',n)) (b : 'cV[R]_m') (P' : {poly (A,b)}) of (P = P' :> 'poly[R]_n) :
    change_base_spec P (Tagged _ (A, b)).

Lemma change_baseP (P : 'poly[R]_n) :
  change_base_spec P (HPolyhedron.matrix_from_hpoly (\repr P)).
Proof.
Admitted.
(*by case: (polyP P).
Qed.*)

End PolyhedronSpec.

Section HasBase.

Variable (R : realFieldType) (n : nat) (m : nat).

Implicit Types (base : m.-base[R,n]) (P : 'poly[R]_n).

CoInductive poly_base_spec base : {poly base} -> Type :=
| PolyBase0 : poly_base_spec (`[poly0])%:poly_base
| PolyBaseN0 I of ('P^=(base; I)%:poly_base `>` `[poly0]) : poly_base_spec 'P^=(base; I)%:poly_base.

Lemma poly_baseP base (P : {poly base}) :
  poly_base_spec P.
Proof.
Admitted.

CoInductive poly_base_empty_spec base (P : {poly base}) : bool -> bool -> Type :=
| ReprActive0 of (P = `[poly0]%:poly_base) : poly_base_empty_spec P true false
| ReprActiveN0 of (P `>` (`[poly0])) : poly_base_empty_spec P false true.

Lemma poly_base_emptyP base (P : {poly base}) :
  poly_base_empty_spec P (P == `[poly0]%:poly_base) (P `>` (`[poly0])).
Proof.
Admitted.

Lemma poly_base_subset base (P : {poly base}) :
  P `<=` 'P(base).
Proof.
case/poly_baseP: P => [|I _]; [exact: poly0_subset | exact: polyEq_antimono0].
Qed.

(* BUG here: self_baseP cannot be made canonical because the structures of the terms
 * '[base] and '[P^=(base; I)] are the same, so making self_baseP canonical would be ignored *)
(*Lemma self_baseP base :
  ['[base] has \base base].
Proof.
apply/has_baseP; exists set0; symmetry; apply/quotP; exact: hpolyEq0.
Qed.*)

Lemma polyI_baseP base (P Q : {poly base}) : [P `&` Q has \base base].
Proof.
case/poly_baseP: P => [|I _]; case/poly_baseP: Q => [|J _];
  try by rewrite ?(quot_equivP polyI0) ?(quot_equivP poly0I) poly0_baseP.
by rewrite (quot_equivP polyEq_polyI) polyEq_baseP.
Qed.
Canonical polyI_base base (P Q : {poly base}) := PolyBase (polyI_baseP P Q).

End HasBase.

Section Active.

Variable (R : realFieldType) (n : nat).

Definition active m (base : m.-base[R,n]) (P : {poly base}) :=
  \bigcup_(I | P `<=` 'P^=(base; I)) I.

Notation "'{eq'  P }" := (active P) : poly_scope.

(*Lemma repr_active_supset base (P : {poly base}) :
  P `<=` '['P^=(base; {eq P})].
case/poly_baseP: (P) => [I] ?; rewrite -polyEq_big_polyI;
  last by apply/pred0Pn; exists I; exact: poly_subset_refl.
by apply/big_polyIsP.
Qed.

Lemma repr_active_prop0 base (P : {poly base}) :
  infer ('['P^=(base; {eq P})] `>` `[poly0]).
Proof.
apply: inferP; move: (repr_active_supset P); apply: poly_proper_subset.
exact: poly_base_proper0.
Qed.*)

Lemma repr_active m (base : m.-base) (P : {poly base}) :
  P `>` (`[poly0]) -> P = 'P^=(base; {eq P})%:poly_base.
Proof.
case/poly_baseP: (P); first by rewrite poly_properxx.
move => I _ _; apply: val_inj => /=.
rewrite -(quot_equivP (polyEq_big_polyI _));
  last by apply/pred0Pn; exists I; exact: poly_subset_refl.
apply/quot_equivP/andP; split.
- by apply/big_polyIsP.
- by apply/big_poly_inf; exact: poly_subset_refl.
Qed.

Lemma activeP m (base : m.-base) (P : {poly base}) I :
  (P `<=` 'P^=(base; I)) = (I \subset {eq P}).
Proof.
apply/idP/idP; first exact: bigcup_sup.
case: (poly_base_emptyP P) => [-> | /repr_active {2}-> /=]; first by rewrite /= poly0_subset.
by move/polyEq_antimono.
Qed.

Lemma repr_active0 m (base : m.-base) :
  {eq (`[poly0]%:poly_base : {poly base})} = setT.
Admitted.

Lemma active_polyEq m (base : m.-base) (I : {set 'I_m}) :
  I \subset {eq 'P^=(base; I)%:poly_base}.
Proof.
rewrite -activeP; exact: poly_subset_refl.
Qed.

Lemma in_active m (base : m.-base) (P : {poly base}) i :
  (i \in {eq P}) = (P `<=` nth_hp base i).
Proof.
suff ->: (P `<=` nth_hp base i) =  (P `<=` 'P^=(base; [set i])).
- by rewrite activeP sub1set.
- rewrite (quot_equivP polyEq1).
Admitted.

Lemma poly_base_subset_eq m (base : m.-base) (P Q : {poly base}) :
    (P `<=` Q) -> ({eq Q} \subset {eq P}).
Proof.
case: (poly_base_emptyP P) => [-> | P_prop0].
- by rewrite repr_active0 poly0_subset subsetT.
- case: (poly_base_emptyP Q) => [-> | Q_prop0].
  + rewrite -subset0N_proper in P_prop0.
    by move/negbTE : P_prop0 ->.
  move/repr_active: Q_prop0 => {1}->.
  by rewrite activeP.
Qed.

Lemma polyI_eq m (base : m.-base) (P Q : {poly base}) :
  {eq P} :|: {eq Q} \subset {eq (P `&` Q)%:poly_base}.
Proof.
rewrite -activeP -(quot_equivP polyEq_polyI).
by apply: polyISS; rewrite activeP.
Qed.

Lemma slice_poly_baseP (c: 'cV[R]_n) (d : R) m (base : m.-base) (P : {poly base})  :
  [ (slice c d P) has \base (slice_base c d base) ].
Proof.
case/poly_baseP: P => [ | I _]; first by rewrite (quot_equivP slice0); exact: poly0_baseP.
apply/has_baseP => _.
by exists (slice_set I); rewrite -(quot_equivP slice_polyEq).
Qed.
Canonical slice_poly_base (c: 'cV[R]_n) (d : R) m (base : m.-base) (P : {poly base})
          := PolyBase (slice_poly_baseP c d P).

Lemma active_slice (c: 'cV[R]_n) (d : R) m (base : m.-base) (P : {poly base}) :
      (slice_set {eq P}) \subset {eq (slice c d P)%:poly_base}.
Proof.
rewrite -activeP -(quot_equivP slice_polyEq).
case: (poly_base_emptyP P) => [-> /= | /= ].
- rewrite {1}(quot_equivP slice0); exact: poly0_subset.
- move/repr_active => {1}->.
  exact: poly_subset_refl.
Qed.

Lemma poly_base_proper m (base : m.-base) (P Q : {poly base}) :
  {eq Q} \proper {eq P} -> P `<` Q.
Proof.
case: (poly_base_emptyP Q) => [->| Q_prop0]; first by rewrite repr_active0 setT_proper.
case: (poly_base_emptyP P) => [->| P_prop0]; first done.
rewrite {2}[Q]repr_active // => /properP [eq_sub] [i i_in i_notin].
rewrite [P]repr_active //.
apply/andP; split; first exact: polyEq_antimono.
apply/poly_subsetPn.
Admitted.

End Active.

Notation "'{eq'  P }" := (active P) : poly_scope.

Section Face.

Variable (R : realFieldType) (n : nat).

Lemma argmin_baseP (m : nat) (base : m.-base[R,n]) (P : {poly base}) c :
  [(argmin P c) has \base base].
Proof.
(* we first suppose that flat_prop holds, ie this is the situation in which
 * P (here quantified as Q) would play the role of the base *)
suff flat_prop: forall p (Q : p.-base), bounded ('P(Q) : 'poly[R]_n) c -> [(argmin ('P(Q) : 'poly[R]_n) c) has \base Q].
- apply/has_baseP; rewrite -bounded_argminN0.
  case/poly_baseP : P => [| I _]; first by rewrite bounded_poly0.
  rewrite /= (quot_equivP polyEq_flatten) => bounded_PI.
  move/flat_prop/has_baseP: (bounded_PI). rewrite -bounded_argminN0.
  move => /(_ bounded_PI) => [[J] ->].
  by move: (polyEq_of_polyEq (T := [polyPredType of 'poly[R]_n]) base J)
    => [K] /quot_equivP ->; exists K. (* TODO: ugly to specify the polyPredType *)
- (* now this is the classic proof of Schrijver *)
  move => m' [A b] c_bounded.
  move: (dual_opt_sol c_bounded) => [u] [u_ge0 c_eq b_u_eq_opt_val].
  rewrite {}c_eq in c_bounded b_u_eq_opt_val *. (* dual_opt_sol is badly specified
                                                 * we should use an inductive spec instead *)
  pose I := [set i | u i 0 > 0].
  have supp_u : forall i, (u i 0 > 0) = (i \in I) by move => i; rewrite inE.
  apply/has_baseP; exists I; apply/quot_equivP; apply/dual_sol_argmin => //.
  move: (opt_point c_bounded) => [x] x_in_PAb; rewrite -b_u_eq_opt_val.
  move/(compl_slack_cond u_ge0 supp_u x_in_PAb) => x_in_PAbI.
  by apply/proper0P; exists x.
Qed.
Canonical argmin_base (m : nat) (base : m.-base) (P : {poly base}) c := PolyBase (argmin_baseP P c).

(*Section Test.

Variable (base : 'hpoly[R]_n) (P Q : {poly base}) (c : 'cV[R]_n).

Set Printing All.
Lemma foo & (infer (bounded P c)) : (argmin P c)%:poly_base = Q.
Abort.
End Test.*)

Definition face_set m (base : m.-base[R,n]) (P : {poly base}) : {set {poly base}} :=
  [set Q : {poly base} | Q `<=` P].

Lemma face_set_self m (base : m.-base) (P : {poly base}) : P \in (face_set P).
Proof.
rewrite inE; exact: poly_subset_refl.
Qed.

(* TO BE FIXED : why do we need extra parenthesis for `[poly0] *)
Lemma poly0_face_set m (base : m.-base) :
  face_set (`[poly0]%:poly_base) = [set `[poly0]%:poly_base] :> {set {poly base}}.
Proof.
apply/setP => P; rewrite !inE /=.
rewrite subset0_equiv; apply/idP/eqP => [? | -> /=].
- by apply/val_inj/quot_equivP.
- exact: poly_equiv_refl.
Qed.

CoInductive face_spec m (base : m.-base) (P : {poly base}) : {poly base} -> Type :=
| EmptyFace : face_spec P (`[poly0])%:poly_base
| ArgMin c of (bounded P c) : face_spec P (argmin P c)%:poly_base.

Lemma faceP m (base : m.-base) (P Q : {poly base}) :
  Q \in face_set P -> face_spec P Q.
Proof.
case: (emptyP ('P(base) : 'poly[R]_n))
  => [/poly_equivP/quot_equivP base_eq0 | base_prop0].
- suff ->: (P = (`[poly0]%:poly_base)).
  + rewrite inE subset0_equiv => /quot_equivP.
    move/val_inj ->; constructor.
    move: (poly_base_subset P); rewrite base_eq0 //=.
    by rewrite subset0_equiv => /quot_equivP/val_inj.
- move: base_prop0 P Q; case: base => A b base_prop0 P Q.
  case/poly_baseP: Q; first constructor.
  move => I; set Q := ('P^= (A, b; I)) %:poly_base.
  rewrite inE; move => Q_prop0 Q_sub_P.
  pose e : 'cV[R]_m := \col_i (if i \in I then 1 else 0).
  have e_ge0 : e >=m 0.
  + apply/gev0P => i; rewrite mxE; case: ifP => _ //=; first exact: ler01.
    have e_gt0 : forall i, (e i 0 > 0) = (i \in I).
  + move => i; rewrite mxE; case: (i \in I); [exact: ltr01 | exact: ltrr].
  pose c := A^T *m e.
  have c_bounded : bounded ('P(A,b) : 'poly[R]_n) c.
  + exact: dual_sol_bounded.
  have c_bounded_P : (bounded P c).
  + apply: (bounded_mono1 c_bounded); apply/andP; split;
      [ exact: (poly_proper_subset Q_prop0) | exact: poly_base_subset ].
  have c_argmin: argmin 'P(A,b) c = Q.
  + apply/quot_equivP.
    by apply: dual_sol_argmin; rewrite {Q_sub_P}.
  suff <- : (argmin P c)%:poly_base = Q by constructor.
  apply: val_inj; rewrite 2!SubK -c_argmin.
  apply/quot_equivP; apply/subset_argmin; first by done.
  apply/andP; split; [ by rewrite c_argmin | exact: poly_base_subset ].
Qed.

Lemma face_set_of_face m (base : m.-base) (P Q : {poly base}) :
  Q \in face_set P -> face_set Q = [set Q' in face_set P | (Q' `<=` Q)].
Proof.
rewrite inE => Q_sub_P; apply/setP => Q'; rewrite !inE.
apply/idP/andP => [Q'_sub_Q | [_?]]; last by done.
by split; try exact: (poly_subset_trans Q'_sub_Q).
Qed.

Corollary face_set_subset m (base : m.-base) (P Q  : {poly base}) :
  Q \in face_set P -> (face_set Q \subset face_set P).
Proof.
move/face_set_of_face ->; apply/subsetP => Q'.
by rewrite inE => /andP [?].
Qed.

Lemma polyI_face_set m (base : m.-base) (P Q Q' : {poly base}) :
  Q \in face_set P -> Q' \in face_set P -> (Q `&` Q')%:poly_base \in face_set P.
Proof.
rewrite !inE => Q_sub_P Q'_sub_P.
by move: (polyISS Q_sub_P Q'_sub_P); rewrite (quot_equivP polyIxx).
Qed.
End Face.

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
