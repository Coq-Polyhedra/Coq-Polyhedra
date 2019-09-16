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
Require Import extra_misc extra_matrix inner_product row_submx vector_order barycenter hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module H := HPolyhedron.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "\polyI_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \polyI_ i '/  '  F ']'").
Reserved Notation "\polyI_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \polyI_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \polyI_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\polyI_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \polyI_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \polyI_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \polyI_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\polyI_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\polyI_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \polyI_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \polyI_ ( i  <  n )  F ']'").
Reserved Notation "\polyI_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \polyI_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \polyI_ ( i  'in'  A ) '/  '  F ']'").

Local Open Scope poly_scope.

Section Def.

Context {R : realFieldType} {n : nat}.

Definition canon (P : 'hpoly[R]_n) :=
  choose (H.poly_equiv P) P.

Structure poly := Poly {
  repr : 'hpoly[R]_n;
  _ : canon repr == repr;
}.

Definition mem_pred_sort P  := (repr P) : {pred 'cV[R]_n}.
Coercion mem_pred_sort : poly >-> pred_sort.

End Def.

Notation "''poly[' R ]_ n" := (@poly R n) (at level 8).
Notation "''poly_' n" := ('poly[_]_n) (at level 8).
Notation "\repr" := (@repr _ _) (at level 0).

Section BasicProperties.

Variables (R : realFieldType) (n : nat).

Canonical poly_subType := [subType for (@repr R n)].
Definition poly_eqMixin := Eval hnf in [eqMixin of 'poly[R]_n by <:].
Canonical poly_eqType := Eval hnf in EqType 'poly[R]_n poly_eqMixin.
Definition poly_choiceMixin := Eval hnf in [choiceMixin of 'poly[R]_n by <:].
Canonical poly_choiceType := Eval hnf in ChoiceType 'poly[R]_n poly_choiceMixin.

Lemma repr_inj : injective (\repr : 'poly[R]_n -> 'hpoly[R]_n).
Proof.
exact: val_inj.
Qed.

Lemma canon_id (P : 'hpoly[R]_n) :
  canon (canon P) == canon P.
Proof.
rewrite /canon; set Q := choose (H.poly_equiv P) P.
have P_eq_Q: (H.poly_equiv P Q) by apply : chooseP; exact: H.poly_equiv_refl.
suff /eq_choose ->: H.poly_equiv Q =1 H.poly_equiv P
  by apply/eqP; apply: choose_id; try exact: H.poly_equiv_refl.
move => x.
by apply/idP/idP; apply: H.poly_equiv_trans; last by rewrite H.poly_equiv_sym.
Qed.

Definition class_of P := Poly (canon_id P).
Notation "''[' P  ]" := (class_of P) (at level 0).

Lemma reprK (P : 'poly[R]_n) :
  '[\repr P] = P.
Proof.
case: P => [P P_eq]; apply: repr_inj; exact: eqP.
Qed.

Lemma repr_equiv (P : 'hpoly[R]_n) : \repr '[P] =i P.
Proof.
by move: (chooseP (H.poly_equiv_refl P)); rewrite H.poly_equiv_sym => /H.poly_equivP.
Qed.

Lemma poly_eqP {P Q : 'poly[R]_n} : P =i Q <-> P = Q.
Proof.
split; last by move ->.
set P' := repr P; set Q' := repr Q; move => P_equiv_Q.
have P'_equiv_Q' : H.poly_equiv P' Q' by apply/H.poly_equivP.
have chooseP'_eq_chooseQ' : H.poly_equiv P' =1 H.poly_equiv Q'.
  by move => z; apply/idP/idP; apply/H.poly_equiv_trans;
  try by rewrite H.poly_equiv_sym in P'_equiv_Q'.
apply: repr_inj.
move: (valP P) => /eqP <-.
move: (valP Q) => /eqP <-.
rewrite /= /canon -(eq_choose chooseP'_eq_chooseQ').
by apply: choose_id; try exact: H.poly_equiv_refl.
Qed.

End BasicProperties.

Notation "''[' P  ]" := (class_of P) (at level 0).

Section PolyPred.

Context {R : realFieldType} {n : nat}.

Definition poly0 : 'poly[R]_n := '[ H.poly0 ].
Definition polyT : 'poly[R]_n := '[ H.polyT ].
Definition polyI (P Q : 'poly[R]_n) : 'poly[R]_n := '[ H.polyI (\repr P) (\repr Q) ].
Definition poly_subset (P Q : 'poly[R]_n) := H.poly_subset (\repr P) (\repr Q).
Definition mk_hs b : 'poly[R]_n := '[ H.mk_hs b ].
Definition bounded (P : 'poly[R]_n) c := H.bounded (\repr P) c.
Definition pointed (P : 'poly[R]_n) := H.pointed (\repr P).
Definition proj (P : 'poly[R]_n) i : 'poly[R]_(n.-1) := '[ H.proj (\repr P) i].
Definition conv V : 'poly[R]_n := '[ (H.conv V) ].

Definition poly_equiv P Q := (poly_subset P Q) && (poly_subset Q P).
Definition poly_proper P Q := ((poly_subset P Q) && (~~ (poly_subset Q P))).

Notation "'`[' 'poly0' ']'" := poly0 (at level 70) : poly_scope.
Notation "'`[' 'polyT' ']'" := polyT (at level 70) : poly_scope.
Notation "P `&` Q" := (polyI P Q) (at level 48, left associativity) : poly_scope.
Notation "P `<=` Q" := (poly_subset P Q) (at level 70, no associativity, Q at next level) : poly_scope.
Notation "P `>=` Q" := (Q `<=` P) (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `=~` Q" := (poly_equiv P Q) (at level 70, no associativity) : poly_scope.
Notation "P `!=~` Q" := (~~ (poly_equiv P Q)) (at level 70, no associativity) : poly_scope.
Notation "P `<` Q" := (poly_proper P Q) (at level 70, no associativity, Q at next level) : poly_scope.
Notation "P `>` Q" := (Q `<` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `<=` Q `<=` S" := ((poly_subset P Q) && (poly_subset Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "P `<` Q `<=` S" := ((poly_proper P Q) && (poly_subset Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "P `<=` Q `<` S" := ((poly_subset P Q) && (poly_proper Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "'`[' 'hs'  b  ']'" := (mk_hs b%PH) (at level 70) : poly_scope.

Notation "\polyI_ ( i <- r | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i <- r | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i <- r ) F" :=
  (\big[polyI/`[polyT]%PH]_(i <- r) F%PH) : poly_scope.
Notation "\polyI_ ( i | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i | P%B) F%PH) : poly_scope.
Notation "\polyI_ i F" :=
  (\big[polyI/`[polyT]%PH]_i F%PH) : poly_scope.
Notation "\polyI_ ( i : I | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i : I | P%B) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( i : I ) F" :=
  (\big[polyI/`[polyT]%PH]_(i : I) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( m <= i < n | P ) F" :=
 (\big[polyI/`[polyT]%PH]_(m <= i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( m <= i < n ) F" :=
 (\big[polyI/`[polyT]%PH]_(m <= i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i < n | P ) F" :=
 (\big[polyI/`[polyT]%PH]_(i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i < n ) F" :=
 (\big[polyI/`[polyT]%PH]_(i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A | P ) F" :=
 (\big[polyI/`[polyT]%PH]_(i in A | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A ) F" :=
 (\big[polyI/`[polyT]%PH]_(i in A) F%PH) : poly_scope.

Lemma in_poly0 : `[poly0] =i pred0.
Proof.
by move => ?; rewrite repr_equiv H.in_poly0.
Qed.

Lemma in_polyT : `[polyT] =i predT.
Proof.
by move => ?; rewrite repr_equiv H.in_polyT.
Qed.

Lemma poly_subsetP {P Q : 'poly[R]_n} : reflect {subset P <= Q} (P `<=` Q).
Proof.
apply: (iffP H.poly_subsetP) => [H x | H x]; exact: H.
Qed.

Lemma poly_subset_mono (P Q : 'hpoly[R]_n) : ('[P] `<=` '[Q]) = (H.poly_subset P Q).
Proof.
apply/poly_subsetP/H.poly_subsetP => [H | H] x x_in_P.
- have /H: x \in '[P] by rewrite repr_equiv.
  by rewrite repr_equiv.
- rewrite !repr_equiv in x_in_P *; exact: H.
Qed.

Lemma poly_subset_refl : reflexive poly_subset.
Proof.
by move => P; apply/poly_subsetP.
Qed.

Lemma poly_subset_trans : transitive poly_subset.
Proof.
move => P' P P'' /poly_subsetP P_eq_P' /poly_subsetP P'_eq_P''.
by apply/poly_subsetP => x; move/P_eq_P'/P'_eq_P''.
Qed.

Lemma poly_subsetPn {P Q : 'poly[R]_n} :
  reflect (exists2 x, (x \in P) & (x \notin Q)) (~~ (P `<=` Q)).
Proof.
by apply: (iffP H.poly_subsetPn) => [[x] H | [x] H]; exists x.
Qed.

Lemma poly_equivP {P Q} : P `=~` Q -> P = Q.
Proof.
move/andP => [/poly_subsetP P_le_Q /poly_subsetP Q_le_P].
apply/poly_eqP => x.
by apply/idP/idP; [exact: P_le_Q | exact: Q_le_P].
Qed.

Lemma in_polyI P Q x : (x \in (P `&` Q)) = ((x \in P) && (x \in Q)).
Proof.
by rewrite !repr_equiv H.in_polyI.
Qed.

Lemma polyI_mono (P Q : 'hpoly[R]_n) : '[P] `&` '[Q] = '[H.polyI P Q].
Proof.
apply/poly_eqP => x.
by rewrite in_polyI !repr_equiv H.in_polyI.
Qed.

Lemma big_polyI_mono (I : finType) (P : pred I) (F : I -> 'hpoly[R]_n) :
  \polyI_(i | P i) '[F i] = '[\big[H.polyI/H.polyT]_(i | P i) (F i)].
Proof.
have class_of_morph : {morph (@class_of R n) : x y / H.polyI x y >-> polyI x y}.
- by move => Q Q'; rewrite polyI_mono.
have polyT_mono : '[H.polyT] = polyT by done.
by rewrite (@big_morph _ _ _ _ _ _ _ class_of_morph polyT_mono).
Qed.

Lemma in_hs : (forall b x, x \in (`[hs b]) = ('[b.1,x] >= b.2))
              * (forall c α x, x \in (`[hs (c, α)]) = ('[c,x] >= α)).
Proof.
set t := (forall b, _).
suff Ht: t by split; [ | move => c α x; rewrite Ht ].
by move => b x; rewrite repr_equiv H.in_hs.
Qed.

Lemma notin_hs :
  (forall b x, (x \notin `[hs b]) = ('[b.1,x] < b.2))
  * (forall c α x, (x \notin `[hs (c, α)]) = ('[c,x] < α)).
Proof.
set t := (forall b, _).
suff Ht: t by split; [ | move => c α x; rewrite Ht ].
by move => b x; rewrite in_hs ltrNge.
Qed.

Definition mk_hp e := `[hs e] `&` `[hs (-e)].
Notation "'`[' 'hp' e  ']'" := (mk_hp e%PH) (at level 70) : poly_scope.

Lemma in_hp :
  (forall b x, (x \in `[hp b]) = ('[b.1,x] == b.2))
  * (forall c α x, (x \in `[hp (c, α)]) = ('[c,x] == α)).
Proof.
set t := (forall b, _).
suff Ht: t by split; [ | move => c α x; rewrite Ht ].
move => b x; rewrite in_polyI.
rewrite [X in X && _]in_hs [X in _ && X]in_hs. (* TODO: remove the [X in ...] makes Coq loop *)
by rewrite vdotNl ler_oppl opprK eq_sym eqr_le.
Qed.

Lemma notin_hp b x :
  (x \in `[hs b]) -> (x \notin `[hp b]) = ('[b.1, x] > b.2).
Proof.
rewrite ltr_def in_hs => ->.
by rewrite in_hp andbT.
Qed.

Let inE := (in_poly0, in_polyT, in_hp, in_polyI, in_hs, inE).

Lemma polyI0 P : (P `&` `[poly0]) = `[poly0].
Proof.
by apply/poly_eqP => x; rewrite !inE andbF.
Qed.

Lemma poly0I P : (`[poly0] `&` P) = `[poly0].
Proof.
by apply/poly_eqP => x; rewrite !inE /=.
Qed.

Lemma poly_subsetIl P Q : P `&` Q `<=` P.
Proof. (* RK *)
apply/poly_subsetP => x.
by rewrite in_polyI; move/andP => [].
Qed.

Lemma poly_subsetIr P Q : P `&` Q `<=` Q.
Proof. (* RK *)
apply/poly_subsetP => x.
by rewrite in_polyI; move/andP => [_] .
Qed.

Lemma polyIS P P' Q : P `<=` P' -> Q `&` P `<=` Q `&` P'.
Proof. (* RK *)
move => sPP'; apply/poly_subsetP => x; rewrite !in_polyI.
case: (x \in Q) => //; exact: poly_subsetP.
Qed.

Lemma polySI P P' Q : P `<=` P' -> P `&` Q `<=` P' `&` Q.
Proof. (* RK *)
move => sPP'; apply/poly_subsetP => x; rewrite !in_polyI.
case: (x \in Q) => //; rewrite ?andbT ?andbF //; exact: poly_subsetP.
Qed.

Lemma polyISS P P' Q Q' : P `<=` P' -> Q `<=` Q' -> P `&` Q `<=` P' `&` Q'.
Proof. (* RK *)
move => /poly_subsetP sPP' /poly_subsetP sQQ'; apply/poly_subsetP => ?.
by rewrite !in_polyI; move/andP => [? ?]; apply/andP; split; [apply/sPP' | apply/sQQ'].
Qed.

Lemma poly_subsetIP P Q Q' : reflect (P `<=` Q /\ P `<=` Q') (P `<=` Q `&` Q').
Proof.
apply: (iffP idP) => [/poly_subsetP subset_P_QIQ' | [/poly_subsetP subset_P_Q /poly_subsetP subset_P_Q']].
- by split; apply/poly_subsetP => x x_in_P; move: (subset_P_QIQ' _ x_in_P); rewrite in_polyI; case/andP.
- by apply/poly_subsetP => x x_in_P; rewrite in_polyI; apply/andP; split; [exact: (subset_P_Q _ x_in_P) | exact: (subset_P_Q' _ x_in_P)].
Qed.

Lemma in_big_polyIP (I : finType) (P : pred I) (F : I -> 'poly[R]_n) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \polyI_(i | P i) (F i)).
Proof.
have -> : (x \in \polyI_(i | P i) F i) = (\big[andb/true]_(i | P i) (x \in (F i))).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?in_polyT ?in_polyI.
rewrite big_all_cond; apply: (iffP allP) => /= H i;
have := H i _; rewrite mem_index_enum; last by move/implyP->.
by move=> /(_ isT) /implyP.
Qed.

Lemma in_big_polyI (I : finType) (P : pred I) (F : I -> 'poly[R]_n) x :
  (x \in \polyI_(i | P i) (F i)) = [forall i, P i ==> (x \in F i)].
Proof.
by apply/in_big_polyIP/forall_inP.
Qed.

Lemma big_poly_inf (I : finType) (j : I) (P : pred I) (F : I -> 'poly[R]_n) :
  P j -> (\polyI_(i | P i) F i) `<=` F j.
Proof. (* RK *)
move => ?.
apply/poly_subsetP => ? /in_big_polyIP in_polyI_cond.
by apply: (in_polyI_cond j).
Qed.

Lemma big_polyI_min (I : finType) (j : I) Q (P : pred I) (F : I -> 'poly[R]_n) :
  P j -> (F j `<=` Q) -> \polyI_(i | P i) F i `<=` Q.
Proof. (* RK *)
by move => ? ?; apply/(@poly_subset_trans (F j) _ _); [apply: big_poly_inf | done].
Qed.

Lemma big_polyIsP (I : finType) Q (P : pred I) (F : I -> 'poly[R]_n) :
  reflect (forall i : I, P i -> Q `<=` F i) (Q `<=` \polyI_(i | P i) F i).
Proof. (* RK *)
apply: (iffP idP) => [Q_subset_polyI ? ? | forall_Q_subset].
- by apply/(poly_subset_trans Q_subset_polyI _)/big_poly_inf.
- apply/poly_subsetP => x x_in_Q.
  apply/in_big_polyIP => j P_j.
  by move: x x_in_Q; apply/poly_subsetP; exact: forall_Q_subset.
Qed.

Lemma projP (P : 'poly[R]_n) i x :
  reflect (exists2 y, x = row' i y & y \in P) (x \in proj P i).
Proof.
rewrite repr_equiv; apply: (iffP idP) => [ /H.projP [y -> y_in_P] | [y -> y_in_P]].
- by exists y.
- by apply/H.projP; exists y.
Qed.

Section ConvexHull.

Lemma convP (V : {fset 'cV[R]_n}) x :
  reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V).
Proof.
rewrite repr_equiv; exact: H.convP.
Qed.

Lemma convexP (P : 'poly[R]_n) (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> poly_subset (conv V) P.
Proof.
move => V_sub_P; apply/poly_subsetP => x.
rewrite repr_equiv; move: x; apply/(H.poly_subsetP _)/H.convexP.
exact: V_sub_P.
Qed.

Lemma convexP2 (P : 'poly[R]_n) (v w : 'cV[R]_n) α :
  v \in P -> w \in P -> 0 <= α <= 1 -> (1-α) *: v + α *: w \in P.
Admitted.

End ConvexHull.

Lemma polyIxx P : P `&` P = P.
Proof.
by apply/poly_eqP => x; rewrite inE andbb.
Qed.

Lemma poly_subset_hsP {P : 'poly[R]_n} {b} :
  reflect (forall x, x \in P -> '[fst b, x] >= snd b) (P `<=` `[hs b]).
Proof.
apply: (iffP poly_subsetP) => [sub x x_in_P | sub x x_in_P ];
  move/(_ _ x_in_P): sub; by rewrite in_hs.
Qed.

Lemma hs_antimono c d d' :
  d <= d' -> `[hs (c, d')] `<=` `[hs (c, d)]. (* RK *)
Proof.
move => d_le_d'.
apply/poly_subset_hsP => x.
rewrite inE => ?.
by apply: (ler_trans d_le_d' _).
Qed.

Lemma hp_extremeL b x y α :
  (x \in `[hs b]) -> (y \in `[hs b]) ->
  0 <= α < 1 -> ((1-α) *: x + α *: y \in `[hp b]) -> (x \in `[hp b]).
Proof.
rewrite !inE.
move => x_in y_in /andP [α_ge0 α_lt1].
case: (α =P 0) => [->| /eqP α_neq0].
- by rewrite subr0 scale0r scale1r addr0.
- have α_gt0 : α > 0
    by rewrite lt0r; apply/andP; split.
  rewrite {α_ge0} vdotDr 2!vdotZr.
  apply: contraTT => x_notin_hp.
  have x_notin_hp' : '[ b.1, x] > b.2.
  + by rewrite ltr_def; apply/andP; split.
  have bary_in_hs : (1-α) *: x + α *: y \in `[hs b].
  + apply: convexP2; try by rewrite inE.
    * by apply/andP; split; apply: ltrW.
  rewrite (* inE *) in_hs vdotDr 2!vdotZr in bary_in_hs. (* TODO: here, rewrite inE loops, why? *)
  suff: b.2 < (1 - α) * '[ b.1, x] + α * '[b.1, y].
  + by rewrite ltr_def bary_in_hs andbT.
  have ->: b.2 = (1 - α) * b.2 + α * b.2.
  + by rewrite mulrBl -addrA addNr mul1r addr0.
    by apply: ltr_le_add; rewrite lter_pmul2l //; rewrite subr_gt0.
Qed.

Lemma hp_extremeR b x y α :
  (x \in `[hs b]) -> (y \in `[hs b]) ->
  0 < α <= 1 -> ((1-α) *: x + α *: y \in `[hp b]) -> (y \in `[hp b]).
Proof.
move => x_in y_in /andP [α_ge0 α_lt1].
set bary := _ + _.
have ->: bary = (1 - (1 - α)) *: y + (1 - α) *: x.
- by rewrite subKr addrC.
apply: hp_extremeL; try by done.
apply/andP; split.
- by rewrite subr_cp0.
- by rewrite cpr_add oppr_lt0.
Qed.

Lemma poly0_subset P : `[poly0] `<=` P.
Proof.
by apply/poly_subsetP => x; rewrite inE.
Qed.

Lemma subset0_equiv {P} : (P `<=` `[poly0]) = (P == `[poly0]).
Proof.
apply/idP/eqP => [| ->]; last exact: poly_subset_refl.
move/poly_subsetP => P_sub0; apply/poly_eqP => x.
rewrite !inE; apply: negbTE.
by apply/negP; move/P_sub0; rewrite !inE.
Qed.

Lemma proper0N_equiv P : ~~ (P `>` `[poly0]) = (P == `[poly0]).
Proof. (* RK *)
rewrite negb_and negbK !poly0_subset //=.
exact: subset0_equiv.
Qed.

Lemma subset0N_proper P : ~~ (P `<=` `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
apply/idP/idP => [? | /andP [_ ?]]; last by done.
by apply/andP; split; [exact: poly0_subset | done].
Qed.

Lemma equiv0N_proper P : (P != `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
by rewrite -proper0N_equiv negbK.
Qed.

CoInductive empty_spec (P : 'poly[R]_n) : bool -> bool -> bool -> Set :=
| Empty of (P =i `[poly0]) : empty_spec P false true true
| NonEmpty of (P `>` `[poly0]) : empty_spec P true false false.

Lemma emptyP P : empty_spec P (P  `>` `[poly0]) (P == `[poly0]) (P `<=` `[poly0]).
Proof.
case: (boolP (P  `>` `[poly0])) => [P_non_empty | P_empty].
- rewrite -subset0N_proper in P_non_empty; move: (P_non_empty) => /negbTE ->.
  rewrite subset0_equiv in P_non_empty; move: (P_non_empty) => /negbTE ->.
  by constructor; rewrite equiv0N_proper in P_non_empty.
- rewrite proper0N_equiv in P_empty; rewrite subset0_equiv P_empty.
  by constructor; apply/poly_eqP/eqP.
Qed.

Lemma proper0P {P : 'poly[R]_n} :
  reflect (exists x, x \in P) (P `>` `[poly0]).
Proof.
rewrite -[_ `<` _]negbK proper0N_equiv -subset0_equiv.
apply/(iffP poly_subsetPn) => [[x] x_in x_notin | [x] x_in];
  exists x; by rewrite ?inE.
Qed.

Definition pick_point P : 'cV[R]_n :=
  match (@proper0P P) with
  | ReflectT P_non_empty => xchoose P_non_empty
  | ReflectF _ => 0
  end.

Lemma pick_pointP {P} :
  (P `>` `[poly0]) -> pick_point P \in P.
Proof. (* RK *)
rewrite /pick_point; case: proper0P => [? _ | _] //; exact: xchooseP.
Qed.

Lemma poly_properP {P Q : 'poly[R]_n} :
  (* TODO: should {subset P <= Q} to (P `<=` Q) ? *)
  reflect ({subset P <= Q} /\ exists2 x, x \in Q & x \notin P) (P `<` Q).
Proof.
apply: (iffP andP) =>
  [[/poly_subsetP ? /poly_subsetPn [x ??]] | [? [x ??]] ].
- by split; [ done | exists x].
- by split; [ apply/poly_subsetP | apply/poly_subsetPn; exists x].
Qed.

Lemma poly_subset_anti {P Q} :
  (P `<=` Q) -> (Q `<=` P) -> P = Q.
Proof.
move => /poly_subsetP P_le_Q /poly_subsetP Q_le_P.
apply/poly_eqP => x; apply/idP/idP => ?;
 [ exact : P_le_Q | exact : Q_le_P].
Qed.

Lemma poly_properEneq {P Q} :
  (P `<` Q) = (P `<=` Q) && (P != Q).
Proof.
apply/idP/andP => [/poly_properP [/poly_subsetP ?] [x x_in x_notin]| [P_sub_Q P_neq_Q] ].
- split; first done.
  apply/eqP => P_eq_Q; rewrite P_eq_Q in x_notin.
  by move/negP: x_notin.
- apply/andP; split; first done.
  move: P_neq_Q; apply: contra => ?; apply/eqP.
  exact: poly_subset_anti.
Qed.

Lemma poly_properW P Q :
  (P `<` Q) -> (P `<=` Q).
Proof.
by rewrite poly_properEneq => /andP [].
Qed.

Lemma poly_properxx P : (P `<` P) = false.
Proof.
by rewrite /poly_proper poly_subset_refl.
Qed.

Lemma poly_proper_subset P P' P'' :
  (P `<` P') -> (P' `<=` P'') -> (P `<` P'').
Proof. (* RK *)
move/poly_properP => [sPP' [x ? ?]] /poly_subsetP sP'P''.
apply/poly_properP; split; first by move => ? ?; apply/sP'P''/sPP'.
by exists x; [apply/sP'P'' | done].
Qed.

Lemma poly_subset_proper P P' P'' :
  (P `<=` P') -> (P' `<` P'') -> (P `<` P'').
Proof. (* RK *)
move => /poly_subsetP sPP' /poly_properP [sP'P'' [x ? x_notin_P']].
apply/poly_properP; split; first by move => ? ?; apply/sP'P''/sPP'.
by exists x; [done | move: x_notin_P'; apply/contra/sPP'].
Qed.

Lemma poly_proper_trans : transitive poly_proper.
Proof. (* RK *)
by move => ? ? ? /poly_properP [? _]; apply/poly_subset_proper/poly_subsetP.
Qed.

Lemma poly_proper_subsetxx P Q : (* to be compared with lter_anti *)
  (P `<` Q `<=` P) = false.
Proof. (* RK *)
by apply/negbTE/nandP/orP; rewrite negb_and negbK -orbA orbC orbN.
Qed.

Lemma poly_subset_properxx P Q :
  (P `<=` Q `<` P) = false.
Proof. (* RK *)
by apply/negbTE/nandP/orP; rewrite negb_and negbK orbA orbC orbA orbN.
Qed.

Lemma boundedP {P : 'poly[R]_n} {c} :
  reflect (exists2 x, x \in P & P `<=` `[hs (c, '[c,x])]) (bounded P c).
Proof.
have eq x : (P `<=` `[hs (c,'[ c, x])]) =
            H.poly_subset (repr P) (H.mk_hs (c, '[ c, x])).
by apply: (sameP H.poly_subsetP);
     apply: (iffP H.poly_subsetP) => sub z;
     move/(_ z): sub; rewrite H.in_hs in_hs.
by apply: (iffP (H.boundedP _ _)) => [[x] H H' | [x] H H']; exists x; rewrite ?inE ?eq in H' *.
Qed.

Lemma boundedPP {P : 'poly[R]_n} {c} :
  reflect (exists x, (x \in P) && (P `<=` `[hs (c, '[c, x])])) (bounded P c).
Proof.
by apply/(iffP boundedP) => [[x] ?? | [x] /andP [??]];
  exists x; first by apply/andP; split.
Qed.

Lemma boundedN0 {P : 'poly[R]_n} {c} :
  bounded P c -> P `>` `[poly0].
Proof.
move/boundedP => [x] [x_in_P _].
by apply/proper0P; exists x.
Qed.

Lemma boundedPn {P} {c} :
  (P `>` `[poly0]) -> reflect (forall K, exists2 x, x \in P & '[c,x] < K) (~~ bounded P c).
Proof.
(*rewrite -subset0N_proper; move => P_non_empty.*)
move => P_neq0.
have reprP_neq0: ~~ H.poly_subset (\repr P) H.poly0.
- move: P_neq0; rewrite -subset0N_proper.
  apply: contraNN => /H.poly_subsetP incl.
  by apply/poly_subsetP => x /incl; rewrite H.in_poly0.
apply: (iffP (H.boundedPn _ reprP_neq0)) => [H K | H K]; move/(_ K): H.
- move/H.poly_subsetPn => [x x_in_P x_not_in_hs].
  by exists x; rewrite H.in_hs -ltrNge in x_not_in_hs.
- move => [x x_in_P c_x_lt_K].
  by apply/H.poly_subsetPn; exists x; rewrite ?H.in_hs -?ltrNge.
Qed.

Lemma bounded_mono1 P Q c :
  bounded P c -> `[poly0] `<` Q `<=` P -> bounded Q c.
Proof. (* RK *)
move => /boundedPP [x /andP [_ /poly_subsetP sPhs]] /andP [Q_non_empty /poly_subsetP sQP].
apply/contraT => /(boundedPn Q_non_empty) Q_unbounded.
move: (Q_unbounded '[ c, x]) => [y y_in_Q x_y_vdot_sineq].
suff : ('[ c, x] <= '[ c, y]) by rewrite lerNgt x_y_vdot_sineq.
by move/sQP/sPhs : y_in_Q; rewrite in_hs.
Qed.

Lemma bounded_poly0 c : bounded (`[poly0]) c = false.
Proof.
by apply: (introF idP); move/boundedP => [x]; rewrite inE.
Qed.

Definition opt_value P c (bounded_P : bounded P c) :=
  let x := xchoose (boundedPP bounded_P) in '[c,x].

Lemma opt_point P c (bounded_P : bounded P c) :
  exists2 x, x \in P & '[c,x] = opt_value bounded_P.
Proof.
rewrite /opt_value; set x := xchoose _.
exists x; last by done.
by move: (xchooseP (boundedPP bounded_P)) => /andP [?].
Qed.

Lemma opt_value_lower_bound {P} {c} (bounded_P : bounded P c) :
  P `<=` (`[ hs (c, opt_value bounded_P)]).
Proof.
by rewrite /opt_value; move/andP : (xchooseP (boundedPP bounded_P)) => [_].
Qed.

Lemma opt_value_antimono1 P Q c (bounded_P : bounded P c) (bounded_Q : bounded Q c) :
  Q `<=` P -> opt_value bounded_P <= opt_value bounded_Q.
Proof. (* RK *)
move => /poly_subsetP sQP.
move: (opt_point bounded_Q) => [x x_in_Q <-].
move/sQP/(poly_subsetP (opt_value_lower_bound bounded_P)) : x_in_Q.
by rewrite in_hs.
Qed.

Definition argmin P c :=
  if @idP (bounded P c) is ReflectT H then
    P `&` `[hp (c, opt_value H)]
  else
    `[poly0].

Lemma argmin_polyI P c (bounded_P : bounded P c) :
  argmin P c = P `&` `[hp (c, opt_value bounded_P)].
Proof.
by rewrite /argmin; case: {-}_/idP => [b' | ?]; rewrite ?[bounded_P]eq_irrelevance.
Qed.

Lemma in_argmin P c x :
  x \in argmin P c = (x \in P) && (P `<=` `[hs (c, '[c, x])]).
Proof.
rewrite /argmin; case: {-}_/idP => [| /negP c_unbounded]; last first.
- rewrite inE; symmetry; apply: negbTE.
  case: (emptyP P) => [-> | P_non_empty]; first by rewrite inE.
  move/(boundedPn P_non_empty)/(_ '[c,x]): c_unbounded => [y y_in_P c_y_lt_c_x].
  rewrite negb_and; apply/orP; right.
  apply/poly_subsetPn; exists y; by rewrite ?notin_hs.
- move => c_bounded; rewrite !inE; apply/andP/andP.
  + move => [x_in_P /eqP ->]; split; by [done | exact: opt_value_lower_bound].
  + move => [x_in_P subset]; split; first by done.
    rewrite -lter_anti; apply/andP; split.
    * move/opt_point : (c_bounded) => [z z_in_P <-].
      by move/poly_subsetP/(_ _ z_in_P): subset; rewrite in_hs.
    * rewrite -in_hs; by apply/(poly_subsetP (opt_value_lower_bound _)).
Qed.

Lemma bounded_argminN0 P c :
  (bounded P c) = (argmin P c `>` `[poly0]).
Proof. (* RK *)
apply/idP/idP => [/boundedP [x ? ?] | /proper0P [x]].
- apply/proper0P; exists x.
  by rewrite in_argmin; apply/andP.
- rewrite in_argmin => /andP [? ?].
  by apply/boundedP; exists x.
Qed.

Lemma argmin_subset P c : argmin P c `<=` P.
Proof. (* RK *)
rewrite /argmin; case: {-}_/idP => [bounded_P | _];
  [exact: poly_subsetIl | exact: poly0_subset].
Qed.

Lemma argmin_opt_value P c (bounded_P : bounded P c) :
  argmin P c `<=` `[hp (c, opt_value bounded_P)].
Proof. (* RK *)
rewrite argmin_polyI; exact: poly_subsetIr.
Qed.

Lemma argmin_lower_bound {c x y} P :
  x \in argmin P c -> y \in P -> '[c,x] <= '[c,y].
Proof. (* RK *)
by rewrite in_argmin; move/andP => [_ /poly_subset_hsP/(_ y)].
Qed.

Lemma subset_opt_value P Q c (bounded_P : bounded P c) (bounded_Q : bounded Q c) :
  argmin Q c `<=` P `<=` Q -> opt_value bounded_P = opt_value bounded_Q. (* RK *)
Proof.
move => /andP [/poly_subsetP s_argminQ_P ?].
apply/eqP; rewrite eqr_le; apply/andP; split; last by apply: opt_value_antimono1.
move: (opt_point bounded_Q) => [x ? x_is_opt_on_Q].
rewrite -x_is_opt_on_Q -in_hs.
apply/(poly_subsetP (opt_value_lower_bound bounded_P))/s_argminQ_P.
rewrite in_argmin; apply/andP; split; first by done.
rewrite x_is_opt_on_Q.
exact: opt_value_lower_bound.
Qed.

Lemma subset_argmin {P Q} {c} :
  bounded Q c -> argmin Q c `<=` P `<=` Q -> argmin P c = argmin Q c.
Proof. (* RK *)
move => bounded_Q /andP [? ?]; apply/poly_equivP.
rewrite {1}/argmin; case: {-}_/idP => [bounded_P | unbounded_P]; apply/andP; split.
- rewrite argmin_polyI (subset_opt_value bounded_P bounded_Q _); last by apply/andP.
  by apply/polyISS; [done | exact: poly_subset_refl].
- apply/poly_subsetIP; split; first by done.
  rewrite (subset_opt_value bounded_P bounded_Q _); last by apply/andP.
  exact: argmin_opt_value.
- exact: poly0_subset.
- move/negP: unbounded_P; apply/contraR.
  rewrite subset0N_proper => non_empty_argmin_Q_c.
  apply/(bounded_mono1 bounded_Q _)/andP; split; last by done.
  by apply/(poly_proper_subset non_empty_argmin_Q_c _).
Qed.

Lemma argmin_eq {P} {c v x} :
  v \in argmin P c -> reflect (x \in P /\ '[c,x] = '[c,v]) (x \in argmin P c).
Proof. (* RK *)
move => v_in_argmin; rewrite in_argmin.
apply: (iffP idP) => [/andP [? /poly_subsetP sPhs] | [? ->]].
- split; first by done.
  apply/eqP; rewrite eqr_le; apply/andP; split; last by apply: (argmin_lower_bound v_in_argmin _).
  by rewrite -in_hs; apply/sPhs/(poly_subsetP (argmin_subset _ c)).
- apply/andP; split; first by done.
  rewrite in_argmin in v_in_argmin.
  exact: (proj2 (andP v_in_argmin)).
Qed.

Lemma bounded_lower_bound P c :
  (P `>` `[poly0]) -> reflect (exists d, P `<=` `[hs (c, d)]) (bounded P c).
Proof.
move => P_non_empty; apply: introP => [ c_bounded | /(boundedPn P_non_empty) c_unbouded ].
- exists (opt_value c_bounded); exact: opt_value_lower_bound.
- move => [d c_bounded]; move/(_ d): c_unbouded => [x x_in_P c_x_lt_K].
  by move/poly_subsetP/(_ _ x_in_P): c_bounded; rewrite in_hs lerNgt => /negP.
Qed.

Definition mk_line (c Ω : 'cV[R]_n) :=
  let S := kermx c in
  \polyI_(i < n) `[hp ((row i S)^T, '[(row i S)^T, Ω])].

Notation "'`[' 'line'  c & Ω  ']'" := (mk_line c Ω) (at level 70) : poly_scope.

Lemma in_lineP {c Ω x : 'cV[R]_n} :
  reflect (exists μ, x = Ω + μ *: c) (x \in `[line c & Ω]).
Proof.
apply: (iffP idP); last first.
- move => [μ ->]; apply/in_big_polyIP => [i _]; rewrite in_hp; apply/eqP.
  rewrite vdotDr vdotZr.
  suff /matrixP/(_ 0 0): '[ (row i (kermx c))^T, c]%:M = 0 :> 'M_1
    by rewrite !mxE mulr1n => ->; rewrite mulr0 addr0.
  rewrite vdot_def -trmx_mul -trmx0; apply: congr1.
  apply/sub_kermxP; exact: row_sub.
- move/in_big_polyIP => H.
  pose d := x - Ω; suff /sub_rVP [μ ]: (d^T <= c^T)%MS.
  rewrite -linearZ /= => /trmx_inj d_eq_mu_c.
  by exists μ; rewrite -d_eq_mu_c /d addrCA addrN addr0.
  rewrite submx_kermx !trmxK.
  apply/row_subP => i; apply/sub_kermxP.
  rewrite -[row _ _]trmxK -vdot_def vdotC [RHS]const_mx11; apply: congr1.
  move/(_ i isT): H; rewrite in_hp => /eqP.
  by rewrite /d vdotBr => ->; rewrite addrN.
Qed.

Lemma pointed0 : pointed (`[poly0]).
Proof.
rewrite /pointed /H.pointed.
suff ->: H.poly_subset (\repr (`[ poly0 ])) H.poly0 by done.
by apply/H.poly_subsetP => x; rewrite repr_equiv.
Qed.

Lemma pointedPn P :
  (P `>` `[poly0]) ->
    reflect (exists c, (c != 0) /\ (forall Ω, Ω \in P -> (`[line c & Ω] `<=` P))) (~~ (pointed P)).
Proof.
move => P_neq0.
have reprP_neq0 : ~~ (H.poly_subset (repr P) H.poly0).
- move: P_neq0; rewrite -subset0N_proper; apply: contraNN.
  move/H.poly_subsetP => reprP_le0.
  apply/poly_subsetP => x; rewrite -[P]reprK repr_equiv => /reprP_le0.
  by rewrite H.in_poly0.
apply: (iffP (H.pointedPn reprP_neq0)) => [[c [? incl]] | [c [? incl]]];
  exists c; split; try by done.
- move => Ω Ω_in_P.
  apply/poly_subsetP => x /in_lineP [μ ->].
  exact: incl.
- move => μ μ_in_P λ.
  apply/(poly_subsetP (incl _ μ_in_P))/in_lineP.
  by exists λ.
Qed.

Definition mk_hline (c Ω : 'cV[R]_n) :=
  `[hs (c, '[c,Ω])] `&` `[line c & Ω].

Notation "'`[' 'hline'  c & Ω  ']'" := (mk_hline c Ω) (at level 70) : poly_scope.

Lemma in_hlineP (c Ω x : 'cV[R]_n) :
  reflect (exists2 μ, μ >= 0 & x = Ω + μ *: c) (x \in `[hline c & Ω]).
Proof.
rewrite !inE; apply: (iffP andP).
- move => [c_x_ge_c_Ω /in_lineP [μ x_eq]].
  rewrite x_eq in c_x_ge_c_Ω *.
  case: (c =P 0) => [-> | c_neq0].
  + exists 0; by rewrite ?scaler0.
  + exists μ; last by done.
    rewrite vdotDr ler_addl vdotZr pmulr_lge0 in c_x_ge_c_Ω; first by done.
    by rewrite vnorm_gt0; apply/eqP.
- move => [μ μ_ge0 ->]; split; last by apply/in_lineP; exists μ.
  rewrite vdotDr ler_addl vdotZr.
  apply: mulr_ge0; first by done.
  exact: vnorm_ge0.
Qed.

Definition mk_pt (Ω : 'cV[R]_n) := conv ([fset Ω]%fset).

Notation "'`[' 'pt'  Ω  ']'" := (mk_pt Ω) (at level 70) : poly_scope.

Lemma in_pt (Ω x : 'cV[R]_n) : (x \in `[pt Ω]) = (x == Ω).
Proof. (* RK *)
apply/idP/idP => [/convP [w /weightP [w_ge0 _ sum_w] ->] | /eqP ->].
- rewrite big_seq_fset1 in sum_w.
  by rewrite /bary big_seq_fset1 sum_w scale1r.
- pose w := [fsfun x : [fset Ω]%fset => 1%R | 0%R] : {fsfun 'cV[R]_n -> R for fun => 0%R}.
  have w_Ω_eq_1: w Ω = 1
    by rewrite fsfun_ffun /=; case: insubP => [? ? ? /= | /= ]; [done | rewrite in_fset1 eq_refl].
  apply/convP; exists w.
  + apply/weightP; split.
    * move => v; rewrite fsfun_ffun.
      by case: insubP => [? _ _ /= | /= _]; [exact: ler01 | done].
    * move => v; rewrite fsfun_ffun.
      by case: insubP => [? -> _ /= | /= _].
    * by rewrite big_seq_fset1.
  + by rewrite /bary big_seq_fset1 w_Ω_eq_1 scale1r.
Qed.

Lemma in_pt_self (Ω : 'cV[R]_n) : Ω \in `[pt Ω].
Proof. (* RK *)
by rewrite in_pt.
Qed.

Lemma pt_proper0 (Ω : 'cV[R]_n) : (`[ poly0 ]) `<` (`[ pt Ω ]).
Proof. (* RK *)
apply/proper0P; exists Ω; exact: in_pt_self.
Qed.

Lemma pick_point_pt (Ω : 'cV[R]_n) :
  pick_point (`[pt Ω]) = Ω.
Proof. (* RK *)
apply/eqP; rewrite -in_pt; apply/pick_pointP; exact: pt_proper0.
Qed.

Lemma pt_subset (Ω : 'cV[R]_n) P : `[pt Ω] `<=` P = (Ω \in P).
Proof. (* RK *)
by apply/idP/idP => [/poly_subsetP s_ptΩ_P | ?];
  [apply/s_ptΩ_P; exact: in_pt_self | apply/poly_subsetP => v; rewrite in_pt => /eqP ->].
Qed.

Lemma pt_proper (Ω : 'cV[R]_n) P : `[pt Ω] `<` P -> (Ω \in P).
Proof.
by move/poly_properW; rewrite pt_subset.
Qed.

(* The notation [segm Ω & Ω'] has been removed because of the lack of symmetry between
 * Ω and Ω', while this should not appear in the [fset Ω; Ω']%fset                     *)
Lemma in_segmP (Ω Ω' x : 'cV[R]_n) :
  reflect (exists2 μ, 0 <= μ <= 1 & x = (1 - μ) *: Ω + μ *: Ω') (x \in conv [fset Ω; Ω']%fset).
Proof. (* RK *)
Admitted.
(*
case: (boolP (Ω == Ω')) => [/eqP -> | Ω_neq_Ω'].
- rewrite fsetUid in_pt.
  apply: (iffP idP) => [/eqP -> | [μ _ ->]].
  + by exists 1; [apply/andP | rewrite scale1r subrr addr0].
  + by rewrite subrr scaler0 addr0.
- apply: (iffP idP) => [/convP [w /weightP [w_ge0 _ sum_w] ->] | [a /andP [? ?] ?]].
  + have w_Ω_eq: w Ω = 1 - w Ω'.
      rewrite -sum_w big_setU1 /=; last by rewrite in_fset1.
      by rewrite big_seq_fset1 -addrA subrr addr0.
    exists (w Ω').
    * apply/andP; split; first by apply: w_ge0.
      by rewrite -subr_ge0 -w_Ω_eq; apply: w_ge0.
    * rewrite /bary big_setU1 /=; last by rewrite in_fset1.
      by rewrite big_seq_fset1 w_Ω_eq scalerBl scale1r -addrA [X in _+X]addrC scalerBr.
  + pose w := [fsfun x : [fset Ω; Ω']%fset => if (val x == Ω') then a else (1-a) | 0%R] : {fsfun 'cV[R]_n -> R for fun => 0%R}.
    have w_Ω'_eq: w Ω' = a
      by rewrite fsfun_ffun /=; case: insubP => [y ? val_y_eq /= | /= ];
        [apply/ifT; rewrite val_y_eq | rewrite in_fset2 eq_refl negb_or /=; move/andP/proj2].
    have w_Ω_eq: w Ω = (1 - a)
      by rewrite fsfun_ffun /=; case: insubP => [y ? val_y_eq /= | /= ];
        [apply/ifF; rewrite val_y_eq; apply/negbTE | rewrite in_fset2 eq_refl /=].
    apply/convP; exists w.
    * apply/weightP; split.
      - move => y; rewrite fsfun_ffun.
        case: insubP => [z _ _ /= | /= _]; last by done.
        by case: (boolP (fsval z == Ω')) => [_ |_]; [done | rewrite subr_ge0].
      - move => y; rewrite fsfun_ffun.
        by case: insubP => [? -> _ /= | /= _].
      - rewrite big_setU1 /=; last by rewrite in_fset1.
        by rewrite big_seq_fset1 w_Ω_eq w_Ω'_eq subrK.
    * rewrite /bary big_setU1 /=; last by rewrite in_fset1.
      by rewrite big_seq_fset1 w_Ω_eq w_Ω'_eq scalerBl scale1r -addrA [X in _+X]addrC -scalerBr.
Qed.*)

Definition compact P :=
  (P `>` `[poly0]) ==>
    [forall i, (bounded P (delta_mx i 0)) && (bounded P (-(delta_mx i 0)))].

Lemma compact0 : compact (`[poly0]).
Proof.
by rewrite /compact poly_properxx.
Qed.

Lemma compactP_Linfty (P : 'poly[R]_n) :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Proof.
rewrite /compact implybE.
case: (emptyP P) => [| P_neq0 ]; last first.
- apply: (iffP idP) => [/forallP ei_mei | [K H]].
  + pose ei i := (andP (ei_mei i)).1.
    pose mei i := (andP (ei_mei i)).2.
    set K := (-(min_seq [
      seq Num.min (opt_value (ei i))
      (opt_value (mei i)) | i :'I_n] 0))%R.
    exists K; move => x x_in_P i.
    suff: ('[delta_mx i 0, x] >= -K /\ '[-(delta_mx i 0), x] >= -K)%R.
    * rewrite vdotNl vdotl_delta_mx ler_opp2 => /andP.
      by rewrite ler_norml.
    * split; rewrite opprK; [ pose f := (ei i) | pose f := (mei i) ];
      move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound f); rewrite inE /=;
      apply: ler_trans; set v := (X in _ <= X);
      suff: Num.min (opt_value (ei i)) (opt_value (mei i)) <= v
        by apply: ler_trans; apply: min_seq_ler; apply: map_f; rewrite mem_enum.
      - rewrite ler_minl; apply/orP; left; exact: lerr.
      - rewrite ler_minl; apply/orP; right; exact: lerr.
  + apply/forallP => i; apply/andP; split;
      [pose v := (delta_mx i 0):'cV[R]_n | pose v := (-(delta_mx i 0):'cV[R]_n)%R];
    apply/bounded_lower_bound => //; exists (-K)%R;
    apply/poly_subsetP => x x_in_P; move/(_ _ x_in_P i): H;
    rewrite inE /=  ?vdotNl vdotl_delta_mx ?ler_opp2;
    by rewrite ler_norml; move/andP => [? ?].
- move/poly_eqP -> => /=; constructor.
  by exists 0; move => x; rewrite inE.
Qed.

Lemma compactP P :
  (P `>` `[poly0]) -> reflect (forall c, bounded P c) (compact P).
Proof.
move => P_neq0.
apply: (iffP idP) => [/compactP_Linfty [K H] c | ?].
- pose v := (- \sum_i `|c i 0| * K)%R.
  suff foo: P `<=` `[hs (c, v)].
  + apply/bounded_lower_bound => //.
    by exists v.
  + apply/poly_subsetP => x x_in_P.
    have: `|'[c,x]| <= \sum_i `|c i 0| * K.
    suff: \sum_i `|c i 0 * x i 0| <= \sum_i `|c i 0| * K.
    * apply: ler_trans; rewrite /vdot; exact: ler_norm_sum.
    apply: ler_sum => i _; rewrite normrM.
    apply: ler_wpmul2l; [ exact: normr_ge0 | exact: H ].
    by rewrite ler_norml => /andP [? _]; rewrite inE.
- rewrite /compact P_neq0 /=.
  by apply/forallP => i; apply/andP; split.
Qed.

Lemma compact_pointed P :
  compact P -> pointed P.
Proof.
case: (emptyP P) => [/poly_eqP ->| P_neq0 P_compact]; first by rewrite pointed0.
apply: contraT => /(pointedPn P_neq0) [c] [c_neq0 hl_sub].
suff: ~~ (bounded P c).
  by move/(compactP P_neq0)/(_ c) : P_compact => ->.
apply/boundedPn => //.
move/proper0P: P_neq0 => [Ω Ω_in_P].
move/(_ _ Ω_in_P): hl_sub => /poly_subsetP hl_sub K.
pose μ := ((K - 1 - '[c,Ω])/'[| c |]^2)%R.
exists (Ω + μ *: c); first by apply: hl_sub; apply/in_lineP; exists μ.
rewrite vdotDr vdotZr mulfVK; last by apply: lt0r_neq0; rewrite vnorm_gt0.
by rewrite addrCA addrN addr0 cpr_add ltrN10.
Qed.

Lemma compact_conv (V : {fset 'cV[R]_n}) : compact (conv V).
Admitted.

Lemma compact_pt (Ω : 'cV[R]_n) : compact (`[pt Ω]).
Admitted.

Definition slice (b : base_elt) P := `[hp b] `&` P.

Lemma slice0 (b : base_elt) : slice b (`[poly0]) = `[poly0].
Proof.
by rewrite /slice polyI0.
Qed.

Definition poly_of_base (base : base_t) :=
  \polyI_(b : base) `[hs (val b)].

Notation "''P' ( base )" := (poly_of_base base) (at level 0) : poly_scope.

Lemma in_poly_of_base x (base : base_t) :
  (x \in 'P(base)) = [forall b : base, x \in `[hs (val b)]].
Proof.
by rewrite in_big_polyI.
Qed.

Lemma poly_base_subset {base : base_t} {e : base_elt} :
  e \in base -> 'P(base) `<=` `[hs e].
Proof.
move => e_in_base.
pose e' := [`e_in_base]%fset; have ->: e = fsval e' by done.
exact: big_poly_inf.
Qed.

Definition polyEq (base I : base_t) :=
  (\polyI_(e : I) `[hp (val e)]) `&` 'P(base).

Notation "''P^=' ( base ; I )" := (polyEq base I) : poly_scope.

Fact in_polyEq x base I :
  (x \in 'P^=(base; I)) = [forall e : I, x \in `[hp (val e)]] && (x \in 'P(base)).
Proof.
by rewrite inE in_big_polyI.
Qed.

Lemma in_polyEqP x base I :
  reflect ((forall e, e \in I -> x \in `[hp e]) /\ x \in 'P(base)) (x \in 'P^=(base; I)).
Proof.
rewrite in_polyEq; apply: (equivP andP); split.
+ by case=> /forallP /= h ->; split=> // e eI; apply: (h [` eI]%fset).
+ by case=> h ->; split=> //; apply/forallP=> -[/= e eI_]; apply/h.
Qed.

Lemma polyEq_eq x base I e :
  x \in 'P^=(base; I) -> e \in I -> x \in `[hp e].
Proof.
by move/in_polyEqP => [x_act _ ?]; apply: x_act.
Qed.

Lemma polyEq0 {base : base_t} :
  'P^=(base; fset0) = 'P(base).
Proof.
apply/poly_eqP=> c; rewrite !in_polyEq; apply: andb_idl.
by move=> _; apply/forallP=> /=; case.
Qed.

Lemma polyEq_antimono (base I I' : base_t[R,n]) :
  (I `<=` I')%fset -> 'P^=(base; I') `<=` 'P^=(base; I).
Proof.
move=> leI; apply/poly_subsetP=> c; rewrite !in_polyEq.
case/andP=> [/forallP /= h ->]; rewrite andbT; apply/forallP=> /=.
by move=> e; apply: (h (fincl leI e)).
Qed.

Lemma polyEq_antimono0 {base I : base_t[R,n]} :
  'P^=(base; I) `<=` 'P(base).
Proof. by rewrite -polyEq0; apply: polyEq_antimono. Qed.

Lemma polyEq_polyI {base I I': base_t[R,n]} :
  'P^=(base; I) `&` 'P^=(base; I') = 'P^=(base; (I `|` I')%fset).
Proof.
apply/poly_eqP=> c; rewrite in_polyI!in_polyEq andbACA andbb.
congr (_ && _); apply/andP/forallP => /=.
+ case=> /forallP /= hI /forallP /= hI' -[/= e]; rewrite in_fsetU => /orP.
  by case=> [eI|eI']; [apply: (hI [`eI]%fset) | apply: (hI' [`eI']%fset)].
+ move=> h; split; apply/forallP=> /= e.
  * by apply: (h (fincl (fsubsetUl I I') e)).
  * by apply: (h (fincl (fsubsetUr I I') e)).
Qed.

Lemma polyEq_big_polyI {base: base_t[R,n]} {I : finType} {P : pred I} {F}  :
  ~~ pred0b P -> \polyI_(i | P i) 'P^=(base; F i) = 'P^=(base; (\bigcup_(i | P i) (F i))%fset).
Proof.
move/pred0Pn => [i0 Pi0].
apply/poly_equivP/andP; split; last first.
- apply/big_polyIsP => [i Pi]; apply/polyEq_antimono; exact: bigfcup_sup.
- apply/poly_subsetP => x /in_big_polyIP x_in.
  apply/in_polyEqP; split; last first.
  rewrite /=.
  move/(_ _ Pi0): x_in; by apply/(poly_subsetP (polyEq_antimono0)).
  move => e /= /bigfcupP [i [/andP [_ Pi] ?]].
  exact: (polyEq_eq (x_in _ Pi)).
Qed.

Lemma polyEq1 {base: base_t[R,n]} {e} :
  'P^=(base; [fset e]%fset) = 'P(base) `&` `[hp e].
Proof.
apply/poly_eqP=> c; rewrite in_polyI !in_polyEq andbC; congr (_ && _).
apply/forallP/idP => /= [h| c_in_e]; first by apply: (h [` fset11 e]%fset).
by case=> /= e'; rewrite in_fset1 => /eqP->.
Qed.

Lemma slice_polyEq {e : base_elt} {base I : base_t[R,n]} :
  slice e 'P^=(base; I) = 'P^=(e +|` base; e +|` I).
Proof.
Admitted.

Definition baseEq (base I : base_t[R,n]) :=
  (base `|` ((@Base.opp_base_elt _ _) @` I))%fset.

Lemma polyEq_flatten (base : base_t[R,n]) (I : {fsubset base}) :
  'P^=(base; I) = 'P(baseEq base I)%fset.
Proof.
Admitted.

Lemma polyEq_of_polyEq (base : base_t[R,n]) (I : {fsubset base}) (J : {fsubset (baseEq base I)}) :
  exists K : {fsubset base}, 'P^=(baseEq base I; J) = 'P^=(base; K).
Proof.
Admitted.

(*
Lemma polyEq_of_polyEq (base base1 base2 : base_t R n) : (* quite short proof after all! *)
   exists base3, 'P^=(baseEq base base1; base2) `=~` 'P^=(base; base3).
Proof.
move: I J; case: base => [A b] I J.
pose f (j : 'I_(#|I| + m)) :=
  match splitP' j with
  | SplitLo' j' _ => (enum_val j')
  | SplitHi' k _ => k
  end.
pose K := I :|: (f @: J); exists K.
apply/andP; split; apply/poly_subsetP => x x_in.
- apply/in_polyEqP; split; last first.
  + move/(poly_subsetP polyEq_antimono0): x_in.
    rewrite -(poly_equivP polyEq_flatten).
    exact: (poly_subsetP polyEq_antimono0).
  + move => k /setUP; case.
    * apply: polyEq_eq; rewrite (poly_equivP polyEq_flatten).
      by move/(poly_subsetP polyEq_antimono0): x_in.
    * move/imsetP => [j'] j'_in_J ->; rewrite /f.
      case: (splitP' j') => [j j'_eq| j j'_eq].
      - move/polyEq_eq/(_ j'_in_J) : x_in; rewrite j'_eq !in_nth_hp /= mul_col_mx !col_mxEu.
        rewrite mulNmx -row_submx_mul mxE [X in _ == X]mxE 2!row_submx_mxE.
        by rewrite eqr_opp.
      - move/polyEq_eq/(_ j'_in_J) : x_in.
        by rewrite j'_eq !in_nth_hp /= mul_col_mx !col_mxEd.
      - apply/in_polyEqP; split; last first.
        + rewrite -(poly_equivP polyEq_flatten).
          move: x x_in; apply/poly_subsetP/polyEq_antimono; exact: subsetUl.
        + move => j /(mem_imset f)/(subsetP (@subsetUr _ I _)) fj_in_K.
          move/polyEq_eq/(_ fj_in_K): x_in.
          rewrite /f; case: splitP' => [j' -> eq| j' ->].
          * rewrite !in_nth_hp /= mul_col_mx !col_mxEu mulNmx -row_submx_mul 2![(- row_submx _ _) j' 0]mxE 2!row_submx_mxE /=.
            rewrite eqr_opp; by rewrite in_nth_hp in eq.
          * by rewrite !in_nth_hp mul_col_mx !col_mxEd.
Qed.
Admitted.*)

End PolyPred.

Notation "'`[' 'poly0' ']'" := poly0 (at level 70) : poly_scope.
Notation "'`[' 'polyT' ']'" := polyT (at level 70) : poly_scope.
Notation "P `&` Q" := (polyI P Q) (at level 48, left associativity) : poly_scope.
Notation "P `<=` Q" := (poly_subset P Q) (at level 70, no associativity, Q at next level) : poly_scope.
Notation "P `>=` Q" := (Q `<=` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `=~` Q" := (poly_equiv P Q) (at level 70, no associativity) : poly_scope.
Notation "P `!=~` Q" := (~~ (poly_equiv P Q)) (at level 70, no associativity) : poly_scope.
Notation "P `<` Q" := (poly_proper P Q) (at level 70, no associativity, Q at next level) : poly_scope.
Notation "P `>` Q" := (Q `<` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `<=` Q `<=` S" := ((poly_subset P Q) && (poly_subset Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "P `<` Q `<=` S" := ((poly_proper P Q) && (poly_subset Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "P `<=` Q `<` S" := ((poly_subset P Q) && (poly_proper Q S)) (at level 70, Q, S at next level) : poly_scope.
Notation "'`[' 'hs'  b  ']'" := (mk_hs b) (at level 70) : poly_scope.
Notation "'`[' 'hp' b  ']'" := (mk_hp b) (at level 70) : poly_scope.
Notation "'`[' 'line'  c & Ω  ']'" := (mk_line c Ω) (at level 70) : poly_scope.
Notation "'`[' 'hline'  c & Ω  ']'" := (mk_hline c Ω) (at level 70) : poly_scope.
Notation "'`[' 'pt'  Ω  ']'" := (mk_pt Ω) (at level 70) : poly_scope.
Notation "''P' ( base )" := (poly_of_base base) (at level 0) : poly_scope.
Notation "''P^=' ( base ; I )" := (polyEq base I) : poly_scope.

Notation "\polyI_ ( i <- r | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i <- r | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i <- r ) F" :=
  (\big[polyI/`[polyT]%PH]_(i <- r) F%PH) : poly_scope.
Notation "\polyI_ ( i | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i | P%B) F%PH) : poly_scope.
Notation "\polyI_ i F" :=
  (\big[polyI/`[polyT]%PH]_i F%PH) : poly_scope.
Notation "\polyI_ ( i : I | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i : I | P%B) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( i : I ) F" :=
  (\big[polyI/`[polyT]%PH]_(i : I) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( m <= i < n | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(m <= i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( m <= i < n ) F" :=
  (\big[polyI/`[polyT]%PH]_(m <= i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i < n | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i < n ) F" :=
  (\big[polyI/`[polyT]%PH]_(i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A | P ) F" :=
  (\big[polyI/`[polyT]%PH]_(i in A | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A ) F" :=
  (\big[polyI/`[polyT]%PH]_(i in A) F%PH) : poly_scope.

Definition inE := (@in_poly0, @in_polyT, @in_hp, @in_polyI, @in_hs, inE).

Section Duality.

Local Open Scope poly_scope.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Implicit Type w : {fsfun base_elt[R,n] -> R for fun => 0%R}.

Lemma farkas (e : base_elt) :
  ('P(base) `>` `[poly0]) -> ('P(base) `<=` `[hs e]) ->
  exists2 w, pweight base w & ((combine base w).1 = e.1 /\ (combine base w).2 >= e.2).
Proof.
rewrite /poly_of_base big_polyI_mono -subset0N_proper 2!poly_subset_mono.
exact: H.farkas.
Qed.

Lemma dual_sol_lower_bound w :
  pweight base w -> 'P(base) `<=` `[hs (combine base w)].
Proof.
move => w_weight.
apply/poly_subsetP => x; rewrite inE in_poly_of_base /=.
rewrite vdot_sumDl => /forallP H.
apply: ler_sum => i _.
rewrite vdotZl; apply: ler_wpmul2l; first exact: (pweight_ge0 w_weight).
by move/(_ i): H; rewrite inE.
Qed.

Lemma dual_opt_sol (c : 'cV[R]_n) (H : bounded 'P(base) c) :
  exists2 w, pweight base w & combine base w = (c, opt_value H).
Proof.
move/(farkas (boundedN0 H)): (opt_value_lower_bound H) => [w] [w_weight [w_comb1 w_comb2]].
exists w; first done.
apply: injective_projections; first done.
apply: ler_anti; apply/andP; split; last done.
move: (opt_point H) => [x] [x_in_P <-].
move/poly_subsetP/(_ _ x_in_P): (dual_sol_lower_bound w_weight).
by rewrite inE w_comb1.
Qed.

Lemma dual_sol_bounded w :
  ('P(base) `>` `[poly0]) -> pweight base w -> bounded 'P(base) (fst (combine base w)).
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists (combine base w).2; exact: dual_sol_lower_bound.
Qed.

Variable (w : {fsfun base_elt[R,n] -> R for fun => 0%R}).
Hypothesis w_pweight : pweight base w.

Lemma compl_slack_cond x :
  x \in 'P(base) -> reflect (x \in `[hp (combine base w)]) (x \in 'P^=(base; supp base w)).
Proof.
move => x_in_P; apply: (iffP idP) => [/in_polyEqP [in_hps _] |].
- rewrite in_hp vdot_sumDl; apply/eqP.
  apply: eq_bigr => i _.
  case: (suppP w_pweight); first by rewrite scale0r vdot0l mul0r.
  by move/in_hps; rewrite inE vdotZl => /eqP <-.
- rewrite in_hp vdot_sumDl => in_comb_hp.
  apply/in_polyEqP; split; last done.
  move => e e_in_supp; move: in_comb_hp; apply: contraTT.
  rewrite notin_hp; last first.
  + move: x x_in_P; apply/poly_subsetP/poly_base_subset.
    exact: (fsubsetP (supp_subset _ w)).
  + move => notin_hp; rewrite eq_sym; apply/ltr_neq.
    apply: sumr_ltrP => [i| ].
    * rewrite vdotZl; apply/ler_wpmul2l; first exact : (pweight_ge0 w_pweight).
      move/(poly_subsetP (poly_base_subset (fsvalP i))): x_in_P.
      by rewrite inE /=.
    * have e_in_base : e \in base by apply/(fsubsetP (supp_subset _ w)).
      exists [` e_in_base]%fset.
      rewrite vdotZl ltr_pmul2l; first done.
      by rewrite -(pweight_gt0 w_pweight).
Qed.

Lemma dual_sol_argmin :
  ('P^=(base; supp base w) `>` `[poly0]) -> argmin 'P(base) (fst (combine base w)) = 'P^=(base; supp base w).
Proof.
have PI_sub_P : 'P^=(base; supp base w) `<=` 'P(base) by exact: polyEq_antimono0.
move => PI_neq0.
have P_neq0 : ('P(base) `>` `[poly0]) by exact: (poly_proper_subset PI_neq0).
move/proper0P : PI_neq0 => [x x_in_PI].
set c := (combine base w).1; have c_bounded := (dual_sol_bounded P_neq0 w_pweight).
rewrite argmin_polyI.
suff ->: opt_value c_bounded = (combine base w).2.
- apply/poly_eqP => y; rewrite inE.
  apply/andP/idP => [[? ?]| y_in_PI]; first exact/compl_slack_cond.
  have y_in_P: y \in ('P(base)) by apply/(poly_subsetP PI_sub_P).
  by split; try exact: compl_slack_cond.
- have x_in_P : x \in ('P(base)) by apply/(poly_subsetP PI_sub_P).
  apply/eqP; rewrite eqr_le; apply/andP; split.
  + move/(_ x_in_PI) : (compl_slack_cond x_in_P); rewrite inE => /eqP <-.
    move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound c_bounded).
    by rewrite inE.
  + move: (opt_point c_bounded) => [y y_in_P <-].
    move/poly_subsetP/(_ _ y_in_P): (dual_sol_lower_bound w_pweight).
    by rewrite inE.
Qed.

End Duality.
