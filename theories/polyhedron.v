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


(*
Structure mixin_of (T : choicePredType 'cV[R]_n) := Mixin {
  poly0 : T; in_poly0 : poly0 =i pred0;
  polyT : T; in_polyT : polyT =i predT;
  polyI : T -> T -> T;
  in_polyI : forall (P Q : T), (polyI P Q) =i [predI P & Q];
  poly_subset : rel T;
  poly_subsetP : forall (P Q : T), reflect {subset P <= Q} (poly_subset P Q);
  poly_subsetPn : forall (P Q : T), reflect (exists2 x, (x \in P) & (x \notin Q)) (~~ (poly_subset P Q));
  mk_hs : base_elt[R,n] -> T;
  in_hs : forall b x, x \in (mk_hs b) = ('[fst b,x] >= snd b);
  bounded : T -> 'cV[R]_n -> bool;
  boundedP : forall (P : T) c, reflect (exists2 x, x \in P & poly_subset P (mk_hs (c,'[c,x]))) (bounded P c);
  boundedPn : forall (P : T) c, ~~ (poly_subset P poly0) -> reflect (forall K, ~~ (poly_subset P (mk_hs (c, K)))) (~~ bounded P c);
  pointed : pred T;
  pointedPn : forall (P : T), ~~ (poly_subset P poly0) -> reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P);
  conv : {fset 'cV[R]_n} -> T;
  convP : forall V x, reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V);
  convexP : forall (P : T) (V : {fset 'cV[R]_n}), {subset V <= P} -> poly_subset (conv V) P
}.
 *)

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
Admitted.

Lemma quotP {P Q : 'hpoly[R]_n} : '[P] = '[Q] <-> P =i Q.
Admitted.

(*
Lemma quot_eqP (P Q : {quot T}) : (P =i Q) -> (P = Q).
Proof.
Admitted.*)

(*rewrite -[P]reprK -[Q]reprK.
set P' := repr P; set Q' := repr Q; move => P_equiv_Q.
have P'_equiv_Q' : P' `=~` Q'
  by apply/poly_equivP => x; move/(_ x): P_equiv_Q; rewrite !repr_equiv.
have chooseP'_eq_chooseQ' : poly_equiv P' =1 poly_equiv Q'.
  by move => z; apply/idP/idP; apply/poly_equiv_trans;
  try by rewrite poly_equiv_sym in P'_equiv_Q'.
apply: repr_inj.
by rewrite /= /canon -(eq_choose chooseP'_eq_chooseQ'); apply: choose_id; try exact: poly_equiv_refl.
Qed.*)

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

Lemma poly_equivP {P Q} : P `=~` Q -> P = Q.
Proof.
Admitted.
(*
apply/(iffP andP) => [[/poly_subsetP P_le_Q /poly_subsetP Q_le_P] x | P_eq_Q ].
- apply/idP/idP; [exact: P_le_Q | exact: Q_le_P].
- by split; apply/poly_subsetP => x; rewrite P_eq_Q.
Qed.*)

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

Lemma in_polyI P Q x : (x \in (P `&` Q)) = ((x \in P) && (x \in Q)).
Proof.
by rewrite !repr_equiv H.in_polyI.
Qed.

Lemma in_hs : (forall b x, x \in (`[hs b]) = ('[fst b,x] >= snd b))
              * (forall c α x, x \in (`[hs (c, α)]) = ('[c,x] >= α)).
Proof.
Admitted.

Lemma notin_hs :
  (forall b x, (x \notin `[hs b]) = ('[b.1,x] < b.2))
  * (forall c α x, (x \notin `[hs (c, α)]) = ('[c,x] < α)).
Admitted.

Definition mk_hp e := `[hs e] `&` `[hs (-e)].
Notation "'`[' 'hp' e  ']'" := (mk_hp e%PH) (at level 70) : poly_scope.

Lemma in_hp :
  (forall b x, (x \in `[hp b]) = ('[fst b,x] == snd b))
  * (forall c α x, (x \notin `[hp (c, α)]) = ('[c,x] == α)).
Admitted.
(*Proof. (* RK *)
by rewrite in_polyI 2!in_hs vdotNl ler_oppl opprK eq_sym eqr_le.
Qed.*)

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

Lemma convP V x :
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

Lemma polyIxx P : P `&` P = P.
Proof.
by apply/poly_eqP => x; rewrite inE Bool.andb_diag. (* TODO: strange to require a cool to Bool.* *)
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
Admitted.

Lemma hp_extremeR b x y α :
  (x \in `[hs b]) -> (y \in `[hs b]) ->
     0 < α <= 1 -> ((1-α) *: x + α *: y \in `[hp b]) -> (y \in `[hp b]).
Admitted.

Lemma poly0_subset P : `[poly0] `<=` P.
Proof.
by apply/poly_subsetP => x; rewrite inE.
Qed.

Lemma proper0N_equiv P : ~~ (P `>` `[poly0]) = (P == `[poly0]).
Proof. (* RK *)
Admitted.
(*rewrite negb_and negbK /poly_equiv !poly0_subset //=.
by apply/idP/idP => [-> | ]; [done | case/andP].
Qed.*)

Lemma subset0N_proper P : ~~ (P `<=` `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
apply/idP/idP => [? | /andP [_ ?]]; last by done.
by apply/andP; split; [exact: poly0_subset | done].
Qed.

Lemma equiv0N_proper P : (P != `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
by rewrite -proper0N_equiv negbK.
Qed.

Lemma subset0_equiv {P} : (P `<=` `[poly0]) = (P == `[poly0]).
Proof. (* RK *)
by apply/negb_inj; rewrite subset0N_proper equiv0N_proper.
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
  (* should {subset P <= Q} to (P `<=` Q) *)
  reflect ({subset P <= Q} /\ exists2 x, x \in Q & x \notin P) (P `<` Q).
Proof.
apply: (iffP andP) =>
  [[/poly_subsetP ? /poly_subsetPn [x ??]] | [? [x ??]] ].
- by split; [ done | exists x].
- by split; [ apply/poly_subsetP | apply/poly_subsetPn; exists x].
Qed.

Lemma poly_subset_anti {P Q} :
  (P `<=` Q) -> (Q `<=` P) -> P = Q.
Admitted.

Lemma poly_properEneq {P Q} :
  (P `<` Q) = (P `<=` Q) && (P != Q).
Proof.
Admitted.
(*apply/idP/andP => [/poly_properP [/poly_subsetP ?] [x x_in x_notin]| [P_sub_Q P_neq_Q] ].
- split; first done.
  apply/negP => P_eq_Q; rewrite (poly_equivP P_eq_Q) in x_notin.
  by move/negP: x_notin.
- apply/andP; split; first done.
  move: P_neq_Q; apply: contra.
  exact: poly_subset_anti.
Qed.*)

Lemma poly_properW P Q :
  (P `<` Q) -> (P `<=` Q).
Admitted.

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
Admitted.

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


(*Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
move=> non_empty_P.
have P_neq0 : ~~ (`[ poly0 ]) \repr P.
  apply/contraT; rewrite -subset0N_proper negbK => /PolyPred.poly_subsetP empty_P.
  move/poly_subsetPn: non_empty_P => [x].
  by move/empty_P; rewrite !inE.
apply: (iffP (pointedPn P_neq0)) => [[c [? incl]] | [c [? incl]]];
  exists c; split; try by done.
- move => μ μ_in_P λ.
  apply/(PolyPred.poly_subsetP _ _ _ (incl _ μ_in_P))/in_lineP.
  by exists λ.
- move => Ω Ω_in_P.
  apply/PolyPred.poly_subsetP => x /in_lineP [μ ->].
  exact: incl.
Qed.*)


Lemma pointedPn P :
  (P `>` `[poly0]) ->
    reflect (exists c, (c != 0) /\ (forall Ω,  Ω \in P -> (`[line c & Ω] `<=` P))) (~~ (pointed P)).
(*RK : I had to add the non_emptiness assumption because now pointed only makes sense under this assumption. I also slightly modified statement*)
Proof. (* RK *)
Admitted.
 (* rewrite -subset0N_proper => non_empty_P.
apply: (iffP (PolyPred.pointedPn non_empty_P)) => [[c [? incl]] | [c [? incl]]];
  exists c; split; try by done.
- move => Ω Ω_in_P.
  apply/poly_subsetP => x /in_lineP [μ ->].
  exact: incl.
- move => μ μ_in_P λ.
  apply/(poly_subsetP (incl _ μ_in_P))/in_lineP.
  by exists λ.
Qed.*)

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

Lemma convexP2 (P : 'poly[R]_n) (v w : 'cV[R]_n) :
  v \in P -> w \in P -> conv ([fset v; w]%fset) `<=` P.
Admitted.

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
Admitted.

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
  (*(P `>` `[poly0]) ==> *)
  [forall i, (bounded P (delta_mx i 0)) && (bounded P (-(delta_mx i 0)))].

Lemma compactP_Linfty P :
  (P `>` `[poly0]) ->
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Admitted.

Lemma compactP P :
  reflect ((*(P `>` `[poly0]) -> *)
      forall c, bounded P c) (compact P).
Admitted.

Lemma compact_pointed P :
  (*(P `>` `[poly0]) -> *) compact P -> pointed P. (* RK *)
Admitted.

Lemma compact_conv (V : {fset 'cV[R]_n}) : (*('|V|%fset > 0)%N ->*) compact (conv V).
Admitted.

Lemma compact_pt (Ω : 'cV[R]_n) : compact (`[pt Ω]).
Admitted.

Definition slice (b : base_elt) P := `[hp b] `&` P.

Lemma slice0 (b : base_elt) : slice b (`[poly0]) = `[poly0].
Admitted.

(*
Definition nth_hs (m : nat) (base: m.-base) i : T :=
  `[hs (row i base.1)^T & (base.2 i 0)].

Definition nth_hp (m : nat) (base: m.-base) i : T :=
  `[hp (row i base.1)^T & (base.2 i 0)].

Lemma in_nth_hs (m : nat) (A : 'M_(m,n)) (b : 'cV_m) i x :
  x \in (nth_hs (A, b) i) = ((A *m x) i 0 >= b i 0).
Proof.
by rewrite inE /= row_vdot.
Qed.

Lemma in_nth_hp (m : nat) (A : 'M_(m,n)) (b : 'cV_m) i x :
  x \in (nth_hp (A, b) i) = ((A *m x) i 0 == b i 0).
Proof.
by rewrite inE /= row_vdot.
Qed.
 *)

Definition poly_of_base (base : base_t) :=
  \polyI_(b : base) `[hs (val b)].

Notation "''P' ( base )" := (poly_of_base base) (at level 0) : poly_scope.

Definition in_poly_of_base x (base : base_t) :
  (x \in 'P(base)) = [forall b : base, x \in `[hs (val b)]].
Proof.
by rewrite in_big_polyI.
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
Admitted.
(*
by rewrite in_polyEq; apply: (equivP andP);
  split; move => [/forall_inP x_sat x_in_PAb].
Qed.*)

Lemma polyEq_eq x base I e :
  x \in 'P^=(base; I) -> e \in I -> x \in `[hp e].
Proof.
by move/in_polyEqP => [x_act _ ?]; apply: x_act.
Qed.

Lemma polyEq0 {base : base_t} :
  'P^=(base; fset0) = 'P(base).
Admitted.

Lemma polyEq_antimono (base I I' : base_t[R,n]) :
  (I `<=` I')%fset -> 'P^=(base; I') `<=` 'P^=(base; I).
Proof.
Admitted.

Lemma polyEq_antimono0 {base I : base_t[R,n]} :
  'P^=(base; I) `<=` 'P(base).
Proof.
Admitted.

Lemma polyEq_polyI {base I I': base_t[R,n]} :
  'P^=(base; I) `&` 'P^=(base; I') = 'P^=(base; (I `|` I')%fset).
Admitted.

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
Admitted.

Lemma slice_polyEq {e : base_elt} {base I : base_t[R,n]} :
  slice e 'P^=(base; I) = 'P^=(e +|` base; e +|` I).
Admitted.

Definition baseEq (base I : base_t[R,n]) :=
  (base `|` ((@Base.opp_base_elt _ _) @` I))%fset.

Lemma polyEq_flatten (base : base_t[R,n]) (I : {fsubset base}) :
  'P^=(base; I) = 'P(baseEq base I)%fset.
Admitted.

Lemma polyEq_of_polyEq (base : base_t[R,n]) (I : {fsubset base}) (J : {fsubset (baseEq base I)}) :
  exists K : {fsubset base}, 'P^=(baseEq base I; J) = 'P^=(base; K).
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

Definition pweight (w : {fsfun base_elt[R,n] -> R for fun => 0%R}) :=
  (finsupp w `<=` base)%fset && [forall v : base, w (val v) >= 0].
Implicit Type w : {fsfun base_elt[R,n] -> R for fun => 0%R}.

Definition combine w : base_elt :=
  (\sum_(v <- base) (w v) *: (fst v), \sum_(v <- base) (w v) * (snd v)).

Lemma dual_opt_sol (c : 'cV[R]_n) (H : bounded 'P(base) c) :
    exists2 w, pweight w & combine w = (c, opt_value H).
Admitted.
(*Proof.
move: (H) => H0. (* duplicate assumption *)
move: H; rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _ .
by move/and3P => [opt_point_in_P /andP [/eqP Au_eq_c u_le0] /eqP eq_value]; exists u.
Qed.*)

Lemma dual_sol_lower_bound w :
  pweight w -> 'P(base) `<=` `[hs (combine w)].
Proof.
Admitted.
(*  move => u_ge0; apply/poly_subsetP => x x_in.
by rewrite inE -vdot_mulmx vdotC; apply: vdot_lev;
  last by rewrite in_poly_of_base in x_in.
Qed.*)

Lemma dual_sol_bounded w :
  ('P(base) `>` `[poly0]) -> pweight w -> bounded 'P(base) (fst (combine w)).
Proof.
Admitted.
(*  move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists '[b,u]; exact: dual_sol_lower_bound.
Qed.*)

Variable (w : {fsfun base_elt[R,n] -> R for fun => 0%R}).
Hypothesis w_ge0 : pweight w.
Variable (I : {fsubset base}).
Hypothesis w_supp : forall v, (w v > 0) = (v \in (I : {fset _})).

Lemma compl_slack_cond x :
  x \in 'P(base) -> reflect (x \in `[hp (combine w)]) (x \in 'P^=(base; I)).
Admitted.

Lemma dual_sol_argmin :
  ('P^=(base; I) `>` `[poly0]) -> argmin 'P(base) (fst (combine w)) = 'P^=(base; I).
Proof.
Admitted.
(*move => PI_non_empty.
have P_non_empty : (('P(A,b) : T) `>` `[poly0]).
- apply: (poly_proper_subset PI_non_empty); exact: polyEq_antimono0.
move/proper0P : PI_non_empty => [x x_in_PI].
set c := _ *m _; have c_bounded := (dual_sol_bounded P_non_empty u_ge0).
rewrite argmin_polyI.
suff ->: opt_value c_bounded = '[b,u].
- apply/poly_equivP => y; rewrite inE.
  apply/andP/idP => [[y_in_P c_y_eq]| y_in_PI].
  + apply/compl_slack_cond => //.
    by rewrite ?inE in c_y_eq; apply/eqP.
  + have y_in_P: y \in ('P(A,b) : T).
    * move: y y_in_PI; apply/poly_subsetP; exact: polyEq_antimono0.
    split; first by done.
    by rewrite inE; apply/eqP/compl_slack_cond.
- have x_in_P : x \in ('P(A,b) : T).
  + move: x x_in_PI; apply/poly_subsetP; exact: polyEq_antimono0.
  apply/eqP; rewrite eqr_le; apply/andP; split.
  - have <- : '[c,x] = '[b,u] by apply/compl_slack_cond.
    move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound c_bounded).
    by rewrite inE.
  - move: (opt_point c_bounded) => [y y_in_P <-].
    move/poly_subsetP/(_ _ y_in_P): (dual_sol_lower_bound u_ge0).
    by rewrite inE.
Qed.
*)

(*
Lemma opt_value_csc (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) (x : 'cV[R]_n) :
  u >=m 0 -> x \in 'P(A,b) ->
    let c := A^T *m u in
      reflect (forall i, u i 0 > 0 -> (A *m x) i 0 = b i 0)
              ('[c,x] == '[b, u]).
Proof.
move => u_ge0 x_in_P /=.
have u_in_dual : u \in Simplex.dual_polyhedron A (A^T *m u)
 by rewrite inE eq_refl.
rewrite -subr_eq0 (Simplex.compl_slack_cond_duality_gap_equiv x_in_P u_in_dual).
apply/(iffP idP).
(* stupid proof, because of the fact that compl_slack_cond has not the right formulation (and compl_slack_condP doesn't help) *)
- move => Hcsc i u_i_gt0.
  move/forallP/(_ i): Hcsc; rewrite inE.
  by move/lt0r_neq0/negbTE: u_i_gt0 => -> /= /eqP.
- move => Hcsc; apply/forallP => i; rewrite -[X in X || _]negbK.
  have ->: (u i 0 != 0) = (u i 0 > 0)
      by rewrite lt0r; move/gev0P/(_ i): u_ge0 ->; rewrite andbT.
  by rewrite -implybE; apply/implyP; rewrite inE; move/Hcsc ->.
Qed.*)

End Duality.


(*
Section ProperPolyhedron.

Local Open Scope poly_scope.

Section Def.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Implicit Types phT : phant T.

Inductive ppoly phT := Ppoly { ppval :> T; _ : ppval `>` `[poly0] }.

End Def.

Notation "'{ppoly'  T '}'" := (@ppoly _ _ _ (Phant T)) (at level 0) : poly_scope.
(*Notation "\ptval" := (@ptval _ _ _ (Phant _)).*)

Section BasicProperties.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Canonical ppoly_subType := [subType for (@ppval _ _ T (Phant T))].
Definition ppoly_eqMixin := Eval hnf in [eqMixin of {ppoly T} by <:].
Canonical ppoly_eqType := Eval hnf in EqType {ppoly T} ppoly_eqMixin.
Definition ppoly_choiceMixin := Eval hnf in [choiceMixin of {ppoly T} by <:].
Canonical ppoly_choiceType := Eval hnf in ChoiceType {ppoly T} ppoly_choiceMixin.

Lemma ppolyP (P : {ppoly T}) : (P `>` `[poly0]).
Proof.
exact: valP.
Qed.

End BasicProperties.
End ProperPolyhedron.

Notation "'{ppoly'  T '}'" := (@ppoly _ _ _ (Phant T)) (at level 0) : poly_scope.

Section Test.

Local Open Scope poly_scope.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Definition ppoly_of (x : T) (b : (x `>` `[poly0])) & (phantom (x `>` `[poly0]) b) : {ppoly T} :=
                               @Ppoly  _ _ _ (Phant T) x b.
Notation "P %:ppoly" := (@ppoly_of P _ (Phantom _ _)) (at level 0) : poly_scope.

Class expose (P : Prop) := Expose : P.
Hint Mode expose ! : typeclass_instances.
Hint Extern 0 (expose _) => (exact) : typeclass_instances.
Lemma exposeP (P : Prop) : P -> expose P. Proof. by []. Qed.

Inductive foo := Foo { P : bool; _ : P}.
Variable P : T.
Hypothesis toto : (P `>` `[poly0]).

Canonical fooT := Foo toto.

(*
Lemma fooP P (b : foo P) : P.
by case : b.
Qed.*)
Canonical bar (P : T) (b : expose (P `>` `[poly0])) := @Ppoly _ _ _ (Phant T) P b.

Require Import Recdef.

Lemma bar' : (P%:ppoly) = P :> T.

Check bar.


Lemma bar (b : fo := foo (P `>` `[polyØ])

End Test.
*)



(*
Section OtherProperties.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).





Canonical polyt_pt (Ω : 'cV[R]_n) := Polyt (Phant T) (compact_pt Ω).
Canonical polyt_conv (V : {fset 'cV[R]_n}) := Polyt (Phant T) (compact_conv V).
Canonical polyt_class (P : {polyt T}) :=
  Polyt (Phant 'poly[R]_n) (eq_imply2 (compact_mono P) (polytP P)).
Definition polyt_of (P : T) (b : (compact P) ) & (phantom (compact P) b) := Polyt (Phant T) b.
Notation "P %:polyt" := (@polyt_of P _ (Phantom (compact P) _)) (at level 0) : poly_scope.

Variable is_face : T -> bool.
 Instance foo (P : T) (b : is_face P) : expose (compact P).
Admitted.
Canonical fooP P (b : is_face P) := Polyt (Phant _) (foo b).
Variable P : T.
Hypothesis (b : compact P).
Let ph := Phantom (compact P) b.
Set Printing All.
Goal (P%:polyt `>` `[poly0]).
apply: polyt_proper0.


Variable (P : T).
Hypothesis b : is_face P.
Eval simpl in (val (fooP b)).

Goal (P `>` `[poly0]).
apply: polyt_proper0.

Instance b' : expose (compact P). exact: exposeP. Qed.
Check (P %:polyt).

Goal ('[ P%:polyt ] `>` `[poly0]).
exact: polyt_proper0.
Qed.

End BasicProperties.
*)
