(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm.
Require Import extra_misc inner_product vector_order extra_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Delimit Scope poly_scope with PH.

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

Module ChoicePred.
Section ClassDef.

Variable V : Type.

Structure mixin_of (T : Type) :=
  Mixin { mem : T -> pred V }.

Record class_of (T : Type) : Type :=
  Class { base : Choice.class_of T;
          mixin : mixin_of T }.

Local Coercion base : class_of >-> Choice.class_of.

Structure type  := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Coercion mixin : class_of >-> mixin_of.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun pT & @pred_sort V pT -> T =>
    fun a mP (pT' := @PredType _ T a mP) & phant_id pT' pT =>
      fun b bT & phant_id (Choice.class bT) b =>
        Pack (Class b (Mixin a)).

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition pred_of_type := @mkPredType _ cT (mem xclass).
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Coercion pred_of_type : type >-> predType.
Canonical pred_of_type.
Notation choicePredType V := (type V).
Notation ChoicePredType V T := (@pack V T _ id _ _ id _ _ id).
Notation "[ 'choicePredType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'choicePredType'  'of'  T ]") : form_scope.
End Exports.
End ChoicePred.

Export ChoicePred.Exports.

Module PolyPred.

Section ClassDef.

Variable (R : realFieldType) (n : nat).

Structure mixin_of (T : choicePredType 'cV[R]_n) := Mixin {
  poly0 : T; in_poly0 : poly0 =i pred0;
  polyT : T; in_polyT : polyT =i predT;
  polyI : T -> T -> T;
  in_polyI : forall P Q, (polyI P Q) =i [predI P & Q];
  poly_subset : rel T;
  poly_subsetP : forall P Q, reflect {subset P <= Q} (poly_subset P Q);
  poly_subsetPn : forall P Q, reflect (exists2 x, (x \in P) & (x \notin Q)) (~~ (poly_subset P Q));
  mk_hs : 'cV[R]_n -> R -> T;
  in_hs : forall c d x, x \in (mk_hs c d) = ('[c,x] >= d);
  bounded : T -> 'cV[R]_n -> bool;
  boundedP : forall P c, reflect (exists2 x, x \in P & poly_subset P (mk_hs c '[c,x])) (bounded P c);
  boundedPn : forall P c, ~~ (poly_subset P poly0) -> reflect (forall K, ~~ (poly_subset P (mk_hs c K))) (~~ bounded P c);
  pointed : pred T;
  pointedPn : forall P, reflect (exists (c x : 'cV[R]_n), (forall μ, x + μ *: c \in P)) (~~ pointed P)
}.

Record class_of (T : Type) : Type :=
  Class { base : ChoicePred.class_of 'cV[R]_n T;
          mixin : mixin_of (ChoicePred.Pack base) }.
Local Coercion base : class_of >-> ChoicePred.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Local Coercion mixin : class_of >-> mixin_of.

Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@ChoicePred.Pack 'cV[R]_n T b0)) :=
  fun bT b & phant_id (@ChoicePred.class 'cV[R]_n bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition choicePredType := @ChoicePred.Pack 'cV[R]_n cT xclass.
Definition pred_of_type := @mkPredType _ cT (ChoicePred.mem xclass).
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ChoicePred.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion pred_of_type : type >-> predType.
Coercion choicePredType : type >-> ChoicePred.type.
Canonical eqType.
Canonical choiceType.
Canonical pred_of_type.
Canonical choicePredType.
Notation polyPredType R n := (@type _ n (Phant R)).
Notation polyPredMixin := mixin_of.
Notation PolyPredType R n m := (@pack _ n (Phant R) _ _ m _ _ id _ id).
Notation "[ 'polyPredType' 'of' T ]" := (@clone _ _ _ T _ _ id)
  (at level 0, format "[ 'polyPredType'  'of'  T ]") : form_scope.
End Exports.
End PolyPred.

Export PolyPred.Exports.

Section PolyPredProperties.

Context {R : realFieldType} {n : nat} {T : polyPredType R n}.

Definition poly0 := PolyPred.poly0 (PolyPred.class T).
Definition polyT := PolyPred.polyT (PolyPred.class T).
Definition polyI := PolyPred.polyI (PolyPred.class T).
Definition poly_subset := PolyPred.poly_subset (PolyPred.class T).
Definition mk_hs := PolyPred.mk_hs (PolyPred.class T).
Definition bounded := PolyPred.bounded (PolyPred.class T).
Definition pointed := PolyPred.pointed (PolyPred.class T).

Definition poly_equiv (P Q : T) := (poly_subset P Q) && (poly_subset Q P).
Definition poly_proper (P Q : T) := ((poly_subset P Q) && (~~ (poly_subset Q P))).

Local Open Scope poly_scope.

Notation "'`[' 'poly0' ']'" := poly0 (at level 70) : poly_scope.
Notation "'`[' 'polyT' ']'" := polyT (at level 70) : poly_scope.
Notation "P `&` Q" := (polyI P Q) (at level 48, left associativity) : poly_scope.
Notation "P `<=` Q" := (poly_subset P Q) (at level 70, no associativity) : poly_scope.
Notation "P `>=` Q" := (Q `<=` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `=~` Q" := (poly_equiv P Q) (at level 70, no associativity) : poly_scope.
Notation "P `!=~` Q" := (~~ (poly_equiv P Q)) (at level 70, no associativity) : poly_scope.
Notation "P `<` Q" := (poly_proper P Q) (at level 70, no associativity) : poly_scope.
Notation "P `>` Q" := (Q `<` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "'`[' 'hs'  c & d  ']'" := (mk_hs c d) (at level 70) : poly_scope.

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

Lemma in_poly0 : (`[poly0] : T) =i pred0.
Proof.
exact: (PolyPred.in_poly0 (PolyPred.class T)).
Qed.

Lemma in_polyT : (`[polyT] : T) =i predT.
Proof.
exact: (PolyPred.in_polyT (PolyPred.class T)).
Qed.

Lemma in_polyI (P Q : T) : (P `&` Q) =i [predI P & Q].
Proof.
exact: (PolyPred.in_polyI (PolyPred.class T)).
Qed.

Lemma poly_subsetIl (P Q : T) : P `&` Q `<=` P.
Admitted.

Lemma poly_subsetIr (P Q : T) : P `&` Q `<=` Q.
Admitted.

Lemma polyIS (P P' Q : T) : P `<=` P' -> Q `&` P `<=` Q `&` P'.
Admitted.

Lemma polySI (P P' Q : T) : P `<=` P' -> P `&` Q `<=` P' `&` Q.
Admitted.

Lemma poly_subsetIP (P Q Q' : T) : reflect (P `<=` Q /\ P `<=` Q') (P `<=` Q `&` Q').
Admitted.

Lemma in_big_polyI (I : finType) (P : pred I) (F : I -> T) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \polyI_(i | P i) (F i)).
Proof.
have -> : (x \in \polyI_(i | P i) F i) = (\big[andb/true]_(i | P i) (x \in (F i))).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?in_polyT ?in_polyI.
rewrite big_all_cond; apply: (iffP allP) => /= H i;
have := H i _; rewrite mem_index_enum; last by move/implyP->.
by move=> /(_ isT) /implyP.
Qed.

Lemma big_poly_inf (I : finType) (j : I) (P : pred I) (F : I -> T) :
  P j -> (\polyI_(i | P i) F i) `<=` F j.
Admitted.

Lemma big_polyI_min (I : finType) (j : I) (Q : T) (P : pred I) (F : I -> T) :
  P j -> (F j `<=` Q) -> \polyI_(i | P i) F i `<=` Q.
Admitted.

Lemma big_polyIsP (I : finType) (Q : T) (P : pred I) (F : I -> T) :
  reflect (forall i : I, P i -> Q `<=` F i) (Q `<=` \polyI_(i | P i) F i).
Admitted.

Lemma in_hs c d x : x \in (`[hs c & d] : T) = ('[c,x] >= d).
Proof.
exact: (PolyPred.in_hs (PolyPred.class T)).
Qed.

Lemma notin_hs c d x : x \notin (`[hs c & d] : T) = ('[c,x] < d).
Proof.
by rewrite in_hs ltrNge.
Qed.

Definition mk_hp c d : T := `[hs c & d] `&` `[hs (-c) & (-d)].

Notation "'`[' 'hp'  c & d  ']'" := (mk_hp c d) (at level 70) : poly_scope.

Lemma in_hp c d x : x \in (`[hp c & d] : T) = ('[c,x] == d).
Proof.
Admitted.

Let inE := (in_poly0, in_polyT, in_polyI, in_hp,  in_hs, inE).

Lemma poly_subsetP {P Q : T} : reflect {subset P <= Q} (P `<=` Q).
Proof.
exact: (PolyPred.poly_subsetP (PolyPred.class T)).
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

Lemma poly_subset_hsP {P : T} {c d} :
  reflect (forall x, x \in P -> '[c,x] >= d) (P `<=` `[hs c & d]).
Proof.
apply: (iffP poly_subsetP) => [sub x x_in_P | sub x x_in_P ];
  move/(_ _ x_in_P): sub; by rewrite in_hs.
Qed.

Lemma poly_equivP {P Q : T} : reflect (P =i Q) (P `=~` Q).
Proof.
apply/(iffP andP) => [[/poly_subsetP P_le_Q /poly_subsetP Q_le_P] x | P_eq_Q ].
- apply/idP/idP; [exact: P_le_Q | exact: Q_le_P].
- by split; apply/poly_subsetP => x; rewrite P_eq_Q.
Qed.

Lemma poly_equiv_refl : reflexive poly_equiv.
Proof.
by move => P; apply/poly_equivP.
Qed.

Lemma poly_equiv_sym : symmetric poly_equiv.
Proof.
by move => P Q; apply: (sameP poly_equivP);
   apply: (iffP poly_equivP) => [H x | H x]; rewrite H.
Qed.

Lemma poly_equiv_trans : transitive poly_equiv.
Proof.
move => P' P P'' /poly_equivP P_eq_P' /poly_equivP P'_eq_P''.
by apply/poly_equivP => x; rewrite P_eq_P'.
Qed.

Lemma poly0_subset (P : T) : `[poly0] `<=` P.
Proof.
by apply/poly_subsetP => x; rewrite inE.
Qed.

Lemma poly_subsetPn {P Q : T} :
  reflect (exists2 x, x \in P & (x \notin Q)) (~~ (P `<=` Q)).
Proof.
exact: (PolyPred.poly_subsetPn (PolyPred.class T)).
Qed.

Lemma proper0N_equiv (P : T): ~~ (P `>` `[poly0]) = (P `=~` `[poly0]).
Admitted.

Lemma subset0N_proper (P : T): ~~ (P `<=` `[poly0]) = (P `>` `[poly0]).
Admitted.

Lemma equiv0N_proper (P : T) : (P `!=~` `[poly0]) = (P `>` `[poly0]).
Admitted.

Lemma subset0_equiv (P : T) : (P `<=` `[poly0]) = (P `=~` `[poly0]).
Admitted.

CoInductive empty_spec (P : T) : bool -> bool -> bool -> Set :=
| Empty of (P =i `[poly0]) : empty_spec P false true true
| NonEmpty of (P `>` `[poly0]) : empty_spec P true false false.

Lemma emptyP (P : T) : empty_spec P (P  `>` `[poly0]) (P `=~` `[poly0]) (P `<=` `[poly0]).
Proof.
case: (boolP (P  `>` `[poly0])) => [P_non_empty | P_empty].
- rewrite -subset0N_proper in P_non_empty; move: (P_non_empty) => /negbTE ->.
  rewrite subset0_equiv in P_non_empty; move: (P_non_empty) => /negbTE ->.
  by constructor; rewrite equiv0N_proper in P_non_empty.
- rewrite proper0N_equiv in P_empty; rewrite subset0_equiv P_empty.
  by constructor; apply/poly_equivP.
Qed.

Lemma proper0P {P : T} :
  reflect (exists x, x \in P) (P `>` `[poly0]).
Proof.
rewrite -[_ `<` _]negbK proper0N_equiv -subset0_equiv.
apply/(iffP poly_subsetPn) => [[x] x_in x_notin | [x] x_in];
  exists x; by rewrite ?inE.
Qed.

Definition pick_point (P : T) :=
  match (@proper0P P) with
  | ReflectT P_non_empty => xchoose P_non_empty
  | ReflectF _ => 0
  end.

Lemma pick_pointP {P : T} :
  (P `>` `[poly0]) -> pick_point P \in P.
Proof. (* RK *)
rewrite /pick_point; case: proper0P => [? _ | _] //; exact: xchooseP.
Qed.

Lemma poly_properP {P Q : T} :
  reflect ({subset P <= Q} /\ exists2 x, x \in Q & x \notin P) (P `<` Q).
Proof.
apply: (iffP andP) =>
  [[/poly_subsetP ? /poly_subsetPn [x ??]] | [? [x ??]] ].
- by split; [ done | exists x].
- by split; [ apply/poly_subsetP | apply/poly_subsetPn; exists x].
Qed.

Lemma poly_properxx (P : T) : (P `<` P) = false.
Proof.
by rewrite /poly_proper poly_subset_refl.
Qed.

Lemma poly_proper_subset (P P' P'' : T) :
  (P `<` P') -> (P' `<=` P'') -> (P `<` P'').
Admitted.

Lemma poly_subset_proper (P P' P'' : T) :
  (P `<=` P') -> (P' `<` P'') -> (P `<` P'').
Admitted.

Lemma poly_proper_trans : transitive poly_proper.
Admitted.

Lemma boundedP {P : T} {c} :
  reflect (exists2 x, (x \in P) & (P `<=` `[hs c & '[c, x]])) (bounded P c).
Proof.
exact: (PolyPred.boundedP (PolyPred.class T)).
Qed.

Lemma boundedPP {P : T} {c} :
  reflect (exists x, (x \in P) && (P `<=` `[hs c & '[c, x]])) (bounded P c).
Proof.
by apply/(iffP boundedP) => [[x] ?? | [x] /andP [??]];
  exists x; first by apply/andP; split.
Qed.

Lemma boundedPn {P : T} {c} :
  (P `>` `[poly0]) -> reflect (forall K, exists2 x, x \in P & '[c,x] < K) (~~ bounded P c).
Proof.
rewrite -subset0N_proper; move => P_non_empty.
apply: (iffP (PolyPred.boundedPn _ P_non_empty)) => [H K | H K]; move/(_ K): H.
- move/poly_subsetPn => [x x_in_P x_not_in_hs].
  exists x; by rewrite notin_hs in x_not_in_hs.
- move => [x x_in_P c_x_lt_K].
  apply/poly_subsetPn; exists x; by rewrite ?notin_hs.
Qed.

Lemma bounded_mono1 (P Q : T) c :
  bounded P c -> Q `<=` P -> bounded Q c.
Admitted.

Definition opt_value (P : T) c (b : bounded P c) :=
  let x := xchoose (boundedPP b) in '[c,x].

Lemma opt_value_mono1 (P Q : T) c (b : bounded P c) (sub : Q `<=` P):
  opt_value b <= opt_value (bounded_mono1 b sub).
Admitted.

Lemma opt_point (P : T) c (b : bounded P c) :
  exists2 x, x \in P & '[c,x] = opt_value b.
Proof.
rewrite /opt_value; set x := xchoose _.
exists x; last by done.
by move: (xchooseP (boundedPP b)) => /andP [?].
Qed.

Lemma opt_value_lower_bound {P : T} {c} (b : bounded P c) :
  P `<=` (`[ hs c & opt_value b ]).
Proof.
by rewrite /opt_value; move/andP : (xchooseP (boundedPP b)) => [_].
Qed.

Definition argmin (P : T) c :=
  if @idP (bounded P c) is ReflectT H then
    P `&` `[hp c & opt_value H]
  else
    `[poly0].

Lemma argmin_polyI (P : T) c (b : bounded P c) :
  argmin P c = P `&` `[hp c & opt_value b].
Proof.
by rewrite /argmin; case: {-}_/idP => [b' | ?]; rewrite ?[b]eq_irrelevance.
Qed.

Lemma in_argmin P c x :
  x \in argmin P c = (x \in P) && (P `<=` `[hs c & '[c, x]]).
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
Admitted.

Lemma argmin_subset P c : argmin P c `<=` P.
Admitted.

Lemma argmin_lower_bound {c x y} (P : T) :
  x \in argmin P c -> y \in P -> '[c,x] <= '[c,y].
Admitted.
(*Proof.
by move/andP => [_ /poly_subset_hsP/(_ y)].
Qed.*)

Lemma argmin_eq {P : T} {c v x} :
  v \in argmin P c -> reflect (x \in P /\ '[c,x] = '[c,v]) (x \in argmin P c).
Admitted.


(*move => y y_in_P.
rewrite /opt_value; set x := xchoose _.
apply: (minimize_lower_bound (P := P)); [exact: (xchooseP (@boundedP _ _ _)) | done].
Qed.*)

Lemma bounded_lower_bound (P : T) c :
  (P `>` `[poly0]) -> reflect (exists d, P `<=` `[hs c & d]) (bounded P c).
Proof.
move => P_non_empty; apply: introP => [ c_bounded | /(boundedPn P_non_empty) c_unbouded ].
- exists (opt_value c_bounded); exact: opt_value_lower_bound.
- move => [d c_bounded]; move/(_ d): c_unbouded => [x x_in_P c_x_lt_K].
  by move/poly_subsetP/(_ _ x_in_P): c_bounded; rewrite in_hs lerNgt => /negP.
Qed.

Definition mk_line (c Ω : 'cV[R]_n) : T :=
  let S := kermx c in
  \polyI_(i < n) `[hp (row i S)^T & '[(row i S)^T, Ω]].

Notation "'`[' 'line'  c & Ω  ']'" := (mk_line c Ω) (at level 70) : poly_scope.
Notation "'`[' 'pt'  Ω  ']'" := (mk_line 0 Ω) (at level 70) : poly_scope.

Lemma in_lineP {c Ω x : 'cV[R]_n} :
  reflect (exists μ, x = Ω + μ *: c) (x \in `[line c & Ω]).
Proof.
apply: (iffP idP); last first.
- move => [μ ->]; apply/in_big_polyI => [i _]; rewrite in_hp; apply/eqP.
  rewrite vdotDr vdotZr.
  suff /matrixP/(_ 0 0): '[ (row i (kermx c))^T, c]%:M = 0 :> 'M_1
    by rewrite !mxE mulr1n => ->; rewrite mulr0 addr0.
  rewrite vdot_def -trmx_mul -trmx0; apply: congr1.
  apply/sub_kermxP; exact: row_sub.
- move/in_big_polyI => H.
  pose d := x - Ω; suff /sub_rVP [μ ]: (d^T <= c^T)%MS.
  rewrite -linearZ /= => /trmx_inj d_eq_mu_c.
  by exists μ; rewrite -d_eq_mu_c /d addrCA addrN addr0.
  rewrite submx_kermx !trmxK.
  apply/row_subP => i; apply/sub_kermxP.
  rewrite -[row _ _]trmxK -vdot_def vdotC [RHS]const_mx11; apply: congr1.
  move/(_ i isT): H; rewrite in_hp => /eqP.
  by rewrite /d vdotBr => ->; rewrite addrN.
Qed.

Lemma in_pt (Ω x : 'cV[R]_n) : (x \in `[pt Ω]) = (x == Ω).
Proof.
Admitted.

Lemma in_pt_self (Ω : 'cV[R]_n) : Ω \in `[pt Ω].
Admitted.

Lemma pointedPn {P : T} :
  reflect (exists c Ω, `[line c & Ω] `<=` P) (~~ (pointed P)).
Proof.
apply: (iffP (PolyPred.pointedPn _ _)) => [[c [Ω]] incl | [c [Ω]] /poly_subsetP incl]; exists c; exists Ω.
- apply/poly_subsetP => x /in_lineP [μ ->]; exact: incl.
- by move => μ; apply/incl/in_lineP; exists μ.
Qed.

Definition mk_hline (c Ω : 'cV[R]_n) : T :=
  `[hs c & '[c,Ω]] `&` `[line c & Ω].

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

Definition mk_segm (Ω Ω' : 'cV[R]_n) : T :=
  let c := Ω' - Ω in
  `[hs (-c) & '[-c, Ω']] `&` `[hline c & Ω].

Notation "'`[' 'segm'  Ω & Ω'  ']'" := (mk_segm Ω Ω') (at level 70) : poly_scope.

Lemma in_segmP (Ω Ω' x : 'cV[R]_n) :
  reflect (exists2 μ, 0 <= μ <= 1 & x = Ω + μ *: (Ω' - Ω)) (x \in `[segm Ω & Ω']).
Proof.
Admitted.

Definition compact (P : T) :=
  (P `>` `[poly0]) ==> [forall i, (bounded P (delta_mx i 0)) && (bounded P (-(delta_mx i 0)))].

Lemma compactP_Linfty (P : T) :
  reflect (exists K, forall x, x \in P -> forall i, `|x i 0| <= K) (compact P).
Admitted.

Lemma compactP P :
  reflect ((P `>` `[poly0]) -> forall c, bounded P c) (compact P).
Admitted.

Lemma compact_pointed P :
  (P `>` `[poly0]) -> compact P -> pointed P. (* RK *)
Admitted.

End PolyPredProperties.

Notation "'`[' 'poly0' ']'" := poly0 (at level 70) : poly_scope.
Notation "'`[' 'polyT' ']'" := polyT (at level 70) : poly_scope.
Notation "P `&` Q" := (polyI P Q) (at level 48, left associativity) : poly_scope.
Notation "P `<=` Q" := (poly_subset P Q) (at level 70, no associativity) : poly_scope.
Notation "P `>=` Q" := (Q `<=` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "P `=~` Q" := (poly_equiv P Q) (at level 70, no associativity) : poly_scope.
Notation "P `!=~` Q" := (~~ (poly_equiv P Q)) (at level 70, no associativity) : poly_scope.
Notation "P `<` Q" := (poly_proper P Q) (at level 70, no associativity) : poly_scope.
Notation "P `>` Q" := (Q `<` P)%PH (at level 70, no associativity, only parsing) : poly_scope.
Notation "'`[' 'hs'  c & d  ']'" := (mk_hs c d) (at level 70) : poly_scope.
Notation "'`[' 'hp'  c & d  ']'" := (mk_hp c d) (at level 70) : poly_scope.
Notation "'`[' 'line'  c & Ω  ']'" := (mk_line c Ω) (at level 70) : poly_scope.
Notation "'`[' 'pt'  Ω  ']'" := (mk_line 0 Ω) (at level 70) : poly_scope.
Notation "'`[' 'hline'  c & Ω  ']'" := (mk_hline c Ω) (at level 70) : poly_scope.
Notation "'`[' 'segm'  Ω & Ω'  ']'" := (mk_segm Ω Ω') (at level 70) : poly_scope.

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

Hint Resolve poly_equiv_refl : core.

Module Quotient.

Local Open Scope poly_scope.


Section Def.

Context {R : realFieldType} {n : nat} {T : polyPredType R n}.
Implicit Types (phT : phant T).

Definition canon (P : T) :=
  choose (poly_equiv P) P.

Structure quot phT := Poly {
  repr : T;
  _ : canon repr == repr;
}.

End Def.

Notation "'{quot'  T '}'" := (@quot _ _ _ (Phant T)) (at level 0).
Notation "\repr" := (@repr _ _ _ (Phant _)) (at level 0).

Section BasicProperties.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Canonical quot_subType := [subType for (@repr _ _ _ (Phant T))].
Definition quot_eqMixin := Eval hnf in [eqMixin of {quot T} by <:].
Canonical quot_eqType := Eval hnf in EqType {quot T} quot_eqMixin.
Definition quot_choiceMixin := Eval hnf in [choiceMixin of {quot T} by <:].
Canonical quot_choiceType := Eval hnf in ChoiceType {quot T} quot_choiceMixin.

Lemma repr_inj : injective (\repr : {quot T} -> T).
Proof.
exact: val_inj.
Qed.

Lemma canon_id (P : T) :
  canon (canon P) == canon P.
Proof.
rewrite /canon; set Q := choose (poly_equiv P) P.
have P_eq_Q: (P `=~` Q) by apply : chooseP; exact: poly_equiv_refl.
suff /eq_choose ->: poly_equiv Q =1 poly_equiv P
  by apply/eqP; apply: choose_id; try exact: poly_equiv_refl.
move => x.
by apply/idP/idP; apply: poly_equiv_trans; last by rewrite poly_equiv_sym.
Qed.

Definition class_of P := Poly (Phant T) (canon_id P).
Notation "''[' P  ]" := (class_of P) (at level 0).

Lemma reprK (P : {quot T}) :
  '[\repr P] = P.
Proof.
case: P => [P P_eq]; apply: repr_inj; exact: eqP.
Qed.

Lemma repr_equiv (P : T) : \repr '[P] =i P.
Proof.
by move: (chooseP (poly_equiv_refl P)); rewrite poly_equiv_sym => /poly_equivP.
Qed.


Definition mem (P : {quot T}) := (mem (\repr P)) : pred 'cV[R]_n.
Canonical quot_predType := mkPredType mem.
Canonical quot_choicePredType := ChoicePredType 'cV[R]_n {quot T}.

Lemma quotP (P Q : T) : '[P] = '[Q] <-> P `=~` Q.
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

Notation "''[' P  ]" := (class_of P) : poly_scope.

Section PolyPredStructure.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Implicit Types P : {quot T}.

Definition poly0 : {quot T} := '[ `[poly0] ].
Definition polyT : {quot T} := '[ `[polyT] ].
Definition polyI P Q : {quot T} := '[ (\repr P) `&` (\repr Q) ].
Definition poly_subset (P Q : {quot T}) := (\repr P) `<=` (\repr Q).
Definition mk_hs c d : {quot T} := '[ `[hs c & d] ].
Definition bounded P c := bounded (\repr P) c.
Definition pointed P := pointed (\repr P).

Let inE := (repr_equiv, @in_poly0, @in_polyT, @in_polyI, @in_hs, inE).

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => ?; rewrite !inE.
Qed.

Lemma in_polyT : polyT =i predT.
Proof.
by move => ?; rewrite !inE.
Qed.

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
by move => x; rewrite !inE.
Qed.

Lemma poly_subsetP P Q : reflect {subset P <= Q} (poly_subset P Q).
Proof.
by apply: (iffP poly_subsetP) => [H x | H x]; exact: H.
Qed.

Lemma poly_subsetPn P Q :
  reflect (exists2 x, (x \in P) & (x \notin Q)) (~~ (poly_subset P Q)).
Proof.
apply: (iffP poly_subsetPn) => [[x] H | [x] H]; exists x; by rewrite !inE in H *.
Qed.

Lemma in_hs c d x : x \in (mk_hs c d) = ('[c,x] >= d).
Proof.
by rewrite !inE.
Qed.

Lemma boundedP P c :
  reflect (exists2 x, x \in P & poly_subset P (mk_hs c '[c,x])) (bounded P c).
Proof.
have eq x : poly_subset P (mk_hs c '[ c, x]) = (repr P `<=` (`[ hs c & '[ c, x] ]))
  by apply: (sameP (poly_subsetP _ _));
     apply: (iffP (PolyPred.poly_subsetP _ _ _)) => sub z;
     move/(_ z): sub; rewrite !inE.
by apply: (iffP boundedP) => [[x] H H' | [x] H H']; exists x; rewrite ?inE ?eq in H' *.
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) -> reflect (forall K, ~~ (poly_subset P (mk_hs c K))) (~~ bounded P c).
Admitted.

Lemma pointedPn P :
  reflect (exists (c x : 'cV[R]_n), (forall μ, x + μ *: c \in (mem P))) (~~ pointed P).
Proof.
apply: (iffP pointedPn) => [[c [Ω]] H| [c [Ω]] H]; exists c; exists Ω.
- by move => μ; apply/(PolyPred.poly_subsetP _ _ _ H) ; apply/in_lineP; exists μ.
- by apply/(PolyPred.poly_subsetP _ _ _) => x /in_lineP [μ ->].
Qed.

Definition quot_polyPredMixin :=
  PolyPred.Mixin in_poly0 in_polyT in_polyI poly_subsetP poly_subsetPn
                 in_hs boundedP boundedPn pointedPn.
Canonical quot_polyPredType := PolyPredType R n quot_polyPredMixin.

End PolyPredStructure.

Module Import Exports.
Canonical quot_subType.
Canonical quot_eqType.
Canonical quot_choiceType.
Canonical quot_predType.
Canonical quot_choicePredType.
Canonical quot_polyPredType.
Notation "'{quot'  T '}'" := (@quot _ _ _ (Phant T)) (at level 0).
Notation "\repr" := (@repr _ _ _ (Phant _)) (at level 0).
Notation "''[' P  ]" := (class_of P) (at level 0).
Notation reprK := reprK.
Notation repr_inj := repr_inj.
Notation repr_equiv := repr_equiv.
Notation quotP := quotP.
End Exports.
End Quotient.

Export Quotient.Exports.

Definition inE := (repr_equiv, @in_poly0, @in_polyT, @in_polyI, @in_hp, @in_hs, inE).

Section QuotientProperties.

Local Open Scope poly_scope.

Context {R : realFieldType} {n : nat} {T : polyPredType R n}.

Lemma quot_equivP (P Q : {quot T}) : (P `=~` Q) -> P = Q.
Admitted.

Lemma poly_subset_mono (P Q : T) : ('[P] `<=` '[Q]) = (P `<=` Q).
Proof.
by apply: (sameP poly_subsetP); apply: (iffP poly_subsetP) => [ H x | H x];
move/(_ x): H; rewrite !inE.
Qed.

Lemma poly_proper_mono (P Q : T) : ('[P] `<` '[Q]) = (P `<` Q).
Proof.
Admitted.

Lemma bounded_mono (P : T) c : bounded '[P] c = bounded P c.
Proof.
by apply: (sameP boundedP); apply: (iffP boundedP) => [[x] H H' | [x] H H'];
  exists x; rewrite ?inE ?poly_subset_mono in H H' *.
Qed.

Lemma polyI_mono (P Q : T) : '[P] `&` '[Q] = '[P `&` Q].
Proof.
by apply/quotP/poly_equivP => x; rewrite !inE.
Qed.

Lemma big_polyI_mono (I : finType) (P : pred I) (F : I -> T) :
  \polyI_(i | P i) '[F i] = '[\polyI_(i | P i) (F i)].
Proof.
rewrite (@big_morph _ _ _ (`[polyT] : {quot T}) (polyI : {quot T} -> {quot T} -> {quot T})) //.
by move => Q Q'; rewrite polyI_mono.
Qed.

Lemma hs_mono (c : 'cV[R]_n) d : `[hs c & d] = '[`[hs c & d]] :> {quot T}.
Proof.
by apply/quotP/poly_equivP => x; rewrite inE.
Qed.

Lemma hp_mono (c : 'cV[R]_n) d : `[hp c & d] = '[`[hp c & d]] :> {quot T}.
Proof.
by apply/quot_equivP/poly_equivP => x; rewrite !inE.
Qed.

Lemma line_mono (c Ω : 'cV[R]_n) : `[line c & Ω] = '[`[line c & Ω]] :> {quot T}.
Proof.
apply/quot_equivP/poly_equivP => x. apply: (sameP in_lineP); rewrite !inE.
exact: in_lineP.
Qed.

Lemma argmin_mono (P : T) c : argmin '[P] c = '[argmin P c].
Admitted.

Lemma pointed_mono (P : T) : pointed '[P] = pointed P.
Proof.
apply: negb_inj.
by apply: (sameP pointedPn); apply: (iffP pointedPn) => [[c [Ω]] H | [c [Ω]] H];
  exists c; exists Ω; rewrite line_mono poly_subset_mono in H *.
Qed.

End QuotientProperties.

Definition quotE := (@poly_subset_mono, @poly_proper_mono, @bounded_mono,
                    @polyI_mono, @big_polyI_mono, @hs_mono, @line_mono,
                    @argmin_mono, @pointed_mono, @hp_mono).