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
Require Import extra_misc extra_matrix inner_product row_submx vector_order barycenter.

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

Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing).
(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
Hint Mode infer ! : typeclass_instances.
Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Module Base.

Section Base.

Variable (R : realFieldType) (n : nat).

Definition base_elt := ('cV[R]_n * R)%type.

Definition opp_base_elt (b : base_elt) : base_elt := (- (fst b), - (snd b)). (* TODO: we should have a notation for that *)

Definition base := {fset base_elt}.

Structure tagged_pair := Tag { untag : (base * base)%type}.
Local Coercion untag : tagged_pair >-> prod.
Structure wf_pair := Wf { tp : tagged_pair ; _ : (tp.2 `<=` tp.1)%fset}.
Local Coercion tp : wf_pair >-> tagged_pair.
Canonical sub_wf_pair := [subType for tp].

Definition wf_pair_of (p : wf_pair) & (phantom (base * base)%type p) : wf_pair := p.
Notation "b %:wf" := (wf_pair_of (Phantom _ b)) (at level 0).

Definition tag0 x := Tag x.
Definition tag1 x := tag0 x.
Definition tag2 x := tag1 x.
Definition tag3 x := tag2 x.
Definition tag4 x := tag3 x.
Definition tag5 x := tag4 x.
Canonical tag5.

(*Lemma wfE (p : wf_pair) :
  (p.1 `<=` p.2)%fset.
Admitted.
Canonical wfEP (p : wf_pair) := @Wf (tag5 (_,_)) (wfE p).

Variable p : wf_pair.
Check ((untag (tp p)) %:wf).
 *)

Lemma wfT (b : base) : (b `<=` b)%fset.
Admitted.
Canonical wfTP (b : base) := @Wf (tag1 (_,_)) (wfT b).

Lemma wf0 (b : base) : (fset0 `<=` b)%fset.
Admitted.
Canonical wf0P (b : base) := @Wf (tag2 (_, _)) (wf0 b).

Definition slice_pair  (e : base_elt) (p : (base * base)%type) :=
  (e |` p.1, e |` p.2)%fset.
Lemma wf_slice (e : base_elt) (x : wf_pair) : (e |` x.2 `<=` e |` x.1)%fset.
Admitted.
Canonical wf_sliceP (e : base_elt) (x : wf_pair) :=
  @Wf (tag3 (slice_pair e x)) (wf_slice e x).

Lemma wf_fset_subset (b : base) (base' : {fset b}) :
  ([fsetval x in base'] `<=` b)%fset.
Admitted.
Canonical wf_fset_subsetP (b : base) (base' : {fset b}) :=
  @Wf (tag4 (_, _)) (wf_fset_subset base').

Canonical wf_fset_inferP (b b' : base) (H : infer (b' `<=` b)%fset) := @Wf (tag0 (_, _)) H.

Section Test.
Variable (b : base) (e : base_elt) (b' : {fset b}) (b'' : base).
Check ((b, fset0)%:wf).
Check ((b, b)%:wf).
Check (slice_pair e (b, fset0)).
Check ((e |` (b, fset0).1, e |` (b, fset0).2)%fset %:wf).
(* Check ((e |` b, e |` fset0)%fset %:wf). *) (* TODO: ask Georges *)
Check (b, [fsetval x in b']%fset)%:wf.
Hypothesis H : (b'' `<=` b)%fset.
Check (b, b'')%:wf.
Lemma foo & infer (b'' `<=` b)%fset : (b, b'')%:wf = (b, b'')%:wf.
Admitted.

End Test.

End Base.

Module Import Exports.
Canonical sub_wf_pair.
Canonical tag5.
Canonical wfTP.
Canonical wf0P.
Canonical wf_sliceP.
Canonical wf_fset_subsetP.
Canonical wf_fset_inferP.
Coercion untag : tagged_pair >-> prod.
Coercion tp : wf_pair >-> tagged_pair.
End Exports.

End Base.

Export Base.Exports.

Notation "'base_elt' [ R , n ]" := (@Base.base_elt R n) (at level 2).
Notation "'base_elt'" := (base_elt[_,_]) (at level 2).
Notation "'base_t' [ R , n ]" := (@Base.base R n) (at level 2).
Notation "'base_t'" := (base_t[_,_]) (at level 2).
Notation "'wf_pair' [ R , n ]" := (@Base.wf_pair R n) (at level 2).
Notation "'wf_pair'" := (wf_pair[_,_]) (at level 2).
Notation "e ||` x" := (Base.slice_pair e x) (at level 70).
Notation "- e" := (Base.opp_base_elt e) : poly_scope.
Bind Scope poly_scope with Base.base_elt.
Notation "b %:wf" := (@Base.wf_pair_of _ _ _ (Phantom _ b)) (at level 0).

Section Test.
Variable (R : realFieldType) (n : nat).
Variable (b : base_t[R,n]) (e : base_elt[R,n])  (b' : base_t[R,n]).
Check ((b, fset0)%:wf).
Check ((b, b)%:wf).
Check (e ||` (b, fset0)).
Check ((e |` (b, fset0).1, e |` (b, fset0).2)%fset %:wf).
(* Check ((e |` b, e |` fset0)%fset %:wf). *) (* TODO: ask Georges *)
Check (-e).
Variable (x : R).
Check (-x).
Hypothesis H : (b' `<=` b)%fset.
Check (b, b')%:wf.
End Test.

Definition baseEq (R : realFieldType) (n : nat) (x : wf_pair[R,n]) : wf_pair :=
  (x.1 `|` ((@Base.opp_base_elt _ _) @` x.2), fset0)%fset %:wf.

Module ChoicePred.
Section ClassDef.

Variable V : Type.

Structure mixin_of (T : Type) :=
  Mixin { mem_pred_sort : T -> pred_sort (predPredType V) }.

Record class_of (T : Type) : Type :=
  Class { base : Choice.class_of T;
          mixin : mixin_of T }.

Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Coercion mixin : class_of >-> mixin_of.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun pT & @pred_sort V pT -> T =>
    fun a (pT' := @PredType _ T a) & phant_id pT' pT =>
      fun b bT & phant_id (Choice.class bT) b =>
        Pack (Class b (Mixin a)).

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pred_of_type := @mkPredType _ cT (mem_pred_sort xclass).
Definition pred_of (P : cT) : pred_sort _ := (mem_pred_sort xclass P).
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pred_of : sort >-> pred_sort.
Canonical eqType.
Canonical choiceType.
Canonical pred_of_type.
Notation choicePredType V := (type V).
Notation ChoicePredType V T := (@pack V T _ id _ id _ _ id).
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
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition choicePredType := @ChoicePred.Pack 'cV[R]_n cT xclass.
(*Definition pred_of_type := @mkPredType _ cT (ChoicePred.mem_pred_sort xclass).*)
Definition pred_of (P : cT) : (pred_sort _) := (ChoicePred.mem_pred_sort xclass P).
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ChoicePred.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pred_of : sort >-> pred_sort.
(*Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion pred_of_type : type >-> predType.
Coercion choicePredType : type >-> ChoicePred.type.*)
Canonical eqType.
Canonical choiceType.
(*Canonical pred_of_type.*)
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

Definition poly0 : T := PolyPred.poly0 (PolyPred.class T).
Definition polyT : T := PolyPred.polyT (PolyPred.class T).
Definition polyI : T -> T -> T := PolyPred.polyI (PolyPred.class T).
Definition poly_subset : rel T := PolyPred.poly_subset (PolyPred.class T).
Definition mk_hs : _ -> T := PolyPred.mk_hs (PolyPred.class T).
Definition bounded : T -> _ -> bool := PolyPred.bounded (PolyPred.class T).
Definition pointed : pred T := PolyPred.pointed (PolyPred.class T).
Definition conv : {fset 'cV[R]_n} -> T := PolyPred.conv (PolyPred.class T).

Definition poly_equiv (P Q : T) := (poly_subset P Q) && (poly_subset Q P).
Definition poly_proper (P Q : T) := ((poly_subset P Q) && (~~ (poly_subset Q P))).

Local Open Scope poly_scope.

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

Lemma in_poly0 : (`[poly0] : T) =i pred0.
Proof.
exact: PolyPred.in_poly0.
Qed.

Lemma in_polyT : (`[polyT] : T) =i predT.
Proof.
exact: PolyPred.in_polyT.
Qed.

Lemma poly_subsetP {P Q : T} : reflect {subset P <= Q} (P `<=` Q).
Proof.
exact: PolyPred.poly_subsetP.
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

(* RK: the next statement of this result seems to be better
Lemma in_polyI (P Q : T) : (P `&` Q) =i [predI P & Q]. *)
Lemma in_polyI (P Q : T) x : (x \in (P `&` Q)) = ((x \in P) && (x \in Q)).
Proof.
exact: (PolyPred.in_polyI (PolyPred.class T)).
Qed.

Lemma polyI0 {P : T} : P `&` (`[poly0]) `=~` `[poly0].
rewrite/poly_equiv.
have: (P `&` (`[ poly0 ]) `<=` (`[ poly0 ])) => [ | -> //=];apply/poly_subsetP => x; rewrite in_polyI (in_poly0 x) //=.
by move/andP/proj2.
Qed.


Lemma poly0I {P : T} : (`[poly0]) `&` P `=~` `[poly0].
rewrite/poly_equiv.
by have: ( (`[ poly0 ]) `&` P `<=` (`[ poly0 ])) => [ | -> //=];apply/poly_subsetP => x; rewrite in_polyI (in_poly0 x).
Qed.

Lemma poly_subsetIl (P Q : T) : P `&` Q `<=` P.
Proof. (* RK *)
apply/poly_subsetP => x.
by rewrite in_polyI; move/andP/proj1.
Qed.

Lemma poly_subsetIr (P Q : T) : P `&` Q `<=` Q.
Proof. (* RK *)
apply/poly_subsetP => x.
by rewrite in_polyI; move/andP/proj2.
Qed.

Lemma polyIS (P P' Q : T) : P `<=` P' -> Q `&` P `<=` Q `&` P'.
Proof. (* RK *)
move => sPP'; apply/poly_subsetP => x; rewrite !in_polyI.
case: (x \in Q) => //; exact: poly_subsetP.
Qed.

Lemma polySI (P P' Q : T) : P `<=` P' -> P `&` Q `<=` P' `&` Q.
Proof. (* RK *)
move => sPP'; apply/poly_subsetP => x; rewrite !in_polyI.
case: (x \in Q) => //; rewrite ?andbT ?andbF //; exact: poly_subsetP.
Qed.

Lemma polyISS (P P' Q Q' : T) : P `<=` P' -> Q `<=` Q' -> P `&` Q `<=` P' `&` Q'.
Proof. (* RK *)
move => /poly_subsetP sPP' /poly_subsetP sQQ'; apply/poly_subsetP => ?.
by rewrite !in_polyI; move/andP => [? ?]; apply/andP; split; [apply/sPP' | apply/sQQ'].
Qed.

Lemma poly_subsetIP (P Q Q' : T) : reflect (P `<=` Q /\ P `<=` Q') (P `<=` Q `&` Q').
Proof.
apply: (iffP idP) => [/poly_subsetP subset_P_QIQ' | [/poly_subsetP subset_P_Q /poly_subsetP subset_P_Q']].
- by split; apply/poly_subsetP => x x_in_P; move: (subset_P_QIQ' _ x_in_P); rewrite in_polyI; case/andP.
- by apply/poly_subsetP => x x_in_P; rewrite in_polyI; apply/andP; split; [exact: (subset_P_Q _ x_in_P) | exact: (subset_P_Q' _ x_in_P)].
Qed.

Lemma polyIxx {P : T} : P `&` P `=~` P.
Proof. (* RK *)
apply/andP; split; first exact: poly_subsetIl.
by apply/poly_subsetIP; split; exact: (poly_subset_refl P).
Qed.

Lemma in_big_polyIP (I : finType) (P : pred I) (F : I -> T) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \polyI_(i | P i) (F i)).
Proof.
have -> : (x \in \polyI_(i | P i) F i) = (\big[andb/true]_(i | P i) (x \in (F i))).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?in_polyT ?in_polyI.
rewrite big_all_cond; apply: (iffP allP) => /= H i;
have := H i _; rewrite mem_index_enum; last by move/implyP->.
by move=> /(_ isT) /implyP.
Qed.

Lemma in_big_polyI (I : finType) (P : pred I) (F : I -> T) x :
  (x \in \polyI_(i | P i) (F i)) = [forall i, P i ==> (x \in F i)].
Proof.
by apply/in_big_polyIP/forall_inP.
Qed.

Lemma big_poly_inf (I : finType) (j : I) (P : pred I) (F : I -> T) :
  P j -> (\polyI_(i | P i) F i) `<=` F j.
Proof. (* RK *)
move => ?.
apply/poly_subsetP => ? /in_big_polyIP in_polyI_cond.
by apply: (in_polyI_cond j).
Qed.

Lemma big_polyI_min (I : finType) (j : I) (Q : T) (P : pred I) (F : I -> T) :
  P j -> (F j `<=` Q) -> \polyI_(i | P i) F i `<=` Q.
Proof. (* RK *)
by move => ? ?; apply/(@poly_subset_trans (F j) _ _); [apply: big_poly_inf | done].
Qed.

Lemma big_polyIsP (I : finType) (Q : T) (P : pred I) (F : I -> T) :
  reflect (forall i : I, P i -> Q `<=` F i) (Q `<=` \polyI_(i | P i) F i).
Proof. (* RK *)
apply: (iffP idP) => [Q_subset_polyI ? ? | forall_Q_subset].
- by apply/(poly_subset_trans Q_subset_polyI _)/big_poly_inf.
- apply/poly_subsetP => x x_in_Q.
  apply/in_big_polyIP => j P_j.
  by move: x x_in_Q; apply/poly_subsetP; exact: forall_Q_subset.
Qed.

Lemma in_hs : (forall b x, x \in (`[hs b] : T) = ('[fst b,x] >= snd b))
              * (forall c α x, x \in (`[hs (c, α)] : T) = ('[c,x] >= α)).
Admitted.
(*
Proof.
exact: PolyPred.in_hs.
Qed.*)

Lemma notin_hs :
  (forall b x, x \notin (`[hs b] : T) = ('[fst b,x] < snd b))
  * (forall c α x, x \notin (`[hs (c, α)] : T) = ('[c,x] < α)).
Admitted.

Definition mk_hp e : T := `[hs e] `&` `[hs (-e)].
Notation "'`[' 'hp' e  ']'" := (mk_hp e%PH) (at level 70) : poly_scope.

Lemma in_hp :
  (forall b x, x \in (`[hp b] : T) = ('[fst b,x] == snd b))
  * (forall c α x, x \notin (`[hp (c, α)] : T) = ('[c,x] == α)).
Admitted.
(*Proof. (* RK *)
by rewrite in_polyI 2!in_hs vdotNl ler_oppl opprK eq_sym eqr_le.
Qed.*)

Let inE := (in_poly0, in_polyT, in_hp, in_polyI, in_hs, inE).

Lemma poly_subset_hsP {P : T} {b} :
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
exact: PolyPred.poly_subsetPn.
Qed.

Lemma proper0N_equiv (P : T) : ~~ (P `>` `[poly0]) = (P `=~` `[poly0]).
Proof. (* RK *)
rewrite negb_and negbK /poly_equiv !poly0_subset //=.
by apply/idP/idP => [-> | ]; [done | case/andP].
Qed.

Lemma subset0N_proper (P : T) : ~~ (P `<=` `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
apply/idP/idP => [? | /andP [_ ?]]; last by done.
by apply/andP; split; [exact: poly0_subset | done].
Qed.

Lemma equiv0N_proper (P : T) : (P `!=~` `[poly0]) = (P `>` `[poly0]).
Proof. (* RK *)
by rewrite -proper0N_equiv negbK.
Qed.

Lemma subset0_equiv {P : T} : (P `<=` `[poly0]) = (P `=~` `[poly0]).
Proof. (* RK *)
by apply/negb_inj; rewrite subset0N_proper equiv0N_proper.
Qed.

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

Definition pick_point (P : T) : 'cV[R]_n :=
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
  (* should {subset P <= Q} to (P `<=` Q) *)
  reflect ({subset P <= Q} /\ exists2 x, x \in Q & x \notin P) (P `<` Q).
Proof.
apply: (iffP andP) =>
  [[/poly_subsetP ? /poly_subsetPn [x ??]] | [? [x ??]] ].
- by split; [ done | exists x].
- by split; [ apply/poly_subsetP | apply/poly_subsetPn; exists x].
Qed.

Lemma poly_subset_anti {P Q : T} :
  (P `<=` Q) -> (Q `<=` P) -> (P `=~` Q).
Admitted.

Lemma poly_properEneq {P Q : T} :
  (P `<` Q) = (P `<=` Q) && (P `!=~` Q).
Proof.
apply/idP/andP => [/poly_properP [/poly_subsetP ?] [x x_in x_notin]| [P_sub_Q P_neq_Q] ].
- split; first done.
  apply/negP => P_eq_Q; rewrite (poly_equivP P_eq_Q) in x_notin.
  by move/negP: x_notin.
- apply/andP; split; first done.
  move: P_neq_Q; apply: contra.
  exact: poly_subset_anti.
Qed.

Lemma poly_properW (P Q : T) :
  (P `<` Q) -> (P `<=` Q).
Admitted.

Lemma poly_properxx (P : T) : (P `<` P) = false.
Proof.
by rewrite /poly_proper poly_subset_refl.
Qed.

Lemma poly_proper_subset (P P' P'' : T) :
  (P `<` P') -> (P' `<=` P'') -> (P `<` P'').
Proof. (* RK *)
move/poly_properP => [sPP' [x ? ?]] /poly_subsetP sP'P''.
apply/poly_properP; split; first by move => ? ?; apply/sP'P''/sPP'.
by exists x; [apply/sP'P'' | done].
Qed.

Lemma poly_subset_proper (P P' P'' : T) :
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

Lemma poly_proper_subsetxx (P Q : T) : (* to be compared with lter_anti *)
  (P `<` Q `<=` P) = false.
Proof. (* RK *)
by apply/negbTE/nandP/orP; rewrite negb_and negbK -orbA orbC orbN.
Qed.

Lemma poly_subset_properxx (P Q : T) :
  (P `<=` Q `<` P) = false.
Proof. (* RK *)
by apply/negbTE/nandP/orP; rewrite negb_and negbK orbA orbC orbA orbN.
Qed.

Lemma boundedP {P : T} {c} :
  reflect (exists2 x, (x \in P) & (P `<=` `[hs (c, '[c, x])])) (bounded P c).
Proof.
exact: PolyPred.boundedP.
Qed.

Lemma boundedPP {P : T} {c} :
  reflect (exists x, (x \in P) && (P `<=` `[hs (c, '[c, x])])) (bounded P c).
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
  by exists x; rewrite notin_hs in x_not_in_hs.
- move => [x x_in_P c_x_lt_K].
  by apply/poly_subsetPn; exists x; rewrite ?notin_hs.
Qed.

Lemma bounded_mono1 (P Q : T) c :
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

Definition opt_value (P : T) c (bounded_P : bounded P c) :=
  let x := xchoose (boundedPP bounded_P) in '[c,x].

Lemma opt_point (P : T) c (bounded_P : bounded P c) :
  exists2 x, x \in P & '[c,x] = opt_value bounded_P.
Proof.
rewrite /opt_value; set x := xchoose _.
exists x; last by done.
by move: (xchooseP (boundedPP bounded_P)) => /andP [?].
Qed.

Lemma opt_value_lower_bound {P : T} {c} (bounded_P : bounded P c) :
  P `<=` (`[ hs (c, opt_value bounded_P)]).
Proof.
by rewrite /opt_value; move/andP : (xchooseP (boundedPP bounded_P)) => [_].
Qed.

Lemma opt_value_antimono1 (P Q : T) c (bounded_P : bounded P c) (bounded_Q : bounded Q c) :
  Q `<=` P -> opt_value bounded_P <= opt_value bounded_Q.
Proof. (* RK *)
move => /poly_subsetP sQP.
move: (opt_point bounded_Q) => [x x_in_Q <-].
move/sQP/(poly_subsetP (opt_value_lower_bound bounded_P)) : x_in_Q.
by rewrite in_hs.
Qed.

Definition argmin (P : T) c :=
  if @idP (bounded P c) is ReflectT H then
    P `&` `[hp (c, opt_value H)]
  else
    `[poly0].

Lemma argmin_polyI (P : T) c (bounded_P : bounded P c) :
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

Lemma argmin_lower_bound {c x y} (P : T) :
  x \in argmin P c -> y \in P -> '[c,x] <= '[c,y].
Proof. (* RK *)
by rewrite in_argmin; move/andP => [_ /poly_subset_hsP/(_ y)].
Qed.

Lemma subset_opt_value (P Q : T) c (bounded_P : bounded P c) (bounded_Q : bounded Q c) :
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

Lemma subset_argmin {P Q : T} {c} :
  bounded Q c -> argmin Q c `<=` P `<=` Q -> argmin P c `=~` argmin Q c.
Proof. (* RK *)
move => bounded_Q /andP [? ?].
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

Lemma argmin_eq {P : T} {c v x} :
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

Lemma bounded_lower_bound (P : T) c :
  (P `>` `[poly0]) -> reflect (exists d, P `<=` `[hs (c, d)]) (bounded P c).
Proof.
move => P_non_empty; apply: introP => [ c_bounded | /(boundedPn P_non_empty) c_unbouded ].
- exists (opt_value c_bounded); exact: opt_value_lower_bound.
- move => [d c_bounded]; move/(_ d): c_unbouded => [x x_in_P c_x_lt_K].
  by move/poly_subsetP/(_ _ x_in_P): c_bounded; rewrite in_hs lerNgt => /negP.
Qed.

Definition mk_line (c Ω : 'cV[R]_n) : T :=
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

Lemma pointedPn {P : T} :
  (P `>` `[poly0]) ->
    reflect (exists c, (c != 0) /\ (forall Ω,  Ω \in P -> (`[line c & Ω] `<=` P))) (~~ (pointed P)).
(*RK : I had to add the non_emptiness assumption because now pointed only makes sense under this assumption. I also slightly modified statement*)
Proof. (* RK *)
rewrite -subset0N_proper => non_empty_P.
apply: (iffP (PolyPred.pointedPn non_empty_P)) => [[c [? incl]] | [c [? incl]]];
  exists c; split; try by done.
- move => Ω Ω_in_P.
  apply/poly_subsetP => x /in_lineP [μ ->].
  exact: incl.
- move => μ μ_in_P λ.
  apply/(poly_subsetP (incl _ μ_in_P))/in_lineP.
  by exists λ.
Qed.

Definition mk_hline (c Ω : 'cV[R]_n) : T :=
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

Lemma convP V x :
  reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V).
Proof.
exact: PolyPred.convP.
Qed.

Lemma convexP (P : T) (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> conv V `<=` P.
Proof.
exact: PolyPred.convexP.
Qed.

Lemma convexP2 (P : T) (v w : 'cV[R]_n) :
  v \in P -> w \in P -> conv ([fset v; w]%fset) `<=` P.
Admitted.

Definition mk_pt (Ω : 'cV[R]_n) : T := conv ([fset Ω]%fset).

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
  pick_point (`[pt Ω] : T) = Ω.
Proof. (* RK *)
apply/eqP; rewrite -in_pt; apply/pick_pointP; exact: pt_proper0.
Qed.

Lemma pt_subset (Ω : 'cV[R]_n) (P : T) : `[pt Ω] `<=` P = (Ω \in P).
Proof. (* RK *)
by apply/idP/idP => [/poly_subsetP s_ptΩ_P | ?];
  [apply/s_ptΩ_P; exact: in_pt_self | apply/poly_subsetP => v; rewrite in_pt => /eqP ->].
Qed.

Lemma pt_proper (Ω : 'cV[R]_n) (P : T) : `[pt Ω] `<` P -> (Ω \in P).
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

Definition compact (P : T) :=
  (*(P `>` `[poly0]) ==> *)
  [forall i, (bounded P (delta_mx i 0)) && (bounded P (-(delta_mx i 0)))].

Lemma compactP_Linfty (P : T) :
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

Lemma compact_pt (Ω : 'cV[R]_n) : compact (`[pt Ω] : T).
Admitted.

Definition slice (b : base_elt) P := `[hp b] `&` P.

Lemma slice0 (b : base_elt) : slice b (`[poly0]) `=~` `[poly0].
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

Definition poly_of_base (base : base_t) : T :=
  \polyI_(b : base) `[hs (val b)].

Notation "''P' ( base )" := (poly_of_base base) (at level 0) : poly_scope.

Definition in_poly_of_base x (base : base_t) :
  (x \in 'P(base)) = [forall b : base, x \in `[hs (val b)]].
Proof.
by rewrite in_big_polyI.
Qed.

Definition polyEq (p : wf_pair) : T :=
  (\polyI_(b : p.2) `[hp (val b)]) `&` 'P(p.1).


Notation "''P^=' ( p )" := (polyEq p) : poly_scope.
Notation "''P^=' ( base ; base' )" := (polyEq (base,base')%:wf) : poly_scope.

Fact in_polyEq x (p : wf_pair) :
  (x \in 'P^=(p)) = [forall b : p.2, x \in `[hp (val b)]] && (x \in 'P(p.1)).
Proof.
by rewrite inE in_big_polyI.
Qed.

Lemma in_polyEqP (x : 'cV[R]_n) (p : wf_pair) :
  reflect ((forall b, b \in p.2 -> x \in `[hp b]) /\ x \in 'P(p.1)) (x \in 'P^=(p)).
Proof.
Admitted.
(*
by rewrite in_polyEq; apply: (equivP andP);
  split; move => [/forall_inP x_sat x_in_PAb].
Qed.*)

Lemma polyEq_eq (x : 'cV[R]_n) (p : wf_pair) b :
  x \in 'P^=(p) -> b \in p.2 -> x \in `[hp b].
Proof.
by move/in_polyEqP => [x_act _ ?]; apply: x_act.
Qed.

Lemma polyEq0 {base : base_t} :
  'P^=(base; fset0) `=~` 'P(base).
Admitted.

(*Lemma polyEq_flatten {base : base_t R n} {base' : {set base}} :
  'P^=(base; base') `=~` 'P(baseEq base base').
Admitted.

Lemma in_hpolyEq_setT (x : 'cV[R]_n) (base : base_t R n) :
  (x \in 'P^=(base; base)) = [forall b : base, x \in `[hp (val b)]].
Admitted.

Lemma polyEq_antimono (base : base_t R n) (base' base'' : {fset base}) :
  (val @` base' `<=` val @` base'')%fset -> 'P^=(base; val @` base') `<=` 'P^=(base; val @` base'').
Proof.
Admitted.

Lemma polyEq_antimono0 {base base' : base_t R n} :
  'P^=(base; base') `<=` 'P(base).
Proof.
Admitted.
(*case : base I => [m A b] I.
by move => x /in_hpolyEqP [].
Qed.*)

(*  case : base => [A b] /=.
rewrite in_hpolyEq.
apply/idP/idP => [/andP [_ /forallP forall_cond] | /eqP A_x_eq_b].
- apply/eqP/colP => j.
  by apply/eqP/(implyP (forall_cond j)).
- apply/andP; split.
  + rewrite inE A_x_eq_b.
    exact: lev_refl.
  + apply/forallP => j.
    apply/implyP => _.
    by rewrite A_x_eq_b.
Qed.*)


(*case: base I J => [m A b] I J.
move => /subsetP I_subset_J x.
rewrite 2!in_hpolyEq.
move/andP => [x_in_P /forallP sat_in_J].
apply/andP; split.
- exact: x_in_P.
- apply/forallP => j.
  apply/implyP => j_in_I.
  apply: (implyP (sat_in_J j)).
  exact: (I_subset_J _ j_in_I).
Qed.*)


Lemma polyEq_polyI {base base' base'': base_t R n} :
  'P^=(base; base') `&` 'P^=(base; base'') `=~` 'P^=(base; (base' `|` base'')%fset).
Admitted.

Lemma polyEq_big_polyI {base: base_t R n} {I : finType} {P : pred I} {F} :
  ~~ pred0b P -> \polyI_(i | P i) 'P^=(base; F i) `=~` 'P^=(base; (\bigcup_(i | P i) (F i))%fset).
Proof.
move/pred0Pn => [i0 Pi0].
apply/andP; split; last first.
(*- apply/big_polyIsP => [i Pi]; apply/polyEq_antimono; exact: bigcup_sup.
- apply/poly_subsetP => x /in_big_polyIP x_in.
  apply/in_polyEqP; split;
    last by move/(_ _ Pi0): x_in; exact: (poly_subsetP polyEq_antimono0).
  move => j /bigcupP => [[i]] Pi; apply: polyEq_eq; exact: x_in.
Qed.*)
Admitted.

Lemma polyEq_of_polyEq (base base1 base2 : base_t R n) : (* quite short proof after all! *)
   exists base3, 'P^=(baseEq base base1; base2) `=~` 'P^=(base; base3).
(*Proof.
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
Qed.*)
Admitted.

Lemma polyEq1 {base: base_t R n} {b} :
  'P^=(base; [fset b]%fset) `=~` 'P(base) `&` `[hp b].
Proof.
Admitted.
(*apply/poly_equivP => x; rewrite in_hpolyEq !inE; apply: congr1; rewrite row_vdot.
by apply/forall_inP/idP => [/(_ _ (set11 i)) | ? j /set1P ->].
Qed.*)
 *)

Lemma slice_polyEq (b : base_elt) (p : wf_pair) :
  slice b 'P^=(p) `=~` 'P^=((b ||` p)%:wf).
Admitted.

End PolyPredProperties.

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
Notation "''P^=' ( p )" := (polyEq p) : poly_scope.
Notation "''P^=' ( base ; base' )" := (polyEq (base,base')%:wf) : poly_scope.

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

Definition mem_pred_sort (P : {quot T}) := (mem (\repr P)) : pred 'cV[R]_n.
Canonical quot_predType := mkPredType mem_pred_sort.
Canonical quot_choicePredType := ChoicePredType 'cV[R]_n {quot T}.

Lemma quotP {P Q : T} : '[P] = '[Q] <-> P `=~` Q.
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

Arguments quotP [R n T].

Notation "''[' P  ]" := (class_of P) : poly_scope.

Section PolyPredStructure.

Variables (R : realFieldType) (n : nat) (T : polyPredType R n).

Implicit Types P : {quot T}.

Definition poly0 : {quot T} := '[ `[poly0] ].
Definition polyT : {quot T} := '[ `[polyT] ].
Definition polyI (P Q : {quot T}) : {quot T} := '[ (\repr P) `&` (\repr Q) ].
Definition poly_subset (P Q : {quot T}) := (\repr P) `<=` (\repr Q).
Definition mk_hs b : {quot T} := '[ `[hs b] ].
Definition bounded P c := bounded (\repr P) c.
Definition pointed P := pointed (\repr P).
Definition conv V : {quot T} := '[ (conv V) ].

Let inE := (repr_equiv, @in_poly0, @in_polyT, @in_polyI, @in_hs, inE).

Lemma in_poly0 : (poly0 : {quot T}) =i pred0.
Proof.
by move => ?; rewrite !inE.
Qed.

Lemma in_polyT : (polyT : {quot T}) =i predT.
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

Lemma in_hs b x : x \in (mk_hs b) = ('[b.1,x] >= b.2).
Proof.
by rewrite !inE.
Qed.

Lemma boundedP P c :
  reflect (exists2 x, x \in P & poly_subset P (mk_hs (c, '[c,x]))) (bounded P c).
Proof.
have eq x : poly_subset P (mk_hs (c,'[ c, x])) = (repr P `<=` (`[ hs (c, '[ c, x]) ]))
  by apply: (sameP (poly_subsetP _ _));
     apply: (iffP (PolyPred.poly_subsetP _ _ _)) => sub z;
     move/(_ z): sub; rewrite !inE.
by apply: (iffP boundedP) => [[x] H H' | [x] H H']; exists x; rewrite ?inE ?eq in H' *.
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs (c, K)))) (~~ bounded P c).
Admitted.

Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
move=> non_empty_P.
have H : ((`[ poly0 ]) `<` \repr P).
  apply/contraT; rewrite -subset0N_proper negbK => /PolyPred.poly_subsetP empty_P.
  move/poly_subsetPn: non_empty_P => [x].
  by move/empty_P; rewrite !inE.
apply: (iffP (pointedPn H)) => [[c [? incl]] | [c [? incl]]];
  exists c; split; try by done.
- move => μ μ_in_P λ.
  apply/(PolyPred.poly_subsetP _ _ _ (incl _ μ_in_P))/in_lineP.
  by exists λ.
- move => Ω Ω_in_P.
  apply/PolyPred.poly_subsetP => x /in_lineP [μ ->].
  exact: incl.
Qed.

Lemma convP V x :
  reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V).
Proof.
rewrite inE; exact: PolyPred.convP.
Qed.

Lemma convexP P (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> poly_subset (conv V) P.
Proof.
move => V_sub_P; apply/poly_subsetP => x.
rewrite !inE; move: x; apply/(PolyPred.poly_subsetP _)/PolyPred.convexP.
exact: V_sub_P.
Qed.

Definition quot_polyPredMixin := PolyPred.Mixin in_poly0 in_polyT in_polyI poly_subsetP poly_subsetPn in_hs boundedP boundedPn pointedPn convP convexP.
Canonical quot_polyPredType := PolyPredType R n quot_polyPredMixin.

End PolyPredStructure.

Module Import Exports.
Canonical quot_subType.
Canonical quot_eqType.
Canonical quot_choiceType.
(*Canonical quot_predType.*)
Canonical quot_choicePredType.
Canonical quot_polyPredType.
Notation "'{quot'  T '}'" := (PolyPred.sort [polyPredType of (@quot _ _ _ (Phant T))]) (at level 0).
Notation "\repr" := (@repr _ _ _ (Phant _)) (at level 0).
Notation "''[' P  ]" := (class_of P) (at level 0).
Notation reprK := reprK.
Notation repr_inj := repr_inj.
Notation repr_equiv := repr_equiv.
Notation quotP := quotP.
End Exports.
End Quotient.

Export Quotient.Exports.

Definition inE := (repr_equiv, @in_poly0, @in_polyT, @in_hp, @in_polyI, @in_hs, inE).

Section QuotientProperties.

Local Open Scope poly_scope.

Context {R : realFieldType} {n : nat} {T : polyPredType R n}.

Lemma quot_equivP {P Q : {quot T}} : (P `=~` Q) -> P = Q.
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

Lemma hs_mono b : `[hs b] = '[`[hs b]] :> {quot T}.
Proof.
by apply/quotP/poly_equivP => x; rewrite inE.
Qed.

Lemma hp_mono b : `[hp b] = '[`[hp b]] :> {quot T}.
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

Lemma pointed_mono (P : T) :
  (P `>` `[poly0]) -> pointed '[P] = pointed P.
(*RK : I had to add the non_emptiness assumption because now pointed only makes sense under this assumption. *)
Proof. (* RK *)
move => non_empty_P.
apply: negb_inj; symmetry.
apply: (sameP (pointedPn non_empty_P)).
rewrite -poly_proper_mono in non_empty_P.
apply: (iffP (pointedPn non_empty_P)) => [[c [? line_incl]] | [c [? line_incl]]];
  exists c; split; try by done.
- move => Ω ?; rewrite -poly_subset_mono -line_mono.
  by apply: line_incl; rewrite inE.
- move => Ω ?; rewrite line_mono poly_subset_mono.
  by apply: line_incl; rewrite -inE.
Qed.

Lemma slice_mono b (P : T) : slice b '[P] = '[slice b P].
Admitted.

Lemma compact_mono (P : T) : compact '[P] = compact P.
Admitted.

Lemma poly_of_base_mono (base : base_t) :
  '['P(base)] = 'P(base) :> {quot T}.
Admitted.

Lemma polyEq_mono (p : wf_pair) :
  '['P^=(p)] = 'P^=(p) :> {quot T}.
Admitted.

End QuotientProperties.

Definition quotE := (@slice_mono, @poly_of_base_mono, @polyEq_mono,
                    @poly_subset_mono, @poly_proper_mono, @bounded_mono,
                    @polyI_mono, @big_polyI_mono, @hs_mono, @line_mono,
                    @argmin_mono, @pointed_mono, @hp_mono).


(*
Section Duality.

Local Open Scope poly_scope.

Variable (R : realFieldType) (n : nat) (T : polyPredType R n).
Variable (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m).

Lemma dual_opt_sol (c : 'cV[R]_n) (H : bounded ('P(A,b) : T) c) :
    exists u, [/\ u >=m 0, c = A^T *m u & '[b, u] = opt_value H].
Admitted.
(*Proof.
move: (H) => H0. (* duplicate assumption *)
move: H; rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _ .
by move/and3P => [opt_point_in_P /andP [/eqP Au_eq_c u_le0] /eqP eq_value]; exists u.
Qed.*)

Variable (u : 'cV[R]_m).

Lemma dual_sol_lower_bound :
  u >=m 0 -> ('P(A, b) : T) `<=` `[hs (A^T *m u) & '[b,u]].
Proof.
move => u_ge0; apply/poly_subsetP => x x_in.
by rewrite inE -vdot_mulmx vdotC; apply: vdot_lev;
  last by rewrite in_poly_of_base in x_in.
Qed.

Lemma dual_sol_bounded :
  (('P(A, b) : T) `>` `[poly0]) -> u >=m 0 -> bounded ('P(A,b) : T) (A^T *m u).
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists '[b,u]; exact: dual_sol_lower_bound.
Qed.

Hypothesis u_ge0 : u >=m 0.
Variable (I : {set 'I_m}).
Hypothesis u_supp : forall i, (u i 0 > 0) = (i \in I).

Lemma compl_slack_cond x :
  x \in ('P(A,b) : T) -> reflect ('[A^T *m u, x] = '[b, u]) (x \in ('P^=(A, b; I) : T)).
Admitted.

Lemma dual_sol_argmin : (('P^=(A, b; I) : T) `>` `[poly0]) -> argmin ('P(A,b) : T) (A^T *m u) `=~` 'P^=(A, b; I).
Proof.
move => PI_non_empty.
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
*)

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

Class infer (P : Prop) := Infer : P.
Hint Mode infer ! : typeclass_instances.
Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Inductive foo := Foo { P : bool; _ : P}.
Variable P : T.
Hypothesis toto : (P `>` `[poly0]).

Canonical fooT := Foo toto.

(*
Lemma fooP P (b : foo P) : P.
by case : b.
Qed.*)
Canonical bar (P : T) (b : infer (P `>` `[poly0])) := @Ppoly _ _ _ (Phant T) P b.

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
  Polyt (Phant {quot T}) (eq_imply2 (compact_mono P) (polytP P)).
Definition polyt_of (P : T) (b : (compact P) ) & (phantom (compact P) b) := Polyt (Phant T) b.
Notation "P %:polyt" := (@polyt_of P _ (Phantom (compact P) _)) (at level 0) : poly_scope.

Variable is_face : T -> bool.
 Instance foo (P : T) (b : is_face P) : infer (compact P).
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

Instance b' : infer (compact P). exact: inferP. Qed.
Check (P %:polyt).

Goal ('[ P%:polyt ] `>` `[poly0]).
exact: polyt_proper0.
Qed.

End BasicProperties.
*)
