(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum zmodp matrix mxalgebra vector finmap.

Import Order.Theory.

Require Import extra_misc extra_matrix inner_product row_submx vector_order barycenter lrel hpolyhedron affine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module H := HPolyhedron.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Local Open Scope poly_scope.

Import GRing.Theory Num.Theory.

Reserved Notation "x `<=` y `<=` z" (at level 70, y, z at next level).
Reserved Notation "x `<=` y `<` z" (at level 70, y, z at next level).
Reserved Notation "x `<` y `<=` z" (at level 70, y, z at next level).
Reserved Notation "x `<` y `<` z" (at level 70, y, z at next level).

Reserved Notation "x `>=` y" (at level 70, y at next level).
Reserved Notation "x `>` y" (at level 70, y at next level).

Reserved Notation "x `<=` y :> T" (at level 70, y at next level).
Reserved Notation "x `<` y :> T" (at level 70, y at next level).
Reserved Notation "x `>=` y :> T" (at level 70, y at next level).
Reserved Notation "x `>` y :> T" (at level 70, y at next level).

Reserved Notation "x `>=<` y" (at level 70, y at next level).
Reserved Notation "x `><` y" (at level 70, y at next level).

Reserved Notation "`<=` y" (at level 35).
Reserved Notation "`>=` y" (at level 35).
Reserved Notation "`<` y" (at level 35).
Reserved Notation "`>` y" (at level 35).
Reserved Notation "`>=<` y" (at level 35).
Reserved Notation "`><` y" (at level 35).
Reserved Notation "`<=` y :> T" (at level 35, y at next level).
Reserved Notation "`>=` y :> T" (at level 35, y at next level).
Reserved Notation "`<` y :> T" (at level 35, y at next level).
Reserved Notation "`>` y :> T" (at level 35, y at next level).
Reserved Notation "`>=<` y :> T" (at level 35, y at next level).
Reserved Notation "`><` y :> T" (at level 35, y at next level).

Reserved Notation "x `<=` y ?= 'iff' c"
  (at level 70, y, c at next level,
       format "x '[hv'  `<=`  y '/'  ?=  'iff'  c ']'").

Reserved Notation "x `<=` y ?= 'iff' c :> T"
  (at level 70, y, c at next level,
       format "x '[hv'  `<=`  y '/'  ?=  'iff'  c  :> T ']'").

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

Reserved Notation "''poly[' R ]_ n"
  (at level 8, n at level 2, format "''poly[' R ]_ n").
Reserved Notation "''poly[' R ]"
  (at level 8, format "''poly[' R ]").
Reserved Notation "''poly_' n"
  (at level 8, format "''poly_' n").
Reserved Notation "''[' P ]"
  (at level 0, format "''[' P ]").

Reserved Notation "'[' 'poly0' ']'" (at level 0).
Reserved Notation "'[' 'polyT' ']'" (at level 0).

Reserved Notation "[ 'hs' b ]" (at level 0, format "[ 'hs'  b ]").
Reserved Notation "[ 'hp' b ]" (at level 0, format "[ 'hp'  b ]").

Reserved Notation "[ 'pt' Ω ]" (at level 0, format "[ 'pt'  Ω ]").

Reserved Notation "[ 'line' c & Ω ]"  (at level 0, format "[ 'line'  c  &  Ω ]").
Reserved Notation "[ 'hline' c & Ω ]" (at level 0, format "[ 'hline'  c  &  Ω ]").

Reserved Notation "''P' ( base )" (at level 0, format "''P' ( base )").
Reserved Notation "''P^=' ( base ; I )" (at level 0, format "''P^=' ( base ;  I )").

Reserved Notation "'[' 'affine' U & Ω ']'"
  (at level 0, format "[ 'affine'  U   &   Ω ]").

Reserved Notation "[ 'segm' u '&' v ]"
  (at level 0, format "[ 'segm'  u  '&'  v ]").


Section Def.
Context {R : realFieldType} (n : nat).

Canonical poly_equiv_equiv :=
  EquivRel (@H.poly_equiv R n)
    H.poly_equiv_refl H.poly_equiv_sym H.poly_equiv_trans.

Definition type := {eq_quot H.poly_equiv}.
Definition type_of of phant R := type.

Notation  "''poly[' R ]" := (type_of (Phant R)).

Canonical poly_quotType := [quotType of type].
Canonical poly_eqType := [eqType of type].
Canonical poly_choiceType := [choiceType of type].
Canonical poly_eqQuotType := [eqQuotType H.poly_equiv of type].

Canonical poly_of_quotType := [quotType of 'poly[R]].
Canonical poly_of_eqType := [eqType of 'poly[R]].
Canonical poly_of_choiceType := [choiceType of 'poly[R]].
Canonical poly_of_eqQuotType := [eqQuotType H.poly_equiv of 'poly[R]].

Identity Coercion type_of_type : type_of >-> type.

Definition mem_pred_sort (P : type) := (repr P) : {pred 'cV[R]_n}.
Coercion mem_pred_sort : type >-> pred_sort.

Definition mk_poly (P : 'hpoly[R]_n) : 'poly[R] := \pi P.
End Def.

Section Def.
Context {R : realFieldType} (n : nat).

Local Notation "''poly[' R ]_ n" := (type_of n (Phant R)).

Inductive poly_type : predArgType := Poly of 'poly[R]_n.

Definition poly_of of phant R := poly_type.

Identity Coercion type_of_poly : poly_of >-> poly_type.

Definition polyval P := let: Poly t := P in t.
Coercion polyval : poly_type >-> type_of.

Canonical poly_subType := Eval hnf in [newType for polyval].
Definition poly_eqMixin := Eval hnf in [eqMixin of poly_type by <:].
Canonical poly2_eqType := Eval hnf in EqType poly_type poly_eqMixin.
Definition poly_choiceMixin := [choiceMixin of poly_type by <:].
Canonical poly2_choiceType := Eval hnf in ChoiceType poly_type poly_choiceMixin.
End Def.

Section Def.
Context (R : realFieldType) (n : nat).

Notation "''poly[' R ]_ n" := (poly_of n (Phant R)).
Notation "''poly[' R ]"    := ('poly[R]_(_)).
Notation "''poly_' n"      := ('poly[_]_n).

Canonical poly2_of_subType    := [subType    of 'poly[R]_n].
Canonical poly2_of_eqType     := [eqType     of 'poly[R]_n].
Canonical poly2_of_choiceType := [choiceType of 'poly[R]_n].

Canonical poly2_predType :=
  PredType (@mem_pred_sort R n : 'poly[R]_n -> pred 'cV[R]_n).

Definition hrepr (P : 'poly[R]_n) := repr (polyval P).
End Def.

Notation "''poly[' R ]_ n" := (poly_of n (Phant R)).
Notation "''poly[' R ]"    := 'poly[R]_(_).
Notation "''poly_' n"      := 'poly[_]_n.

Definition mk_poly2 (R : realFieldType) n P : 'poly[R]_n := Poly (mk_poly P).

Notation "''[' P ]" := (@mk_poly2 _ _ P).

Section BasicProperties.

Context {R : realFieldType} (n : nat).

Lemma polyW (P : 'poly[R]_n -> Type) :
  (forall p : 'hpoly[R]_n, P '[p]) -> forall p : 'poly[R]_n, P p.
Proof. by move=> ih -[]; apply: quotW. Qed.

Lemma mem_polyE {P : 'poly[R]_n} x : (x \in P) = (x \in hrepr P).
Proof. by []. Qed.

Lemma repr_equiv (P : 'hpoly[R]_n) : hrepr '[P] =i P.
Proof. by apply/H.poly_equivP/eqmodP => /=; rewrite reprK. Qed.

Lemma mem_mk_poly {P : 'hpoly[R]_n} x : (x \in '[P]) = (x \in P).
Proof. by rewrite mem_polyE repr_equiv. Qed.

Lemma poly_eqP {P Q : 'poly[R]_n} : (P =i Q) <-> (P = Q).
Proof.
split=> [|->//]; elim/polyW: P => P; elim/polyW: Q => Q /=.
move=> eq_PQ; apply/val_inj/eqmodP/H.poly_equivP => /= x.
by move/(_ x): eq_PQ; rewrite !mem_mk_poly.
Qed.
End BasicProperties.

Arguments polyW [R n] P.

Section PolyPred.

Context {R : realFieldType} {n : nat}.

Implicit Types (P Q : 'poly[R]_n).

Definition poly0 : 'poly[R]_n := '[ H.poly0 ].
Definition polyI P Q := '[ H.polyI (hrepr P) (hrepr Q) ].

Lemma mem_poly0 x : x \in poly0 = false.
Proof. by rewrite repr_equiv H.in_poly0. Qed.

Lemma mem_polyI x P Q : x \in polyI P Q = (x \in P) && (x \in Q).
Proof. by rewrite repr_equiv H.in_polyI. Qed.

Definition poly_subset P Q := H.poly_subset (hrepr P) (hrepr Q).
Definition poly_equiv  P Q := poly_subset P Q && poly_subset Q P.
Definition poly_proper P Q := (Q != P) && poly_subset P Q.

Lemma poly_subsetP {P Q : 'poly[R]_n} : reflect {subset P <= Q} (poly_subset P Q).
Proof. by apply: (iffP H.poly_subsetP). Qed.

Lemma poly_eqE P Q : (P == Q) = poly_equiv P Q.
Proof.
apply/eqP/idP=> [->|]; first by apply/andP; split; apply/poly_subsetP.
case/andP=> /poly_subsetP le_PQ /poly_subsetP le_QP.
by apply/poly_eqP=> x; apply/idP/idP => [/le_PQ|/le_QP].
Qed.

Local Lemma _poly_subset_refl : reflexive poly_subset.
by move=> P; apply/poly_subsetP.
Qed.

Local Lemma _poly_subset_anti : antisymmetric poly_subset.
move=> P Q /andP[] /poly_subsetP le_PQ /poly_subsetP le_QP.
by apply/poly_eqP=> x; apply/idP/idP => [/le_PQ|/le_QP].
Qed.

Local Lemma _poly_subset_trans : transitive poly_subset.
move=> P2 P1 P3 /poly_subsetP le_12 /poly_subsetP le_23.
by apply/poly_subsetP=> x /le_12 /le_23.
Qed.

Fact polyh_display : unit. Proof. exact: tt. Qed.

Definition poly_LtPOrderMixin :=
  LePOrderMixin  (fun _ _ => erefl _) _poly_subset_refl _poly_subset_anti _poly_subset_trans.

Canonical poly_of_LtPOrderType :=
  Eval hnf in POrderType polyh_display 'poly[R]_n poly_LtPOrderMixin.

Lemma poly_leE P Q : (P <= Q)%O = poly_subset P Q.
Proof. by []. Qed.

Lemma poly_leP P Q : reflect {subset P <= Q} (P <= Q)%O.
Proof. by rewrite poly_leE; apply: (iffP poly_subsetP). Qed.

Program Canonical poly_MeetSemilattice :=
  Eval hnf in MeetSemilatticeType 'poly[R]_n
    (@MeetSemilatticeMixin _ _ polyI _ _ _ _).

Next Obligation.
by move=> P Q; apply/poly_eqP=> x; rewrite !mem_polyI andbC.
Qed.

Next Obligation.
by move=> P1 P2 P3; apply/poly_eqP=> x; rewrite !mem_polyI andbA.
Qed.

Next Obligation.
by move=> P; apply/poly_eqP=> x; rewrite !mem_polyI andbb.
Qed.

Next Obligation.
apply/poly_leP/eqP => [|<-]; last first.
+ by move=> c; rewrite mem_polyI => /andP[].
move=> le_xy; apply/poly_eqP=> c; rewrite mem_polyI.
by apply: andb_idr; apply: le_xy.
Qed.

Program Definition poly_bottomMixin :=
  @BottomMixin polyh_display [porderType of 'poly[R]_n] poly0 _.
Next Obligation. by apply/poly_leP=> v; rewrite mem_poly0. Qed.

Canonical poly_B :=
  Eval hnf in BSemilatticeType 'poly[R]_n poly_bottomMixin.

Definition polyT : 'poly[R]_n := '[ H.polyT ].

Definition bounded (P : 'poly[R]_n) c := H.bounded (hrepr P) c.
Definition pointed (P : 'poly[R]_n) := H.pointed (hrepr P).
Definition lift_poly (k : nat) (P : 'poly[R]_n) : 'poly[R]_(n+k) := '[ H.lift_poly k (hrepr P)].

Lemma in_poly0 : poly0 =i pred0.
Proof. by move => ?; rewrite repr_equiv H.in_poly0. Qed.

Lemma in_polyT : polyT =i predT.
Proof. by move => ?; rewrite repr_equiv H.in_polyT. Qed.
End PolyPred.

Notation poly_le   := (@Order.le polyh_display _) (only parsing).
Notation poly_lt   := (@Order.lt polyh_display _) (only parsing).
Notation poly_ge   := (@Order.ge polyh_display _) (only parsing).
Notation poly_gt   := (@Order.gt polyh_display _) (only parsing).
Notation poly_leif := (@Order.leif polyh_display _) (only parsing).
Notation poly_cmp  := (@Order.comparable polyh_display _) (only parsing).
Notation poly_meet := (@Order.meet polyh_display _).

Notation "<=%P"  := poly_le   : fun_scope.
Notation ">=%P"  := poly_ge   : fun_scope.
Notation "<%P"   := poly_lt   : fun_scope.
Notation ">%P"   := poly_gt   : fun_scope.
Notation "<?=%P" := poly_leif : fun_scope.
Notation ">=<%P" := poly_cmp  : fun_scope.
Notation "><%P"  := (fun x y => ~~ (poly_cmp x y)) : fun_scope.

Notation "`<=` y" := (poly_ge y) : poly_scope.
Notation "`<=` y :> T" := (`<=` (y : T)) (only parsing) : poly_scope.
Notation "`>=` y"  := (poly_le y) : poly_scope.
Notation "`>=` y :> T" := (`>=` (y : T)) (only parsing) : poly_scope.

Notation "`<` y" := (poly_gt y) : poly_scope.
Notation "`<` y :> T" := (`<` (y : T)) (only parsing) : poly_scope.
Notation "`>` y" := (poly_lt y) : poly_scope.
Notation "`>` y :> T" := (`>` (y : T)) (only parsing) : poly_scope.

Notation "`>=<` y" := (poly_cmp y) : poly_scope.
Notation "`>=<` y :> T" := (`>=<` (y : T)) (only parsing) : poly_scope.

Notation "`><` y" := (fun x => ~~ (poly_cmp y x)) : poly_scope.
Notation "`><` y :> T" := (`><` (y : T)) (only parsing) : poly_scope.

Notation "x `<=` y" := (poly_le x y) : poly_scope.
Notation "x `<=` y :> T" := ((x : T) `<=` (y : T)) (only parsing) : poly_scope.
Notation "x `>=` y" := (y `<=` x) (only parsing) : poly_scope.
Notation "x `>=` y :> T" := ((x : T) `>=` (y : T)) (only parsing) : poly_scope.

Notation "x `<` y"  := (poly_lt x y) : poly_scope.
Notation "x `<` y :> T" := ((x : T) `<` (y : T)) (only parsing) : poly_scope.
Notation "x `>` y"  := (y `<` x) (only parsing) : poly_scope.
Notation "x `>` y :> T" := ((x : T) `>` (y : T)) (only parsing) : poly_scope.

Notation "x `<=` y `<=` z" := ((x `<=` y) && (y `<=` z)) : poly_scope.
Notation "x `<` y `<=` z" := ((x `<` y) && (y `<=` z)) : poly_scope.
Notation "x `<=` y `<` z" := ((x `<=` y) && (y `<` z)) : poly_scope.
Notation "x `<` y `<` z" := ((x `<` y) && (y `<` z)) : poly_scope.

Notation "x `<=` y ?= 'iff' C" := (poly_leif x y C) : poly_scope.
Notation "x `<=` y ?= 'iff' C :> R" := ((x : R) `<=` (y : R) ?= iff C)
  (only parsing) : poly_scope.

Notation "x `>=<` y" := (poly_cmp x y) : poly_scope.
Notation "x >< y" := (~~ (poly_cmp x y)) : poly_scope.

Notation "'[' 'poly0' ']'" := (@Order.bottom polyh_display _) : poly_scope.
Notation "'[' 'polyT' ']'" := (@polyT _ _) : poly_scope.

Notation "P `&` Q" := (poly_meet P Q) (at level 48, left associativity) : poly_scope.

Notation "\polyI_ ( i <- r | P ) F" :=
  (\big[polyI/[polyT]%PH]_(i <- r | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i <- r ) F" :=
  (\big[polyI/[polyT]%PH]_(i <- r) F%PH) : poly_scope.
Notation "\polyI_ ( i | P ) F" :=
  (\big[polyI/[polyT]%PH]_(i | P%B) F%PH) : poly_scope.
Notation "\polyI_ i F" :=
  (\big[polyI/[polyT]%PH]_i F%PH) : poly_scope.
Notation "\polyI_ ( i : I | P ) F" :=
  (\big[polyI/[polyT]%PH]_(i : I | P%B) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( i : I ) F" :=
  (\big[polyI/[polyT]%PH]_(i : I) F%PH) (only parsing) : poly_scope.
Notation "\polyI_ ( m <= i < n | P ) F" :=
 (\big[polyI/[polyT]%PH]_(m <= i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( m <= i < n ) F" :=
 (\big[polyI/[polyT]%PH]_(m <= i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i < n | P ) F" :=
 (\big[polyI/[polyT]%PH]_(i < n | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i < n ) F" :=
 (\big[polyI/[polyT]%PH]_(i < n) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A | P ) F" :=
 (\big[polyI/[polyT]%PH]_(i in A | P%B) F%PH) : poly_scope.
Notation "\polyI_ ( i 'in' A ) F" :=
 (\big[polyI/[polyT]%PH]_(i in A) F%PH) : poly_scope.

Section Order.
Context {R : realFieldType} (n : nat).

Lemma poly_subset_mono (P Q : 'hpoly[R]_n) : '[P] `<=` '[Q] = H.poly_subset P Q.
Proof.
apply/poly_subsetP/H.poly_subsetP => [H | H] x x_in_P.
- have /H: x \in '[P] by rewrite repr_equiv.
  by rewrite repr_equiv.
- rewrite !repr_equiv in x_in_P *; exact: H.
Qed.

Lemma poly_subsetPn {P Q : 'poly[R]_n} :
  reflect (exists2 x, (x \in P) & (x \notin Q)) (~~ (P `<=` Q)).
Proof.
by apply: (iffP H.poly_subsetPn) => [[x] H | [x] H]; exists x.
Qed.

Lemma poly_eq0Pn {P : 'poly[R]_n} : reflect (exists x, x \in P) (P != [poly0]).
Proof.
have := @poly_subsetPn P [poly0]; rewrite lex0; case=> h; constructor.
+ by case: h=> x xP _; exists x.
+ by case=> x xP; apply: h; exists x => //; rewrite in_poly0.
Qed.

Lemma in_polyI (P Q : 'poly[R]_n) x : (x \in (P `&` Q)) = ((x \in P) && (x \in Q)).
Proof.
by rewrite !repr_equiv H.in_polyI.
Qed.

Lemma polyI_mono (P Q : 'hpoly[R]_n) : '[P] `&` '[Q] = '[H.polyI P Q].
Proof.
apply/poly_eqP => x.
by rewrite in_polyI !repr_equiv H.in_polyI.
Qed.

Lemma big_polyI_mono (I : Type) (r : seq I) (P : pred I) (F : I -> 'hpoly[R]_n) :
  \polyI_(i <- r | P i) '[F i] = '[\big[H.polyI/H.polyT]_(i <- r | P i) (F i)].
Proof.
have class_of_morph : {morph (fun x : 'hpoly[R]_n => '[x]) : x y / H.polyI x y >-> x `&` y}.
- by move => Q Q'; rewrite polyI_mono.
have polyT_mono : '[H.polyT] = polyT by done.
by rewrite (@big_morph _ _ _ _ _ _ _ class_of_morph (@polyT_mono _ _)).
Qed.

Let inE := (@in_poly0, @in_polyT, in_polyI, inE).

Lemma polyIC : commutative (@polyI R n).
Proof. by apply: meetC. Qed.

Lemma polyIA : associative (@polyI R n).
Proof. by apply: meetA. Qed.

Lemma polyTI : left_id [polyT] (@polyI R n).
Proof.
by move => P; apply/poly_eqP => x; rewrite !inE.
Qed.

Lemma polyIT : right_id [polyT] (@polyI R n).
Proof.
by move => P; apply/poly_eqP => x; rewrite !inE andbT.
Qed.

Canonical polyI_monoid := Monoid.Law polyIA polyTI polyIT.
Canonical polyI_comonoid := Monoid.ComLaw polyIC.

Lemma in_big_polyIP (I : finType) (P : pred I) (F : I -> 'poly[R]_n) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \polyI_(i | P i) (F i)).
Proof.
have -> : (x \in \polyI_(i | P i) F i) = (\big[andb/true]_(i | P i) (x \in (F i))).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?in_polyT ?in_polyI.
by rewrite big_all_cond; apply: (iffP allP) => /= [H i | H i ?];
  apply/implyP/H; exact: mem_index_enum.
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
by move => ? ?; apply/(@le_trans _ _ (F j)); [apply: big_poly_inf | done].
Qed.

Lemma big_polyIsP (I : finType) Q (P : pred I) (F : I -> 'poly[R]_n) :
  reflect (forall i : I, P i -> Q `<=` F i) (Q `<=` \polyI_(i | P i) F i).
Proof. (* RK *)
apply: (iffP idP) => [Q_subset_polyI ? ? | forall_Q_subset].
- by apply/(le_trans Q_subset_polyI)/big_poly_inf.
- apply/poly_subsetP => x x_in_Q.
  apply/in_big_polyIP => j P_j.
  by move: x x_in_Q; apply/poly_subsetP; exact: forall_Q_subset.
Qed.

Lemma in_lift_poly (k : nat) (P : 'poly[R]_n) x :
  (x \in lift_poly k P) = (usubmx x \in P).
Proof.
by rewrite repr_equiv H.lift_polyP mem_polyE.
Qed.

Lemma mem_poly_convex (P : 'poly[R]_n) :
  convex_pred (mem P).
Proof.
by move => ??????; apply/H.convexP2.
Qed.

CoInductive empty_spec (P : 'poly[R]_n) : bool -> bool -> bool -> Set :=
| Empty of (P = [poly0]) : empty_spec P false true true
| NonEmpty of (P `>` [poly0]) : empty_spec P true false false.

Lemma emptyP P : empty_spec P (P  `>` [poly0]) (P == [poly0]) (P `<=` [poly0]).
Proof. by rewrite lex0 lt0x; case: posxP => ?; constructor. Qed.

Lemma proper0P {P : 'poly[R]_n} :
  reflect (exists x, x \in P) (P `>` [poly0]).
Proof. by rewrite lt0x; apply: poly_eq0Pn. Qed.

Definition ppick P : 'cV[R]_n :=
  match (@proper0P P) with
  | ReflectT P_non_empty => xchoose P_non_empty
  | ReflectF _ => 0
  end.

Lemma ppickP {P} : (P `>` [poly0]) -> ppick P \in P.
Proof. (* RK *)
rewrite /ppick; case: proper0P => [? _ | _] //; exact: xchooseP.
Qed.

Lemma poly_properP {P Q : 'poly[R]_n} :
  (* FIXME: STRUB: simplify *)
  (* TODO: should {subset P <= Q} to (P `<=` Q) ? *)
  reflect ({subset P <= Q} /\ exists2 x, x \in Q & x \notin P) (P `<` Q).
Proof.
apply: (iffP andP).
+ case=> ne_QP le_PQ; split; first by apply/poly_subsetP.
  move: ne_QP; rewrite poly_eqE /poly_equiv le_PQ andbT.
  by move/poly_subsetPn.
case=> /poly_subsetP => -> [x xQ xPN]; split=> //.
by apply/negP=> /eqP/poly_eqP /(_ x); rewrite xQ (negbTE xPN).
Qed.

End Order.

Section BasicObjects.

Context {R : realFieldType} (n : nat).

Implicit Type (e : lrel[R]_n) (V : 'affine[R]_n).

Definition mk_hs b : 'poly[R]_n := '[ H.mk_hs b ].
Notation "'[' 'hs' b ']'" := (mk_hs b) : poly_scope.

Lemma in_hs :
    (forall (b : lrel[R]_n) x, x \in [hs b] = ('[b.1,x] >= b.2))
  * (forall (c : 'cV_n) (α : R) x, x \in [hs [<c, α>]] = ('[c,x] >= α)).
Proof.
set t := (forall b, _).
suff Ht: t by split; [ | move => c α x; rewrite Ht ].
by move => b x; rewrite repr_equiv H.in_hs.
Qed.

Lemma notin_hs :
  (forall (b : lrel[R]_n) x, (x \notin [hs b]) = ('[b.1,x] < b.2))
  * (forall (c : 'cV_n) (α : R) x, (x \notin [hs [<c, α>]]) = ('[c,x] < α)).
Proof.
set t := (forall b, _).
suff Ht: t by split; [ | move => c α x; rewrite Ht ].
by move => b x; rewrite in_hs ltNge.
Qed.

Lemma in_hsN (e : lrel[R]_n) x : (x \in [hs -e]) = ('[e.1,x] <= e.2).
Proof.
by rewrite in_hs /= vdotNl ler_opp2.
Qed.

Definition aff V : 'poly[R]_n :=
  match affineP V with
  | Affine0 => poly0
  | Affine V _ =>
    let U := vbasis V in
    \polyI_(i < \dim V) ([hs U`_i] `&` [hs (- U`_i)]) (* define on sequence instead *)
  end.

Notation "V %:PH" := (aff V) (at level 2, left associativity, format "V %:PH").

Lemma eq_subl (T : Type) (m m' m'': mem_pred T) :
  m =i m' -> {subset m <= m''} -> {subset m' <= m''}.
Proof.
by move => eq sub x x_in; apply/sub; rewrite eq.
Qed.

Lemma eq_subr (T : Type) (m m' m'': mem_pred T) :
  m' =i m'' -> {subset m <= m'} -> {subset m <= m''}.
Proof.
by move => eq sub x x_in; rewrite -eq; apply/sub.
Qed.

Lemma affE {V : 'affine[R]_n} : V %:PH =i V.
Proof.
rewrite /aff.
case/affineP: V.
- by move => x; rewrite in_poly0 in_affine0.
- move => U _ x.
  rewrite in_affineE.
  apply/in_big_polyIP/allP => h.
  + move => e /tnthP [i ->].
    apply/eqP/le_anti; move/(_ i isT): h.
    by rewrite in_polyI in_hsN in_hs andbC (tnth_nth 0).
  + move => i _.
    rewrite in_polyI in_hsN in_hs.
    move/(_ _ (mem_tnth i (vbasis U)))/eqP: h.
    rewrite (tnth_nth 0) => ->.
    by rewrite lexx.
Qed.

Lemma hpE e : [hp e]%:PH = [hs e] `&` [hs (-e)] :> 'poly[R]_n.
Proof.
apply/poly_eqP => x.
by rewrite affE in_hp in_polyI in_hsN in_hs lte_anti eq_sym.
Qed.

Lemma aff_inj : injective aff.
Proof.
move => V V' /poly_eqP eq.
by apply/affine_eqP => x; move/(_ x): eq; rewrite !affE.
Qed.

Lemma affI : {morph aff : V V' / Order.meet V V' >-> Order.meet V V'}.
Proof.
by move => V V'; apply/poly_eqP => x; rewrite in_polyI !affE in_affineI.
Qed.

Lemma affS : {mono aff : V V' / (V <= V')%O >-> (V `<=` V')}.
Proof.
move => ??.
by apply/poly_leP/affine_leP => incl x; rewrite ?affE => x_in;
   move/(_ x): incl; rewrite ?affE  => /(_ x_in).
Qed.

Lemma aff0 : affine0%:PH = [poly0] :> 'poly[R]_n.
Proof.
apply/poly_eqP => x.
by rewrite affE in_affine0 in_poly0.
Qed.

Lemma affT : affineT%:PH = [polyT] :> 'poly[R]_n.
Proof.
apply/poly_eqP => x.
by rewrite affE in_affineT in_polyT.
Qed.

Lemma aff_bigI (I : finType) (P : pred I) (F : I -> 'affine[R]_n) :
  (\affineI_(i | P i) (F i))%:PH = (\polyI_(i | P i) (F i)%:PH).
Proof.
by rewrite (big_morph aff affI affT).
Qed.

Lemma aff_eq0 (V : 'affine[R]_n) : V%:PH = [poly0] -> V = affine0.
Proof.
by rewrite -aff0; apply/aff_inj.
Qed.

Lemma aff_ltE (V V' : 'affine[R]_n) : (V%:PH `<` V'%:PH) = (V < V')%O.
Proof.
by rewrite lt_def affS (inj_eq aff_inj).
Qed.

Lemma aff_lt0x (V : 'affine[R]_n) : (aff V `>` [poly0]) = (V != affine0).
Proof.
by rewrite lt0x -aff0 (inj_eq aff_inj).
Qed.

Let inE := (@in_poly0, @in_polyT, @affE, @in_hp, in_hs, @in_polyI, inE).

Lemma notin_hp b x :
  (x \in [hs b]) -> (x \notin [hp b]) = ('[b.1, x] > b.2).
Proof.
by rewrite lt_def in_hs => ->; rewrite in_hp andbT.
Qed.

Lemma hs_hp c (x : lrel[R]_n) : c \in [hp x] -> c \in [hs x].
Proof. by rewrite !inE => /eqP->. Qed.

Lemma hsN_hp c (x : lrel[R]_n) : c \in [hp x] -> c \in [hs -x].
Proof. by rewrite !inE => /eqP /= <-; rewrite vdotNl. Qed.

Lemma hsN_subset (e : lrel[R]_n) x : (x \notin [hs -e]) -> x \in [hs e].
Proof.
by rewrite in_hsN -ltNge in_hs => /ltW.
Qed.

Lemma hp_subset_hs (e : lrel[R]_n) : [hp e]%:PH `<=` [hs e].
Proof.
by apply/poly_subsetP => x; rewrite !inE => /eqP ->.
Qed.

Lemma hsC_convex (e : lrel[R]_n) : convex_pred [predC [hs e]].
Proof.
move => x y x_in y_in α /andP [α_ge0 α_le1]; rewrite !inE -!ltNge in x_in y_in *.
rewrite vdotDr !vdotZr.
case: (ltrP '[e.1,x] '[e.1,y]) => [/ltW ?|?].
- apply/le_lt_trans: y_in.
  have {2}->: '[ e.1, y] = (1 - α) * '[ e.1, y] + α * '[ e.1, y].
  + by rewrite mulrBl mul1r addrAC -addrA addrN addr0.
  + by rewrite ler_add ?ler_wpmul2l ?subr_ge0.
- apply/le_lt_trans: x_in.
  have {2}->: '[ e.1, x] = (1 - α) * '[ e.1, x] + α * '[ e.1, x].
  + by rewrite mulrBl mul1r addrAC -addrA addrN addr0.
  + by rewrite ler_add ?ler_wpmul2l ?subr_ge0.
Qed.

Lemma poly_subset_hsP {P : 'poly[R]_n} {b : lrel} :
  reflect (forall x, x \in P -> '[fst b, x] >= snd b) (P `<=` [hs b]).
Proof.
apply: (iffP poly_subsetP) => [sub x x_in_P | sub x x_in_P ];
  move/(_ _ x_in_P): sub; by rewrite in_hs.
Qed.

Lemma hs_antimono (c : 'cV_n) (d d' : R) :
  d <= d' -> [hs [<c, d'>]] `<=` [hs [<c, d>]]. (* RK *)
Proof.
move => d_le_d'.
apply/poly_subset_hsP => x.
rewrite inE => ?.
by apply: (le_trans d_le_d' _).
Qed.

Lemma hp_itv (e : lrel[R]_n) (y z: 'cV[R]_n) :
  y \in [hs e] -> z \notin [hs e] ->
    exists2 α, (0 <= α < 1) & (1-α) *: y + α *: z \in [hp e].
Proof.
rewrite !inE -ltNge => Hy Hz.
set α := (e.2 - '[e.1, y])/('[e.1,z] - '[e.1,y]).
have z_lt_y: '[e.1,z] < '[e.1, y] by exact : (lt_le_trans Hz).
have neq0: '[e.1,z] - '[e.1, y] != 0 by rewrite subr_eq0 ltr_neq.
exists α.
- apply/andP; split.
  + by rewrite /α mulr_le0 // 1?invr_le0 subr_le0 // ?ltW.
  + by rewrite lter_ndivr_mulr ?subr_lt0 // mul1r ltr_add2r.
- by rewrite inE vdotDr !vdotZr mulrBl mul1r addrAC -addrA -mulrBr divfK // addrCA addrN addr0.
Qed.

Lemma hp_extremeL b x y α :
  (x \in [hs b]) -> (y \in [hs b]) ->
  0 <= α < 1 -> ((1-α) *: x + α *: y \in [hp b]) -> (x \in [hp b]).
Proof.
rewrite !inE.
move => x_in y_in /andP [α_ge0 α_lt1].
case: (α =P 0) => [->| /eqP α_neq0].
- by rewrite subr0 scale0r scale1r addr0.
- have α_gt0 : α > 0 by rewrite lt0r; apply/andP; split.
  rewrite {α_ge0} vdotDr 2!vdotZr.
  apply: contraTT => x_notin_hp.
  have x_notin_hp' : '[ b.1, x] > b.2.
  + by rewrite lt_def; apply/andP; split.
  have bary_in_hs : (1-α) *: x + α *: y \in [hs b].
  + apply: mem_poly_convex; try by rewrite inE.
    * by apply/andP; split; apply: ltW.
  rewrite (* inE *) in_hs vdotDr 2!vdotZr in bary_in_hs. (* TODO: here, rewrite inE loops, why? *)
  suff: b.2 < (1 - α) * '[ b.1, x] + α * '[b.1, y].
  + by rewrite lt_def bary_in_hs andbT.
  have ->: b.2 = (1 - α) * b.2 + α * b.2.
  + by rewrite mulrBl -addrA addNr mul1r addr0.
  + by apply: ltr_le_add; rewrite lter_pmul2l // subr_gt0.
Qed.

Lemma hp_extremeR b x y α :
  (x \in [hs b]) -> (y \in [hs b]) ->
  0 < α <= 1 -> ((1-α) *: x + α *: y \in [hp b]) -> (y \in [hp b]).
Proof.
move => x_in y_in /andP [α_ge0 α_lt1]; rewrite combine2C.
apply: hp_extremeL => //; apply/andP; split.
- by rewrite subr_cp0.
- by rewrite cpr_add oppr_lt0.
Qed.

Lemma boundedP {P : 'poly[R]_n} {c} :
  reflect (exists2 x, x \in P & P `<=` [hs [<c, '[c,x]>]]) (bounded P c).
Proof.
have eq x : (P `<=` [hs [<c,'[ c, x]>]]) =
            H.poly_subset (hrepr P) (H.mk_hs [<c, '[c, x]>]).
by apply: (sameP H.poly_subsetP);
     apply: (iffP H.poly_subsetP) => sub z;
     move/(_ z): sub; rewrite H.in_hs in_hs.
by apply: (iffP (H.boundedP _ _)) => [[x] H H' | [x] H H']; exists x; rewrite ?inE ?eq in H' *.
Qed.

Lemma boundedPP {P : 'poly[R]_n} {c} :
  reflect (exists x, (x \in P) && (P `<=` [hs [<c, '[c, x]>]])) (bounded P c).
Proof.
by apply/(iffP boundedP) => [[x] ?? | [x] /andP [??]];
  exists x; first by apply/andP; split.
Qed.

Lemma boundedN0 {P : 'poly[R]_n} {c} :
  bounded P c -> P `>` [poly0].
Proof.
case/boundedP=> [x x_in_P _].
by apply/proper0P; exists x.
Qed.

Lemma boundedPn {P : 'poly[R]_n} {c} :
  (P `>` [poly0]) -> reflect (forall K, exists2 x, x \in P & '[c,x] < K) (~~ bounded P c).
Proof.
(*rewrite -subset0N_proper; move => P_non_empty.*)
move => P_neq0.
have hreprP_neq0: ~~ H.poly_subset (hrepr P) H.poly0.
- move: P_neq0; rewrite lt0x.
  apply: contraNN => /H.poly_subsetP incl; rewrite -lex0.
  by apply/poly_subsetP=> x /incl; rewrite H.in_poly0.
apply: (iffP (H.boundedPn _ hreprP_neq0)) => [H K | H K]; move/(_ K): H.
- move/H.poly_subsetPn => [x x_in_P x_not_in_hs].
  by exists x; rewrite H.in_hs -ltNge in x_not_in_hs.
- move => [x x_in_P c_x_lt_K].
  by apply/H.poly_subsetPn; exists x; rewrite ?H.in_hs -?ltNge.
Qed.

Lemma bounded_mono1 (P Q : 'poly[R]_n) c :
  bounded P c -> [poly0] `<` Q `<=` P -> bounded Q c.
Proof. (* RK *)
move => /boundedPP [x /andP [_ /poly_subsetP sPhs]] /andP [Q_non_empty /poly_subsetP sQP].
apply/contraT => /(boundedPn Q_non_empty) Q_unbounded.
move: (Q_unbounded '[ c, x]) => [y y_in_Q x_y_vdot_sineq].
suff : ('[ c, x] <= '[ c, y]) by rewrite leNgt x_y_vdot_sineq.
by move/sQP/sPhs : y_in_Q; rewrite in_hs.
Qed.

Lemma bounded_poly0 c : @bounded R n [poly0] c = false.
Proof.
by apply: (introF idP) => /boundedP [?]; rewrite inE.
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
  P `<=` [ hs [<c, opt_value bounded_P>]].
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
    P `&` [hp [<c, opt_value H>]]%:PH
  else
    [poly0].

Lemma argmin_polyI P c (bounded_P : bounded P c) :
  argmin P c = P `&` [hp [<c, opt_value bounded_P>]]%:PH.
Proof.
by rewrite /argmin; case: {-}_/idP => [b' | ?]; rewrite ?[bounded_P]eq_irrelevance.
Qed.

Lemma in_argmin P c x :
  x \in argmin P c = (x \in P) && (P `<=` [hs [<c, '[c, x]>]]).
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
    rewrite -lte_anti; apply/andP; split.
    * move/opt_point : (c_bounded) => [z z_in_P <-].
      by move/poly_subsetP/(_ _ z_in_P): subset; rewrite in_hs.
    * rewrite -in_hs; by apply/(poly_subsetP (opt_value_lower_bound _)).
Qed.

Lemma bounded_argminN0 P c :
  (bounded P c) = (argmin P c `>` [poly0]).
Proof. (* RK *)
apply/idP/idP => [/boundedP [x ? ?] | /proper0P [x]].
- apply/proper0P; exists x.
  by rewrite in_argmin; apply/andP.
- rewrite in_argmin => /andP [? ?].
  by apply/boundedP; exists x.
Qed.

Lemma argmin_subset P c : argmin P c `<=` P.
Proof. (* RK *)
rewrite /argmin; case: {-}_/idP => [bounded_P | _].
+ by apply: leIl. + by apply: le0x.
Qed.

Lemma argmin_opt_value P c (bounded_P : bounded P c) :
  argmin P c `<=` [hp [<c, opt_value bounded_P>]]%:PH.
Proof. (* RK *)
rewrite argmin_polyI; exact: leIr.
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
apply/eqP; rewrite eq_le; apply/andP; split; last by apply: opt_value_antimono1.
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
move => bounded_Q /andP [? ?]; rewrite (rwP eqP) eq_le.
rewrite {-2}/argmin; case: {-}_/idP => [bounded_P | unbounded_P]; apply/andP; split.
- rewrite argmin_polyI (subset_opt_value bounded_P bounded_Q _); last by apply/andP.
  by apply/leI2; [done | exact: lexx].
- rewrite lexI -(rwP andP); split; first by done.
  rewrite (subset_opt_value bounded_P bounded_Q _); last by apply/andP.
  exact: argmin_opt_value.
- by apply: le0x.
- move/negP: unbounded_P; apply/contraR.
  rewrite lex0 -lt0x => non_empty_argmin_Q_c.
  apply/(bounded_mono1 bounded_Q _)/andP; split; last by done.
  by apply/(lt_le_trans non_empty_argmin_Q_c).
Qed.

Lemma argmin_eq {P} {c v x} :
  v \in argmin P c -> reflect (x \in P /\ '[c,x] = '[c,v]) (x \in argmin P c).
Proof. (* RK *)
move => v_in_argmin; rewrite in_argmin.
apply: (iffP idP) => [/andP [? /poly_subsetP sPhs] | [? ->]].
- split; first by done.
  apply/eqP; rewrite eq_le; apply/andP; split; last by apply: (argmin_lower_bound v_in_argmin _).
  by rewrite -in_hs; apply/sPhs/(poly_subsetP (argmin_subset _ c)).
- apply/andP; split; first by done.
  rewrite in_argmin in v_in_argmin.
  exact: (proj2 (andP v_in_argmin)).
Qed.

Lemma bounded_lower_bound (P : 'poly[R]_n) c :
  (P `>` [poly0]) -> reflect (exists d, P `<=` [hs [<c, d>]]) (bounded P c).
Proof.
move => P_non_empty; apply: introP => [ c_bounded | /(boundedPn P_non_empty) c_unbouded ].
- exists (opt_value c_bounded); exact: opt_value_lower_bound.
- move => [d c_bounded]; move/(_ d): c_unbouded => [x x_in_P c_x_lt_K].
  by move/poly_subsetP/(_ _ x_in_P): c_bounded; rewrite in_hs leNgt => /negP.
Qed.

Lemma notin_argmin (P : 'poly_n) (c : 'cV[R]_n) (bounded_P : bounded P c) :
  forall x, x \in P -> x \notin argmin P c -> x \notin [hs - ([<c, opt_value bounded_P>])].
Proof.
move => x x_in_P; apply/contra.
rewrite argmin_polyI in_polyI x_in_P /=.
rewrite hpE in_polyI andbC => -> /=.
by move: x_in_P; apply/poly_subsetP/opt_value_lower_bound.
Qed.

Lemma argmin_polyIN (P : 'poly[R]_n) (c : 'cV_n) (bounded_P : bounded P c) :
  argmin P c = P `&` [hs -[<c, opt_value bounded_P>]].
Proof.
rewrite argmin_polyI hpE meetA [X in X `&` _ = _]meet_l //.
by apply: opt_value_lower_bound.
Qed.

Lemma ex_iff T (P1 P2 : T -> Prop) :
  (forall x : T, P1 x <-> P2 x) -> ((exists x, P1 x) <-> (exists x, P2 x)).
Proof.
by move=> H; split; move=> [x Hx]; exists x; apply H.
Qed.

Lemma ex2_iff T (P1 P2 Q : T -> Prop) :
  (forall x : T, P1 x <-> P2 x) -> ((exists2 x, P1 x & Q x) <-> (exists2 x, P2 x & Q x)).
Proof.
Admitted.

Lemma line_subset_hs (e : lrel[R]_n) (Ω c : 'cV[R]_n) :
  Ω \in [hs e] -> ([line c & Ω ]%:PH `<=` [hs e]) = ('[e.1,c] == 0).
Proof.
move => Ω_in_e.
apply/idP/eqP.
- apply/contraTeq => e_c_neq0; apply/poly_subsetPn.
  under ex2_iff do rewrite affE.
  exists (Ω + (e.2 - 1 - '[e.1, Ω])/'[e.1, c] *: c).
  + by apply/in_lineP; exists ((e.2 - 1 - '[e.1, Ω])/'[e.1, c]).
  + by rewrite inE vdotDr vdotZr divfK // addrCA addrN addr0 lter_sub_addr cpr_add ler10.
- move => e_c_eq0; apply/poly_subsetP => x; rewrite affE => /in_lineP [μ ->].
  by rewrite inE vdotDr vdotZr e_c_eq0 mulr0 addr0 -in_hs.
Qed.

Lemma pointed0 : @pointed R n [poly0].
Proof.
rewrite /pointed /H.pointed /=.
suff ->: H.poly_subset (@hrepr R n [poly0]) H.poly0 by done.
by apply/H.poly_subsetP => x; rewrite repr_equiv.
Qed.

Lemma pointedPn P :
  reflect (exists Ω, exists2 d, d != 0 & [line d & Ω]%:PH `<=` P) (~~ (pointed P)).
Proof.
apply/(iffP (H.pointedPn _)) => [[x [d] d_neq0 sub]| [x [d] d_neq0 sub]]; exists x; exists d => //.
- by apply/poly_subsetP => ?; rewrite affE => /in_lineP [μ ->]; apply/sub.
- by move => μ; apply/(poly_subsetP sub); rewrite affE; apply/in_lineP; exists μ.
Qed.

Lemma pointedS (P Q : 'poly[R]_n) :
  P `<=` Q -> pointed Q -> pointed P.
Proof.
move => P_sub_Q.
apply: contraTT; move/pointedPn => [Ω [c c_neq0 line_sub]].
apply/pointedPn; exists Ω; exists c => //.
by apply/(le_trans line_sub).
Qed.

Definition mk_hline (c Ω : 'cV[R]_n) :=
  [hs [<c, '[c,Ω]>]] `&` [line c & Ω]%:PH.

Notation "'[' 'hline' c & Ω ']'" := (mk_hline c Ω) : poly_scope.

Lemma in_hlineP (c Ω x : 'cV[R]_n) :
  reflect (exists2 μ, μ >= 0 & x = Ω + μ *: c) (x \in [hline c & Ω]).
Proof.
rewrite !inE; apply: (iffP andP).
- move => [c_x_ge_c_Ω /in_lineP [μ x_eq]].
  rewrite x_eq in c_x_ge_c_Ω *.
  case: (c =P 0) => [-> | c_neq0].
  + exists 0; rewrite ?scaler0 //.
  + exists μ => //.
    rewrite vdotDr ler_addl vdotZr pmulr_lge0 // in c_x_ge_c_Ω.
    by rewrite vnorm_gt0; apply/eqP.
- move => [μ μ_ge0 ->]; split; last by apply/in_lineP; exists μ.
  rewrite vdotDr ler_addl vdotZr.
  by apply: mulr_ge0; rewrite ?vnorm_ge0.
Qed.

Definition compact (P : 'poly[R]_n) :=
  (P `>` [poly0]) ==>
    [forall i, (bounded P (delta_mx i 0)) && (bounded P (-(delta_mx i 0)))].

Lemma compact0 : compact ([poly0]).
Proof.
by rewrite /compact ltxx.
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
      apply: le_trans; set v := (X in _ <= X);
      suff: Num.min (opt_value (ei i)) (opt_value (mei i)) <= v
        by apply: le_trans; apply: min_seq_ler; apply: map_f; rewrite mem_enum.
      - rewrite leIx; apply/orP; left; exact: lexx.
      - rewrite leIx; apply/orP; right; exact: lexx.
  + apply/forallP => i; apply/andP; split;
      [pose v := (delta_mx i 0):'cV[R]_n | pose v := (-(delta_mx i 0):'cV[R]_n)%R];
    apply/bounded_lower_bound => //; exists (-K)%R;
    apply/poly_subsetP => x x_in_P; move/(_ _ x_in_P i): H;
    rewrite inE /=  ?vdotNl vdotl_delta_mx ?ler_opp2;
    by rewrite ler_norml; move/andP => [? ?].
- move => -> /=; constructor.
  by exists 0; move => x; rewrite inE.
Qed.

Lemma compactP P :
  (P `>` [poly0]) -> reflect (forall c, bounded P c) (compact P).
Proof.
move => P_neq0.
apply: (iffP idP) => [/compactP_Linfty [K H] c | ?].
- pose v := (- \sum_i `|c i 0| * K)%R.
  suff foo: P `<=` [hs [<c, v>]].
  + apply/bounded_lower_bound => //.
    by exists v.
  + apply/poly_subsetP => x x_in_P.
    have: `|'[c,x]| <= \sum_i `|c i 0| * K.
    suff: \sum_i `|c i 0 * x i 0| <= \sum_i `|c i 0| * K.
    * apply: le_trans; rewrite /vdot; exact: ler_norm_sum.
    apply: ler_sum => i _; rewrite normrM.
    apply: ler_wpmul2l; [ exact: normr_ge0 | exact: H ].
    by rewrite ler_norml => /andP [? _]; rewrite inE.
- rewrite /compact P_neq0 /=.
  by apply/forallP => i; apply/andP; split.
Qed.

Lemma compact_pointed P :
  compact P -> pointed P.
Proof.
case: (emptyP P) => [->| P_neq0 P_compact]; rewrite ?pointed0 //.
apply: contraT => /pointedPn [Ω [c]] c_neq0 /poly_subsetP hl_sub.
suff: ~~ (bounded P c) by move/(compactP P_neq0)/(_ c) : P_compact => ->.
apply/boundedPn => // K.
pose μ := ((K - 1 - '[c,Ω])/'[| c |]^2)%R.
exists (Ω + μ *: c); first by apply/hl_sub; rewrite affE; apply/in_lineP; exists μ.
rewrite vdotDr vdotZr mulfVK ?lt0r_neq0 ?vnorm_gt0 //.
by rewrite addrCA addrN addr0 cpr_add ltrN10.
Qed.

Lemma subset_compact (P Q : 'poly[R]_n) :
  compact P -> Q `<=` P -> compact Q.
Proof.
move => P_compact Q_sub_P.
case: (emptyP Q) => [->| Q_prop0]; rewrite ?compact0 //.
apply/compactP => // c.
have P_prop0: P `>` [poly0] by apply/lt_le_trans: Q_sub_P.
have h: [poly0] `<` Q `<=` P by apply/andP; split.
by move/(compactP P_prop0)/(_ c)/bounded_mono1/(_ h): P_compact.
Qed.

Definition slice (b : lrel) P := [hp b]%:PH `&` P.

Lemma slice0 (b : lrel) : slice b ([poly0]) = [poly0].
Proof.
by rewrite /slice meetx0.
Qed.

Lemma sliceS (e : lrel[R]_n) : {homo slice e : P Q / P `<=` Q}.
Proof. by move=> ???; apply: leI2. Qed.

Lemma in_slice (e : lrel) (P : 'poly_n) c :
  c \in slice e P = (c \in [hp e]) && (c \in P).
Proof. by rewrite in_polyI affE. Qed.

Lemma le_slice (e : lrel[R]_n) P : slice e P `<=` P.
Proof. by apply/poly_subsetP=> x; rewrite in_slice => /andP[]. Qed.

Definition poly_of_base (base : base_t[R,n]) :=
  \polyI_(b : base) [hs (val b)].

Notation "''P' ( base )" := (poly_of_base (base)%fset) : poly_scope.

Lemma in_poly_of_base x (base : base_t) :
  (x \in 'P(base)) = [forall b : base, x \in [hs (val b)]].
Proof.
by rewrite in_big_polyI.
Qed.

Lemma in_poly_of_baseP (x : 'cV_n) (base : base_t) :
  reflect (forall b, b \in base -> x \in [hs b]) (x \in 'P(base)).
Proof.
rewrite in_poly_of_base. apply: (iffP forallP) => /= h.
+ by move=> b bb; apply: (h [` bb]%fset).
+ by move=> b; apply: h.
Qed.

Lemma is_poly_of_base (P : 'poly[R]_n) :
  exists base : base_t[R,n], P == 'P(base).
Proof.
case: {2}(hrepr P) (erefl (hrepr P)) => m A b eq.
exists [fset [<(row i A)^T, b i 0>] | i : 'I_m]%fset.
have equiv: forall i x, (x \in [hs [<(row i A)^T, b i 0>]]) = ((A *m x) i 0 >= b i 0)
  by move => ??; rewrite inE /= row_vdot.
apply/eqP/poly_eqP => x; rewrite mem_polyE eq inE.
apply/forallP/in_poly_of_baseP => [h ? /imfsetP [i /= _ ->] | h i].
- by rewrite equiv; apply/h.
- by rewrite -equiv; apply/h/in_imfset.
Qed.

Definition orthant :=
  let base := ((fun i => [<delta_mx i 0, 0>]) @` 'I_n)%fset in
  'P(base).

Lemma in_orthant x :
  (x \in orthant) = (x >=m 0).
Proof.
apply/in_poly_of_baseP/gev0P => [H i | H e /imfsetP [i /= _ ->]].
- move/(_ [<delta_mx i 0, 0>]) : H; rewrite in_hs vdotl_delta_mx /= => H.
  by apply/H/in_imfset. (* TODO: in_imfset doesn't work if it is replaced by the lemma below *)
- rewrite in_hs vdotl_delta_mx; exact: H.
Qed.

Lemma poly_of_base_subset_hs {base : base_t} {e : lrel} :
  e \in base -> 'P(base) `<=` [hs e].
Proof.
move => e_in_base.
pose e' := [`e_in_base]%fset; have ->: e = fsval e' by done.
exact: big_poly_inf.
Qed.

Lemma poly_of_base_antimono (base base' : base_t[R,n]) :
  (base `<=` base')%fset -> 'P(base') `<=` 'P(base).
Proof.
move/fsubsetP => sub.
apply/poly_subsetP => ??.
apply/in_poly_of_baseP => ? /sub.
by apply/in_poly_of_baseP.
Qed.

Definition polyEq (base I : base_t) :=
  [affine <<I>>]%:PH `&` 'P(base).

Notation "''P^=' ( base ; I )" := (polyEq (base)%fset (I)%fset) : poly_scope.

Fact in_polyEq x base I :
  (x \in 'P^=(base; I)) = [forall e : I, x \in [hp (val e)]] && (x \in 'P(base)).
Proof.
by rewrite in_polyI affE affine_span in_big_affineI.
Qed.

Lemma in_polyEqP x base I :
  reflect ((forall e, e \in I -> x \in [hp e]) /\ x \in 'P(base)) (x \in 'P^=(base; I)).
Proof.
rewrite in_polyEq; apply: (equivP andP); split.
+ by case=> /forallP /= h ->; split=> // e eI; apply: (h [` eI]%fset).
+ by case=> h ->; split=> //; apply/forallP=> -[/= e eI_]; apply/h.
Qed.

Lemma polyEq_eq x base I e :
  x \in 'P^=(base; I) -> e \in I -> x \in [hp e].
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
rewrite (rwP eqP) eq_le; apply/andP; split; last first.
- apply/big_polyIsP => [i Pi]; apply/polyEq_antimono; exact: bigfcup_sup.
- apply/poly_subsetP => x /in_big_polyIP x_in.
  apply/in_polyEqP; split; last first.
  rewrite /=.
  move/(_ _ Pi0): x_in; by apply/(poly_subsetP (polyEq_antimono0)).
  move => e /= /bigfcupP [i /andP [_ Pi] ?].
  exact: (polyEq_eq (x_in _ Pi)).
Qed.

Lemma polyEq1 {base: base_t[R,n]} {e} :
  'P^=(base; [fset e]%fset) = 'P(base) `&` [hp e]%:PH.
Proof.
apply/poly_eqP=> c. rewrite [RHS]in_polyI !in_polyEq andbC affE; congr (_ && _).
apply/forallP/idP => /= [h| c_in_e]; first by apply: (h [` fset11 e]%fset).
by case=> /= e'; rewrite in_fset1 => /eqP->.
Qed.

Lemma in_fslice {T : choiceType} (x : T) (A : {fset T}) y :
  y \in (x +|` A) = (y == x) || (y \in A).
Proof. by apply: in_fset1U. Qed.

Lemma nmono_in_poly_of_base (P Q : base_t[R,n]) :
  (Q `<=` P)%fset -> 'P(P) `<=` 'P(Q).
Proof.
move=> /fsubsetP leQP; apply/poly_subsetP=> x; rewrite !in_poly_of_base.
move/forallP=> /= hP; apply/forallP=> -[/= q].
by move/leQP => qP; apply: (hP [`qP]%fset).
Qed.

Lemma slice_polyEq {e : lrel} {base I : base_t[R,n]} :
  slice e 'P^=(base; I) = 'P^=(e +|` base; e +|` I).
Proof.
apply/poly_eqP=> c; rewrite in_slice; apply/andP/idP.
+ case=> ce cP; apply/in_polyEqP; split.
  - move=> b; rewrite in_fslice=> /orP[/eqP->//|bI].
    by case/in_polyEqP: cP => /(_ _ bI).
  - rewrite in_poly_of_base; apply/forallP => -[/= b].
    rewrite in_fslice => /orP[/eqP->|]; first by apply: hs_hp.
    move=> bb; case/in_polyEqP: cP => _.
    by rewrite in_poly_of_base => /forallP /= /(_ [`bb]%fset).
+ case/in_polyEqP => ceI cPeb; split.
  - by apply: ceI; rewrite in_fslice eqxx.
  apply/in_polyEqP; split; last first.
  - move: {ceI} c cPeb; apply/poly_subsetP.
    by apply/nmono_in_poly_of_base/fsubsetU1.
  by move=> b bI; apply: ceI; rewrite in_fslice bI orbT.
Qed.

Local Notation "\- I" := (-%R @` I)%fset
  (at level 2).

Definition baseEq (base I : base_t[R,n]) := (base `|` \- I)%fset.

Lemma in_oppbase (I: base_t[R,n]) x :
  (-x \in \- I) = (x \in I).
Proof. apply/imfsetP/idP => /=.
+ by case=> y yI /oppr_inj ->.
+ by move=> xI; exists x.
Qed.

Lemma in_baseEq (base I : base_t[R,n]) c :
  c \in baseEq base I = (c \in base) || (c \in \- I).
Proof. by rewrite /baseEq in_fsetU. Qed.

Lemma in_baseEqP (base I : base_t[R,n]) c :
  reflect (c \in base \/ c \in \- I) (c \in baseEq base I).
Proof. by rewrite in_baseEq; apply/orP. Qed.

Lemma fsubset_incl {T : choiceType} (E : {fset T}) (I : {fsubset E}) (x : T) :
  x \in FSubset.untag I -> x \in E.
Proof. by case: I => /= tf /fsubsetP le /le. Qed.

Lemma polyEq_flatten (base : base_t[R,n]) (I : {fsubset base}) :
  'P^=(base; I) = 'P(baseEq base I)%fset.
Proof.
apply/poly_eqP=> c; rewrite !in_polyEq; apply/andP/idP.
+ case=> /forallP /= chp cPb; rewrite in_poly_of_base.
  apply/forallP=> -[/= x /in_baseEqP[]]; last first.
  - case/imfsetP=> /= y yI -> {x}; apply: hsN_hp.
    by apply: (chp [`yI]%fset).
  - by move=> xb; move/in_poly_of_baseP: cPb; apply.
+ move/in_poly_of_baseP => /= h; split.
  - apply/forallP=> /= -[b bI]; rewrite -affE hpE in_polyI 2?{1}h {h} //= in_baseEq.
    * by rewrite in_oppbase bI orbT.
    * by rewrite (fsubset_incl bI).
  - by apply/in_poly_of_baseP=> /= b bb; rewrite h // in_baseEq bb.
Qed.

Lemma imfsetU {T U : choiceType} (f : T -> U) (A B : {fset T}) :
  (f @` (A `|` B) = (f @` A) `|` (f @` B))%fset.
Proof.
apply/fsetP=> x; rewrite in_fsetE; apply/idP/idP.
+ case/imfsetP=> /= y yAB ->; apply/orP; move: yAB.
  rewrite in_fsetU => /orP[yA|yB]; [left | right];
    by apply/imfsetP; exists y.
+ case/orP => /imfsetP[] /= y hy ->; apply/imfsetP;
    by exists y => //=; rewrite in_fsetU hy ?orbT.
Qed.

Lemma baseEq_comp (base I J : base_t[R,n]) :
  baseEq (baseEq base I) J = baseEq base (I `|` J)%fset.
Proof.
by apply/fsetP=> c; rewrite !in_baseEq imfsetU in_fsetU orbA.
Qed.

Lemma baseEq_eqR (base I J : base_t[R,n]) :
     (I `\` \- base)%fset = (J `\` \- base)%fset
  -> baseEq base I = baseEq base J.
Proof.
move/fsetP => eq; apply/fsetP => c; rewrite !in_baseEq.
case/boolP: (c \in base) => //= cNb; move/(_ (-c)): eq.
rewrite !in_fsetE in_oppbase (negbTE cNb) /=.
by rewrite -(in_oppbase I) -(in_oppbase J) /= opprK.
Qed.

Lemma polyEq_of_polyEq
  (base : base_t[R,n]) (I : {fsubset base}) (J : {fsubset (baseEq base I)})
:
  exists K : {fsubset base}, 'P^=(baseEq base I; J) = 'P^=(base; K).
Proof.
pose vI := FSubset.untag I; pose vJ := FSubset.untag J.
pose  L := ((vI `|` vJ) `&` base)%fset.
pose vK := [fset x | x : base & fsval x \in L]%fset.
pose  K := FSubset.fsubset_of_fsetval vK.
exists K; rewrite !polyEq_flatten baseEq_comp.
congr ('P (_)); apply: baseEq_eqR.
apply/fsetP=> c; apply/idP/idP; last first.
+ rewrite in_fsetD => /andP[cNb cK]; rewrite in_fsetD cNb /=.
  case/imfsetP: cK => /= y /imfsetP[] /= -[/= z zb] zL -> ->.
  by move: zL; rewrite inE 2!in_fsetE /= zb andbT.
rewrite 2!in_fsetE => /andP[Ncb] /orP[cI|cJ].
+ rewrite in_fsetD Ncb /=; apply/imfsetP => /=.
  have cb: c \in base by apply/(fsubsetP (valP I)).
  exists [`cb]%fset => //; apply/imfsetP => /=.
  by exists [`cb]%fset => //; rewrite inE 2!in_fsetE /= cI cb.
+ have: c \in baseEq base I by apply/(fsubsetP (valP J)).
  case/in_baseEqP => [cb|cNb].
  - rewrite inE Ncb /=; apply/imfsetP => //=.
    exists [`cb]%fset => //; apply/imfsetP => //=.
    by exists [`cb]%fset => //; rewrite inE 2!in_fsetE /= cJ cb orbT.
  - move: cNb; rewrite -{1}[c]opprK (in_oppbase I).
    move/(fsubsetP (valP I)) => /(in_imfset imfset_key -%R) /=.
    by rewrite opprK (negbTE Ncb).
Qed.                            (* FIXME: QED is too long! *)

End BasicObjects.

Arguments orthant {R n}.

Notation "'[' 'hs' b ']'" := (mk_hs b) : poly_scope.
Notation "'[' 'hline' c & Ω ']'" := (mk_hline c Ω) : poly_scope.
Notation "''P' ( base )" := (poly_of_base (base)%fset) : poly_scope.
Notation "''P^=' ( base ; I )" := (polyEq (base)%fset (I)%fset) : poly_scope.
Notation "V %:PH" := (aff V) (at level 2, left associativity, format "V %:PH").

Definition inE := (@in_poly0, @in_polyT, @in_hp, @in_polyI, @in_hs, inE).

Module Proj0.
Section Proj0.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n.+1]).

Notation "'beproj0' e" := [< row' 0 e.1, e.2 >] (at level 40).
Notation "'get0' e" := (e.1 0 0) (at level 40).

Definition scale0 (e : lrel[R]_n.+1) : lrel[R]_n.+1 :=
  let α := get0 e in
  if α > 0 then α^-1 *: e
  else if α < 0 then (-α)^-1 *: e
  else e.

Lemma get0_scale0 e : get0 (scale0 e) = Num.sg (get0 e).
Proof.
rewrite /scale0; case: (ltrgt0P (get0 e)) => h; rewrite ?mxE.
- by rewrite gtr0_sg ?mulVf ?lt0r_neq0.
- by rewrite ltr0_sg ?invrN ?mulNr ?mulVf ?ltr0_neq0.
- by rewrite h sgr0.
Qed.

Lemma hs_scale0 e : [hs e] = [hs (scale0 e)].
Proof.
apply/poly_eqP => x; rewrite 2!in_hs.
rewrite /scale0; case: (ltrgt0P (get0 e)) => ?;
by rewrite ?vdotZl ?ler_pmul2l ?invr_gt0 ?oppr_gt0.
Qed.

Let sbase    := [fset (scale0 e) | e in base]%fset.
Let base0    := [fset e in sbase | get0 e == 0]%fset.
Let base_pos := [fset e in sbase | (get0 e == 1)]%fset.
Let base_neg := [fset e in sbase | (get0 e == -1)]%fset.

Lemma sbaseU : sbase = (base0 `|` base_pos `|` base_neg)%fset.
Proof.
apply/fsetP => e; rewrite !inE; apply/idP/idP.
- move/imfsetP => [{}e e_in ->]; rewrite get0_scale0.
  case/sgrP: (get0 e) => h.
  + do 2![apply/orP; left].
    by rewrite in_imfset /=.
  + apply/orP; left; apply/orP; right.
    by rewrite in_imfset /=.
  + apply/orP; right.
    by rewrite in_imfset /=.
- by rewrite -orbA; move/or3P; case => /andP [].
Qed.

Definition lift0 (α : R) (x : 'cV[R]_n) := (col_mx α%:M x) : 'cV[R]_(n.+1).

Lemma lift0K α x : row' 0 (lift0 α x) = x.
Proof.
apply/colP => i; rewrite !mxE /=; case: splitP => j.
- by rewrite [j]ord1_eq0 fintype.lift0 //.
- by rewrite fintype.lift0 => /succn_inj/ord_inj ->.
Qed.

Lemma vdot11 (x y : R) : '[x%:M, y%:M] = x*y.
Proof.
apply/(scalar_mx_inj (ltn0Sn 0)).
by rewrite vdotC vdot_def tr_scalar_mx scalar_mxM.
Qed.

Lemma col_mx_row'0 (x : 'cV[R]_(n.+1)) :
  x = col_mx (x 0 0)%:M (row' 0 x).
Proof.
apply/colP => i; case: (splitP' (m := 1) i) => [k -> | k ->].
- by rewrite [k]ord1_eq0 (col_mxEu (m1 := 1)) lshift0 !mxE mulr1n.
- by rewrite (col_mxEd (m1 := 1)) !mxE rshift1.
Qed.

Lemma vdot_lift0 (e : lrel[R]_n.+1) α x :
  '[e.1, lift0 α x] = (get0 e) * α + '[(beproj0 e).1, x].
Proof.
by rewrite {1}[e.1]col_mx_row'0 (vdot_col_mx (n := 1)) vdot11.
Qed.

Lemma row'0_in_hs (e : lrel[R]_n.+1) x :
  get0 e = 0 -> (x \in [hs e]) -> row' 0 x \in [hs beproj0 e].
Proof.
rewrite 2!in_hs {2}[e.1]col_mx_row'0 {1}[x]col_mx_row'0 (vdot_col_mx (n := 1)).
by move => ->; rewrite raddf0 vdot0l add0r.
Qed.

Lemma lift_in_base0 e α x :
  e \in base0 -> (x \in ([hs (beproj0 e)] : 'poly[R]_n)) ->
    lift0 α x \in ([hs e] : 'poly[R]_(n.+1)).
Proof.
rewrite in_fset => /andP[_ /eqP get0_eq0].
by rewrite !in_hs vdot_lift0 get0_eq0 mul0r add0r.
Qed.

Let gap (e : lrel[R]_n.+1) x := e.2 - '[row' 0 e.1, x].

Lemma lift_in_base_pos e α x :
  e \in base_pos -> α >= gap e x -> (lift0 α x) \in [hs e].
rewrite in_fset => /andP[_ /eqP get0_eq1].
by rewrite in_hs vdot_lift0 get0_eq1 mul1r ler_sub_addr.
Qed.

Lemma lift_in_base_neg e α x :
  e \in base_neg -> α <= -(gap e x) -> (lift0 α x) \in [hs e].
rewrite in_fset => /andP[_ /eqP get0_eqN1].
rewrite in_hs vdot_lift0 get0_eqN1 mulN1r addrC ler_sub_addr -ler_sub_addl.
by rewrite opprD opprK addrC.
Qed.

Fact poly_of_sbase : 'P(sbase) = 'P(base).
Proof.
apply/poly_eqP => x.
apply/in_poly_of_baseP/in_poly_of_baseP => [x_in ?? | x_in ? /imfsetP [i i_in ->]].
by rewrite hs_scale0; apply/x_in; rewrite in_imfset.
by rewrite -hs_scale0; apply/x_in.
Qed.

Definition proj0 : base_t[R,n] :=
  let combine_pos_neg := [fset (e1 + e2)%R | e1 in base_pos, e2 in base_neg]%fset in
  ([fset beproj0 (val e) | e in base0] `|` [fset beproj0 (val e) | e in combine_pos_neg])%fset.

Lemma proj0P x :
  reflect (exists2 y, x = row' 0 y & y \in 'P(base)) (x \in 'P(proj0)).
Proof.
rewrite /proj0.
apply/(iffP idP) => [ x_in | [y ->] ].
- pose s_pos := [seq gap e x | e <- base_pos].
  pose s_neg := [seq (-gap e x) | e <- base_neg].
  have pos_le_neg : forall y z, y \in s_pos -> z \in s_neg -> y <= z.
  + move => ?? /mapP [e e_in ->] /mapP [e' e'_in ->].
    rewrite -subr_le0 opprK addrACA -opprD -vdotDl -linearD /=.
    rewrite subr_le0 -in_hs.
    have ->: [<row' 0 (e.1 + e'.1), e.2 + e'.2>] = beproj0 (e+e') by [].
    apply/poly_subsetP/poly_of_base_subset_hs: x_in.
    by apply/fsetUP; right; rewrite in_imfset ?in_imfset2.
  pose α_pos := (max_seq s_pos (min_seq s_neg 0)).
  pose α_neg := (min_seq s_neg (max_seq s_pos 0)).
  have {}pos_le_neg: α_pos <= α_neg.
  + rewrite /α_pos /α_neg.
    case: max_seqP => [-> //= | y [y_in _]].
    case: min_seqP => [_ | z [z_in _]]; first by rewrite max_seq_ger.
    by apply/pos_le_neg.
  exists (lift0 α_pos x); first by rewrite lift0K.
  rewrite -poly_of_sbase; apply/in_poly_of_baseP => e.
  rewrite sbaseU => /fsetUP; case. move/fsetUP; case.
  + move => e_in_base0; rewrite lift_in_base0 //.
    apply/poly_subsetP/poly_of_base_subset_hs: x_in.
    by apply/fsetUP; left; rewrite in_imfset.
  + move => e_in_base_pos; apply/lift_in_base_pos => //.
    have: gap e x \in s_pos by apply/map_f.
    by apply/max_seq_ger.
  + move => e_in_base_neg; apply/lift_in_base_neg => //.
    apply/(le_trans pos_le_neg).
    have: - (gap e x) \in s_neg by apply/map_f.
    by apply/min_seq_ler.
- rewrite -poly_of_sbase => y_in; apply/in_poly_of_baseP => e.
  move/fsetUP; case; move/imfsetP => [{}e e_in ->].
  + apply/row'0_in_hs; move: e_in; rewrite !inE => /andP[e_in /eqP] //.
    by move => _; rewrite -in_hs; apply/poly_subsetP/poly_of_base_subset_hs: y_in.
  + move: e_in => /imfset2P [{}e e_in] [e' e'_in] ->.
    move: e_in e'_in; rewrite !inE => /andP [e_in /eqP get0e] /andP [e'_in /eqP get0e'].
    rewrite -in_hs; apply/row'0_in_hs => /=.
    * by rewrite mxE get0e get0e' addrN.
    * by rewrite inE /= vdotDl; apply/ler_add; rewrite -in_hs;
      apply/poly_subsetP/poly_of_base_subset_hs: y_in.
Qed.

End Proj0.
End Proj0.

Section Projection.

Section Proj0.

Context {R : realFieldType} {n : nat}.

Definition proj0 (P : 'poly[R]_n.+1) :=
  let base := xchoose (is_poly_of_base P) in
  'P(Proj0.proj0 base).

Lemma proj0P {P} {x} :
  reflect (exists2 y, x = row' 0 y & y \in P) (x \in proj0 P).
Proof.
rewrite /proj0; move: (xchooseP (is_poly_of_base P)) => /eqP {1}->.
exact: Proj0.proj0P.
Qed.

End Proj0.

Section Proj.

Context {R : realFieldType} {n : nat}.

Fixpoint proj (k : nat) : 'poly[R]_(k+n) -> 'poly[R]_n :=
  match k with
  | 0 => id
  | (km1.+1)%N as k => (proj (k := km1)) \o (proj0)
  end.

Lemma projP {k : nat} {P : 'poly[R]_(k+n)} {x} :
  reflect (exists y, col_mx y x \in P) (x \in proj P).
Proof.
elim: k P => [ P | k Hind P].
- apply: (iffP idP) => [x_in_proj | [?]].
  + by exists 0; rewrite col_mx0l.
  + by rewrite col_mx0l.
- apply: (iffP (Hind _)) => [[y H] | [y H]].
  + move/proj0P: H => [y' eq y'_in_P].
    exists (usubmx (m1 := k.+1) y'); suff ->: x = dsubmx (m1 := k.+1) y' by rewrite vsubmxK.
    apply/colP => i.
    move/colP/(_ (@rshift k n i)): eq; rewrite !mxE.
    case: splitP'; last first.
    * move => ? /rshift_inj <- ->; apply: congr2; last done.
      by apply/ord_inj => /=.
    * move => ? /eqP; by rewrite eq_sym (negbTE (lrshift_distinct _ _)).
  + exists (row' ord0 y); apply/proj0P.
    exists (col_mx y x); by rewrite -?row'Ku.
Qed.

End Proj.

End Projection.

Section Map.

Variable (R : realFieldType) (n k : nat) (A : 'M[R]_(k,n)).

Let A' := row_mx (-A) (1%:M).

Definition map_poly (P : 'poly_n) :=
  proj ((lift_poly k P) `&` (\polyI_i [hp [<(row i A')^T, 0>]]%:PH)).

Lemma in_map_polyP (P : 'poly_n) x :
  reflect (exists2 y, x = A*m y & y \in P) (x \in map_poly P).
Proof.
have in_vectA' y z : (col_mx y z \in (\polyI_i [hp [<(row i A')^T, 0>]]%:PH)) = (z == A *m y).
- apply/in_big_polyIP/eqP => [h | /colP h i _];
    do ?[apply/colP => i; move/(_ i isT): h];
    rewrite affE in_hp /= row_row_mx tr_row_mx vdot_col_mx !row_vdot mul1mx mulNmx mxE;
    rewrite (can2_eq (addKr _) (addNKr _)) opprK addr0; exact/eqP.
apply: (iffP projP) => [[y] | [y -> y_in_P]].
- rewrite in_polyI in_lift_poly in_vectA' col_mxKu => /andP [? /eqP ->].
  by exists y.
- exists y; rewrite in_polyI in_lift_poly in_vectA' col_mxKu.
  by apply/andP; split.
Qed.

End Map.

Section Hull.

Variable (R : realFieldType) (n : nat) .

Definition mat_fset (V : {fset 'cV[R]_n}) :=
  (\matrix_(i < #|`V|) (fnth i)^T)^T.

Definition vect_fset (V : {fset 'cV[R]_n}) (w : 'cV[R]_n -> R) :=
  \col_(i < #|`V|) (w (fnth i)).

Lemma vect_fsetK (V : {fset 'cV[R]_n}) (c : 'cV[R]__) :
  vect_fset V (vect_to_fsfun c) = c.
Proof.
apply/colP=> i; rewrite mxE /vect_to_fsfun fsfun_ffun insubT ?fnthP //=.
by move=> h; rewrite (bool_irrelevance h (fnthP _)) frankK.
Qed.

Definition cone V :=
  map_poly (mat_fset V) orthant.

Definition conv V :=
  map_poly (mat_fset V) (orthant `&` ([hp [<const_mx 1, 1>]]%:PH)).

Notation "[ 'segm' u '&' v ]" := (conv [fset u; v]%fset).

Lemma combine_mulmxE (w : {fsfun 'cV[R]_n ~> _}) (V : {fset 'cV[R]_n}) :
  (finsupp w `<=` V)%fset -> combine w = mat_fset V *m vect_fset V w.
Proof.
move=> le_wV; rewrite (combinewE le_wV) mulmx_sum_col.
rewrite (reindex (@frank _ _)) /=; last first.
+ by apply/onW_bij/bij_frank.
apply: eq_bigr=> x _; rewrite !mxE val_fnthK; congr (_ *: _).
by rewrite -tr_row rowK trmxK val_fnthK.
Qed.

Lemma in_coneP V x :
  reflect
    (exists2 w : {conic 'cV[R]_n ~> _},
       (finsupp w `<=` V)%fset & x = combine w)
    (x \in cone V).
Proof.
apply: (iffP (in_map_polyP _ _ _)) => /= [[c ->]|[w le_wV ->]].
+ rewrite in_orthant => ge0_c; pose w := vect_to_fsfun c.
  exists (mkConicFun (conic_vect_to_fsfun ge0_c)); rewrite /= -/w.
  - by apply: finsupp_vect_to_fsfun.
  by rewrite (combine_mulmxE (finsupp_vect_to_fsfun c)) vect_fsetK.
+ exists (vect_fset V w); first by rewrite (combine_mulmxE le_wV).
  by rewrite in_orthant; apply/gev0P => i; rewrite mxE ge0_fconic.
Qed.

Lemma in_convP V x :
  reflect
    (exists2 w : {convex 'cV[R]_n ~> _},
       (finsupp w `<=` V)%fset & x = combine w)
    (x \in conv V).
Proof.
apply: (iffP (in_map_polyP _ _ _)) => /= [[c ->]|[w le_wV ->]].
+ rewrite in_polyI in_orthant affE in_hp => /andP[/= ge0_c /eqP Σc_eq_1].
  exists (mkConvexfun (convex_vect_to_fsfun ge0_c Σc_eq_1)) => /=.
  - by apply: finsupp_vect_to_fsfun.
  by rewrite (combine_mulmxE (finsupp_vect_to_fsfun c)) vect_fsetK.
+ exists (vect_fset V w); first by rewrite (combine_mulmxE le_wV).
  rewrite in_polyI in_orthant affE in_hp /= -(rwP andP); split.
  - by apply/gev0P=> i; rewrite mxE ge0_fconvex.
  - rewrite vdotC vdotr_const_mx1 (reindex (@frank _ _)) /=; last first.
    * by apply/onW_bij/bij_frank.
    rewrite -[X in _==X](wgt1_fconvex w) (weightwE le_wV).
    by apply/eqP/eq_bigr=> i _; rewrite mxE val_fnthK.
Qed.

Lemma conv0 : conv fset0 = [poly0].
Proof.
apply/eqP; rewrite -lex0.
apply/poly_subsetP => x /in_convP[w].
by rewrite fsubset0 fconvex_insupp_neq0.
Qed.

Lemma conv_subset (P : 'poly[R]_n) (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> (conv V) `<=` P.
Proof.
move=> le_VP; apply/poly_subsetP=> x /in_convP.
case=> [w /fsubsetP le_wV ->]; apply: convexW=> /=.
+ by move=> /= e1 e2 e1P e2Pa rg01_a; apply: mem_poly_convex.
+ by move=> c /le_wV /le_VP.
Qed.

Lemma in_conv (V : {fset 'cV[R]_n}) : {subset V <= conv V}.
Proof.
move => x x_in_V; apply/in_convP.
by exists (fcvx1 x); rewrite ?finsupp_fcvx1 ?fsub1set ?combine_fcvx1.
Qed.

Lemma conv_prop0 (V : {fset 'cV[R]_n}) : (V != fset0)%fset -> (conv V `>` [poly0]).
Proof.
by move/fset0Pn => [v ?];  apply/proper0P; exists v; apply/in_conv.
Qed.

Lemma convS : {homo conv : P Q / (P `<=` Q)%fset >-> P `<=` Q}.
Proof.
move => V W /fsubsetP sub.
by apply/conv_subset => ? /sub; exact: in_conv.
Qed.

Lemma in_segmP (Ω Ω' x : 'cV[R]_n) :
  reflect
    (exists2 μ, 0 <= μ <= 1 & x = (1 - μ) *: Ω + μ *: Ω')
    (x \in [segm Ω & Ω']).
Proof.
apply: Bool.iff_reflect;
  rewrite -[X in _ <-> X](rwP (in_convP _ _));
  exact: cvxsegP.
Qed.

Lemma in_segm (v v' : 'cV[R]_n) :
  (v \in [segm v & v']) * (v' \in [segm v & v']).
Proof.
split; by apply/in_conv; rewrite !inE eq_refl ?orbT.
Qed.

Definition in_segml v v' := (in_segm v v').1.
Definition in_segmr v v' := (in_segm v v').2.

Lemma segm_prop0 (v v' : 'cV[R]_n) : [segm v & v'] `>` [poly0].
Proof.
apply/proper0P; exists v; apply/in_segml.
Qed.

Lemma compact_conv (V : {fset 'cV[R]_n}) : compact (conv V).
Proof.
case/altP: (V =P fset0) => [->| V_neq0]; first by rewrite conv0 compact0.
set P := conv V.
have P_prop0 := conv_prop0 V_neq0.
apply/(compactP P_prop0) => c; apply/(bounded_lower_bound _ P_prop0).
exists (min_seq [seq '[c,v] | v <- V] 0%R).
by apply/conv_subset => v v_in; rewrite inE /= min_seq_ler ?map_f.
Qed.

End Hull.

Notation "[ 'segm' u '&' v ]" := (conv [fset u; v]%fset) : poly_scope.

Section Affine.

Variable (R : realFieldType) (n : nat).

Implicit Type (U : {vspace 'cV[R]_n}) (Ω : 'cV[R]_n).

Lemma dim_cVn U : (\dim U <= n)%N.
Proof.
by move/dimvS: (subvf U); rewrite dimvf /Vector.dim /= muln1.
Qed.

Lemma affine_subset_poly_of_base (base : base_t[R,n]) :
  [affine << base >>]%:PH `<=` 'P(base).
Proof.
apply/poly_subsetP => x; rewrite affE => /in_affineP x_in.
apply/in_poly_of_baseP => e /memv_span/x_in.
by move/eqP; rewrite -in_hp -affE; apply/(poly_subsetP (hp_subset_hs _)). (* UGLY *)
Qed.

Lemma polyEqT_affine (base : base_t[R,n]) :
  'P^=(base; base) = [affine << base >>]%:PH.
Proof.
by rewrite /polyEq meet_l // affine_subset_poly_of_base.
Qed.

Lemma conv_pt (Ω : 'cV[R]_n) : conv [fset Ω]%fset = [pt Ω]%:PH.
Proof.
apply/poly_eqP => x; rewrite affE in_pt.
apply/idP/eqP => [/in_convP [w le_wΩ ->]| ->].
+ rewrite (combinewE le_wΩ) big_fset1 /=; move: le_wΩ.
  rewrite fsubset1 fconvex_insupp_neq0 orbF => /eqP fw.
  have := wgt1_fconvex w; rewrite weightE fw big_fset1 /=.
  by move=> ->; rewrite scale1r.
+ apply/in_convP; exists (fcvx1 Ω); by rewrite ?finsupp_fcvx1 ?combine_fcvx1.
Qed.

Lemma in_pt_self (Ω : 'cV[R]_n) : Ω \in [pt Ω].
Proof. (* RK *)
by rewrite in_pt.
Qed.

Lemma pt_proper0 (Ω : 'cV[R]_n) : [poly0] `<` ([pt Ω]%:PH). (* TODO: useful ?*)
Proof. (* RK *)
by apply/proper0P; exists Ω; rewrite affE in_pt_self.
Qed.

Lemma ppick_pt (Ω : 'cV[R]_n) :
  ppick [pt Ω]%:PH = Ω.
Proof. (* RK *)
by apply/eqP; rewrite -in_pt -affE; apply/ppickP; exact: pt_proper0.
Qed.

Lemma pt_subset (Ω : 'cV[R]_n) P : [pt Ω]%:PH `<=` P = (Ω \in P).
Proof. (* RK *)
by apply/idP/idP => [/poly_subsetP s_ptΩ_P | ?];
  [apply/s_ptΩ_P; rewrite affE in_pt_self | apply/poly_subsetP => v; rewrite affE in_pt => /eqP ->].
Qed.

Lemma pt_proper (Ω : 'cV[R]_n) P : [pt Ω]%:PH `<` P -> (Ω \in P).
Proof.
by move/ltW; rewrite pt_subset.
Qed.

Lemma pointed_affine U Ω :
  pointed [affine U & Ω]%:PH = (U == 0)%VS.
Proof.
apply/idP/idP.
- apply: contraTT => U_neq0.
  apply/pointedPn; exists Ω; exists (vpick U).
  + by rewrite vpick0.
  + by rewrite affS mk_affineS -memvE memv_pick.
- move => /eqP ->; apply: contraT.
  move/pointedPn => [Ω' [d /eqP d_ne0]]; rewrite affS => /affine_leP sub.
  have: Ω' \in [line d & Ω'] by  apply/in_lineP; exists 0; rewrite scale0r addr0.
  move/sub; rewrite in_pt => /eqP eq.
  have: Ω' + d\in [line d & Ω'] by  apply/in_lineP; exists 1; rewrite scale1r.
  by move/sub; rewrite eq in_pt => /eqP/(canRL (addKr _)); rewrite addNr.
Qed.

End Affine.

Section Duality.

Local Open Scope poly_scope.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Implicit Type w : {fsfun lrel[R]_n -> R for fun => 0%R}.

Lemma farkas (e : lrel) :
  ('P(base) `>` [poly0]) -> ('P(base) `<=` [hs e]) ->
  exists2 w : {conic lrel ~> R},
         (finsupp w `<=` base)%fset
       & (combine w).1 = e.1 /\ (combine w).2 >= e.2.
Proof.
rewrite /poly_of_base big_polyI_mono lt0x -lex0 2!poly_subset_mono.
exact: H.farkas.
Qed.

Lemma dual_sol_lower_bound (w : {conic lrel ~> R}) :
  (finsupp w `<=` base)%fset -> 'P(base) `<=` [hs (combine w)].
Proof.
move=> le_wB; apply/poly_subsetP => x; rewrite inE in_poly_of_base /=.
rewrite (combineb1E le_wB) (combineb2E le_wB) vdot_sumDl => /forallP h.
apply: ler_sum => i _; rewrite vdotZl; apply: ler_wpmul2l.
+ by apply: ge0_fconic.
+ by move/(_ i): h; rewrite inE.
Qed.

Lemma dual_opt_sol (c : 'cV[R]_n) (H : bounded 'P(base) c) :
  exists2 w : {conic lrel ~> R},
    (finsupp w `<=` base)%fset & combine w = [<c, opt_value H>].
Proof.
move/(farkas (boundedN0 H)): (opt_value_lower_bound H).
case=> [w w_weight [w_comb1 w_comb2]]; exists w => //.
apply/eqP/be_eqP; split=> //; apply/le_anti/andP; split=> //.
case: (opt_point H) => [x x_in_P <-].
move/poly_subsetP/(_ _ x_in_P): (dual_sol_lower_bound w_weight).
by rewrite inE w_comb1.
Qed.

Lemma dual_sol_bounded (w : {conic lrel ~>R}) :
     ('P(base) `>` [poly0])
  -> (finsupp w `<=` base)%fset
  -> bounded 'P(base) (combine w).1.
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists (combine w).2; exact: dual_sol_lower_bound.
Qed.

Variable (w : {conic lrel[R]_n ~> R}).

Hypothesis le_wb : (finsupp w `<=` base)%fset.

Lemma compl_slack_cond x : x \in 'P(base) ->
  reflect (x \in [hp (combine w)]) (x \in 'P^=(base; finsupp w)).
Proof.
move => x_in_P; apply: (iffP idP) => [/in_polyEqP [in_hps _] |].
- rewrite in_hp !(combinebE le_wb) vdot_sumDl; apply/eqP.
  apply: eq_bigr => i _.
  case: finsuppP; first by rewrite scale0r vdot0l mul0r.
  by move/in_hps; rewrite inE vdotZl => /eqP <-.
- rewrite in_hp !(combinebE le_wb) vdot_sumDl => in_comb_hp.
  apply/in_polyEqP; split; last done.
  move => e e_in_supp; move: in_comb_hp; apply: contraTT.
  rewrite notin_hp; last first.
  + move: x x_in_P; apply/poly_subsetP/poly_of_base_subset_hs.
    exact: (fsubsetP le_wb).
  + move => notin_hp; rewrite eq_sym; apply/ltr_neq.
    apply: sumr_ltrP => [i| ].
    * rewrite vdotZl; apply/ler_wpmul2l; first exact : ge0_fconic.
      move/(poly_subsetP (poly_of_base_subset_hs (fsvalP i))): x_in_P.
      by rewrite inE /=.
    * have e_in_base : e \in base by apply/(fsubsetP le_wb).
      exists [` e_in_base]%fset.
      rewrite vdotZl ltr_pmul2l; first done.
      by rewrite gt0_fconic.
Qed.

Lemma dual_sol_argmin : ('P^=(base; finsupp w) `>` [poly0]) ->
  argmin 'P(base) (combine w).1 = 'P^=(base; finsupp w).
Proof.
have PI_sub_P : 'P^=(base; finsupp w) `<=` 'P(base) by exact: polyEq_antimono0.
move => PI_neq0.
have P_neq0 : ('P(base) `>` [poly0]) by exact: (lt_le_trans PI_neq0).
move/proper0P : PI_neq0 => [x x_in_PI].
set c := (combine w).1; have c_bounded := (dual_sol_bounded P_neq0 le_wb).
rewrite argmin_polyI.
suff ->: opt_value c_bounded = (combine w).2.
- apply/poly_eqP => y; rewrite inE affE beE.
  apply/andP/idP => [[? ?]| y_in_PI]; first exact/compl_slack_cond.
  have y_in_P: y \in ('P(base)) by apply/(poly_subsetP PI_sub_P).
  by split; try exact: compl_slack_cond.
- have x_in_P : x \in ('P(base)) by apply/(poly_subsetP PI_sub_P).
  apply/eqP; rewrite eq_le; apply/andP; split.
  + move/(_ x_in_PI) : (compl_slack_cond x_in_P); rewrite inE => /eqP <-.
    move/poly_subsetP/(_ _ x_in_P): (opt_value_lower_bound c_bounded).
    by rewrite inE.
  + move: (opt_point c_bounded) => [y y_in_P <-].
    move/poly_subsetP/(_ _ y_in_P): (dual_sol_lower_bound le_wb).
    by rewrite inE.
Qed.

End Duality.

Section Separation.

Variable (R : realFieldType) (n : nat).

Definition homog (x : 'cV[R]_n) : lrel[R]_(n+1) := [<col_mx x (1%:M), 0>].

Definition inv_homog (e : lrel[R]_(n+1)) : 'cV[R]_n := usubmx e.1.

Lemma homogK : cancel homog inv_homog.
Proof.
move => x; by rewrite /inv_homog col_mxKu.
Qed.

Variable (V : {fset 'cV[R]_n}).

Let base := (homog @` V)%fset.

Lemma homog_in x : x \in V -> homog x \in base.
Proof.
by move => ?; apply/in_imfset.
Qed.

Definition lift_homog (x : V) := [` homog_in (fsvalP x)]%fset.

Lemma lift_homog_inj : injective lift_homog.
Proof.
move => x y /(congr1 val)/(congr1 inv_homog) /=.
by rewrite !homogK; move/val_inj.
Qed.

Lemma lift_homog_bij : bijective lift_homog.
Proof.
have ex_inv : forall e, e \in base -> exists x : V, e == homog (val x).
- move => e /imfsetP [x /= x_in_V ->].
  by exists [` x_in_V]%fset => /=.
pose inv (e : base) := xchoose (ex_inv _ (fsvalP e)).
suff h: cancel inv lift_homog.
- exists inv => //.
  by move => x; apply/lift_homog_inj; rewrite h.
- move => e; apply/val_inj => /=.
  by move/eqP: (xchooseP (ex_inv _ (fsvalP e))) ->.
Qed.

Variable (x : 'cV[R]_n).

Lemma separation :
  x \notin conv V -> exists2 e, x \notin [hs e] & (conv V `<=` [hs e]).
Proof.
move => x_notin.
suff: ~~ ('P(base) `<=` [hs (homog x)]).
- move/poly_subsetPn => [z z_in z_notin].
  pose e := [<usubmx z, - (dsubmx z 0 0)>].
  have in_hs_e: forall y, (y \in [hs e]) = (z \in [hs (homog y)]).
  + move => y; rewrite 2!in_hs -{1}[z]vsubmxK vdot_col_mx vdot1 vdotC.
    by rewrite -lter_sub_addr add0r.
  exists e.
  + by move: z_notin; apply/contraNN; rewrite in_hs_e.
  + apply/conv_subset => v v_in_V; rewrite in_hs_e.
    have: homog v \in base by exact: in_imfset.
    by move/poly_of_base_subset_hs/poly_subsetP/(_ _ z_in).
- move: x_notin; apply: contraNN.
  have non_empty: 'P(base) `>` [poly0].
  + apply/proper0P; exists 0.
    apply/in_poly_of_baseP => ? /imfsetP [v _ ->].
    by rewrite in_hs /= vdot0r.
  move/(farkas non_empty) => [w w_pweight].
  rewrite (combineb1E w_pweight) (reindex _ (onW_bij _ lift_homog_bij)) => /=.
  under eq_big do [| rewrite scale_col_mx scalemx1]; rewrite sum_col_mx.
  move => [combine_eq _].
  pose w' : fsfun (fun _ : 'cV_n => 0) := [fsfun v in V => w (homog v)]%fset.
  have supp_w' : (finsupp w' `<=` V)%fset by apply/finsupp_sub.
  have {combine_eq} : col_mx (combine w') (weight w')%:M = col_mx x 1%:M.
  rewrite -combine_eq (combinewE supp_w') (weightwE supp_w') raddf_sum /=.
  by apply/eqP; rewrite col_mx_eq; apply/andP; split;
    under [X in X == _]eq_big do [| rewrite fsfunE ifT //].
  move/eq_col_mx => [ <- w'_weight].
  suff w'_cvx : convex w' by apply/in_convP; exists (mkConvexfun w'_cvx).
  apply/convexP; split.
  + move => v /(fsubsetP supp_w') v_in_V.
    by rewrite fsfunE ifT //; apply/conicwP/valP.
  + by move/colP/(_ 0): w'_weight; rewrite !mxE !mulr1n.
Qed.

End Separation.

(* -------------------------------------------------------------------- *)
Module MkNonRedundantBase.
Section MkNonRedundantBase.

Context {R : realFieldType} {n : nat}.

Fixpoint mk_nonredundant_base (base res : seq lrel[R]_n) :=
  match base with
  | [::] => res
  | e::base' =>
    if 'P([fset e in base' ++ res]) `<=` [hs e] then mk_nonredundant_base base' res
    else (mk_nonredundant_base base' (e::res))
  end.

Lemma poly_of_baseU (base base': base_t[R,n]) :
  'P(base `|`  base') = 'P(base) `&` 'P(base').
Proof.
apply/poly_eqP => x; rewrite inE.
apply/in_poly_of_baseP/andP => [x_in | [/in_poly_of_baseP x_in /in_poly_of_baseP x_in']].
- by split; apply/in_poly_of_baseP => e e_in;
            apply/x_in; move: e_in; apply/fsubsetP;
            [apply/fsubsetUl | apply/fsubsetUr].
- by move => e; rewrite inE => /orP; case; [apply/x_in | apply/x_in'].
Qed.

Lemma poly_of_base1 (e : lrel[R]_n) :
  'P([fset e]) = [hs e].
Proof.
apply/poly_eqP => x; apply/in_poly_of_baseP/idP => [x_in | x_in ?].
- by apply/x_in; rewrite inE eq_refl.
- by rewrite inE => /eqP ->.
Qed.

Lemma poly_of_baseU1 (base: base_t[R,n]) (e0 : lrel[R]_n) :
  'P(e0 |` base) = [hs e0] `&` 'P(base).
Proof.
by rewrite poly_of_baseU poly_of_base1.
Qed.

Lemma fset_of_cons (K : choiceType) (x : K) (l : seq K) :
  ([fset y in x :: l] = x |` [fset y in l])%fset.
Proof.
by apply/fsetP => ?; rewrite !inE.
Qed.

Lemma poly_of_nonredundant_base (base0 base1: seq lrel[R]_n) :
  let base := mk_nonredundant_base base0 base1 in
  'P([fset e in base]) = 'P([fset e in base0 ++ base1]).
Proof.
elim: base0 base1 => [//=| e base' /= h_ind base1].
case: ifP => [ | _]; symmetry.
- by rewrite /= !fset_of_cons !poly_of_baseU1 h_ind meet_r.
- rewrite h_ind; apply/congr1.
  by apply/fsetP => i; rewrite !inE /= orbCA.
Qed.

Lemma mk_nonredundant_base_subset (base0 base1 : seq lrel[R]_n) :
  {subset (mk_nonredundant_base base0 base1) <= base0 ++ base1}.
Proof.
elim: base0 base1 => [/= ? //| e base0 /= h_ind base1].
case: ifP => [_ ?|_ ?].
- by move/h_ind; rewrite inE => ->; rewrite orbT.
- move/h_ind; rewrite mem_cat !inE mem_cat.
  by rewrite orbCA.
Qed.

Lemma mk_nonredundant_baseP (base0 base1 : seq lrel[R]_n) :
  let base := mk_nonredundant_base base0 base1 in
  forall e, e \in base -> e \notin base1 -> ~~ ('P(([fset e in base] `\ e)) `<=` [hs e]).
Proof.
elim: base0 base1 => [? /= ??/negP //| e base0 /= h_ind base1].
case: ifP => [ _| /negbT subN e']; first exact: h_ind.
case/altP: (e =P e') => [eq | /negbTE neq ? /negbTE e'_notin].
- rewrite !eq in subN *.
  move => ??; move: subN; apply/contra.
  apply/le_trans/poly_of_base_antimono/fsubsetP => i.
  rewrite !inE /= => /andP [/negbTE neq].
  by move/mk_nonredundant_base_subset; rewrite mem_cat inE neq /=.
- by apply/h_ind; rewrite // inE eq_sym neq e'_notin.
Qed.

End MkNonRedundantBase.
End MkNonRedundantBase.

Section NonRedundantBase.

Context {R : realFieldType} {n : nat}.

Definition non_redundant_base (base : base_t[R,n]) :=
  [forall e : base, ~~ ('P(base `\ (val e)) `<=` [hs (val e)])].

Lemma non_redundant_baseP (base : base_t[R,n]) :
  reflect (forall e, e \in base -> ~~ ('P((base `\ e)) `<=` [hs e])) (non_redundant_base base).
Proof.
apply/(iffP forallP) => [h | h].
- move => e e_in; have ->: e = val [` e_in ]%fset by [].
  by apply/h.
- move => ?; apply/h; exact: valP.
Qed.

Definition mk_non_redundant_base (base : base_t[R,n]) :=
  [fset e in MkNonRedundantBase.mk_nonredundant_base base [::]]%fset.

Lemma poly_of_non_redundant_base (base : base_t[R,n]) :
  'P(mk_non_redundant_base base) = 'P(base).
Proof.
rewrite MkNonRedundantBase.poly_of_nonredundant_base cats0.
by apply/congr1/fsetP => ?; rewrite inE.
Qed.

Lemma mk_non_redundant_baseP (base : base_t[R,n]) :
  non_redundant_base (mk_non_redundant_base base).
Proof.
apply/non_redundant_baseP => e e_in_base.
apply/MkNonRedundantBase.mk_nonredundant_baseP => //=.
by rewrite /mk_non_redundant_base inE in e_in_base.
Qed.

End NonRedundantBase.
