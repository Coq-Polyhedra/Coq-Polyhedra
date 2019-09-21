(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import simplex barycenter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Delimit Scope poly_scope with PH.

(* -------------------------------------------------------------------- *)
Reserved Notation "'base_elt' [ R , n ]"
  (at level 8, format "'base_elt' [ R , n ]").

Reserved Notation "'base_elt'"
  (at level 8).

Reserved Notation "'base_t' [ R , n ]"
  (at level 8, format "'base_t' [ R , n ]").

Reserved Notation "'base_t'"
  (at level 8).

Reserved Notation "[< A , b >]"
  (at level 8, format "[< A ,  b >]").

Reserved Notation "''hpoly[' R ]_ n"
  (at level 8, format "''hpoly[' R ]_ n").

Reserved Notation "''hpoly_' n"
  (at level 8, format "''hpoly_' n").

Reserved Notation "P .`c" (at level 2, format "P .`c").
Reserved Notation "P .`A" (at level 2, format "P .`A").
Reserved Notation "P .`b" (at level 2, format "P .`b").

(* -------------------------------------------------------------------- *)
Section Base.
Context {R : Type} (n : nat).

Variant base_elt_type : predArgType := BaseElt of ('cV[R]_n * R).

Coercion base_elt_val b := let: BaseElt b := b in b.

Canonical base_elt_subType := Eval hnf in [newType for base_elt_val].
End Base.

Notation "'base_elt' [ R , n ]" := (@base_elt_type R n).
Notation "'base_elt'" := (base_elt[_,_]).
Notation "'base_t' [ R , n ]" := {fset base_elt[R,n]}.
Notation "'base_t'" := (base_t[_,_]).
Notation "[< A , b >]" := (BaseElt (A, b)).

(* -------------------------------------------------------------------- *)
Definition be_eqMixin (R : eqType) n :=
  Eval hnf in [eqMixin of base_elt[R,n] by <:].
Canonical be_eqType (R : eqType) n:=
  Eval hnf in EqType base_elt[R,n]  (be_eqMixin R n).
Definition be_choiceMixin (R : choiceType) n :=
  [choiceMixin of base_elt[R,n] by <:].
Canonical be_choiceType (R : choiceType) n :=
  Eval hnf in ChoiceType base_elt[R,n] (be_choiceMixin R n).
Definition be_countMixin (R : countType) n :=
  [countMixin of base_elt[R,n] by <:].
Canonical be_countType (R : countType) n :=
  Eval hnf in CountType base_elt[R,n] (be_countMixin R n).
Canonical be_subCountType (R : countType) n :=
  Eval hnf in [subCountType of base_elt[R,n]].
Definition be_finMixin (R : finType) n :=
  [finMixin of base_elt[R,n] by <:].
Canonical be_finType (R : finType) n :=
  Eval hnf in FinType base_elt[R,n] (be_finMixin R n).
Canonical be_subFinType (R : finType) n :=
  Eval hnf in [subFinType of base_elt[R,n]].

(* -------------------------------------------------------------------- *)
Section BaseTheory.
Context (R : Type) (n : nat).

Lemma beW (P : base_elt[R,n] -> Prop) :
  (forall A b, P [<A, b>]) -> (forall b, P b).
Proof. by move=> ih [[]]. Qed.

Lemma beE (b : base_elt[R,n]) : [<b.1, b.2>] = b.
Proof. by elim/beW: b. Qed.
End BaseTheory.

Lemma be_eqE (R : eqType) n (b1 b2 : base_elt[R,n]) :
  (b1 == b2) = [&& b1.1 == b2.1 & b1.2 == b2.2].
Proof. by []. Qed.

Lemma be_eqP (R : eqType) n (b1 b2 : base_elt[R,n]) :
  reflect (b1.1 = b2.1 /\ b1.2 = b2.2) (b1 == b2).
Proof.
rewrite be_eqE; apply: (iffP andP).
+ by case=> [/eqP-> /eqP->]. + by case=> -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Section BaseZmod.
Context {R : zmodType} {n : nat}.

Implicit Types (b : base_elt[R,n]).

Definition be0         := [< (0 : 'cV[R]_n), (0 : R) >].
Definition beadd b1 b2 := [< b1.1 + b2.1, b1.2 + b2.2 >].
Definition beopp b     := [< -b.1, -b.2 >].

Lemma be_zmod_mixin :
  [/\ associative beadd
    , commutative beadd
    , left_id be0 beadd
    & left_inverse be0 beopp beadd].
Proof. split.
+ by move=> b1 b2 b3; rewrite /beadd 2!addrA.
+ by move=> b1 b2; rewrite /beadd [b2.1 + _]addrC [b2.2 + _]addrC.
+ by move=> b; rewrite /beadd 2!add0r beE.
+ by move=> b; rewrite /beadd 2!addNr.
Qed.

Let beaddA  := let: And4 h _ _ _ := be_zmod_mixin in h.
Let beaddC  := let: And4 _ h _ _ := be_zmod_mixin in h.
Let beadd0r := let: And4 _ _ h _ := be_zmod_mixin in h.
Let beaddNr := let: And4 _ _ _ h := be_zmod_mixin in h.

Definition be_zmodMixin := ZmodMixin beaddA beaddC beadd0r beaddNr.
Canonical be_zmodType := Eval hnf in ZmodType base_elt be_zmodMixin.

Lemma beaddE b1 b2 : b1 + b2 = [< b1.1 + b2.1, b1.2 + b2.2 >].
Proof. by []. Qed.

Lemma beoppE b : -b = [< -b.1, -b.2 >].
Proof. by []. Qed.
End BaseZmod.

(* -------------------------------------------------------------------- *)
Section BaseLmod.
Context {R : ringType} {n : nat}.

Implicit Types (b : base_elt[R,n]).

Definition bescale c b := [< c *: b.1, c * b.2 >].

Lemma be_lmod_mixin :
  [/\ forall c1 c2 b, bescale c1 (bescale c2 b) = bescale (c1 * c2) b
    , left_id 1 bescale
    , right_distributive bescale +%R
    & forall b, {morph bescale^~ b : x y / x + y}].
Proof. split.
+ by move=> c1 c2 b; rewrite /bescale scalerA mulrA.
+ by move=> b; rewrite /bescale scale1r mul1r beE.
+ by move=> c b1 b2; rewrite /bescale scalerDr !beaddE mulrDr.
+ by move=> b c1 c2; rewrite /bescale beaddE scalerDl mulrDl.
Qed.

Let bescaleA  := let: And4 h _ _ _ := be_lmod_mixin in h.
Let bescale1  := let: And4 _ h _ _ := be_lmod_mixin in h.
Let bescaleDr := let: And4 _ _ h _ := be_lmod_mixin in h.
Let bescaleDl := let: And4 _ _ _ h := be_lmod_mixin in h.

Definition be_lmodMixin := LmodMixin bescaleA bescale1 bescaleDr bescaleDl.
Canonical be_lmodType := Eval hnf in LmodType R base_elt be_lmodMixin.

Lemma bescaleE c b : c *: b = [< c *: b.1, c * b.2 >].
Proof. by []. Qed.
End BaseLmod.

(* -------------------------------------------------------------------- *)
Section BaseMorph.
Context {R : zmodType} {n : nat}.

Implicit Types (b : base_elt[R,n]).

Lemma beadd_p1E b1 b2 : (b1 + b2).1 = b1.1 + b2.1.
Proof. by []. Qed.

Lemma beadd_p2E b1 b2 : (b1 + b2).2 = b1.2 + b2.2.
Proof. by []. Qed.
End BaseMorph.

(* -------------------------------------------------------------------- *)
Section PWeight.

Variable (R : realFieldType) (K : choiceType) (base : {fset K}).

Implicit Type (w : {fsfun K -> R for fun => 0%R}).

Definition pweight w :=
  (finsupp w `<=` base)%fset && [forall e : base, w (val e) >= 0].

Lemma pweightP w :
  reflect ((finsupp w `<=` base)%fset /\ (forall e, e \in base -> w e >= 0)) (pweight w).
Proof.
suff equiv : reflect (forall e, e \in base -> w e >= 0) [forall e : base, w (val e) >= 0]
  by apply/(iffP andP) => [[? /equiv ?] | [? /equiv ?]].
apply/(iffP forallP) => [H e e_in_base | H e].
- by move/(_ [` e_in_base]%fset): H.
- by apply: H; exact: fsvalP.
Qed.

Definition supp w := [fset e in base | w e > 0]%fset.

Definition uniform_pweight (I : {fsubset base}) : {fsfun K -> R for fun => 0%R} :=
  [fsfun e : I => 1 | 0]%fset.

Lemma uniform_pweightP I : pweight (uniform_pweight I).
Proof.
rewrite /uniform_pweight.
apply/pweightP; split.
- apply: (fsubset_trans (y := I)); first exact: finsupp_sub.
  exact: (valP I).
- move => e _.
  by rewrite fsfun_ffun; case: insubP => [?|?] /=; rewrite ?ler01.
Qed.

Lemma uniform_supp (I : {fsubset base}) : supp (uniform_pweight I) = I.
Proof.
apply/fsetP => e.
rewrite /supp !inE /uniform_pweight fsfun_ffun.
case: insubP => [? -> <- /=| /negbTE -> /=].
- rewrite ltr01 andbT.
  by apply/(fsubsetP (valP I)).
- by rewrite ltrr andbF.
Qed.

Section Extra.

Variable (w : {fsfun K -> R for fun => 0%R}).
Hypothesis w_pweight : pweight w.

Lemma finsupp_subset : (finsupp w `<=` base)%fset.
Proof.
by move/pweightP : w_pweight => [].
Qed.

Lemma pweight_ge0 e : w e >= 0.
Proof.
case: finsuppP => [| e_in_supp]; first done.
move/pweightP : w_pweight => [_ H]; apply: H.
exact: (fsubsetP finsupp_subset).
Qed.

Lemma supp_subset : (supp w `<=` base)%fset.
Proof.
exact: fset_sub.
Qed.

CoInductive supp_spec e : R -> bool -> Type :=
  | SuppOut : e \notin supp w -> supp_spec e 0 false
  | SuppIn of (e \in supp w) : supp_spec e (w e) true.

Lemma suppP e : supp_spec e (w e) (w e > 0).
Proof.
case: (boolP (e \in supp w)) => [e_in | e_notin].
- suff ->: w e > 0 by constructor.
  by move: e_in; rewrite 2!inE => /andP [_].
- case: finsuppP => [| e_in_finsupp]; rewrite ?ltrr; first by constructor.
  suff ->: w e = 0 by rewrite ltrr; constructor.
  apply/eqP; move: e_notin; apply: contraR => w_e_neq0.
  have e_in_base : e \in base by exact: (fsubsetP finsupp_subset).
  suff w_e_gt0: w e > 0 by rewrite !inE; apply/andP; split.
  by rewrite ltr_def; apply/andP; split; last exact: pweight_ge0.
Qed.

Lemma pweight_gt0 e : (e \in supp w) = (w e > 0).
Proof.
by case: suppP; first exact: negbTE.
Qed.

End Extra.

Fact valP' (v : base) : v \in (xpredT : pred base).
by [].
Qed.

Notation m := #| predT : pred base|.

Definition vect_to_pweight (y : 'cV[R]_m) :=
  [fsfun v : base => y (enum_rank_in (valP' v) v) 0] : {fsfun K -> R for fun => 0%R}.

Lemma vect_to_pweightP (w : 'cV[R]_m) :
  w >=m 0 -> pweight (vect_to_pweight w).
Proof.
move/gev0P => w_pos.
apply/pweightP; split; first exact: finsupp_sub.
move => ? ?; rewrite fsfun_ffun insubT /=; exact: w_pos.
Qed.

End PWeight.

Section Combine.
Context {R : realFieldType} {n : nat} (base : base_t[R,n]).

Definition combine (w : base_elt -> R) : base_elt :=
  \sum_(v : base) w (val v) *: (val v).

Lemma combine1E w : (combine w).1 = \sum_(v : base) w (val v) *: (val v).1.
Proof. by apply (big_morph (fst \o val) beadd_p1E). Qed.

Lemma combine2E w : (combine w).2 = \sum_(v : base) w (val v) * (val v).2.
Proof. by apply (big_morph (snd \o val) beadd_p2E). Qed.

Definition combineE := (combine1E, combine2E).
End Combine.

Module HPolyhedron.

Section Def.

Variable (R : realFieldType) (n : nat).

Record hpoly := HPoly {
  nb_ineq : nat ;
  _ : 'M[R]_(nb_ineq,n) ;
  _ : 'cV[R]_nb_ineq
}.

Definition mem_hpoly P : {pred 'cV[R]_n} :=
  let: HPoly _ A b := P in
  [pred x : 'cV_n | (A *m x) >=m b].
Coercion mem_hpoly : hpoly >-> pred_sort.

End Def.

Notation "''hpoly[' R ]_ n" := (hpoly R n).
Notation "''hpoly_' n" := (hpoly _ n).

Section Choice.

Variable R : realFieldType.
Variable n : nat.

Definition matrix_from_hpoly (P : 'hpoly[R]_n) :=
  let: HPoly _ A b := P in
    Tagged (fun m => 'M[R]_(m,n) * 'cV[R]_m)%type (A, b).

Definition hpoly_from_matrix (M : {m : nat & 'M[R]_(m,n) * 'cV[R]_m}%type) :=
  let: (A, b) := tagged M in
    HPoly A b.

Lemma matrix_from_hpolyK :
  cancel matrix_from_hpoly hpoly_from_matrix.
Proof.
by move => [m A b]; rewrite /matrix_from_hpoly /hpoly_from_matrix.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyK.
Canonical hpoly_eqType := Eval hnf in EqType 'hpoly[R]_n hpoly_eqMixin.
Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType 'hpoly[R]_n hpoly_choiceMixin.

End Choice.

Section PolyPred.

Context {R : realFieldType} {n : nat}.

Implicit Type (P : 'hpoly[R]_n).

Definition hpoly_c (P : 'hpoly[R]_n) : nat
  := let: HPoly c A b := P in c.

Definition hpoly_A (P : 'hpoly[R]_n) :'M_(hpoly_c P, _)
  := let: HPoly c A b := P in A.

Definition hpoly_b (P : 'hpoly[R]_n) :'cV_(hpoly_c P)
  := let: HPoly c A b := P in b.

Notation "P .`c" := (hpoly_c P).
Notation "P .`A" := (hpoly_A P).
Notation "P .`b" := (hpoly_b P).

Lemma in_hpolyE (P : 'hpoly[R]_n) x : (x \in P) = (P.`A *m x) >=m (P.`b).
Proof. by case: P. Qed.

Definition mk_hs (b : base_elt[R,n]) : 'hpoly[R]_n := HPoly (b.1)^T (b.2)%:M.

Lemma in_hs b x : x \in (mk_hs b ) = ('[b.1,x] >= b.2).
Proof.
rewrite inE vdotC -vdot_def.
by apply/forallP/idP => [ /(_ 0) | H i]; rewrite ?[i]ord1_eq0 !mxE /= !mulr1n.
Qed.

Definition poly0 := mk_hs [<0,1>].

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => x; rewrite in_hs vdot0l inE ler10.
Qed.

Definition polyT : 'hpoly[R]_n := @HPoly _ _ 0 (const_mx 0) 0.

Lemma in_polyT : polyT =i predT.
Proof.
by move => x; rewrite !inE mul0mx lev_refl.
Qed.

Definition polyI P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    HPoly (col_mx A A') (col_mx b b').

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
move => x.
case: P => mP AP bP; case: Q => mQ AQ bQ.
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Definition bounded P c :=
  let: HPoly _ A b := P in
    Simplex.bounded A b c.

Definition opt_value P c :=
  let: HPoly _ A b := P in
    Simplex.opt_value A b c.

Definition poly_subset P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    (~~ Simplex.feasible A b) ||
      [forall i, (Simplex.bounded A b (row i A')^T) && (Simplex.opt_value A b (row i A')^T >= b' i 0)].

Lemma poly_subsetP {P Q : 'hpoly[R]_n} :
  reflect {subset P <= Q} (poly_subset P Q).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [/orP poly_subset_P_Q | subset_P_Q].
- case: poly_subset_P_Q => [empty_P | /forallP hs_incl x x_in_P].
  + move => x x_in_P.
    move: empty_P; apply/contraR => _.
    by apply/Simplex.feasibleP; exists x.
  + apply/forallP => i.
    move/andP: (hs_incl i) => [/Simplex.boundedP [_ opt_is_opt] ?].
    apply: (@ler_trans _ (Simplex.opt_value A b (row i A')^T) _ _); first by done.
    by rewrite -row_vdot; apply: opt_is_opt.
- apply/orP.
  case: (boolP (Simplex.feasible A b)) => [feasible_P | _]; last by left.
  right.
  apply/forallP => i.
  suff bounded_P_row_i_A': Simplex.bounded A b (row i A')^T.
    apply/andP; split; first exact: bounded_P_row_i_A'.
    move/Simplex.boundedP: bounded_P_row_i_A' => [[x [/subset_P_Q  x_in_Q <-]] _].
    rewrite row_vdot.
    exact: ((forallP x_in_Q) i).
  apply/(Simplex.boundedP_lower_bound _ feasible_P).
  exists (b' i 0).
  move => x /subset_P_Q x_in_Q.
  rewrite row_vdot.
  exact: ((forallP x_in_Q) i).
Qed.

Lemma poly_subsetPn {P Q : 'hpoly[R]_n} :
  reflect (exists2 x, x \in P & x \notin Q) (~~ (poly_subset P Q)).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [| [?] ? not_in_Q];
  last by move: not_in_Q; apply/contra; move/poly_subsetP ->.
rewrite negb_or negbK negb_forall.
move/andP => [feasible_P /existsP [i /nandP unbounded_or]].
have unbounded_suff:
  ~~ Simplex.bounded A b (row i A')^T -> exists2 x : 'cV_n, (x \in HPoly A b) & (x \notin HPoly A' b').
  rewrite -(Simplex.unbounded_is_not_bounded _ feasible_P) => /Simplex.unboundedP unbounded_P_row_i_A'.
  move: (unbounded_P_row_i_A' (b' i 0)) => [x [x_in_P ineq]].
  exists x; try by done.
  move: ineq; apply: contraL => x_in_Q.
  rewrite -lerNgt row_vdot.
  exact: ((forallP x_in_Q) i).
case: unbounded_or; first exact: unbounded_suff.
case: (boolP (Simplex.bounded A b (row i A')^T)) => [? | ? _]; last by apply: unbounded_suff.
rewrite -ltrNge => ineq.
exists (Simplex.opt_point A b (row i A')^T); first exact: Simplex.opt_point_is_feasible.
move: ineq; apply: contraL => opt_point_in_Q.
rewrite -lerNgt /Simplex.opt_value row_vdot.
exact: ((forallP opt_point_in_Q) i).
Qed.

Lemma boundedP (P : 'hpoly[R]_n) c :
  reflect (exists2 x, (x \in P) & poly_subset P (mk_hs [<c, '[c,x]>])) (bounded P c).
Proof. (* RK *)
case: P => m A b.
apply/(equivP (Simplex.boundedP A b c) _);
  split => [[[x [? opt_value_eq]] opt_value_is_opt] | [x ? /poly_subsetP incl_hs]].
- exists x; first by done.
  apply/poly_subsetP => y y_in_P.
  rewrite in_hs opt_value_eq.
  by apply: opt_value_is_opt.
- have opt_value_eq: '[ c, x] = Simplex.opt_value A b c.
    apply: Simplex.opt_value_is_optimal; first by done.
    by move => y /incl_hs; rewrite in_hs.
  split.
  + by exists x.
  + move => y /incl_hs.
    by rewrite in_hs -opt_value_eq.
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs [<c, K>]))) (~~ bounded P c).
Proof. (* RK *)
case: P => m A b non_empty_P.
have feasible_P: Simplex.feasible A b
  by move/poly_subsetPn: non_empty_P => [x ? _];
  apply/Simplex.feasibleP; exists x.
rewrite /bounded (Simplex.bounded_is_not_unbounded c feasible_P) negbK.
apply/(equivP (Simplex.unboundedP A b c) _);
  split => [unbounded_cond_point K | unbounded_cond_hs K].
- apply/poly_subsetPn.
  move: (unbounded_cond_point K) => [x [? val_x_sineq]].
  exists x; first by done.
  by rewrite in_hs -ltrNge.
- move/poly_subsetPn: (unbounded_cond_hs K) => [x ? x_not_in_hs].
  exists x; split; first by done.
  by rewrite in_hs -ltrNge in x_not_in_hs.
Qed.

Definition pointed P :=
  ~~ (poly_subset P poly0) ==>
  let: HPoly _ A _ := P in
    Simplex.pointed A.

Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
case: P => m A b non_empty_P.
rewrite /pointed non_empty_P /=.
have feasible_P: exists x, x \in HPoly A b
    by move/poly_subsetPn: non_empty_P => [x ? _]; exists x.
apply/(equivP (Simplex.pointedPn A) _); split =>
  [[d [? /Simplex.feasible_dirP d_feas_dir /Simplex.feasible_dirP md_feas_dir]] | [d [? d_recession_dir]]];
    exists d; split; try by done.
- move => x x_in_P λ.
  case: (boolP (0 <= λ)) => [? | ?].
  + by apply: d_feas_dir.
  + rewrite -[d]opprK scalerN -scaleNr.
    apply: md_feas_dir; try by done.
    by rewrite oppr_ge0; apply: ltrW; rewrite ltrNge.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  by move => x x_in_P λ _; apply: d_recession_dir.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  move => x x_in_P λ _; rewrite scalerN -scaleNr.
  by apply: d_recession_dir.
Qed.


Lemma convexP2 (P : 'hpoly[R]_n) (v w : 'cV[R]_n) α :
  v \in P -> w \in P -> 0 <= α <= 1 -> (1-α) *: v + α *: w \in P.
Proof.
case: P => m A b.
rewrite !inE => vP wP.
case/andP => [gt0_a lt1_a]; rewrite mulmxDr -!scalemxAr.
rewrite -[b]scale1r -{1}[1](subrK α) scalerDl.
by rewrite lev_add // lev_wpscalar // subr_ge0.
Qed.

Definition poly_equiv P Q := (poly_subset P Q) && (poly_subset Q P).

Lemma poly_equivP {P Q : 'hpoly[R]_n} : reflect (P =i Q) (poly_equiv P Q).
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

Section Farkas.

Variable (base : base_t[R,n]).

Let P := \big[polyI/polyT]_(b : base) (mk_hs (val b)).

Definition nth_fset (K : choiceType) (V : {fset K}) (i : 'I_#|predT : pred V|) :=
  val (enum_val i).

Lemma nth_fsetP (K : choiceType) (V : {fset K}) (i : 'I_#|predT : pred V|) :
  nth_fset i \in V.
Proof.
rewrite /nth_fset; exact: fsvalP.
Qed.

Notation m := #| xpredT : pred base |.

Let A := \matrix_(i < m) ((nth_fset i).1)^T.
Let b := \col_(i < m) ((nth_fset i).2).

Lemma combinemE w :
  (A^T *m w = (combine base (vect_to_pweight w)).1)
  * ('[b, w] = (combine base (vect_to_pweight w)).2).
Proof.
split; rewrite combineE.
- rewrite /=; apply/colP => i; rewrite mxE summxE.
  rewrite (reindex (@enum_val _ base)) /=.
  + apply/eq_bigr => j _; rewrite /= !mxE mulrC; apply: congr2; last done.
    rewrite /vect_to_pweight fsfun_ffun /= insubT; first exact: fsvalP.
    move => H /=; apply: congr2; last done.
      by rewrite fsetsubE enum_valK_in.
  + apply: onW_bij; exact: enum_val_bij.
- rewrite /= /vdot.
  rewrite (reindex (@enum_val _ base)) /=.
  + apply/eq_bigr => j _; rewrite /= !mxE mulrC; apply: congr2; last done.
    rewrite /vect_to_pweight fsfun_ffun /= insubT; first exact: fsvalP.
    move => H /=; apply: congr2; last done.
      by rewrite fsetsubE enum_valK_in.
  + apply: onW_bij; exact: enum_val_bij.
Qed.

Lemma memP : P =i HPoly A b.
Proof.
move => x.
have -> : (x \in P) = (\big[andb/true]_(b : base) ('[(val b).1, x] >= (val b).2)).
by rewrite /P; elim/big_rec2: _ => [|i y b' Pi <-];
  rewrite ?in_polyT ?in_polyI ?inE; last by rewrite lev_scalar_mx vdotC vdot_def.
rewrite inE big_andE.
apply/forall_inP/forallP => [H i | H e _].
- move/(_ (enum_val i) isT): H => /=.
  by rewrite -row_vdot rowK trmxK mxE.
- move/(_ (enum_rank_in (valP' e) e)): H.
  rewrite -row_vdot rowK trmxK mxE.
  by rewrite /nth_fset enum_rankK_in.
Qed.

Lemma farkas (e : base_elt) :
  ~~ (poly_subset P poly0) -> (poly_subset P (mk_hs e)) ->
  exists2 w, (pweight base w) & ((combine base w).1 = e.1 /\ (combine base w).2 >= e.2).
Proof.
move => P_neq0 /poly_subsetP incl.
have incl' : poly_subset (HPoly A b) (mk_hs e).
- by apply/poly_subsetP => x; rewrite -memP; apply/incl.
case: (Simplex.simplexP A b e.1).
- move => ? /(intro_existsT (Simplex.infeasibleP _ _)).
  suff -> : Simplex.feasible A b by done.
  apply/Simplex.feasibleP.
  move/poly_subsetPn: P_neq0 => [x x_in_P _].
  by exists x; rewrite inE; rewrite memP in x_in_P.
- move => ? /(intro_existsT (Simplex.unboundedP_cert _ _ _))/Simplex.unboundedP/(_ e.2)
    [x [x_in_PAb ineq]].
  have /incl: x \in P by rewrite memP inE.
  by rewrite in_hs; move/(ltr_le_trans ineq); rewrite ltrr.
- move => [x w] [x_feas w_feas csc].
  rewrite inE /= in w_feas; move/andP: w_feas => [/eqP w_feas1 w_pos].
    exists (vect_to_pweight w).
  + exact: vect_to_pweightP.
  + rewrite -2!combinemE; split; first done.
    by rewrite -csc /=; rewrite -in_hs; apply/incl; rewrite memP inE.
Qed.

End Farkas.

End PolyPred.


Section Proj1.

Variable (R : realFieldType) (n : nat).

(* TODO: simplify proj1 to set to a situation in which i = ord0 and P : 'hpoly[R]_(n.+1) *)
Definition proj1 i (P : 'hpoly[R]_n) :=
  let: HPoly _ A b := P in
  let Jeq0 := [set j | A j i == 0] in
  let Jlt0 := [set j | A j i < 0] in
  let Jgt0 := [set j | A j i > 0] in
  let bJeq0 := row_submx b Jeq0 in
  match (@idP (#|Jlt0| > 0)%N) with
  | ReflectT Jlt0_not_empty =>
    if (#|Jgt0| > 0)%N then
      let AJlt0 := row_submx A Jlt0 in
      let AJgt0 := row_submx A Jgt0 in
      let AJlt0i := row_submx (col' i A) Jlt0 in
      let AJgt0i := row_submx (col' i A) Jgt0 in
      let AJeq0i := row_submx (col' i A) Jeq0 in
      let bJlt0 := row_submx b Jlt0 in
      let bJgt0 := row_submx b Jgt0 in
      let q := (#|Jgt0| * #|Jlt0|)%N in
      let b'' := \matrix_(h < q , j < 1) ((bJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) j)
                                         * (AJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) i)
                                         - (bJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) j)
                                           * (AJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) i)) in
      let A'' := \matrix_(h < q , j < n.-1) ((AJlt0i (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) j)
                                            * (AJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) i)
                                            - (AJgt0i (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) j)
                                              * (AJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) i)) in
      HPoly (col_mx A'' AJeq0i) (col_mx b'' bJeq0)
    else
      HPoly (row_submx (col' i A) Jeq0) bJeq0
  | _ =>
    if (#|Jgt0| > 0)%N then
      HPoly (row_submx (col' i A) Jeq0) bJeq0
    else
      HPoly (col' i A) b
  end.

Theorem proj1P i (P : 'hpoly[R]_n) x :
  reflect (exists2 y, x = row' i y & y \in P) (x \in proj1 i P).
Proof.
case: P => m A b.
rewrite /proj1.
set Jeq0 := [set j | A j i == 0].
set Jlt0 := [set j | A j i < 0].
set Jgt0 := [set j | A j i > 0].
set bJeq0 := row_submx b Jeq0.
case: {-}_/idP => [Jlt0_not_empty | /negP Jlt0_empty];
  case: (boolP (#|Jgt0| > 0)%N) => [Jgt0_not_empty | Jgt0_empty].
- set AJlt0 := row_submx A Jlt0.
  set AJgt0 := row_submx A Jgt0.
  set AJlt0i := row_submx (col' i A) Jlt0.
  set AJgt0i := row_submx (col' i A) Jgt0.
  set AJeq0i := row_submx (col' i A) Jeq0.
  set bJlt0 := row_submx b Jlt0.
  set bJgt0 := row_submx b Jgt0.
  set q := (#|Jgt0| * #|Jlt0|)%N.
  set b'' := \matrix_(h < q , j < 1) ((bJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) j)
                                        * (AJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) i)
                                      - (bJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) j)
                                        * (AJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) i)).
  set A'' := \matrix_(h < q , j < n.-1) ((AJlt0i (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) j)
                                        * (AJgt0 (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) i)
                                      - (AJgt0i (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord h) )) j)
                                        * (AJlt0 (Ordinal (ltn_pmod (nat_of_ord h) Jlt0_not_empty)) i)).
  apply/(iffP idP) => [x_in_proj | [y -> y_in]].
  + set S := [seq ((col' i A *m x) k 0 - b k 0)/(- A k i) | k <- (enum Jlt0)].
    set y := \col_(k < n) match (unlift i k) with | Some j => x j 0 | None => (min_seq S 0) end.
    exists y; first by rewrite row'_eq.
    apply/forallP => k.
    case: (boolP (k \in (Jlt0 :|: Jgt0))) => [/setUP k_in_U | k_not_in_U].
    * case: k_in_U => [k_in_Jlt0 | k_in_Jgt0].
      - rewrite (mulmx_col'_row' A y i) [y i 0]mxE unlift_none addrC -ler_sub_addr -ler_subr_addl -mulNr mulrC row'_eq -ler_pdivl_mulr;
          last by rewrite inE -oppr_gt0 in k_in_Jlt0.
        by apply: min_seq_ler; apply: map_f; rewrite mem_enum.
      - rewrite (mulmx_col'_row' A y i) addrC -ler_sub_addr -ler_subr_addl -mulNr mulrC row'_eq [y i 0]mxE unlift_none.
        have min_seq_at: has [pred i | min_seq S 0 == i] S.
          apply/min_seq_eq/contraT; rewrite negbK => /eqP S_nil.
          have Jlt0_non_empty: exists j, j \in Jlt0 by apply/card_gt0P.
          move: Jlt0_non_empty => [j j_in_Jlt0].
          suff : ((col' i A *m x) j 0 - b j 0)/(- A j i) \in S by rewrite S_nil in_nil.
          by apply: map_f; rewrite mem_enum.
        move/hasP: min_seq_at => [? /mapP [j j_in_S ->] /= /eqP ->].
        rewrite -mulrA [X in _*X]mulrC mulrA ler_pdivr_mulr;
          last by rewrite mem_enum inE -oppr_gt0 in j_in_S.
        rewrite 2!mulrBl !mulrN 2!opprK -ler_sub_addr -addrA addrC lter_sub_addl.
        have HcastJlt0: (#|(enum Jlt0)| = #|Jlt0|)%N
          by rewrite cardE; apply: card_uniqP; exact: enum_uniq.
        set j' := (enum_rank_in j_in_S j).
        set k' := (enum_rank_in k_in_Jgt0 k).
        set r := (k' * #|Jlt0| + j')%N.
        have r_lt_q: (r < q)%N by apply: (@leq_trans ((k'.+1)* #|Jlt0|)%N);
          [rewrite -[k'.+1]addn1 mulnDl mul1n ltn_add2l; move: (ltn_ord j'); rewrite -HcastJlt0
            | rewrite (leq_pmul2r Jlt0_not_empty); exact: ltn_ord].
        move: ((forallP x_in_proj) (lshift #|Jeq0| (Ordinal r_lt_q))).
        rewrite mul_col_mx 2!col_mxEu 5!mxE.
        have k_eq: k = (enum_val (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord (Ordinal r_lt_q))))).
          have ->: (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord (Ordinal r_lt_q)))) = k'
            by apply: ord_inj; rewrite /= (divnMDl _ _ Jlt0_not_empty) -HcastJlt0 (divn_small (ltn_ord j')) addn0.
          by rewrite enum_rankK_in.
        have j_eq: j = (enum_val (Ordinal (ltn_pmod (Ordinal r_lt_q) Jlt0_not_empty))).
          have ->: (Ordinal (ltn_pmod (k' * #|Jlt0| + j') Jlt0_not_empty)) = cast_ord HcastJlt0 j'
            by apply: ord_inj; rewrite /= modnMDl -HcastJlt0; apply: modn_small; exact: ltn_ord.
          rewrite -((enum_rankK_in j_in_S) j j_in_S) (enum_val_nth (enum_val (enum_rank_in j_in_S j)))
                     [RHS](enum_val_nth (enum_val (enum_rank_in j_in_S j))).
          have ->: (enum (enum Jlt0)) = enum Jlt0 by apply: eq_enum; exact: mem_enum.
          by apply/eqP; rewrite (nth_uniq _ _ _ (enum_uniq (mem Jlt0))) // -cardE -?HcastJlt0; exact: ltn_ord.
        suff ->: (A'' *m x) (Ordinal r_lt_q) 0 = (col' i A *m x) j 0 * A k i - (col' i A *m x) k 0 * A j i by rewrite -k_eq -j_eq.
        rewrite !mxE 2!mulr_suml -sumrB.
        apply: eq_bigr => h _.
        by rewrite !mxE k_eq j_eq -[X in _ = X - _]mulrA -[X in _ = _ - X]mulrA [X in _ = _*X - _]mulrC
             [X in _ =  _ -_*X]mulrC [X in _ = X - _]mulrA [X in _ = _ - X]mulrA mulrBl.
    * have k_in_Jeq0: k \in Jeq0
        by rewrite inE; move: k_not_in_U; apply/contraR; rewrite neqr_lt in_setU !inE.
      move: ((forallP x_in_proj) (rshift q (enum_rank_in k_in_Jeq0 k))).
      rewrite mul_col_mx 2!col_mxEd -row_submx_mul 2!mxE enum_rankK_in // (mulmx_col'_row' A y i) row'_eq.
      rewrite inE in k_in_Jeq0.
      by rewrite (eqP k_in_Jeq0) mul0r add0r.
  + apply/forallP => j.
    case: (splitP' j) => [k -> | k ->].
    * set k' := (Ordinal (ltn_pmod k Jlt0_not_empty)).
      move: (enum_valP k'); rewrite inE => ?.
      set k'' := (Ordinal (ltn_divLR' Jlt0_not_empty (ltn_ord k))).
      move: (enum_valP k''); rewrite inE => ?.
      have ->: ((col_mx A'' AJeq0i) *m row' i y) (lshift #|Jeq0| k) 0 = (AJlt0i *m row' i y) k' 0 * AJgt0 k'' i  - (AJgt0i *m row' i y) k'' 0 * AJlt0 k' i.
        rewrite mul_col_mx col_mxEu !mxE /= 2!mulr_suml -sumrB.
        apply: eq_bigr => h _.
        by rewrite !mxE mulrBl [X in X * y _ _]mulrC -[X in X-_]mulrA mulrC -[X in _ - X]mulrA [X in _ - _*X]mulrC [X in _ - X]mulrA.
      rewrite col_mxEu mxE -2!row_submx_mul !row_submx_mxE ler_subl_addr -[X in _ <= X]addrA -ler_subl_addl [X in _ <= X]addrC -2!mulrBl
          -ler_pdivl_mulr // -[X in _ <= X]mulrA [X in _ <= _ * X]mulrC [X in _ <= X]mulrA -[X in _ <= X]opprK -mulrN -mulNr -ler_pdivr_mulr;
            last by rewrite oppr_gt0.
      rewrite ler_oppr.
      apply: (@ler_trans _ (y i 0)).
      - rewrite ler_pdivr_mulr // mulrC ler_subl_addr -mulmx_col'_row'.
        by apply: (forallP y_in).
      - rewrite ler_oppr ler_pdivr_mulr; last by rewrite oppr_gt0.
        rewrite mulrNN mulrC ler_subl_addr -mulmx_col'_row'.
        by apply: (forallP y_in).
    * suff ->: ((col_mx A'' AJeq0i) *m row' i y) (rshift q k) 0 = (A *m y) (enum_val k) 0
        by rewrite col_mxEd mxE; apply: (forallP y_in).
      rewrite mul_col_mx col_mxEd -row_submx_mul row_submx_mxE (mulmx_col'_row' A y i).
      by move: (enum_valP k); rewrite inE => /eqP ->; rewrite mul0r add0r.
- apply: (iffP idP) => [x_in_proj | [y -> y_in]].
  + set S := [seq ((col' i A *m x) k 0 - b k 0)/(- A k i) | k <- (enum Jlt0)].
    set y := \col_(k < n) match (unlift i k) with | Some j => x j 0 | None => (min_seq S 0) end.
    exists y; first by rewrite row'_eq.
    apply/forallP => k.
    case: (boolP (k \in Jlt0)) => [k_in_Jlt0 | k_not_in_Jlt0].
    * rewrite (mulmx_col'_row' A y i) [y i 0]mxE unlift_none addrC -ler_sub_addr -ler_subr_addl -mulNr mulrC row'_eq -ler_pdivl_mulr;
        last by rewrite inE -oppr_gt0 in k_in_Jlt0.
      by apply: min_seq_ler; apply: map_f; rewrite mem_enum.
    * have k_in_Jeq0: k \in Jeq0.
        rewrite inE; move/norP: (conj k_not_in_Jlt0 Jgt0_empty).
        apply/contraR; rewrite neqr_lt !inE; move/orP.
        case => [k_in_Jlt0 | ?]; apply/orP; first by left.
        by right; rewrite card_gt0; apply/set0Pn; exists k; rewrite inE.
      move: ((forallP x_in_proj) (enum_rank_in k_in_Jeq0 k)).
      rewrite -row_submx_mul 2!mxE enum_rankK_in // (mulmx_col'_row' A y i) row'_eq.
      rewrite inE in k_in_Jeq0.
      by rewrite (eqP k_in_Jeq0) mul0r add0r.
  + apply/forallP => j.
    rewrite -row_submx_mul 2!mxE.
    have ->: (col' i A *m row' i y) (enum_val j) 0 = (A *m y) (enum_val j) 0 - A (enum_val j) i * y i 0
      by rewrite (mulmx_col'_row' A y i) [X in _ = X -_]addrC -addrA subrr addr0.
    move: (enum_valP j); rewrite inE => /eqP ->.
    by rewrite mul0r subr0; apply: (forallP y_in).
- apply: (iffP idP) => [x_in_proj | [y -> y_in]].
  + set S := [seq ((col' i A *m x) k 0 - b k 0)/(A k i) | k <- (enum Jgt0)].
    set y := \col_(k < n) match (unlift i k) with | Some j => x j 0 | None => (- min_seq S 0) end.
    exists y; first by rewrite row'_eq.
    apply/forallP => k.
    case: (boolP (k \in Jgt0)) => [k_in_Jgt0 | k_not_in_Jgt0].
    * rewrite (mulmx_col'_row' A y i) [y i 0]mxE unlift_none addrC -ler_sub_addr -ler_subr_addl -mulrN mulrC row'_eq opprK -ler_pdivl_mulr;
        last by rewrite inE in k_in_Jgt0.
      by apply: min_seq_ler; apply: map_f; rewrite mem_enum.
    * have k_in_Jeq0: k \in Jeq0.
        rewrite inE; move/norP: (conj k_not_in_Jgt0 Jlt0_empty).
        apply/contraR; rewrite neqr_lt !inE; move/orP.
        case => [k_in_Jlt0 | ?]; apply/orP; last by left.
        by right; rewrite card_gt0; apply/set0Pn; exists k; rewrite inE.
      move: ((forallP x_in_proj) (enum_rank_in k_in_Jeq0 k)).
      rewrite -row_submx_mul 2!mxE enum_rankK_in // (mulmx_col'_row' A y i) row'_eq.
      rewrite inE in k_in_Jeq0.
      by rewrite (eqP k_in_Jeq0) mul0r add0r.
  + apply/forallP => j.
    rewrite -row_submx_mul 2!mxE.
    have ->: (col' i A *m row' i y) (enum_val j) 0 = (A *m y) (enum_val j) 0 - A (enum_val j) i * y i 0
      by rewrite (mulmx_col'_row' A y i) [X in _ = X -_]addrC -addrA subrr addr0.
    move: (enum_valP j); rewrite inE => /eqP ->.
    by rewrite mul0r subr0; apply: (forallP y_in).
- apply: (iffP idP) => [x_in_proj | [y -> y_in]].
  + set y := \col_(k < n) match (unlift i k) with | Some j => x j 0 | None => 0 end.
    exists y; first by rewrite row'_eq.
    apply/forallP => k.
    rewrite (mulmx_col'_row' A y i) row'_eq [y i 0]mxE unlift_none mulr0 add0r.
    exact: ((forallP x_in_proj) k).
  + apply/forallP => j.
    have ->: (col' i A *m row' i y) j 0 = (A *m y) j 0 - A j i * y i 0
      by rewrite (mulmx_col'_row' A y i) [X in _ = X -_]addrC -addrA subrr addr0.
    suff ->: A j i = 0 by rewrite mul0r subr0; exact: ((forallP y_in) j).
    apply/eqP; move/norP: (conj Jlt0_empty Jgt0_empty).
    apply/contraR; rewrite neqr_lt; move/orP.
    by case => [? | ?]; apply/orP; [left | right]; rewrite card_gt0; apply/set0Pn; exists j; rewrite inE.
Qed.

End Proj1.

Section Projection.

Variable (R : realFieldType) (n : nat).

Fixpoint proj (k : nat) : 'hpoly[R]_(k+n) -> 'hpoly[R]_n :=
  match k with
  | 0 => id
  | (km1.+1)%N as k => (proj (k := km1)) \o (proj1 ord0)
  end.

Lemma projP (k : nat) (P : 'hpoly[R]_(k+n)) x :
  reflect (exists y, col_mx y x \in P) (x \in proj P).
Proof.
elim: k P => [ P | k Hind P].
- apply: (iffP idP) => [x_in_proj | [?]].
  + by exists 0; rewrite col_mx0l.
  + by rewrite col_mx0l.
- apply: (iffP (Hind _)) => [[y H] | [y H]].
  + move/(proj1P (n := k.+1+n)): H => [y' eq y'_in_P]. (* TODO: n needs to be explicitly specified *)
    exists (usubmx y'); suff ->: x = dsubmx y' by rewrite vsubmxK.
    apply/colP => i.
    move/colP/(_ (@rshift k n i)): eq; rewrite !mxE.
    case: splitP'; last first.
    * move => ? /rshift_inj <- ->; apply: congr2; last done.
      by apply/ord_inj => /=.
    * move => ? /eqP; by rewrite eq_sym (negbTE (lrshift_distinct _ _)).
  + exists (row' ord0 y); apply/(proj1P (n := (k.+1+n))).
    exists (col_mx y x); by rewrite -?row'Ku.
Qed.

End Projection.

Section Lift.

Variable (R : realFieldType) (n k : nat).

Definition lift_poly (P : 'hpoly[R]_n) : 'hpoly[R]_(n+k) :=
  let: HPoly _ A b := P in
  HPoly (row_mx A 0) b.

Lemma lift_polyP (P : 'hpoly[R]_n) x :
  (x \in lift_poly P) = (usubmx x \in P).
Admitted.

End Lift.

Module Import Exports.
Canonical hpoly_eqType.
Canonical hpoly_choiceType.
Notation "''hpoly[' R ]_ n" := (@hpoly R n) (at level 8).
Notation "''hpoly_' n" := ('hpoly[_]_n) (at level 8).
Notation "P .`c" := (hpoly_c P) (at level 2, format "P .`c").
Notation "P .`A" := (hpoly_A P) (at level 2, format "P .`A").
Notation "P .`b" := (hpoly_b P) (at level 2, format "P .`b").
End Exports.
End HPolyhedron.

Export HPolyhedron.Exports.
Coercion mem_hpoly := HPolyhedron.mem_hpoly.
