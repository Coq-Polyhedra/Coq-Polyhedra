(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2017, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector perm.
Require Import extra_misc inner_product vector_order extra_matrix row_submx exteqtype hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''poly[' R ]_ n" (at level 8, n at level 2, format "''poly[' R ]_ n").
Reserved Notation "''poly_' n" (at level 8, n at level 2).
Reserved Notation "''[' P ]" (at level 0, format "''[' P ]").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section QuotDef.

Variable R : realFieldType.
Variable n : nat.

Definition canon (P : 'hpoly[R]_n) := choose (ext_eq_op P) P.

Record poly := Poly {
  hpoly : 'hpoly[R]_n;
  _ : canon hpoly == hpoly;
}.

Lemma canon_id P : canon (canon P) == canon P.
Proof.
rewrite /canon.
set P' := choose (ext_eq_op P) P.
have P_eq_P': (P ==i P') by exact: chooseP.
suff /eq_choose ->: ext_eq_op P' =1 ext_eq_op P.
- by apply/eqP; apply: choose_id.
- move => Q.
  by apply/idP/idP; apply: ext_eq_trans; last by rewrite ext_eq_sym.
Qed.

Definition class_of P := Poly (canon_id P).

End QuotDef.

Arguments hpoly [R n].
Prenex Implicits hpoly.
Notation "''poly[' R ]_ n" := (@poly R n).
Notation "''poly_' n" := ('poly[_]_n).
Notation "''[' P ]" := (class_of P).

Section QuotStruct.

Variable R : realFieldType.
Variable n : nat.

Canonical poly_subType := [subType for (@hpoly R n)].
Definition poly_eqMixin := Eval hnf in [eqMixin of 'poly[R]_n by <:].
Canonical poly_eqType := Eval hnf in EqType 'poly[R]_n poly_eqMixin.
Definition poly_choiceMixin := Eval hnf in [choiceMixin of 'poly[R]_n by <:].
Canonical poly_choiceType := Eval hnf in ChoiceType 'poly[R]_n poly_choiceMixin.
Definition mem_poly (P : 'poly[R]_n) := hpoly P : pred_class.

Lemma hpoly_inj : injective (@hpoly R n).
Proof.
exact: val_inj.
Qed.

Lemma hpolyK (P : 'poly[R]_n) : '[ hpoly P ] = P.
case: P => [P P_eq]; apply: hpoly_inj.
exact: eqP.
Qed.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpoly[R]_n -> Type :=
  HpolySpec Q of (P = '[Q]) : hpoly_spec P Q.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma poly_eqE (P Q : 'hpoly[R]_n) : ('[ P ] == '[ Q ]) = (P ==i Q).
Proof.
Admitted.

Lemma poly_eqP (P Q : 'hpoly[R]_n) : ('[ P ] = '[ Q ]) <-> (P =i Q).
Proof.
Admitted.

End QuotStruct.

Arguments hpolyP [R n].
Prenex Implicits hpolyP.
Coercion mem_poly : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

Lemma mem_quotP (P : 'hpoly[R]_n) : '[ P ] =i P.
Proof.
move => x; rewrite /mem_poly.
by case/hpolyP: '[P] => Q /poly_eqP.
Qed.

Let quotE := mem_quotP.

Definition non_empty (P : 'poly[R]_n) := (HPrim.non_empty (hpoly P)).

Lemma non_emptyP (P : 'poly[R]_n) :
  reflect (exists x, x \in P) (non_empty P).
Proof.
exact: (equivP HPrim.non_emptyP).
Qed.

Arguments non_emptyP [P].

Lemma non_empty_quotP (P : 'hpoly[R]_n) :
  non_empty '[ P ] = HPrim.non_empty P.
Proof.
apply/(sameP non_emptyP)/(equivP HPrim.non_emptyP).
by split; move => [x x_in]; exists x; rewrite ?quotE in x_in *.
Qed.

Definition is_included_in_hyperplane (P : 'poly[R]_n) c d :=
  HPrim.is_included_in_hyperplane (hpoly P) c d.

Lemma is_included_in_hyperplaneP (P : 'poly[R]_n) c d :
  reflect (forall x : 'cV_n, x \in P -> '[ c, x] = d)
          (is_included_in_hyperplane P c d).
Proof.
exact: (equivP HPrim.is_included_in_hyperplaneP).
Qed.

Arguments is_included_in_hyperplaneP [P c d].

Lemma is_included_in_hyperplane_quotP (P : 'hpoly[R]_n) c d :
  is_included_in_hyperplane '[ P ] c d = HPrim.is_included_in_hyperplane P c d.
Proof.
apply/(sameP is_included_in_hyperplaneP)/(equivP HPrim.is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite quotE.
Qed.

Variable c : 'cV[R]_n.

Definition bounded (P: 'poly[R]_n) := HPrim.bounded c (hpoly P).
Definition unbounded (P: 'poly[R]_n) := HPrim.unbounded c (hpoly P).
Definition opt_value (P: 'poly[R]_n) := HPrim.opt_value c (hpoly P).

CoInductive lp_state (P : 'poly[R]_n) : option R -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state P None false false false
| Bounded (v : R) of (exists x, x \in P /\ '[c,x] = v) * (forall x, x \in P -> v <= '[c,x]) : lp_state P (Some v) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P None true false true.

Lemma lp_stateP P :
  lp_state P (opt_value P) (non_empty P) (bounded P) (unbounded P).
Admitted.
(*
Proof. (* RK *)
unlock opt_value non_empty bounded unbounded; rewrite /HPrim.opt_value.
case: (HPrim.lp_stateP c (hpoly P)) =>
  [empty_hpoly_P | x [x_in_hpoly_P x_is_opt] | unbounded_hpoly_P].
- constructor.
  move => x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)) empty_hpoly_P.
- constructor.
  split.
  + exists x.
    split; last by done.
      by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
  + move => y.
    rewrite -{1}[P]reprK (mem_polyhedron_quotP y (hpoly P)).
    exact: x_is_opt.
- constructor.
  move => K.
  move: (unbounded_hpoly_P K) => [x ?].
  exists x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
Qed.*)

Lemma boundedP (P : 'poly[R]_n) :
  reflect (exists x, x \in P /\ (forall y, y \in P -> '[ c, x] <= '[ c, y]))
         (bounded P).
Proof.
exact: (equivP HPrim.boundedP).
Qed.

Lemma unboundedP (P : 'poly[R]_n) :
  reflect (forall K, exists x, x \in P /\ '[c,x] < K) (unbounded P).
Proof.
exact: (equivP HPrim.unboundedP).
Qed.

Lemma bounded_certP P :
  non_empty P -> reflect (exists K, (forall z, z \in P -> '[c,z] >= K)) (bounded P).
Proof.
move => P_non_empty.
exact: (equivP (HPrim.bounded_certP _)).
Qed.

Lemma lp_quotP (P : 'hpoly[R]_n) :
  (non_empty '[ P ] = HPrim.non_empty P)
  * (bounded '[ P ] = HPrim.bounded c P)
  * (unbounded '[ P ] = HPrim.unbounded c P)
  * (opt_value '[ P ] = HPrim.opt_value c P).
Proof.
Admitted.

End Lift.

Section Base.

Variable R : realFieldType.
Variable n : nat.

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists I , P == '[ 'P^=(base; I) ]].

Variable P : 'poly[R]_n.
Variable base: 'hpoly[R]_n.
Hypothesis P_base : has_base P base.

Definition active :=
  let P' := hpoly P in
  let: 'P(A,b) as base := base return {set 'I_(#ineq base)} in
    [ set i : 'I_(#ineq base) | is_included_in_hyperplane P (row i A)^T (b i 0) ].

Definition active :=




Lemma hpoly_of_baseP (P: 'poly[R]_n) (base : 'hpoly[R]_n) :
  has_base P base -> P = '[  ]

  isSome [pick I | P == '[ 'P^=(base; I) ]].
Admitted.
Search _ isSome.


Variable P : 'poly[R]_n.
Variable base : 'hpoly[R]_n.


Check (existsP (idP (has_base P base))).

Definition hpoly_base (P

End EquivRel.

Arguments hpoly_equiv_rel [R n].

Definition poly R n := {eq_quot (@hpoly_equiv_rel R n)}%qT.

Notation "''poly[' R ]_ n" := (@poly R n).
Notation "''poly_' n" := ('poly[_]_n).
Notation "\poly" := (\pi_('poly_ _))%qT.
Notation "''[' P ]" := (\pi_('poly_ _) P)%qT.
Notation "P =e Q" := ('[ P ] = '[ Q ]).
Notation "P ==e Q" := ('[ P ] == '[ Q ]).

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

Definition mem_polyhedron (R : realFieldType) (n : nat) : 'poly[R]_n -> pred_class :=
  lift_fun1 'poly[R]_n id.
Coercion mem_polyhedron : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpoly[R]_n -> Type :=
  HpolySpec Q of (P = '[Q]) : hpoly_spec P Q.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma ext_eqquotP (P Q : 'hpoly[R]_n) :
  (P =i Q) <-> (P =e Q).
Proof.
by split => [? |]; [ apply/eqquotP/ext_eqP | move/eqquotP/ext_eqP].
Qed.

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists Q : 'hpolyEq(base), P == '[Q]].

Lemma has_baseP (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  reflect (exists (Q : 'hpolyEq(base)), P = '[Q]) (has_base P base).
Proof.
exact: exists_eqP.
Qed.

Lemma repr_hpolyEq (P : 'poly[R]_n) (Q : 'hpoly[R]_n) :
  P = '[Q] -> P = '['P^=(Q; set0)].
Proof.
case: Q => [m A b] ->.
apply/ext_eqquotP => x.
rewrite hpolyEq_inE.
suff ->: [forall j in set0, (A *m x) j 0 == b j 0]
  by rewrite andbT.
by apply/forall_inP => j; rewrite inE.
Qed.

Lemma self_base (P : 'poly[R]_n) (Q : 'hpoly[R]_n) :
  P = '[Q] -> has_base P Q.
Proof.
move/repr_hpolyEq => P_eq.
by apply/existsP; exists 'P^=(Q; set0); rewrite P_eq.
Qed.

Lemma mem_polyhedron_quotP (x : 'cV[R]_n) :
  { mono \poly : P / x \in P >-> (x \in mem_polyhedron P) }.
Proof.
unlock mem_polyhedron => P /=.
by case: (hpolyP '[ P ]) => Q /ext_eqquotP.
Qed.

Canonical mem_polyhedron_quot x := Eval hnf in PiMono1 (mem_polyhedron_quotP x).
Canonical polyhedron_predType := Eval hnf in @mkPredType 'cV[R]_n 'poly[R]_n (@mem_polyhedron R n).

Definition non_empty := lift_fun1 'poly[R]_n (@HPrim.non_empty R n).

Lemma non_empty_quotP :
  { mono \poly : P / HPrim.non_empty P >-> non_empty P }.
Proof.
unlock non_empty => P /=.
case: (hpolyP '[ P ]) => Q /ext_eqquotP P_eq_i_Q.
apply/idP/idP => /HPrim.non_emptyP [x H];
  apply/HPrim.non_emptyP; exists x; by rewrite ?P_eq_i_Q in H *.
Qed.

Canonical non_empty_quot := Eval hnf in PiMono1 non_empty_quotP.

Implicit Type c : 'cV[R]_n.

Definition bounded c := lift_fun1 'poly[R]_n (HPrim.bounded c).
Definition unbounded c := lift_fun1 'poly[R]_n (HPrim.unbounded c).
Definition opt_value c := lift_fun1 'poly[R]_n (HPrim.opt_value c).

CoInductive lp_state c (P : 'poly[R]_n) : option R -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state c P None false false false
| Bounded (v : R) of (exists x, x \in P /\ '[c,x] = v) * (forall x, x \in P -> v <= '[c,x]) : lp_state c P (Some v) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state c P None true false true.

Lemma lp_stateP c P :
  lp_state c P (opt_value c P) (non_empty P) (bounded c P) (unbounded c P).
Proof. (* RK *)
unlock opt_value non_empty bounded unbounded; rewrite /HPrim.opt_value.
case: (HPrim.lp_stateP c (hpoly P)) =>
  [empty_hpoly_P | x [x_in_hpoly_P x_is_opt] | unbounded_hpoly_P].
- constructor.
  move => x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)) empty_hpoly_P.
- constructor.
  split.
  + exists x.
    split; last by done.
      by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
  + move => y.
    rewrite -{1}[P]reprK (mem_polyhedron_quotP y (hpoly P)).
    exact: x_is_opt.
- constructor.
  move => K.
  move: (unbounded_hpoly_P K) => [x ?].
  exists x.
  by rewrite -{1}[P]reprK (mem_polyhedron_quotP x (hpoly P)).
Qed.

Variable c : 'cV[R]_n.

Lemma bounded_quotP :
  (* TODO: we should prove all the quotP statements in a row,
           using the (h)lp_stateP statement *)
  { mono \poly : P / HPrim.bounded c P >-> bounded c P }.
Proof.
unlock bounded => P /=.
case: (hpolyP '[ P ]) => Q.
move => /ext_eqquotP P_eq_Q.
case: (HPrim.lp_stateP c P); case: (HPrim.lp_stateP c Q); try by done.
- move => z [z_in_Q _] /(_ z).
  by rewrite P_eq_Q z_in_Q inE.
- move => Q_empty z [z_in_Q _]; move/(_ z): Q_empty.
  by rewrite -P_eq_Q z_in_Q inE.
- move => Q_unbounded z [z_in_P z_opt].
  move/(_ '[c,z]): Q_unbounded => [x [x_in_Q x_lt_z]].
  rewrite -P_eq_Q in x_in_Q.
  move/(_ _ x_in_Q): z_opt => z_le_x.
  by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
- move => z [z_in_Q z_opt] P_unbounded.
  move/(_ '[c,z]): P_unbounded => [x [x_in_P x_lt_z]].
  rewrite P_eq_Q in x_in_P.
  move/(_ _ x_in_P): z_opt => z_le_x.
  by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
Qed.

Canonical bounded_quot := Eval hnf in PiMono1 bounded_quotP.

Lemma unbounded_quotP :
  { mono \poly : P / HPrim.unbounded c P >-> unbounded c P }.
Proof.
unlock unbounded => P /=.
case: (hpolyP '[ P ]) => Q /ext_eqquotP P_eq_Q.
case: (HPrim.lp_stateP c P); case: (HPrim.lp_stateP c Q); try by done.
+ move => Q_unbounded.
  move/(_ 0): Q_unbounded => [x [x_in_Q x_lt_0]].
  move/(_ x).
    by rewrite P_eq_Q x_in_Q inE.
+ move => Q_unbounded z [z_in_P z_opt].
  move/(_ '[c,z]): Q_unbounded => [x [x_in_Q x_lt_z]].
  rewrite -P_eq_Q in x_in_Q.
  move/(_ _ x_in_Q): z_opt => z_le_x.
    by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
+ move => Q_empty P_unbounded.
  move/(_ 0): P_unbounded => [x [x_in_Q x_lt_0]].
  move: (Q_empty x).
    by rewrite -P_eq_Q x_in_Q inE.
+ move => z [z_in_Q z_opt] P_unbounded.
  move/(_ '[c,z]): P_unbounded => [x [x_in_P x_lt_z]].
  rewrite P_eq_Q in x_in_P.
  move/(_ _ x_in_P): z_opt => z_le_x.
    by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
Qed.

Canonical unbounded_quot := Eval hnf in PiMono1 unbounded_quotP.

Lemma opt_value_quotP :
  { mono \poly : P / HPrim.opt_value c P >-> opt_value c P }.
Proof.
unlock opt_value => P /=.
case: (hpolyP '[ P ]) => Q /ext_eqquotP P_eq_Q.
rewrite /HPrim.opt_value.
case: (HPrim.lp_stateP c P); case: (HPrim.lp_stateP c Q) => /=; try by done.
+ move => z [z_in_Q _] /(_ z).
    by rewrite (P_eq_Q z) z_in_Q inE.
+ move => Q_empty z [z_in_P _].
    by rewrite (P_eq_Q z) (Q_empty z) inE in z_in_P.
+ move => z [z_in_Q z_opt_in_Q].
  move => y [y_in_P y_opt_in_P].
  apply/congr1/eqP; rewrite eqr_le; apply/andP; split.
  * rewrite P_eq_Q in y_in_P; exact: z_opt_in_Q.
  * rewrite -P_eq_Q in z_in_Q; exact: y_opt_in_P.
+ move => Q_unbounded z [z_in_P z_opt].
  move/(_ '[c,z]): Q_unbounded => [x [x_in_Q x_lt_z]].
  rewrite -P_eq_Q in x_in_Q.
  move/(_ _ x_in_Q): z_opt => z_le_x.
    by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
+ move => z [z_in_Q z_opt] P_unbounded.
  move/(_ '[c,z]): P_unbounded => [x [x_in_P x_lt_z]].
  rewrite P_eq_Q in x_in_P.
  move/(_ _ x_in_P): z_opt => z_le_x.
    by move/andP: (conj z_le_x x_lt_z); rewrite lter_anti.
Qed.

Canonical opt_value_quot := Eval hnf in PiMono1 opt_value_quotP.

End Lift.

Section Face.

Variable R : realFieldType.
Variable n : nat.

Definition face_of (P : 'poly[R]_n) :=
  let Q := 'P^=(hpoly P; set0) in
    lift_fun1 'poly[R]_n (hface_of Q).

Lemma face_ofP (F P : 'poly[R]_n) :
  (non_empty P) ->
    reflect (exists c, bounded c P /\ (forall x, (x \in P /\ Some '[c,x] = opt_value c P) <-> x \in F))
          (face_of P F). (* RK *)
Proof.
unlock face_of.
case: (hpolyP F) => G ->.
case: (hpolyP P) => Q /repr_hpolyEq P_repr.
move => P_non_empty; rewrite P_repr polyE in P_non_empty.
apply: (iffP idP).
- move/(hface_ofP _ P_non_empty) => [c [? ?]].
  exists c; split.
  + by rewrite P_repr polyE.
  + by move => x; rewrite P_repr !polyE.
- move => [c [bounded_c_P H]].
  apply/(hface_ofP _ P_non_empty).
  exists c; split.
  + by rewrite P_repr polyE in bounded_c_P.
  + move => x.
    by move/(_ x): H; rewrite {1 2}P_repr !polyE.
Qed.

Fact has_face_imp_non_empty P F : face_of P F -> non_empty P.
Proof.
unlock face_of.
case: (hpolyP P) => Q /repr_hpolyEq ->.
rewrite polyE; exact: has_hface_imp_non_empty.
Qed.

Lemma face_of_quotP (P F : 'poly[R]_n) :
  forall base (P' : 'hpolyEq(base)) (F' : 'hpoly[R]_n),
    P = '[P'] -> F = '[F'] -> face_of P F = hface_of P' F'.
Proof. (* RK *)
move => base P' F' P_eq_P' F_eq_F'.
case: (boolP (non_empty P)) => [ P_non_empty | P_empty ].
- apply/(sameP (face_ofP _ P_non_empty)).
  rewrite P_eq_P' polyE in P_non_empty.
  apply/(equivP (hface_ofP _ P_non_empty)).
  split.
  + move => [c [bounded_c_P' F'_is_opt]].
    exists c.
    split.
    * by rewrite P_eq_P' polyE.
    * move => x.
      by rewrite P_eq_P' F_eq_F' !polyE.
  + move => [c [bounded_c_P F_is_opt]].
    exists c.
    split.
    * by rewrite P_eq_P' polyE in bounded_c_P.
    * move => x.
      move: (F_is_opt x).
      by rewrite P_eq_P' F_eq_F' !polyE.
- have -> : face_of P F = false
    by move: P_empty; apply: contraNF; exact: has_face_imp_non_empty.
  symmetry.
  move: P_empty; rewrite P_eq_P' polyE.
  by apply: contraNF; exact: has_hface_imp_non_empty.
Qed.

Arguments face_of_quotP [P F base P' F'].

Definition active (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  match [pick Q : 'hpolyEq(base) | P == '[Q]] with
  | Some Q => \active Q
  | None => set0
  end.

Lemma active_quotP (P : 'poly[R]_n) (base : 'hpoly[R]_n) (Q : 'hpolyEq(base)) :
  P = '[Q] -> active P base = \active Q. (* RK *)
Proof.
case: base Q => [m A b] Q.
case: (hpolyP P) => hP ->.
move/ext_eqquotP => P_eq_Q.
apply/eqP.
rewrite eqEsubset.
apply/andP.
split.
- apply/subsetP => i.
  rewrite /active.
  case: pickP => [Q' /eqP/ext_eqquotP P_eq_Q' | ].
  + move/activeP => i_in_active_Q'.
    apply/activeP => x x_in_Q.
    apply: i_in_active_Q'.
    by rewrite -P_eq_Q' P_eq_Q.
  + by rewrite inE.
- apply/subsetP => i /activeP i_in_active_Q.
  rewrite /active.
  case: pickP => [Q' /eqP/ext_eqquotP P_eq_Q' | empty_class_P].
  + apply/activeP => x x_in_Q'.
    apply: i_in_active_Q.
    by rewrite -P_eq_Q P_eq_Q'.
  + move: (empty_class_P Q).
    by move/ext_eqquotP/eqP: P_eq_Q ->.
Qed.

Lemma face_of_defP (P F : 'poly[R]_n) :
  forall base, has_base P base ->
          reflect ([/\ has_base F base, non_empty F & (active P base) \subset (active F base)])
                  (face_of P F).
Proof.
move => base P_base.
apply/(iffP idP);
  move/has_baseP : P_base => [P' P_eq_P'];
  move: (hpolyP F) => [F' F_eq_F'];
  rewrite (face_of_quotP P_eq_P' F_eq_F').
- move/andP => [F'_non_empty /existsP [F'']
                 /andP [/ext_eqP/ext_eqquotP F'_eq_F'' active_subset]].
  move: (F_eq_F'); rewrite F'_eq_F'' => F_eq_F''.
  split.
  + by apply/has_baseP; exists F''.
  + by rewrite F_eq_F' polyE.
  + by rewrite (active_quotP P_eq_P') (active_quotP F_eq_F'').
- move => [F_base F_non_empty active_subset].
  apply/andP; split.
  + by rewrite F_eq_F' polyE in F_non_empty.
  + apply/existsP.
    move/has_baseP : F_base => [F'' F_eq_F''].
    exists F''; apply/andP; split.
    * by apply/ext_eqP/ext_eqquotP; rewrite -F_eq_F''.
    * by rewrite -(active_quotP P_eq_P') -(active_quotP F_eq_F'').
Qed.

Arguments face_of_defP [P F base].

(*Lemma face_ofP F P :
  reflect (exists c, bounded P c /\ forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in F)))
           (face_of F P).
Proof.
Admitted.

Lemma totoP (base : 'hpoly[R]_n) (P_NF : 'hpolyEq(base)) F :
  reflect (
      non_empty F
      /\  exists Q : 'hpolyEq(base),
        (\eq_set P_NF \subset \eq_set Q) /\ (F = '[ HPolyEqS Q ])) (face_of '[ HPolyEqS P_NF ] F).
Proof.
case: (hpolyP F) => F' ->.
rewrite !polyE.
apply: (iffP andP).
- move => [F_non_empty /existsP [Fb /andP [superset /eqP ->]]].
  split; first by done.
  by exists Fb; split.
- move => [F_non_empty [Fb [superset ->]]].
  split; first by done.
  apply/existsP. exists Fb.
  by apply/andP; split.
Qed.*)

(*CoInductive hpolyEq_spec (P : 'poly[R]_n) : Type :=
  HPolySpecNF (base: 'hpoly[R]_n) (Q : 'hpolyEq(base)) of (P = '[ HPolyEqS Q ]) : hpolyEq_spec P.

Fact hpolyEqP (P : 'poly[R]_n) :
  hpolyEq_spec P.
Proof.
(*move: (erefl (hpoly P)).
case: {2}(hpoly P) => [base Q] /=.*)
constructor.
case: {-1}(hpoly P) (erefl (hpoly P)) => [base Q] /= <-.
by rewrite reprK.
Qed.*)

Section Ex.

Variable P : 'poly[R]_n.
Variable F : 'poly[R]_n.
Variable G : 'poly[R]_n.

Fact foo' : face_of P F -> face_of F G -> face_of P G.
case/hpolyP: P => P_base ->.
have P_self_base := (self_base (erefl '[ P_base ])).
move/(face_of_defP P_self_base) => [F_base _ active_F].
move/(face_of_defP F_base) => [G_base G_non_empty active_G].
apply/(face_of_defP P_self_base); split; try by done.
by apply/(subset_trans _ active_G).
Qed.

End Ex.

End Face.
