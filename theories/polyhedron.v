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
Reserved Notation "{ 'eq' P 'on' base }" (at level 0, format "{ 'eq' P  'on'  base }").
Reserved Notation "{ 'eq' P }" (at level 0, format "{ 'eq'  P }").
Reserved Notation "[ P 'has' '\base' base ]" (at level 0, format "[ P  'has'  '\base'  base ]").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section QuotDef.

Variable R : realFieldType.
Variable n : nat.

Definition canon (hP : 'hpoly[R]_n) :=
  choose (ext_eq_op hP) hP.

Record poly := Poly {
  hpoly : 'hpoly[R]_n;
  _ : canon hpoly == hpoly;
}.

Lemma canon_id hP :
  canon (canon hP) == canon hP.
Proof.
rewrite /canon.
set hQ := choose (ext_eq_op hP) hP.
have hP_eq_hQ: (hP ==i hQ) by exact: chooseP.
suff /eq_choose ->: ext_eq_op hQ =1 ext_eq_op hP
  by apply/eqP; apply: choose_id.
move => hR.
by apply/idP/idP; apply: ext_eq_trans; last by rewrite ext_eq_sym.
Qed.

Definition class_of hP := Poly (canon_id hP).

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

Lemma hpoly_inj :
  injective (@hpoly R n).
Proof.
exact: val_inj.
Qed.

Lemma hpolyK (P : 'poly[R]_n) :
  '[hpoly P] = P.
Proof.
case: P => [P P_eq]; apply: hpoly_inj.
exact: eqP.
Qed.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpoly[R]_n -> Type :=
  HpolySpec hQ of (P = '[hQ]) : hpoly_spec P hQ.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma poly_eqE (hP hQ : 'hpoly[R]_n) :
  ('[hP] == '[hQ]) = (hP ==i hQ).
Proof. (* RK: to be improved? *)
apply/idP/idP => [/eqP eq_classes | hP_eq_hQ].
- have canonhP : canon (hpoly '[hP]) = (hpoly '[hP])
    by exact: (eqP (canon_id hP)).
  have canonhQ : canon (hpoly '[hQ]) = (hpoly '[hQ])
    by exact: (eqP (canon_id hQ)).
  rewrite [in LHS]eq_classes canonhQ /= in canonhP.
  have: hQ ==i canon hQ
    by rewrite /canon; apply/chooseP.
  rewrite canonhP ext_eq_sym.
  apply: ext_eq_trans.
  by rewrite /canon; apply/chooseP.
- have H: ext_eq_op hQ =1 ext_eq_op hP
    by move => hR; apply/idP/idP; apply: ext_eq_trans; [done | rewrite ext_eq_sym].
  apply/eqP; apply: hpoly_inj.
  rewrite /= /canon (eq_choose H).
  by apply: choose_id.
Qed.

Lemma poly_eqP (hP hQ : 'hpoly[R]_n) :
  ('[hP] = '[hQ]) <-> (hP =i hQ).
Proof. (* RK: to be improved? *)
split.
- by move/eqP; rewrite poly_eqE; apply/HPrim.hpoly_ext_eqP.
- move/HPrim.hpoly_ext_eqP => ?.
  by apply/eqP; rewrite poly_eqE.
Qed.

End QuotStruct.

Arguments hpolyP [R n].
Prenex Implicits hpolyP.
Coercion mem_poly : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

Lemma mem_quotP (hP : 'hpoly[R]_n) : '[hP] =i hP.
Proof.
move => x; rewrite /mem_poly.
by case/hpolyP: '[hP] => hQ /poly_eqP.
Qed.

Let quotE := mem_quotP.

Definition non_empty (P : 'poly[R]_n) := (HPrim.non_empty (hpoly P)).

Lemma non_emptyP (P : 'poly[R]_n) :
  reflect (exists x, x \in P) (non_empty P).
Proof.
exact: (equivP HPrim.non_emptyP).
Qed.

Arguments non_emptyP [P].

Lemma non_empty_quotP (hP : 'hpoly[R]_n) :
  non_empty '[hP] = HPrim.non_empty hP.
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

Lemma is_included_in_hyperplane_quotP (hP : 'hpoly[R]_n) c d :
  is_included_in_hyperplane '[hP] c d = HPrim.is_included_in_hyperplane hP c d.
Proof.
apply/(sameP is_included_in_hyperplaneP)/(equivP HPrim.is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite quotE.
Qed.

Definition is_included_in (P Q : 'poly[R]_n) :=
  HPrim.is_included_in (hpoly P) (hpoly Q).

Lemma is_included_inP (P Q : 'poly[R]_n) :
  reflect {subset P <= Q } (is_included_in P Q).
Proof.
Admitted.

Lemma is_included_in_quotP (P Q : 'poly[R]_n) (hP hQ : 'hpoly[R]_n) :
  P = '[hP] -> Q = '[hQ] -> is_included_in P Q = HPrim.is_included_in hP hQ.
Proof.
Admitted.

Variable c : 'cV[R]_n.

Definition bounded (P : 'poly[R]_n) := HPrim.bounded c (hpoly P).
Definition unbounded (P : 'poly[R]_n) := HPrim.unbounded c (hpoly P).
Definition opt_value (P : 'poly[R]_n) := HPrim.opt_value c (hpoly P).

CoInductive lp_state (P : 'poly[R]_n) : option R -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state P None false false false
| Bounded (v : R) of (exists x, x \in P /\ '[c,x] = v) * (forall x, x \in P -> v <= '[c,x]) : lp_state P (Some v) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P None true false true.

Lemma lp_stateP P :
  lp_state P (opt_value P) (non_empty P) (bounded P) (unbounded P).
Proof.
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

Lemma lp_quotE (hP : 'hpoly[R]_n) :
  (non_empty '[hP] = HPrim.non_empty hP)
  * (bounded '[hP] = HPrim.bounded c hP)
  * (unbounded '[hP] = HPrim.unbounded c hP)
  * (opt_value '[hP] = HPrim.opt_value c hP).
Proof.
Admitted.

End Lift.

Arguments is_included_in_hyperplaneP [R n P c d].
Prenex Implicits is_included_in_hyperplaneP.

Section Base.

Variable R : realFieldType.
Variable n : nat.

Definition has_base (P : 'poly[R]_n) (base : 'hpoly[R]_n) :=
  [exists I , P == '['P^=(base; I)]].

Notation "[ P 'has' '\base' base ]" := (has_base P base).

Lemma has_baseP (P : 'poly[R]_n) (base : 'hpoly[R]_n) :
  reflect (exists I, P = '[ 'P^=(base; I) ]) [P has \base base].
Proof.
exact: exists_eqP.
Qed.

Lemma repr_hpolyEq (P : 'poly[R]_n) (hP : 'hpoly[R]_n) :
  P = '[hP] -> P = '['P^=(hP; set0)].
Proof.
case: hP => [m A b] ->.
apply/poly_eqP => x; rewrite hpolyEq_inE.
suff ->: [forall j in set0, (A *m x) j 0 == b j 0]
  by rewrite andbT.
by apply/forall_inP => j; rewrite inE.
Qed.

Lemma self_base (P : 'poly[R]_n) (hP : 'hpoly[R]_n) :
  P = '[hP] -> has_base P hP.
Proof.
move/repr_hpolyEq => P_eq.
by apply/has_baseP; exists set0.
Qed.

Lemma hpoly_base (P : 'poly[R]_n) :
  has_base P (hpoly P).
Proof.
by apply/self_base; rewrite hpolyK.
Qed.

Definition active (P : 'poly[R]_n) base :=
  let: 'P(A,b) as base := base return {set 'I_(#ineq base)} in
    [ set i: 'I_(#ineq base) | is_included_in_hyperplane P (row i A)^T (b i 0) ].

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).

Lemma active_inP (P : 'poly[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) i :
  reflect (forall x, x \in P -> (A *m x) i 0 = b i 0) (i \in { eq(P) on 'P(A,b) }).
Proof.
rewrite inE; apply/(equivP is_included_in_hyperplaneP).
by split; move => H x; move/(_ x): H; rewrite row_vdot.
Qed.

Arguments active_inP [P m A b].
Prenex Implicits active_inP.

Variable P : 'poly[R]_n.
Variable m : nat.
Variable A : 'M[R]_(m,n).
Variable b : 'cV[R]_m.
Hypothesis P_base : [ P has \base 'P(A,b) ].

Lemma activeP I :
  P = '['P^=(A, b; I)] -> I \subset { eq P }.
Proof.
move => P_eq.
apply/subsetP => i i_in_I; apply/active_inP => x.
rewrite P_eq mem_quotP.
by rewrite hpolyEq_inE => /andP [_ /forall_inP/(_ _ i_in_I)/eqP].
Qed.

Lemma hpoly_of_baseP :
  P = '[ 'P^=(A, b; { eq P }) ].
Proof.
move/has_baseP: P_base => [I P_eq_Pact].
move/activeP: (P_eq_Pact); rewrite {}P_eq_Pact.
set P' := 'P^=(A, b; I).
move => I_subset; apply/poly_eqP.
move => x; apply/idP/idP => [x_in |].
- have x_in_P': x \in '[P'] by rewrite mem_quotP.
  have x_in_Pab : x \in 'P(A, b)
    by rewrite hpolyEq_inE in x_in; move/andP: x_in => [?].
  rewrite hpolyEq_inE; rewrite x_in_Pab.
  by apply/forall_inP => i /active_inP/(_ _ x_in_P') ->.
- rewrite hpolyEq_inE => /andP [x_in_Pab /forall_inP act_eq].
  rewrite hpolyEq_inE; apply/andP; split; first by done.
  apply/forall_inP => i i_in_I.
  suff: i \in { eq '[P'] on 'P(A, b) } by exact: act_eq.
  + by move/subsetP/(_ _ i_in_I): I_subset.
Qed.

End Base.

Notation "{ 'eq' P 'on' base }" := (active P base).
Notation "{ 'eq' P }" := (active P _).
Notation "[ P 'has' '\base' base ]" := (has_base P base).

Section Face.

Variable R : realFieldType.
Variable n : nat.

Lemma inclusion_on_base (P Q : 'poly[R]_n) (base : 'hpoly[R]_n) :
  [P has \base base] -> [Q has \base base] ->
  reflect {subset P <= Q} ({ eq Q on base } \subset { eq P on base }).
Proof. (* TODO: should follow from the relint point of P and/or Q *)
Admitted.

Definition face_of (P : 'poly[R]_n) :=
  let base := hpoly P in
  [ pred Q : 'poly[R]_n |
    [ && non_empty Q, [ Q has \base base ]
                      & { eq P on base } \subset { eq Q on base } ]].

Lemma face_ofP (P Q : 'poly[R]_n) :
  (non_empty P) ->
    reflect (exists c, bounded c P /\ (forall x, (x \in P /\ Some '[c,x] = opt_value c P) <-> x \in Q))
            (Q \in face_of P).
Proof.
Admitted.
(*
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
Qed.*)

Arguments face_ofP [P Q].

Fact has_face_imp_non_empty P Q :
  Q \in (face_of P) -> non_empty P.
Proof.
move => /and3P [ /non_emptyP [x x_in_Q] Q_base ].
move/(inclusion_on_base Q_base (hpoly_base _)) => Q_subset_P.
by apply/non_emptyP; exists x; apply: Q_subset_P.
Qed.

Lemma face_baseP (P Q : 'poly[R]_n) :
  forall base, has_base P base ->
          reflect ([/\ non_empty Q, has_base Q base &
                                   { eq P on base } \subset { eq Q on base } ])
                  (Q \in (face_of P)).
Proof.
move => base P_base.
case: (boolP (non_empty P)) => [P_non_empty | P_empty].
- apply/(iffP (face_ofP P_non_empty)).



 P_base.
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



Lemma face_of_quotP (P Q : 'poly[R]_n) (base: 'hpoly[R]_n) :


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
