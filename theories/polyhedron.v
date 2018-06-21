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
Require Import extra_misc inner_product vector_order extra_matrix row_submx hpolyhedron.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "p1 =i p2"
  (at level 70, format "'[hv' p1 '/ '  =i  p2 ']'", no associativity).
Reserved Notation "''[' P ]" (at level 0, format "''[' P ]").

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section ExtensionalEqualityNF.
(* Instead of this, we should declare a structure such that
 * =i is equivalent to a decidable relation                 *)

Variable R : realFieldType.
Variable n : nat.

Import HPrim. (* we need to import HPrim to benefit from
               * the canonical structure on hpoly_ext_eq *)

Definition hpolyNF_ext_eq := [ rel P Q : 'hpolyNF[R]_n | hpoly_ext_eq P Q ].

Lemma hpolyNF_ext_eq_refl :
  reflexive hpolyNF_ext_eq.
Proof.
move => P /=; rewrite ?eqmodE.
exact: equiv_refl.
Qed.

Lemma hpolyNF_ext_eq_sym :
  symmetric hpolyNF_ext_eq.
Proof.
move => P Q /=; rewrite ?eqmodE.
exact: equiv_sym.
Qed.

Lemma hpolyNF_ext_eq_trans :
  transitive hpolyNF_ext_eq.
Proof.
move => P Q S /=; rewrite ?eqmodE.
exact: equiv_trans.
Qed.

Canonical hpolyNF_equiv_rel : equiv_rel 'hpolyNF[R]_n :=
  EquivRel hpolyNF_ext_eq hpolyNF_ext_eq_refl hpolyNF_ext_eq_sym hpolyNF_ext_eq_trans.

End ExtensionalEqualityNF.

Implicit Arguments hpolyNF_equiv_rel [R n].

Notation "P =e Q" := (hpolyNF_equiv_rel P Q).

Section Def.

Variable R : realFieldType.
Variable n : nat.

Definition polyhedron := {eq_quot (@hpolyNF_equiv_rel R n)}%qT.
Canonical polyhedron_eqType := [eqType of polyhedron].
Canonical polyhedron_choiceType := [choiceType of polyhedron].
Canonical polyhedron_eqQuotType := [eqQuotType (@hpolyNF_equiv_rel R n) of polyhedron].

Notation "''[' P ]" := (@Pi.f _ _ (Phant _) P).

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

CoInductive hpoly_spec (P : polyhedron) : 'hpolyNF[R]_n -> Type :=
  HpolySpec Q of (P = ('[ Q ])) : hpoly_spec P Q.

Lemma hpolyP (P : polyhedron) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Definition mem_polyhedron : polyhedron -> pred_class :=
  lift_fun1 polyhedron id.

Lemma mem_polyhedron_quotP x :
  { mono \pi_(polyhedron_eqQuotType)%qT : P / x \in P >-> (x \in mem_polyhedron P) }.
Proof. (* RK *)
unlock mem_polyhedron => P /=.
case: (hpolyP '[ P ]) => Q.
move/eqmodP.
/hpoly_eqP ?.
Qed.

Canonical mem_polyhedron_quot x :=
  Eval hnf in PiMono1 (mem_polyhedron_quotP x).
Canonical polyhedron_predType :=
  Eval hnf in @mkPredType 'cV[R]_n polyhedron mem_polyhedron.
Coercion mem_polyhedron : polyhedron >-> pred_class.

Definition non_empty := lift_fun1 polyhedron (@H.non_empty R n).

(*
Lemma non_empty_quotP (P Q: 'hpoly[R]_n) : P =i Q -> non_empty P = non_empty Q.
Admitted.
Lemma bounded_quotP (c: 'cV[R]_n) P Q : P =i Q -> bounded P c = bounded Q c.
Admitted.
Lemma opt_value_quotP (c: 'cV[R]_n) P Q : P =i Q -> opt_value P c = opt_value Q c.
Admitted.*)

Lemma non_empty_quotP :
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.non_empty P >-> non_empty P }.
Proof. (*RK*)
unlock non_empty => P /=.
case: (hpolyP '[ P ]) => Q /hpoly_eqP P_eq_i_Q.
apply/idP/idP => /non_emptyP [x H];
  apply/non_emptyP; exists x; by rewrite ?P_eq_i_Q in H *.
Qed.

Canonical non_empty_quot := Eval hnf in PiMono1 non_empty_quotP.
(* in this way, piE will rewrite non_empty '[P] into H.non_empty P *)

Implicit Type c : 'cV[R]_n.

Definition bounded c := lift_fun1 polyhedron ((@H.bounded _ _)^~ c). (* TODO: IMPLICIT ARGUMENTS (or change the argument order in hpolyhedron?) !!! *)
Definition unbounded c := lift_fun1 polyhedron ((@H.unbounded _ _)^~ c).
Definition opt_point c := lift_fun1 polyhedron ((@H.opt_point _ _)^~ c).
Definition opt_value c := lift_fun1 polyhedron ((@H.opt_value _ _)^~ c).

CoInductive lp_state (P : polyhedron) c : option ('cV[R]_n) -> bool -> bool -> bool -> Type :=
| Empty of P =i pred0 : lp_state P c None false false false
| Bounded (z : 'cV_n) of (z \in P) * (forall x, x \in P -> '[c, z] <= '[c,x]) : lp_state P c (Some z) true true false
| Unbounded of (forall K, exists x, x \in P /\ '[c,x] < K) : lp_state P c None true false true.

Lemma lp_stateP P c :
  lp_state P c (opt_point c P) (non_empty P) (bounded c P) (unbounded c P).
Proof.
Admitted.

(*
Fact bounded_quotP_aux (P Q : 'hpolyEq[R]_(n)) : (*RK*)
  (Q =e P) -> H.bounded P c -> H.bounded Q c. (* TODO: why Q =e P is not displayed like this? *)
Proof.
case:

  case: P => [P0 ].

  [mP AP bP] [[IP] nfP]].
case: Q => [[mQ AQ bQ] [[IQ] nfQ]].
move/hpoly_eqP => P_eq_i_Q.
case: (H.lp_stateP .

set APeq := col_mx AP (- (row_submx AP IP)).
set bPeq := col_mx bP (- row_submx bP IP).
move/hpoly_eqP => P_eq_i_Q.
rewrite /= in P_eq_i_Q; unlock in P_eq_i_Q.
rewrite /=; unlock.
move/boundedP => Pbounded.
rewrite /H.bounded /hpolyhedron.bounded /=; unlock.
apply/(S.Simplex.boundedP_lower_bound c).
- apply/S.Simplex.feasibleP.
  move/proj1: Pbounded => [x [x_in_P _]].
  exists x.
  by rewrite P_eq_i_Q.
- exists (opt_value 'P(APeq, bPeq) c).
  move => x x_in_P.
  rewrite P_eq_i_Q in x_in_P.
  exact: ((proj2 Pbounded) x x_in_P).
Qed.
 *)

Variable c: 'cV[R]_n.

Lemma bounded_quotP :
  (* TODO: we should prove all the quotP statements in a row,
           using the (h)lp_stateP statement *)
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.bounded P c >-> bounded c P }.
Proof. (*RK*)
unlock bounded => P /=.
case: (hpolyP '[ P ]) => Q.
move => /hpoly_eqP P_eq_Q.
case: (hlp_stateP P c); case: (hlp_stateP Q c); try by done.
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

Lemma all_in_one_quotP :
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.bounded P c >-> bounded c P } *
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.unbounded P c >-> unbounded c P } *
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.opt_value P c >-> opt_value c P }.
Proof. (*RK*)
split. split.
- unlock bounded => P /=.
  case: (hpolyP '[ P ]) => Q /hpoly_eqP P_eq_Q.
  case: (hlp_stateP P c); case: (hlp_stateP Q c); try by done.
  + move => z [z_in_Q _] /(_ z).
    by rewrite P_eq_Q z_in_Q inE.
  + move => Q_empty z [z_in_Q _]; move/(_ z): Q_empty.
    by rewrite -P_eq_Q z_in_Q inE.
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
- unlock unbounded => P /=.
  case: (hpolyP '[ P ]) => Q /hpoly_eqP P_eq_Q.
  case: (hlp_stateP P c); case: (hlp_stateP Q c); try by done.
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
- unlock opt_value => P /=.
  case: (hpolyP '[ P ]) => Q /hpoly_eqP P_eq_Q.
  case: (hlp_stateP P c); case: (hlp_stateP Q c); try by done.
  + move => Q_empty P_empty.
    suff Q_not_bounded: (H.bounded Q c) = false.
      suff P_not_bounded: (H.bounded P c) = false
        by rewrite /H.opt_value /omap /obind /oapp /H.opt_point Q_not_bounded P_not_bounded.
      apply: negbTE; apply: contraT.
      move/negPn/boundedP => [x [x_in_P _]].
      by rewrite (P_empty x) inE in x_in_P.
    apply: negbTE; apply: contraT.
    move/negPn/boundedP => [x [x_in_Q _]].
    by rewrite (Q_empty x) inE in x_in_Q.
  + move => z [z_in_Q _] /(_ z).
    by rewrite (P_eq_Q z) z_in_Q inE.
  + move/(_ 0) => [z [z_in_Q _]] /(_ z).
    by rewrite (P_eq_Q z) z_in_Q inE.
  + move => Q_empty z [z_in_P _].
    by rewrite (P_eq_Q z) (Q_empty z) inE in z_in_P.
  + move => z [z_in_Q z_opt_in_Q].
    move => y [y_in_P y_opt_in_P].
    rewrite (opt_value_is_optimal z_in_Q z_opt_in_Q).
    suff z_opt_in_P : forall x : 'cV_n, x \in P -> '[ c, z] <= '[ c, x].
      rewrite -(P_eq_Q z) in z_in_Q.
      by rewrite (opt_value_is_optimal z_in_Q z_opt_in_P).
    move => x.
    rewrite (P_eq_Q x).
    exact: (z_opt_in_Q x).
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
  + move => Q_unbounded P_unbounded.
    have Q_non_empty: H.non_empty Q.
      move/(_ 0): Q_unbounded => [x [x_in_Q _]].
      by apply/non_emptyP; exists x.
    have P_non_empty: H.non_empty P.
      move/(_ 0): P_unbounded => [x [x_in_P _]].
      by apply/non_emptyP; exists x.
    suff Q_not_bounded: (H.bounded Q c) = false.
      suff P_not_bounded: (H.bounded P c) = false
        by rewrite /H.opt_value /omap /obind /oapp /H.opt_point Q_not_bounded P_not_bounded.
      apply: negbTE; rewrite -unbounded_is_not_bounded //.
      by apply/unboundedP.
    apply: negbTE; rewrite -unbounded_is_not_bounded //.
    by apply/unboundedP.
Qed.

Canonical bounded_quot := Eval hnf in PiMono1 bounded_quotP.

Canonical opt_value_quot := PiMono1 opt_value_quotP.

End Def.

Notation "''poly[' R ]_ n" := (polyhedron R n) (at level 0, format "''poly[' R ]_ n").
Notation "''poly_' n" := (polyhedron _ n) (at level 0, only parsing).
Notation "''[' P ]" := (\pi_(polyhedron_eqQuotType _ _)%qT P) (at level 0, format "''[' P ]").
Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

Section Face.

Variable R : realFieldType.
Variable n : nat.

(*Fact foo (P: 'poly[R]_n) x : x \in P.
case/hpolyP: {1}P => Q ->.
rewrite polyE.
case: Q => m A b.
rewrite inE.*)

Definition face_of :=
  lift_fun2 'poly[R]_n (fun F P => hface_of F P).

(*
Lemma is_face_ofP (F P : 'polyh[R]_n) :
  (non_empty P) ->
    reflect (exists c, bounded P c /\ (forall x, x \in F <-> (x \in P /\ '[c,x] = opt_value P c)))
          (face_of F P).
Proof.
unlock feasible.
move => Hfeas.
apply: (iffP idP).
- unlock is_face_of.
  move/(is_hface_ofP (repr F) Hfeas) => [c [Hbounded H]].
  exists c; split.
  + by rewrite -[P]reprK piE.
  + move => x.
    by rewrite -[F]reprK -[P]reprK !piE.
- move => [c [Hbounded H]].
  unlock is_face_of.
  apply/(is_hface_ofP (repr F) Hfeas).
  exists c; split.
  + by rewrite -[P]reprK piE in Hbounded.
  + move => x.
    by move/(_ x): H; rewrite -{1}[F]reprK -{1 2}[P]reprK !piE.
Qed.*)


Fact face_of_quotP_aux (P F P' F' : 'hpolyEq[R]_n) :
  H.non_empty P -> (P = P' %[mod polyhedron_eqQuotType R n])%qT ->
    (F = F' %[mod polyhedron_eqQuotType R n])%qT ->
      (hface_of P) F -> (hface_of P') F'.
Proof.
Admitted.
(*move => P_non_empty P_eq_P' F_eq_F'.
have P'_non_empty: H.non_empty P'
  by rewrite -(non_empty_quotP P') -P_eq_P' (non_empty_quotP P).
move/((hface_ofP P_non_empty) F) => [c [bounded_c F_is_face_wrt_c]].
apply/(hface_ofP P'_non_empty).
exists c; split.
- move: (bounded_quotP c P') => bounded_quotP_c_P'.
  (* RK: I believe that this could we avoided if we do not   *)
  rewrite /H.bounded in bounded_quotP_c_P'.         (* define H.bounded and work only with hpolyhedron.bounded *)
  by rewrite -bounded_quotP_c_P' -P_eq_P' (bounded_quotP c P) /H.bounded.
- move => x x_in_P' /=.
  rewrite -(mem_polyhedron_quotP x P') -P_eq_P' (mem_polyhedron_quotP x P) in x_in_P'.
  move: (F_is_face_wrt_c x x_in_P').
  rewrite -(mem_polyhedron_quotP x F) F_eq_F' (mem_polyhedron_quotP x F').
  move: (opt_value_quotP c P) => opt_value_quotP_c_P.                         (* RK: The same commet as  *)
  rewrite /H.opt_value P_eq_P' (opt_value_quotP c P') in opt_value_quotP_c_P. (* above but for opt_value *)
  by rewrite -(opt_value_quotP_c_P) /H.opt_value.
Qed.*)

Lemma face_of_quotP : {mono \pi : P F / (fun (P F : 'hpolyEq[R]_n) => hface_of P F) P F >-> face_of P F}%qT.
Proof. (* RK: to be improved? *)
unlock face_of => P F.
case/hpolyP : '[ P ] => Q H_PQ.
case/hpolyP : '[ F ] => G H_FG.
case: (boolP (non_empty '[ P ])) => [P_non_empty | P_empty ].
- have P_eq_hpolyP: (P =e (hpoly '[ P ]))
    by rewrite -{1}['[P]]hpolyK.
  have F_eq_hpolyF: (F =e (hpoly '[ F] ))
    by rewrite -{1}['[F]]hpolyK.
  apply/idP/idP.
  + move: (P_non_empty); rewrite -{1}['[P]]hpolyK piE => hpolyP_non_empty.
    symmetry in P_eq_hpolyP.
    symmetry in F_eq_hpolyF.
    exact: face_of_quotP_aux.
  + rewrite (non_empty_quotP P) in P_non_empty.
    exact: face_of_quotP_aux.
- apply/idP/idP => [F_face_of_P | F_face_of_P].
  + have P_non_empty : non_empty (\pi_(polyhedron_eqQuotType R n)%qT P)
      by unlock non_empty; rewrite /H.non_empty; apply: (has_face_imp_non_empty F_face_of_P).
    move/andP: (conj P_non_empty P_empty).
    by rewrite andbN.
  + have P_non_empty : non_empty (\pi_(polyhedron_eqQuotType R n)%qT P)
      by rewrite (non_empty_quotP P); apply: (has_face_imp_non_empty F_face_of_P).
    move/andP: (conj P_non_empty P_empty).
    by rewrite andbN.
Qed.

Canonical face_of_quot := PiMono2 face_of_quotP.

Lemma face_ofP F P :
  reflect (exists c, bounded P c /\ forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in F)))
           (face_of F P).
Proof.
Admitted.

Lemma totoP (base : 'hpoly[R]_n) (P_NF : 'hpolyNF(base)) F :
  reflect (
      non_empty F
      /\  exists Q : 'hpolyNF(base),
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
Qed.

(*CoInductive hpolyNF_spec (P : 'poly[R]_n) : Type :=
  HPolySpecNF (base: 'hpoly[R]_n) (Q : 'hpolyNF(base)) of (P = '[ HPolyEqS Q ]) : hpolyNF_spec P.

Fact hpolyNFP (P : 'poly[R]_n) :
  hpolyNF_spec P.
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
case/hpolyP: P => [P_Eq H_P].
case/hpolyP: F => [F_Eq H_F].
case/hpolyP: G => [G_Eq H_G].
rewrite H_P H_F H_G.
rewrite polyE /= => /andP [F_non_empty].
move/existsP => [F' /andP [F'_superset /eqP H_F']].
rewrite H_F' polyE /= => /andP [G_non_empty].
move/existsP => [G' /andP [G'_superset /eqP H_G']].
rewrite H_G' polyE /=.
apply/andP; split.
- have: non_empty G.
  + by rewrite H_G polyE.
  have <-: '[ {| base := \base(P_Eq); hpolyeq_with_base := G' |} ] = G.
  + by rewrite H_G.
  by rewrite polyE /=.
- apply/existsP; exists G'; apply/andP; split; last by done.
  by apply/(subset_trans _ G'_superset).
Qed.

Fact foo'' : face_of P F -> face_of P G -> ({subset F <= G} <-> face_of G F).
Admitted.



End Face.
