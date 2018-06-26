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

Reserved Notation "P =e Q"
         (at level 70, format "'[hv' P '/ '  =e  Q ']'", no associativity).
Reserved Notation "P ==e Q"
         (at level 70, format "'[hv' P '/ '  ==e  Q ']'", no associativity).
Reserved Notation "''poly[' R ]_ n" (at level 8, n at level 2, format "''poly[' R ]_ n").
Reserved Notation "''poly_' n" (at level 8, n at level 2).
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

Definition hpolyNF_ext_eq := [ rel P Q : 'hpolyNF[R]_n | P ==i Q :> 'hpoly[R]_n ].

Lemma hpolyNF_ext_eq_refl :
  reflexive hpolyNF_ext_eq.
Proof.
by move => ? /=.
Qed.

Lemma hpolyNF_ext_eq_sym :
  symmetric hpolyNF_ext_eq.
Proof.
move => ? ? /=; exact: ext_eq_sym.
Qed.

Lemma hpolyNF_ext_eq_trans :
  transitive hpolyNF_ext_eq.
Proof.
move => P Q S /=; exact: ext_eq_trans.
Qed.

Canonical hpolyNF_equiv_rel : equiv_rel 'hpolyNF[R]_n :=
  EquivRel hpolyNF_ext_eq hpolyNF_ext_eq_refl hpolyNF_ext_eq_sym hpolyNF_ext_eq_trans.

End ExtensionalEqualityNF.

Arguments hpolyNF_equiv_rel [R n].

Definition poly R n := {eq_quot (@hpolyNF_equiv_rel R n)}%qT.

Notation "''poly[' R ]_ n" := (@poly R n).
Notation "''poly_' n" := ('poly[_]_n).
Notation "''[' P ]" := (\pi_('poly_ _) P)%qT.
Notation "\poly" := (\pi_('poly_ _))%qT.
Notation "P =e Q" := (\poly P = \poly Q).
Notation "P ==e Q" := (\poly P == \poly Q).

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

Definition mem_polyhedron (R : realFieldType) (n : nat) : 'poly[R]_n -> pred_class :=
  lift_fun1 'poly[R]_n id.
Coercion mem_polyhedron : poly >-> pred_class.

Section Lift.

Variable R : realFieldType.
Variable n : nat.

CoInductive hpoly_spec (P : 'poly[R]_n) : 'hpolyNF[R]_n -> Type :=
  HpolySpec Q of (P = '[ Q ]) : hpoly_spec P Q.

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma ext_eqquotP (P Q: 'hpolyNF[R]_n) : (P =i Q) <-> (P =e Q).
Proof.
by split => [? |]; [ apply/eqquotP/ext_eqP | move/eqquotP/ext_eqP].
Qed.

Lemma mem_polyhedron_quotP (x: 'cV[R]_n) :
  { mono \poly : P / x \in P >-> (x \in mem_polyhedron P) }.
Proof.
unlock mem_polyhedron => P /=.
by case: (hpolyP '[ P ]) => Q /ext_eqquotP.
Qed.

Canonical mem_polyhedron_quot x :=
  Eval hnf in PiMono1 (mem_polyhedron_quotP x).
Canonical polyhedron_predType :=
  Eval hnf in @mkPredType 'cV[R]_n 'poly[R]_n (@mem_polyhedron R n).

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
Proof.
Admitted.

Variable c: 'cV[R]_n.

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

Lemma opt_value_quotP :
  { mono \poly : P / HPrim.opt_value c P >-> opt_value c P }.
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

Canonical bounded_quot := Eval hnf in PiMono1 bounded_quotP.
Canonical unbounded_quot := Eval hnf in PiMono1 unbounded_quotP.
Canonical opt_value_quot := Eval hnf in PiMono1 opt_value_quotP.

End Lift.

Section Face.

Variable R : realFieldType.
Variable n : nat.

Definition face_of :=
  lift_fun2 'poly[R]_n (fun F P => hpolyEq_face_of P F). (* RK *)

Lemma face_ofP (F P : 'poly[R]_n) :
  (non_empty P) ->
    reflect (exists c, bounded c P /\ (forall x, (x \in P /\ Some '[c,x] = opt_value c P) <-> x \in F))
          (face_of F P). (* RK *)
Proof.
unlock non_empty => non_empty_P /=.
apply: (iffP idP).
- unlock face_of.
  move/(hpolyEq_face_ofP (hpoly F) non_empty_P) => [c [? ?]].
  exists c; split.
  + by rewrite -[P]reprK piE.
  + move => x.
    by rewrite -[F]reprK -[P]reprK !piE.
- move => [c [bounded_c_P H]].
  unlock face_of.
  apply/(hpolyEq_face_ofP (repr F) non_empty_P).
  exists c; split.
  + by rewrite -[P]reprK piE in bounded_c_P.
  + move => x.
    by move/(_ x): H; rewrite -{1}[F]reprK -{1 2}[P]reprK !piE.
Qed.

Fact face_of_quotP_aux (P F P' F' : 'hpolyEq[R]_n) :
  HPrim.non_empty P -> (P = P' %[mod polyhedron_eqQuotType R n])%qT ->
    (F = F' %[mod polyhedron_eqQuotType R n])%qT ->
      (hpolyEq_face_of P) F -> (hpolyEq_face_of P') F'.
Proof.
Admitted.
(*move => P_non_empty P_eq_P' F_eq_F'.
have P'_non_empty: HPrim.non_empty P'
  by rewrite -(non_empty_quotP P') -P_eq_P' (non_empty_quotP P).
move/((hface_ofP P_non_empty) F) => [c [bounded_c F_is_face_wrt_c]].
apply/(hface_ofP P'_non_empty).
exists c; split.
- move: (bounded_quotP c P') => bounded_quotP_c_P'.
  (* RK: I believe that this could we avoided if we do not   *)
  rewrite /HPrim.bounded in bounded_quotP_c_P'.         (* define HPrim.bounded and work only with hpolyhedron.bounded *)
  by rewrite -bounded_quotP_c_P' -P_eq_P' (bounded_quotP c P) /HPrim.bounded.
- move => x x_in_P' /=.
  rewrite -(mem_polyhedron_quotP x P') -P_eq_P' (mem_polyhedron_quotP x P) in x_in_P'.
  move: (F_is_face_wrt_c x x_in_P').
  rewrite -(mem_polyhedron_quotP x F) F_eq_F' (mem_polyhedron_quotP x F').
  move: (opt_value_quotP c P) => opt_value_quotP_c_P.                         (* RK: The same commet as  *)
  rewrite /HPrim.opt_value P_eq_P' (opt_value_quotP c P') in opt_value_quotP_c_P. (* above but for opt_value *)
  by rewrite -(opt_value_quotP_c_P) /HPrim.opt_value.
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
      by unlock non_empty; rewrite /HPrim.non_empty; apply: (has_face_imp_non_empty F_face_of_P).
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
