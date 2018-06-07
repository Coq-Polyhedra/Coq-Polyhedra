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

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module H := HPolyPrim.

Section Def.

Variable R : realFieldType.
Variable n : nat.

Notation hpolyEq_rel := (hpolyEq_equiv_rel R n).

Definition polyhedron := {eq_quot hpolyEq_rel}%qT.
Canonical polyhedron_eqType := [eqType of polyhedron].
Canonical polyhedron_choiceType := [choiceType of polyhedron].
Canonical polyhedron_quotType := [quotType of polyhedron].
Canonical polyhedron_eqQuotType := [eqQuotType hpolyEq_rel of polyhedron].

Notation "''<|' P |>" := (\pi_(polyhedron_eqQuotType)%qT P) (at level 0, format "''<|' P |>").

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

CoInductive hpoly_spec (P : polyhedron) : 'hpoly[R]_n -> Type :=
  HpolySpec Q of (P = ('<|Q|> )) : hpoly_spec P Q.

Lemma hpolyP (P : polyhedron) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma hpoly_eqP (P Q : 'hpolyEq[R]_n) :
  (P =i Q) <-> (P =e Q).
Proof.
apply: (rwP2 (b := (hpolyhedron_ext_eq P Q))).
- exact: hpolyhedron_ext_eqP.
- exact: eqmodP.
Qed.

Definition mem_polyhedron : polyhedron -> pred_class :=
  lift_fun1 polyhedron id.

Lemma mem_polyhedron_quotP x :
  { mono \pi_(polyhedron_eqQuotType)%qT : P / x \in P >-> (x \in mem_polyhedron P) }.
Proof. (* RK *)
unlock mem_polyhedron => P /=.
by case: (hpolyP '<| P |>) => Q /hpoly_eqP ?.
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
case: (hpolyP '<| P |>) => Q /hpoly_eqP P_eq_i_Q.
apply/idP/idP => [/non_emptyP [x ?] |/non_emptyP [x ?]];
  apply/non_emptyP; exists x; by [rewrite (P_eq_i_Q x) |rewrite -(P_eq_i_Q x)].
Qed.

Canonical non_empty_quot := Eval hnf in PiMono1 non_empty_quotP.
(* in this way, piE will rewrite non_empty '<|P|> into H.non_empty P *)

(*Section Ex.
Lemma foo (P P': 'hpolyEq[R]_n) :
  (P =e P') -> H.non_empty P = H.non_empty P'.
Proof.
move => H_PP'.
have ->: H.non_empty P = non_empty '<|P|> by rewrite piE.
have ->: H.non_empty P' = non_empty '<|P'|> by rewrite piE.
by rewrite H_PP'.
(* alternative:
suff <-: (non_empty '<|P|>) = H.non_empty P.
- by rewrite H_PP' piE.
- by rewrite piE.*)
Qed.
End Ex.*)

Variable c : 'cV[R]_n.

Definition bounded := lift_fun1 polyhedron (@H.bounded R n).

Fact bounded_quotP_aux (P Q : 'hpolyEq[R]_(n)) : (*RK*)
  (Q = P %[mod polyhedron_quotType])%qT -> H.bounded P c ->
    H.bounded Q c.
Proof.
case: P => [[mP AP bP] [[IP] ?]] /=.
case: Q => [[mQ AQ bQ] [[IQ] ?]] /=.
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

Lemma bounded_quotP :
  { mono \pi_(polyhedron_eqQuotType)%qT : P / H.bounded P c >-> bounded P c }.
Proof. (*RK*)
unlock bounded => P /=.
case: (hpolyP '<| P |>) => Q.
move => P_eq_e_Q.
apply/idP/idP => [Qbounded | Pbounded].
- exact: (bounded_quotP_aux P_eq_e_Q Qbounded).
- by apply: (bounded_quotP_aux _ Pbounded); symmetry.
Qed.

Canonical bounded_quot := Eval hnf in PiMono1 bounded_quotP.

Definition opt_value := lift_fun1 polyhedron (@H.opt_value R n).

Fact not_bounded_opt_point (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) : (*RK*)
    (~~ S.Simplex.bounded A b c) -> S.Simplex.opt_point A b c = 0.
Proof.
Admitted.

Lemma opt_value_quotP :
  {mono \pi_(polyhedron_eqQuotType)%qT : P / (H.opt_value P c) >-> (opt_value P c)}.
Proof.
unlock opt_value => P /=.
case: (hpolyP '<| P |>) => Q.
case: P => [[mP AP bP] [[IP] ?]] /=.
case: Q => [[mQ AQ bQ] [[IQ] ?]] /=.
set AQeq := col_mx AQ (- row_submx AQ IQ).
set bQeq := col_mx bQ (- row_submx bQ IQ).
set APeq := col_mx AP (- row_submx AP IP).
set bPeq := col_mx bP (- row_submx bP IP).
case: (boolP (S.Simplex.bounded AQeq bQeq c)) => [Q_bounded | Q_unbounded].
- move/hpoly_eqP => P_eq_i_Q.
  rewrite [LHS]/H.opt_value /hpolyhedron.opt_value.
  apply: (opt_value_is_optimal _).
  + rewrite P_eq_i_Q /=; unlock.
    by apply: S.Simplex.opt_point_is_feasible.
  + move => y y_in_P.
    rewrite P_eq_i_Q /= in y_in_P; unlock in y_in_P.
    rewrite /=; unlock.
    exact: ((proj2 (S.Simplex.boundedP _ _ _ Q_bounded)) _ y_in_P).
- move => P_eq_e_Q. symmetry in P_eq_e_Q.
  suff P_unbounded : ~~ S.Simplex.bounded APeq bPeq c
    by rewrite /=; unlock;
    rewrite /H.opt_value /hpolyhedron.opt_value /opt_point
      (not_bounded_opt_point Q_unbounded) (not_bounded_opt_point P_unbounded).
  move: Q_unbounded; apply: contra.
  move: (bounded_quotP_aux P_eq_e_Q).
  by rewrite /H.bounded /hpolyhedron.bounded /=; unlock.
Qed.

Canonical opt_value_quot := PiMono1 opt_value_quotP.

End Def.

Notation "''poly[' R ]_ n" := (polyhedron R n) (at level 0, format "''poly[' R ]_ n").
Notation "''poly_' n" := (polyhedron _ n) (at level 0, only parsing).
Notation "''<|' P |>" := (\pi_(polyhedron_eqQuotType _ _)%qT P) (at level 0, format "''<|' P |>").
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

Lemma face_of_quotP : {mono \pi : P F / (fun (P F : 'hpolyEq[R]_n) => hface_of P F) P F >-> face_of P F}%qT.
Admitted.
(*
Proof.
move => F P.
unlock face_of.
(*case/hpolyP : '<| P |> => Q H_PQ.
case/hpolyP : '<| F |> => G H_FG. *)
case: (boolP (non_empty '<| P |>)) => [P_non_empty | ].
- apply/idP/idP; last first.
  move: (P_non_empty); rewrite piE => P_non_empty'.
  move/(hface_ofP P_non_empty') => [c [bounded_c F_is_face_wrt_c]].
  move: P_non_empty; rewrite -{1}['<|P|>]hpolyK piE => P_non_empty.
  apply/(hface_ofP P_non_empty).
  exists c; split. rewrite -['<|P|>]hpolyK piE.

  first by rewrite -(bounded_quotP c H_PQ).
  move => x; rewrite -H_PQ -H_FG -(opt_value_quotP c H_PQ).
  exact: F_is_face_wrt_c.


         /(_ _).

case: (boolP (non_empty P')) => P'_non_empty.
- have P_non_empty: H.non_empty P by rewrite polyE in P'_non_empty.
  have hpolyP'_non_empty: H.non_empty (hpoly P').
  + by rewrite -non_empty_quotP reprK.
    (* TODO: this is surely not the right way to prove this *)
  unlock face_of.
  apply/idP/idP.


  have H: H.non_empty (hpoly '<| P |>).
  + by rewrite -['<| P |>]reprK polyE in P_non_empty.
    (* TODO: this is certainly not the right thing to do *)
  have H': H.non_empty P.
  +


  + move/(hface_ofP _ H) => [c [bounded_c F_is_face_wrt_c]].
    apply/(hface_ofP _ P_non_empty); exists c.
    split.
    rewrite polyE. -{1}[P]reprK.
    Check reprK.

    apply/hface_ofP; exists c.
move => x x_in_P.*)

Canonical face_of_quot := PiMono2 face_of_quotP.

Lemma face_ofP F P :
  reflect (exists c, bounded P c /\ forall x, (x \in P -> ('[c,x] = opt_value P c <-> x \in F)))
           (face_of F P).
Proof.
Admitted.


Lemma totoP (base: 'hpoly[R]_n) (P_NF : 'hpolyNF(base)) F :
  reflect (
      non_empty F
      /\  exists Q : 'hpolyNF(base),
        (\eq_set P_NF \subset \eq_set Q) /\ (F = '<| HPolyEqS Q |>)) (face_of '<| HPolyEqS P_NF |> F).
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
  HPolySpecNF (base: 'hpoly[R]_n) (Q : 'hpolyNF(base)) of (P = '<| HPolyEqS Q |>) : hpolyNF_spec P.

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
  have <-: '<| {| base := \base(P_Eq); hpolyeq_with_base := G' |} |> = G.
  + by rewrite H_G.
  by rewrite polyE /=.
- apply/existsP; exists G'; apply/andP; split; last by done.
  by apply/(subset_trans _ G'_superset).
Qed.

Fact foo'' : face_of P F -> face_of P G -> ({subset F <= G} <-> face_of G F).
Admitted.





End Face.
