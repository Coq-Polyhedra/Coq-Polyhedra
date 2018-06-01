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

Notation hpoly_rel := (hpoly_equiv_rel R n).

Definition polyhedron := {eq_quot hpoly_rel}%qT.
Canonical polyhedron_eqType := [eqType of polyhedron].
Canonical polyhedron_choiceType := [choiceType of polyhedron].
Canonical polyhedron_quotType := [quotType of polyhedron].
Canonical polyhedron_eqQuotType := [eqQuotType hpoly_rel of polyhedron].

Notation "''<|' P |>" := (\pi_(polyhedron_quotType)%qT P) (at level 0, format "''<|' P |>").

Notation polyE := piE.
Notation hpoly := repr.
Notation hpolyK := reprK.

CoInductive hpoly_spec (P : polyhedron) : 'hpoly_n -> Type :=
  HpolySpec Q of (P = ('<|Q|> )) : hpoly_spec P Q.

Lemma hpolyP (P : polyhedron) :
  hpoly_spec P (hpoly P).
Proof.
by constructor; rewrite hpolyK.
Qed.

Lemma hpoly_eqP (P Q : 'hpoly[R]_n) :
  (P =i Q) <-> (P =e Q).
Proof.
apply: (rwP2 (b := (hpolyhedron_ext_eq P Q))).
- exact: hpolyhedron_ext_eqP.
- exact: eqmodP.
Qed.

Definition mem_polyhedron : polyhedron -> pred_class :=
  lift_fun1 polyhedron id.

Lemma mem_polyhedron_quotP x : {mono \pi : P / x \in P >-> x \in mem_polyhedron P}%qT.
Proof.
unlock mem_polyhedron => P /=.
case: (hpolyP '<| P |>) => Q.
by move/hpoly_eqP.
Qed.

Canonical mem_polyhedron_quot x := Eval hnf in PiMono1 (mem_polyhedron_quotP x).
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
  { mono \pi : P / H.non_empty P >-> non_empty P }%qT.
Proof.
move => P.
Admitted.

Canonical non_empty_quot := Eval hnf in PiMono1 non_empty_quotP.
(* in this way, piE will rewrite non_empty '<|P|> into H.non_empty P *)

Section Ex.
Lemma foo (P P': 'hpoly[R]_n) :
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
End Ex.

Variable c: 'cV[R]_n.

Definition bounded := lift_fun1 polyhedron (@H.bounded R n).

Lemma bounded_quotP : { mono \pi : P / H.bounded P c >-> bounded P c }%qT.
Admitted.

Canonical bounded_quot := Eval hnf in PiMono1 bounded_quotP.

Definition opt_value := lift_fun1 polyhedron (@H.opt_value R n).

Lemma opt_value_quotP : {mono \pi : P / (H.opt_value P c) >-> (opt_value P c)}%qT.
Admitted.

Canonical opt_value_quot := PiMono1 opt_value_quotP.

End Def.

Notation "''poly[' R ]_ n" := (polyhedron R n) (at level 0, format "''poly[' R ]_ n").
Notation "''poly_' n" := (polyhedron _ n) (at level 0, only parsing).
Notation "''<|' P |>" := (\pi_('poly_ _)%qT P) (at level 0, format "''<|' P |>").
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
  lift_fun2 'poly[R]_n (fun F P => F \is a hface_of P).

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

Lemma face_of_quotP : {mono \pi : F P / F \is a hface_of P >-> face_of F P}%qT.
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
move => x x_in_P.


End Face.
