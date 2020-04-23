(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx.
Require Import hpolyhedron polyhedron barycenter poly_base.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

(* Goal :

On suppose qu'on est à la base admissible I, et on considère i \in I.

Pour tout j \notin I, on note
- c_ij := A_j * (col i A_I^{-1}) <- c_{ij} := '[j.1, d] pour j \in base `\` I, où
d est tel que 'P^=(base; I \` i) = [line d & _] et '[i.1, d] = 1
- r_j := A_j x^I - b_j (qui ne dépend pas de i)

Proposition
Soit I une base admissible, i \in I, et j \notin I. Alors J = I - i + j est une base admissible ssi les conditions suivantes sont satisfaites :
* c_ij != 0
* r_j > 0 ==> j \in arg max_(k notin I | c_ik < 0) (r_k / c_ik).

*)

Section Basis.
Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.
Context (P : {poly base}).
Hypothesis Pprop0 : P `>` [poly0].

Implicit Type (I : {fsubset base}).

Definition is_basis I :=
  [&& (#|` I | == n)%N, (\dim <<I>> == n)%N & ([poly0] `<` 'P^=(base; I) `<=` P)].

Lemma card_basis I :
  is_basis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.

Lemma basis_proper0 I :
  is_basis I -> 'P^=(base; I) `>` [poly0].
Proof.
by case/and3P => _ _ /andP [].
Qed.

Lemma basis_feasible I :
  is_basis I -> 'P^=(base; I) `<=` P.
Proof.
by case/and3P => _ _ /andP [].
Qed.

Lemma dim_span_basis I :
  is_basis I -> (\dim <<I>> = n)%N.
Proof.
by case/and3P => _ /eqP ->.
Qed.

Lemma span_basis I :
  is_basis I -> (<< I >> = << {eq 'P^=(base; I)%:poly_base} >>)%VS.
Proof.
case/and3P => _ /eqP dimI_eq_n /andP [PI_prop0 _].
apply/eqP; rewrite eqEdim; apply/andP; split.
- by apply/sub_span/fsubsetP/active_polyEq.
- by rewrite dimI_eq_n; apply/dim_span_active.
Qed.

Lemma dim_basis I :
  is_basis I -> dim 'P^=(base; I) = 1%N.
Proof.
move => I_basis.
rewrite dimN0_eq ?basis_proper0 //.
by rewrite -span_basis // dim_span_basis // subnn.
Qed.

Lemma basis_vertex I :
  is_basis I -> exists2 x, x \in vertex_set P & 'P^=(base; I) = [pt x].
Proof.
move => basis_I. case/eqP/dim1P: (dim_basis basis_I) => x ptPbaseI.
move : (basis_feasible basis_I).
rewrite ptPbaseI. move => ptx_subset_P; exists x => //.
rewrite in_vertex_setP -ptPbaseI face_setE.
- by rewrite ptPbaseI.
- by rewrite pvalP.
Qed.

Lemma vertexP (x : 'cV_n) :
  x \in vertex_set P ->
        exists Q : {poly base}, [/\ [pt x] = Q, dim Q = 1%N & (Q `<=` P)].
Proof.
case/imfsetP => Q /=; rewrite inE => /andP [].
case/face_setP => {}Q ? /eqP ? ->.
by exists Q; split; rewrite -?dim1_pt_ppick.
Qed.

Lemma foo (K : fieldType) (vT : vectType K) (X : seq vT) :
  exists2 Y, {subset Y <= X} & basis_of <<X>>%VS Y.
Admitted.

Lemma vertex_basis x :
  x \in vertex_set P -> exists2 I, is_basis I & 'P^=(base; I) = [pt x].
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- have : dim Q = 1%N => // dimQ_eq1bis.
  move : dimQ_eq1. rewrite dimN0_eq.
  rewrite -[X in _ = X]addn0 -addn1 [X in X = _]addnC => inj.
  move : (addnI inj) => H. rewrite -[X in X = _]addn0 -H subnKC => //=.
  by apply dim_span_active; rewrite dimN0 dimQ_eq1bis.
  by rewrite dimN0 dimQ_eq1bis.
case: (foo {eq Q}) => X X_sub X_basis.
set I := [fset x in base | x \in X]%fset%:fsub.
have I_eq_X : (I : {fset _}) =i X.
- rewrite /eq_mem => y; rewrite !inE /=. apply andb_idl => in_X.
move : (X_sub y in_X) => in_eqQ.
by move : (fsubset_incl in_eqQ).
have Q_base_I: 'P^=(base; I) = Q.
rewrite polyEq_affine.
move : (eq_span I_eq_X) => span_eq.
rewrite span_eq (vector.span_basis X_basis) -polyEq_affine.
have hyp: Q = 'P^=(base; {eq Q})%:poly_base.
by apply repr_active; rewrite dimN0 dimQ_eq1.
by rewrite [Y in _ = (pval Y)]hyp.
exists I; last first.
- by [].
- apply/and3P; split.
+ admit.
+ have X_basis2 : basis_of <<{eq Q}>> X. by [].
  move : X_basis; rewrite basisEfree dim_eqQ => /and3P [] freeX span_sub.
  move : X_basis2; rewrite basisEdim dim_eqQ => /andP [] span_sub2.
  move => leqn geqn.
  have : size X = n. apply anti_leq; apply/andP; split => //.
  move: (eq_span I_eq_X) => span_eq.
  move: (sub_span X_sub) => X_sub_eqQ.
  move => size_X; apply/eqP; apply anti_leq; apply /andP; split.
  rewrite span_eq -[Y in (_ <= Y)%N]size_X; exact: dim_span.
  by rewrite -[Y in (Y <= _)%N]dim_eqQ; apply dimv_leqif_eq; rewrite span_eq.
+ apply/andP; split; rewrite Q_base_I //.
  by rewrite dimN0 dimQ_eq1.
Proof.


  
Lemma dim_basisD1 I i :
  (i \in (I : {fset _})) -> dim ('P^=(base; ((I `\ i)%fset)%:fsub)%:poly_base) = 2%N.
Admitted.

End Basis.
