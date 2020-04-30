(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssrnum ssralg zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx xvector.
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

Section PBasis.
Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.
Context (P : {poly base}).
Hypothesis Pprop0 : P `>` [poly0].

Implicit Type (I : {fsubset base}).

Definition is_pbasis I :=
  [&& (#|` I | == n)%N, (\dim <<I>> == n)%N & ([poly0] `<` 'P^=(base; I) `<=` P)].

Lemma card_pbasis I :
  is_pbasis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.

Lemma pbasis_proper0 I :
  is_pbasis I -> 'P^=(base; I) `>` [poly0].
Proof.
by case/and3P => _ _ /andP [].
Qed.

Lemma pbasis_feasible I :
  is_pbasis I -> 'P^=(base; I) `<=` P.
Proof.
by case/and3P => _ _ /andP [].
Qed.

Lemma dim_span_pbasis I :
  is_pbasis I -> (\dim <<I>> = n)%N.
Proof.
by case/and3P => _ /eqP ->.
Qed.

Lemma span_pbasis I :
  is_pbasis I -> (<< I >> = << {eq 'P^=(base; I)%:poly_base} >>)%VS.
Proof.
case/and3P => _ /eqP dimI_eq_n /andP [PI_prop0 _].
apply/eqP; rewrite eqEdim; apply/andP; split.
- by apply/sub_span/fsubsetP/active_polyEq.
- by rewrite dimI_eq_n; apply/dim_span_active.
Qed.

Lemma dim_pbasis I :
  is_pbasis I -> dim 'P^=(base; I) = 1%N.
Proof.
move => I_pbasis.
rewrite dimN0_eq ?pbasis_proper0 //.
by rewrite -span_pbasis // dim_span_pbasis // subnn.
Qed.

Lemma pbasis_vertex I :
  is_pbasis I -> exists2 x, x \in vertex_set P & 'P^=(base; I) = [pt x].
Proof.
move => pbasis_I. case/eqP/dim1P: (dim_pbasis pbasis_I) => x ptPbaseI.
move : (pbasis_feasible pbasis_I).
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

Lemma vertex_pbasis x :
  x \in vertex_set P -> exists2 I, is_pbasis I & 'P^=(base; I) = [pt x].
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have Q_prop0: Q `>` [poly0] by rewrite dimN0 dimQ_eq1.
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- apply/anti_leq/andP; split; rewrite ?dim_span_active //.
  move: dimQ_eq1; rewrite dimN0_eq // => /succn_inj/eqP.
  by rewrite subn_eq0.
case: (ebasisP {eq Q}) => I I_sub I_basis.
have I_sub_base: (I `<=` base)%fset. (* TODO: missing canonical in fsubset *)
- by apply/(fsubset_trans I_sub)/fsubset_subP.
have Q_base_I: 'P^=(base; I) = Q.
- rewrite polyEq_affine (vector.span_basis I_basis) -polyEq_affine.
  by rewrite [Q in RHS]repr_active //=.
exists (I%:fsub) => //; apply/and3P; split.
Search _ card_basis.
- by rewrite (card_basis I_basis) dim_eqQ.
- by rewrite (vector.span_basis I_basis) dim_eqQ.
- by rewrite Q_base_I; apply/andP; split.
Qed.

Lemma dim_pbasisD1 I i :
  is_pbasis I -> (i \in (I : {fset _}))
  -> dim ('P^=(base; ((I `\ i)%fset)%:fsub)%:poly_base) = 2%N.
Proof.
move => I_pbasis i_in_I /=.
Check polyEq_affine.

End PBasis.
