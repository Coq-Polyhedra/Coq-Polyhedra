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

Implicit Type (I : {fsubset base}).

Definition is_basis I :=
  [&& (#|` I | == n)%N, (dim 'P^=(base; I) == 1%N) & ({eq P} `<=` I)%fset].

Lemma card_basis I :
  is_basis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.

Lemma basis_proper0 I :
  is_basis I -> 'P^=(base; I) `>` [poly0].
Admitted.

Lemma basis_feasible I :
  is_basis I -> 'P^=(base; I) `<=` P.
Admitted.

Lemma dim_span_basis I :
  (\dim <<I>> = n)%N.
Admitted.

Lemma basis_vertex I :
  is_basis I -> exists2 x, x \in vertex_set P & 'P^=(base; I) = [pt x].
Admitted.

Lemma vertex_basis x :
  x \in vertex_set P -> exists2 I, is_basis I & 'P^=(base; I) = [pt x].
Admitted.

(*
Lemma dim_basisD1 I i : i \in I -> dim 'P^=(base; (I `\ i)%fset) = 2%N.
  is_basis I -> (\dim <<I>> = n)%N.
Admitted.*)

End Basis.
