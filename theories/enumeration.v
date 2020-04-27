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

Section FooBar.
Variable (K : fieldType) (vT : vectType K) .

Fixpoint mybasis (X res : seq vT) :=
  match X with
  | [::] => res
  | x :: X' => if (x \in <<X' ++ res >>)%VS then mybasis X' res
              else mybasis X' (x::res)
  end.

Definition mybasis_fset (X : {fset vT}) :=
  let supp := [seq x | x <- X] in
  [fset e in mybasis supp [::]]%fset.

Lemma mybasis_subseq_aux (X : seq vT):
  forall (res: seq vT) (x : vT), (x \in mybasis X res) -> x \in X ++ res.
Proof.
elim : X => //=.
move => a l Hind res x. case : (a \in <<l ++ res>>%VS) => x_in_myb.
- move : (Hind _ _ x_in_myb) => // x_in_cat.
  by rewrite in_cons; apply/orP; right.
- move : (Hind _ _ x_in_myb); rewrite in_cons !mem_cat in_cons.
  by case/or3P; move => ->; [apply orbC | | rewrite Bool.orb_assoc orbC].
Qed.

Lemma mybasis_subseq (X: seq vT):
  forall (x:vT), (x \in mybasis X [::]) -> x \in X.
Proof.
by move => x H; rewrite -(cats0 X); apply mybasis_subseq_aux.
Qed.

Lemma mybasis_free_aux (X : seq vT):
  forall res, free res -> free (mybasis X res).
Proof.
elim : X => //.
move => a l Hind res /=.
have disjcase : (a \in <<l++res>>%VS)\/(a \notin <<l++res>>%VS).
- apply/orP; case : (a \in <<l++res>>%VS) => //.
- case : disjcase.
  + move => ->; exact (Hind _).
  + move => a_free res_free.
    case : (a \in <<l++res>>%VS); apply Hind => //.
    rewrite free_cons; apply/andP; split => //.
    rewrite span_cat in a_free. move: a_free; apply contra => in_res.
    rewrite -[Y in Y \in _]add0r; apply memv_add => //.
    exact : mem0v.
Qed.

Lemma mybasis_free (X : seq vT) :
  free (mybasis X [::]).
Proof.
apply mybasis_free_aux. exact : nil_free.
Qed.

Lemma mybasis_span_aux (X: seq vT) :
  forall res, <<mybasis X res>>%VS == <<X++res>>%VS.
Proof.
elim : X => //=.
move => a l Hind res.
have disjcase : (a \in <<l++res>>%VS)\/(a \notin <<l++res>>%VS).
- by apply/orP; case : (a \in <<l++res>>%VS).
- case : disjcase.
  + move => a_in_span.
    rewrite a_in_span span_cons.
    Check addv_idPl.
    move/eqP : (Hind res) => ->; rewrite eq_sym.
    by apply /eqP/addv_idPr.
  + move => a_notin_span.
    have : (a \in <<l++res>>%VS) = false
    by move : a_notin_span; case : (a \in <<l++res>>%VS).
    move => ->. move/eqP : (Hind (a::res)) => ->.
    apply/eqP; apply /eq_span/perm_mem.
    rewrite -cat_rcons -cat_cons. apply perm_cat => //.
    apply/permPl. exact : perm_rcons.
Qed.

Lemma mybasis_span (X: seq vT) :
  <<mybasis X [::]>>%VS == <<X>>%VS.
Proof.
rewrite -[Y in _ == <<Y>>%VS](cats0 X). exact : mybasis_span_aux.
Qed.

Lemma mybasis_basis (X: seq vT):
  basis_of <<X>>%VS (mybasis X [::]).
Proof.
apply/andP; split.
- exact : mybasis_span.
- exact : mybasis_free.
Qed.

Lemma foo (X : {fset vT}) :
  exists2 Y, (Y `<=` X)%fset & basis_of <<X>>%VS Y.
Proof.
exists (mybasis_fset X).
Admitted.
End FooBar.

(*
  + rewrite -[in RHS]dim_eqQ.
    apply anti_leq; apply/andP; split; move: X_basis.
    *
  have uniq_X : uniq X by apply/free_uniq/(basis_free X_basis).
  by rewrite -[Y in _ == Y]size_X -uniq_size_uniq.
*)

Lemma vbasis_card (K : fieldType) (vT : vectType K) (U : {vspace vT}) (X : {fset vT}) :
  basis_of U X -> #|` X | = (\dim U)%N.
Proof.
move => X_basis.
apply/anti_leq/andP; split; move: X_basis.
+ by rewrite basisEdim => /andP [].
+ by rewrite basisEfree => /and3P [].
Qed.

Lemma vertex_basis x :
  x \in vertex_set P -> exists2 I, is_basis I & 'P^=(base; I) = [pt x].
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have Q_prop0: Q `>` [poly0] by rewrite dimN0 dimQ_eq1.
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- apply/anti_leq/andP; split; rewrite ?dim_span_active //.
  move: dimQ_eq1; rewrite dimN0_eq // => /succn_inj/eqP.
  by rewrite subn_eq0.
case: (foo {eq Q}) => I I_sub I_basis.
have I_sub_base: (I `<=` base)%fset. (* TODO: missing canonical in fsubset *)
- by apply/(fsubset_trans I_sub)/fsubset_subP.
have Q_base_I: 'P^=(base; I) = Q.
- rewrite polyEq_affine (vector.span_basis I_basis) -polyEq_affine.
  by rewrite [Q in RHS]repr_active //=.
exists (I%:fsub) => //; apply/and3P; split.
- by rewrite /= (vbasis_card I_basis) dim_eqQ.
- by rewrite (vector.span_basis I_basis) dim_eqQ.
- by rewrite Q_base_I; apply/andP; split.
Proof.

Lemma dim_basisD1 I i :
  (i \in (I : {fset _})) -> dim ('P^=(base; ((I `\ i)%fset)%:fsub)%:poly_base) = 2%N.
Admitted.

End Basis.
