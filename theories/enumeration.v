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
Local Open Scope fset_scope.
Import GRing.Theory Num.Theory.

(* Goal :

On suppose qu'on est à la base admissible I, et on considère i \in I.

Pour tout j \notin I, on note
- c_ij := A_j * (col i A_I^{-1}) <- c_{ij} := '[j.1, d] pour j \in base `\` I, où
d est tel que affine << I \` i >> = [line d & _] et '[i.1, d] = 1
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

Lemma span_polyEq (I J : base_t) :
  (<<I>> = <<J>>)%VS -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by rewrite !polyEq_affine => ->.
Qed.

Lemma basis_polyEq (I J : base_t) :
  basis_of <<I>>%VS J -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by move/span_basis/span_polyEq.
Qed.

Definition is_pbasis I :=
   [&& (#|` I | == n)%N, (dim (affine <<I>>%VS) == 1)%N & (affine <<I>>%VS `<=` P)%PH].


(*Definition is_pbasis I :=
  [&& (#|` I | == n)%N, (\dim <<I>> == n)%N & ([poly0] `<` 'P^=(base; I) `<=` P)].*)

Lemma card_pbasis I :
  is_pbasis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.


(*Definition point_of_pbasis I := ppick (affine <<I>>%VS).
Lemma point_of_pbasisP I :
  is_pbasis I -> affine <<I>>%VS = [pt (point_of_pbasis I)].*)


Lemma pbasis_proper0 I :
  is_pbasis I -> affine <<I>> `>` [poly0]. (*affine <<I>>%VS `>` .*)
Proof.
by case/and3P => _ /eqP dimI _; rewrite dimN0 dimI.
Qed.

Lemma pbasis_feasible I :
  is_pbasis I -> (affine <<I>> `<=` P)%PH.
Proof.
by case/and3P.
Qed.

Lemma dim_affine_pbasis I :
  is_pbasis I -> (dim (affine <<I>>) = 1)%N.
Proof.
by case/and3P => _ /eqP.
Qed.


Lemma pbasis_active I :
  is_pbasis I -> 'P^=(base; I) = affine <<I>>.
Proof.
move => pbasisI; rewrite polyEq_affine.
apply/meet_idPr/(le_trans (pbasis_feasible _)) => //.
exact: poly_base_subset.
Qed.

Lemma pbasis_free I :
  is_pbasis I -> free I.
Proof.
move => pbasis_I.
move: (dim_affine_pbasis pbasis_I).
rewrite dimN0_eq; [rewrite active_affine /=| exact: (pbasis_proper0 pbasis_I)].
move/eq_add_S/eqP; rewrite subn_eq0 => dimI_sub.
apply/(@basis_free _ _ <<I>>%VS); rewrite basisEdim; apply/andP; split => //.
by move: (card_pbasis pbasis_I) => ->.
Qed.

(*Lemma span_pbasis I :
  is_pbasis I -> (<< I >> = << {eq 'P^=(base; I)%:poly_base} >>)%VS.
Proof.
Admitted.*)

Lemma pbasis_vertex I :
  is_pbasis I -> exists2 x, x \in vertex_set P & affine <<I>> = [pt x].
Proof.
move => pbasis_I.
case/eqP/dim1P: (dim_affine_pbasis pbasis_I) => x ptPbaseI.
move : (pbasis_feasible pbasis_I).
rewrite ptPbaseI; move => ptx_subset_P; exists x => //.
rewrite in_vertex_setP -ptPbaseI face_setE.
- by rewrite ptPbaseI.
- by rewrite -pbasis_active // pvalP.
Qed.

Lemma vertexP (x : 'cV_n) :
  x \in vertex_set P ->
        exists Q : {poly base}, [/\ [pt x] = Q, dim Q = 1%N & (Q `<=` P :> 'poly[R]_n)].
Proof.
case/imfsetP => Q /=; rewrite inE => /andP [].
case/face_setP => {}Q ? _ /eqP ? ->.
by exists Q; split; rewrite -?dim1_pt_ppick.
Qed.

Lemma vertex_pbasis x :
  x \in vertex_set P -> exists2 I, is_pbasis I & [pt x] = affine <<I>>%VS.
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have Q_prop0: Q `>` [poly0] by rewrite dimN0 dimQ_eq1.
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- apply/anti_leq/andP; split; rewrite ?dim_span_active //.
  move: dimQ_eq1; rewrite dimN0_eq // => /succn_inj/eqP.
  by rewrite subn_eq0.
case: (ebasisP0 {eq Q}) => I I_sub I_basis.
have I_sub_base: (I `<=` base)%fset. (* TODO: missing canonical in fsubset *)
- by apply/(fsubset_trans I_sub)/fsubset_subP.
have I_pbasis : is_pbasis (I%:fsub).
- apply/and3P; split => /=.
  + by rewrite (card_basis I_basis) dim_eqQ.
  + by rewrite (span_basis I_basis) -hullN0_eq // -dim_hull dimQ_eq1.
  + by rewrite (span_basis I_basis) -hullN0_eq //
  (dim1_pt_ppick dimQ_eq1) hull_pt -dim1_pt_ppick.
exists (I%:fsub) => //.
rewrite -pbasis_active // (span_polyEq (span_basis I_basis)).
by rewrite [Q in LHS]repr_active //=.
Qed.

Definition adj_basis I I' := #|` (I `&` I') |%fset = n.-1.
Definition adj_vertex x x' := (x != x') && ([segm x & x'] \in face_set P).

Lemma adj_vertexL x x' : adj_vertex x x' -> x \in vertex_set P.
Proof.
case/andP => ? /vertex_setS; rewrite vertex_set_segm.
move/fsubsetP => H.
by apply: (H x); rewrite !inE eq_refl /=.
Qed.

Lemma adj_vertexR x x' : adj_vertex x x' -> x' \in vertex_set P.
Proof.
case/andP => ? /vertex_setS; rewrite vertex_set_segm.
move/fsubsetP => H.
by apply: (H x'); rewrite !inE eq_refl orbT.
Qed.


Lemma adj_vertex_prebasis x x':
  adj_vertex x x' -> exists J : {fsubset base},
    [/\ [segm x & x'] = 'P^=(base; J)%:poly_base, (\dim <<J>>)%N = n.-1 & free J].
Proof.
rewrite /adj_vertex => /andP [x_neq_x'].
case/face_setP => Q Q_sub_P Q_eq.
have Q_prop0: Q `>` [poly0] by rewrite -Q_eq segm_prop0.
case: (ebasisP0 {eq Q}) => J J_sub J_basis.
have J_sub' : (J `<=` base)%fset
  by apply/(fsubset_trans J_sub)/fsubset_subP.
exists J%:fsub; split.
- by rewrite [Q]repr_active //= (basis_polyEq J_basis).
- have dimQ2: (dim Q) = 2%N by rewrite -Q_eq dim_segm x_neq_x'.
move: (span_basis J_basis) => ->.
rewrite (dimN0_eq Q_prop0) in dimQ2. move/eq_add_S: dimQ2 => dimQeq.
rewrite -subn1 -dimQeq subKn => //.
by apply ltnW; rewrite -subn_gt0 dimQeq.
- by move/basis_free: J_basis.
Qed.

Definition is_pbasis_of (x : 'cV_n) (I : {fsubset base}) :=
  is_pbasis I /\ [pt x] = affine <<I>>%VS.

Lemma is_pbasis_of_pbasis (x: 'cV_n) (I : {fsubset base}) :
is_pbasis_of x I -> is_pbasis I.
Proof.
by case.
Qed.

Lemma is_pbasis_of_eq x I : is_pbasis_of x I -> [pt x] = affine <<I>>%VS.
Proof.
by case.
Qed.

Lemma vertex_pbasis_of I x :
  x \in vertex_set P ->
        let Qx : {poly base} := insubd [poly0]%:poly_base [pt x] in
        basis_of <<{eq Qx}>>%VS I -> is_pbasis_of x I.
Proof.
move => x_vtx.
case/vertexP: (x_vtx) => Q [Q_eq dim_Q Q_sub].
rewrite Q_eq valKd /= => basis_eqQ_I.
have Q_prop0: ([ poly0 ] `<` Q)%PH by rewrite -Q_eq pt_proper0.
have x_eq : [pt x] = affine <<I>>.
+ by rewrite (span_basis basis_eqQ_I) -hullN0_eq // -Q_eq hull_pt.
split => //; apply/and3P; split; rewrite -?x_eq ?dim_pt ?Q_eq //.
rewrite (card_basis basis_eqQ_I).
rewrite dimN0_eq in dim_Q => //.
move/succn_inj/eqP: dim_Q; rewrite subn_eq0 => n_leq_dim.
by apply/eqP/anti_leq/andP; split => //; rewrite dim_span_active.
Qed.

Lemma free_card (K : fieldType) (vT : vectType K) (X : {fset vT}) :
  free X -> (\dim <<X>> = #|` X |)%N.
Proof.
move => free_X.
by symmetry; apply/card_basis/andP.
Qed.

Lemma pt_inj : injective (mk_affine (<[0]>%VS : {vspace 'cV[R]_n})).
Proof.
move=> x1 x2 pt_eq.
by rewrite -(ppick_pt x1) -(ppick_pt x2) pt_eq.
Qed.
(* TODO: to be moved in polyhedron.v *)

Lemma fsetI_propl (K : choiceType) (S S' : {fset K}):
  #|` S| = #|` S'| -> S != S' -> (S `&` S' `<` S)%fset.
Proof.
move=> cardS_eq_cardS'; apply contra_neqT;
  rewrite fproperEcard fsubsetIl /= ltnNge negbK => cardS_sub_cardI.
have cardS_eq_cardI: #|` S| = #|` S `&` S'| by
  apply/anti_leq/andP; split => //; apply/fsubset_leq_card/fsubsetIl.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
- by apply/fsetIidPl/eqP; rewrite eqEfcard fsubsetIl cardS_sub_cardI.
- by apply/fsetIidPr/eqP; rewrite eqEfcard fsubsetIr -cardS_eq_cardS'
  cardS_sub_cardI.
Qed.

Lemma adj_vertex_basis x x' :
  adj_vertex x x' -> exists I, exists I',
      [/\ is_pbasis_of x I, is_pbasis_of x' I' & adj_basis I I'].
Proof.
move=> adj_x_x'.
case: (adj_vertex_prebasis adj_x_x') => J [segm_J dim_J free_J].
have x_vtx := (adj_vertexL adj_x_x').
have x_vtx' := (adj_vertexR adj_x_x').
have: [pt x] \in face_set P /\ [pt x'] \in face_set P
  by rewrite -!in_vertex_setP.
case => /face_setP [Qx Qxsub Qxpt] /face_setP [Qx' Qx'sub Qx'pt].
set S := ('P^=(base; J)) %:poly_base.
have [eq_sub_eq_x eq_sub_eq_x'] : ({eq S} `<=` {eq Qx})%fset /\ ({eq S} `<=` {eq Qx'})%fset.
- rewrite !activeS // -segm_J -1?Qxpt -1?Qx'pt pt_subset.
  + by rewrite in_segmr.
  + by rewrite in_segml.
have J_sub_eqS: (J `<=` {eq S})%fset by rewrite -activeP le_refl.
have {}eq_sub_eq_x : (J `<=` {eq Qx})%fset.
- by apply: (fsubset_trans J_sub_eqS).
have {}eq_sub_eq_x' : (J `<=` {eq Qx'})%fset.
- by apply: (fsubset_trans J_sub_eqS).
rewrite {J_sub_eqS}.
case: (ebasisP eq_sub_eq_x free_J) => I [J_sub_I I_sub_eq_x I_basis].
case: (ebasisP eq_sub_eq_x' free_J) => I' [J_sub_I' I'_sub_eq_x' I'_basis].
have I_sub_base: (I `<=` base)%fset
  by apply/(fsubset_trans I_sub_eq_x)/fsubset_subP.
have I'_sub_base: (I' `<=` base)%fset
  by apply/(fsubset_trans I'_sub_eq_x')/fsubset_subP.
exists I%:fsub; exists I'%:fsub.
have is_pbasis_of_x_I : is_pbasis_of x I%:fsub.
- apply/vertex_pbasis_of => //; by rewrite Qxpt valKd.
have is_pbasis_of_x'_I' : is_pbasis_of x' I'%:fsub.
- apply/vertex_pbasis_of => //; by rewrite Qx'pt valKd.
split => //.
have card_J: (#|` J | = n.-1)%N by rewrite -free_card.
rewrite /adj_basis /=.
suff ->: (I `&` I')%fset = J by [].
apply/eqP; rewrite eq_sym eqEfcard card_J; apply/andP; split.
- by apply/fsubsetIP.
- have [Qx_prop0 Qx'_prop0]: Qx `>` [ poly0 ] /\ Qx' `>` [ poly0 ]
  by split; rewrite -?Qxpt -?Qx'pt pt_proper0.
  have card_I: #|` I| = n.
    by move/is_pbasis_of_pbasis/card_pbasis: is_pbasis_of_x_I.
  have card_I': #|` I'| = n.
    by move/is_pbasis_of_pbasis/card_pbasis: is_pbasis_of_x'_I'.
  have eq_card: #|` I| = #|` I'| by rewrite card_I card_I'.
  have /(fsetI_propl eq_card)/fproper_ltn_card: (I != I').
  + case/andP: adj_x_x' => x_neq_x' _.
    rewrite -(inj_eq pt_inj) in x_neq_x'.
    move: x_neq_x'; apply/contra_neq.
    by rewrite (is_pbasis_of_eq is_pbasis_of_x_I)
      (is_pbasis_of_eq is_pbasis_of_x'_I') /= => ->.
    rewrite card_I. by case: {4 8}n.
  (* TODO: horrible (it's XA's fault) *)
Qed.

Lemma foo' x (I : {fsubset base}) :
  x \in P -> [pt x] = affine <<I>>%VS -> #|` I| = n -> is_pbasis I.
Proof.
move => x_in_P pt_eq cardI.
apply/and3P; split; rewrite -?pt_eq.
- by apply/eqP.
- by rewrite dim_pt.
- by rewrite pt_subset.
Qed.

Lemma dim_affine2 (U : {vspace lrel[R]_n}) :
  (dim (affine U) = 2)%N ->
  exists2 x, x \in affine U & exists2 d, d != 0 & (affine U) = [line d & x].
Admitted.

Variable (x: 'cV[R]_n) (I : {fsubset base}) (i : lrel[R]_n).

Hypothesis (Hbasis : is_pbasis_of x I) (i_in_I : i \in (I : base_t)).

Lemma n_prop0 : (n > 0)%N.
Admitted.

Lemma dim_pbasisD1 :
  exists d, (affine << (I `\ i)%fset >> == [line d & x]) && ('[i.1, d] == 1).
Proof.
(* proof sketch
 * first show that dim affine << (I `\ i)%fset >> = 2%N
 * use dim_affine2 to exhibit d
 * show that '[i.1,d] != 0, and replace d by (| '[i.1,d] |^-1 *: d
 *)
Admitted.

Definition dir := xchoose dim_pbasisD1.

Definition c (j : lrel[R]_n) := '[befst j, dir].

Definition r (j : lrel[R]_n) :=
  '[j.1, ppick (affine << I >>%VS)] - j.2.

(*
Proposition
Soit I une base admissible, i \in I, et j \notin I. Alors J = I - i + j est une base admissible ssi les conditions suivantes sont satisfaites :
* c_ij != 0
* r_j > 0 ==> j \in arg max_(k notin I | c_ik < 0) (r_k / c_ik).
*)

Variable (j : lrel[R]_n).
Hypothesis (j_in_base : j \in base).
Let I' : {fsubset base} := (I `\  i)%:fsub. (* TODO: type is mandatory here *)
Let J : {fsubset base} := (j |` I')%:fsub.

Hypothesis (j_notin_I : j \notin (I : base_t)).

Lemma card_pivot:
  (#|` J| == n)%N.
Proof.
rewrite cardfsU1 in_fsetE negb_and j_notin_I orbT cardfsD /=.
by rewrite fsetI1 i_in_I cardfs1 subnKC
  (card_pbasis (is_pbasis_of_pbasis Hbasis)) ?n_prop0.
Qed.

Lemma foo1:
  forall k: lrel[R]_n, k \in (I': {fset _}) -> c k = 0.
Proof.
move: (xchooseP dim_pbasisD1);
rewrite /= -/dir => /andP [/eqP affine_eq dir_dot] k k_in_I'.
apply/eqP; rewrite /c lfunE /= -(@line_subset_hs _ _ _ x dir).
- by rewrite -affine_eq; apply poly_base_subset_hs.
- move/pbasis_active: (is_pbasis_of_pbasis Hbasis).
  rewrite -(is_pbasis_of_eq Hbasis) => polyEq_x.
  have: x \in 'P^=(base;I) by rewrite polyEq_x in_pt_self.
  move/polyEq_eq => H.
  move: k_in_I'; rewrite in_fsetD1.
  case/andP=> _ k_in_I.
  apply: hs_hp; exact: (H k).
Qed.

Lemma free_I': free I'.
Proof.
move: (pbasis_free (is_pbasis_of_pbasis Hbasis)) => free_I.
apply:(@catl_free _ _ [fset i]).
have uniq_I: uniq I by apply: free_uniq.
have: perm_eq I (I'++[fset i]).
- apply: uniq_perm.
  + by [].
  + apply (leq_size_uniq uniq_I).
    * by move=> y; rewrite mem_cat !in_fsetE => ->; rewrite andbT orNb.
    * by rewrite size_cat (cardfsD1 i I) i_in_I cardfs1 addnC.
  + move=> y; rewrite mem_cat !in_fsetE orb_andl orNb /=.
    have: (y == i) -> (y \in (I:{fset _})) by move/eqP => ->.
    by case: (y == i) => H /=; [rewrite orbT; apply H|rewrite orbF].
  by move=> perm_eq_I_I''; rewrite -(perm_free perm_eq_I_I'').
Qed.

Lemma free_pivot : c j != 0 -> free J.
Proof.
apply/contra_neqT; have: perm_eq J (j :: I').
+ apply: uniq_perm => /=; first by apply: fset_uniq.
  * by rewrite fset_uniq !in_fsetE negb_and j_notin_I orbT.
  * by move=> v; rewrite !(in_cons, in_fsetE).
move/perm_free=> ->; rewrite free_cons free_I' andbT negbK.
move/coord_span => ->; rewrite /c linear_sum vdot_sumDl /=.
rewrite big1 // => k _; rewrite linearZ /= vdotZl.
set v := (X in _ * X); rewrite [v](_ : _ = 0); first by rewrite mulr0.
by apply/foo1/mem_nth.
Qed.

(*
c = fun j : lrel => '[ befst j, dir]
     : lrel -> R
*)

Lemma be_lift y :
  y \in affine <<J>>%VS -> j.1 \in (befst @: <<I'>>)%VS -> j \in <<I'>>%VS.
Admitted.

Lemma dir_orth : (<[dir]> = (befst @: <<I'>>)^OC)%VS.
Admitted.

Goal c j = 0 -> j.1 \in (befst @: <<I'>>)%VS.
Proof.
rewrite /c.
Admitted.

(* Remark: we must show that, if #J = n, then free J <-> dim affine <<J>> = 1
 * In particular, this requires to assume that affine <<J>> is nonempty         *)
(* J is a basis iff #J = n and dim affine <<J>> = 1 *)
(* Moreover, J is feasible if affine <<J>> `<=` P
 * 1st step: show that J is a basis iff c j != 0 *)

(* 2nd step: show that the basic point associated with J is given by
 * ppick (affine <<J>>) = ppick (affine <<I>>) + (r j) / (c j) *: dir
 * It suffices to show that this point belongs to affine <<J>> *)

(* 3rd step: When r j > 0, show that
   affine <<J>> is feasible <-> (forall k, k \notin (I : {fset _}) ->
                                c k < 0 -> (r j) / (c j) >= (r k) / (c k)) *)

Lemma pivot :
  reflect (c j != 0 /\ (r j > 0 -> forall k, k \notin (I : {fset _}) ->
                        c k < 0 -> (r j) / (c j) >= (r k) / (c k)))
          (is_pbasis J).
Admitted.

End PBasis.
