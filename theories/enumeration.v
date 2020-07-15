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
(*Local Open Scope fset_scope.*)
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
have cardS_eq_cardI: (#|` S| = #|` S `&` S'|)%fset by
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

End PBasis.


Section Pivot.

Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.
Context (P : {poly base}).
Hypothesis Pprop0 : P `>` [poly0].

Implicit Type (I : {fsubset base}).

Variable (x: 'cV[R]_n) (I : {fsubset base}) (i : lrel[R]_n).

Hypothesis (Hbasis : is_pbasis_of P x I) (i_in_I : i \in (I : base_t)).
Hypothesis (i_not_in_eqP : i \notin <<{eq P}>>%VS).

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

Lemma dir_prop_line:
  (affine << (I `\ i)%fset >> = [line dir & x]).
Proof.
  by move:(xchooseP dim_pbasisD1); rewrite -/dir => /andP [/eqP].
Qed.

Lemma dir_prop_vdot:
  ('[i.1, dir] = 1).
Proof.
  by move: (xchooseP dim_pbasisD1); rewrite -/dir => /andP [/eqP] _ /eqP.
Qed.

(*
Proposition
Soit I une base admissible, i \in I, et j \notin I. Alors J = I - i + j est une base admissible ssi les conditions suivantes sont satisfaites :
* c_ij != 0
* r_j > 0 ==> j \in arg max_(k notin I | c_ik < 0) (r_k / c_ik).
*)

Variable (j : lrel[R]_n).
Hypothesis (j_in_base : j \in base).
Let I' : {fsubset base} := (I `\  i)%:fsub%fset. (* TODO: type is mandatory here *)
Let J : {fsubset base} := (j |` I')%:fsub%fset.

Hypothesis (j_notin_I : j \notin (I : base_t)).

(* Remark: we must show that, if #J = n, then free J <-> dim affine <<J>> = 1
 * In particular, this requires to assume that affine <<J>> is nonempty         *)
(* J is a basis iff #J = n and dim affine <<J>> = 1 *)
(* Moreover, J is feasible if affine <<J>> `<=` P
 * 1st step: show that J is a basis iff c j != 0 *)

 Hypothesis prop_affine_J : ([poly0] `<` (affine <<J>>%VS))%PH.

Lemma card_pivot:
  (#|` J| = n)%N.
Proof.
rewrite cardfsU1 in_fsetE negb_and j_notin_I orbT cardfsD /=.
by rewrite fsetI1 i_in_I cardfs1 subnKC
  (card_pbasis (is_pbasis_of_pbasis Hbasis)) ?n_prop0.
Qed.

Lemma cancel_c_I':
  forall k: lrel[R]_n, k \in (I': {fset _}) -> c k = 0.
Proof.
move => k k_in_I'.
apply/eqP; rewrite /c lfunE /= -(@line_subset_hs _ _ _ x dir).
- by rewrite -dir_prop_line; apply poly_base_subset_hs.
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
apply:(@catl_free _ _ [fset i]%fset).
have uniq_I: uniq I by apply: free_uniq.
have: perm_eq I (I'++[fset i])%fset.
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
by apply/cancel_c_I'/mem_nth.
Qed.

(*
c = fun j : lrel => '[ befst j, dir]
     : lrel -> R
*)

Lemma be_lift:
  befst j \in (befst @: <<I'>>)%VS -> j \in <<I'>>%VS.
Admitted.

Lemma dir_orth' :
  <[dir]>%VS = (<<[fset (val e).1 | e in (I' : {fset _})]%fset>>)^OC%VS.
Admitted.

Lemma dir_orth : (<[dir]> = (befst @: <<I'>>)^OC)%VS.
Proof.
move: dir_prop_line => h.
have x_in: x \in affine <<(I `\ i)%fset>>.
by rewrite h; apply/in_lineP; exists 0; rewrite scale0r GRing.addr0.
rewrite {1}(affine_orth x_in) line_affine in h.
by move/(mono_inj le_refl (@subv_anti _ _) (mk_affineS x)): h => ->.
Qed.

Lemma ker_c: c j = 0 -> befst j \in (befst @: <<I'>>)%VS.
Proof.
rewrite /c => vdot_befstj_dir.
have: forall y, y \in [:: dir] -> '[y, befst j] = 0
  by move => y; rewrite inE; move/eqP => ->; rewrite vdotC.
move/(orthv_spanP [:: dir] (befst j))=> /=.
by rewrite span_seq1 dir_orth orthK.
Qed.

Lemma pivot_free: free J -> c j != 0.
Proof.
apply: contraTneq; move/ker_c/be_lift => j_in_span_I'.
have: perm_eq J (j :: I').
+ apply: uniq_perm => /=; first by apply: fset_uniq.
  * by rewrite fset_uniq !in_fsetE negb_and j_notin_I orbT.
  * by move=> v; rewrite !(in_cons, in_fsetE).
by move/perm_free => ->; rewrite free_cons free_I' andbT negbK.
Qed.

Lemma free_J_equiv_basis:
(free J <-> (dim (affine <<J>>%VS) = 1)%N).
Proof.
split.
- move => free_J.
  by rewrite dimN0_eq // active_affine free_card // card_pivot subnn.
- rewrite dimN0_eq // active_affine.
  move/eqP; rewrite eqSS subn_eq0 -{1}card_pivot => size_dim_J.
  by apply (@basis_free _ _ <<J>>%VS); rewrite basisEdim size_dim_J andbT.
Qed.

Lemma pivot_basis:
  c j != 0 <-> (dim (affine <<J>>%VS) = 1)%N.
Proof.
rewrite -free_J_equiv_basis; split.
- exact: free_pivot.
- exact: pivot_free.
Qed.


(* 2nd step: show that the basic point associated with J is given by
 * ppick (affine <<J>>) = ppick (affine <<I>>) + (r j) / (c j) *: dir
 * It suffices to show that this point belongs to affine <<J>> *)
Section PointPivot.
Hypothesis J_is_basis : (dim (affine <<J>>%VS) = 1)%N.

Definition point_pivot :=
  (ppick (affine <<I>>%VS) - ((r j) / (c j)) *: dir).

Lemma point_pivot_in_I':
  point_pivot \in affine <<I'>>.
Proof.
apply/in_affine => v v_in_span_I'.
rewrite in_hp vdotDr vdotNr vdotZr.
move: (memv_line dir); rewrite dir_orth => /orthvP ->.
- rewrite mulr0 subr0 -in_hp.
  move/is_pbasis_of_pbasis/pbasis_proper0/ppickP/in_affine: Hbasis => -> //.
  by move: v_in_span_I'; apply/subvP/base_vect_subset/fsubD1set.
- have ->: v.1 = befst v by rewrite lfunE.
  by apply/memv_img.
Qed.

Lemma point_pivot_in_j :
  point_pivot \in [hp j].
rewrite in_hp /point_pivot vdotDr vdotNr vdotZr /r.
have -> : j.1 = befst j by rewrite lfunE.
rewrite -/(c j) -{2}(divr1 (c j)) mulf_div mulr1 -mulrA mulfV.
- by rewrite mulr1 /r opprB addrC -addrA [X in _ + (X)]addrC subrr addr0.
- by apply/pivot_basis.
Qed.

Lemma affine_addv (U V : {vspace lrel[R]_n}) :
  affine (U + V)%VS = affine U `&` affine V.
Proof.
apply/le_anti/andP; split.
- by rewrite lexI; apply/andP; split; apply/affineS; rewrite ?addvSl ?addvSr.
- apply/poly_subsetP => z; rewrite in_polyI => /andP [z_in_U z_in_V].
  apply/in_affine => y /memv_addP [y1 y1_in] [y2 y2_in] ->.
  rewrite in_hp; rewrite /= vdotDl; apply/eqP/congr2; apply/eqP;
    rewrite -in_hp; by [apply/(in_affine U) | apply/(in_affine V)].
Qed.

Lemma point_pivot_in_affine_J:
  (point_pivot \in (affine (<<J>>%VS)))%PH.
Proof.
rewrite span_fsetU span_fset1 affine_addv affine1.
rewrite in_polyI; apply/andP; split.
- by apply/point_pivot_in_j.
- by apply/point_pivot_in_I'.
Qed.

Lemma point_pivot_eq_affine_J:
  [pt point_pivot] = affine <<J>>%VS.
Proof.
move: point_pivot_in_affine_J; rewrite -pt_subset.
case/eqP/dim1P: J_is_basis => y ->.
move/poly_subsetP => pts_subset.
have -> //: point_pivot = y.
by apply/eqP; rewrite -in_pt; apply: pts_subset; exact: in_pt_self.
Qed.

End PointPivot.

(* 3rd step: When r j > 0, show that
   affine <<J>> is feasible <-> (forall k, k \notin (I : {fset _}) ->
    c k < 0 -> (r j) / (c j) >= (r k) / (c k)) *)

Section Feasible.

Hypothesis J_is_basis : (dim (affine <<J>>%VS) = 1)%N.
Hypothesis P_is_Pbase : P = 'P(base)%:poly_base.


Definition condition_feasible := (forall k, k \in base ->
  k \notin (J : {fset _}) ->
  (r k) >= ((r j) / (c j)) * (c k)).
Definition condition_argmax :=
  (forall k, k \in base -> k \notin (J : {fset _}) ->
  c k < 0 -> (r j) / (c j) >= (r k) / (c k)).

Lemma ker_r k: k \in (I : base_t) -> r k = 0.
Proof.
move => k_in_I.
move: (ppickP (pbasis_proper0 (is_pbasis_of_pbasis Hbasis))).
move/in_affine => hp_forall_v.
move/hp_forall_v: (memv_span k_in_I).
rewrite /r.
rewrite in_hp; move/eqP => ->.
by rewrite subrr.
Qed.

Lemma r_ge0 k: k \in base -> r k >= 0.
Proof.
move => k_in_base.
move: (pbasis_feasible (is_pbasis_of_pbasis Hbasis)).
rewrite /r.
rewrite -(is_pbasis_of_eq Hbasis) pt_subset ppick_pt P_is_Pbase /=.
move/in_poly_of_baseP => in_hs_base.
by move: (in_hs_base k k_in_base); rewrite in_hs subr_ge0.
Qed.

Lemma pivot_feasible_condition:
  (affine <<J>> `<=` P) ->
  condition_feasible.
Proof.
rewrite -point_pivot_eq_affine_J // pt_subset P_is_Pbase /=.
move/in_poly_of_baseP => hs_base_point_pivot.
rewrite /condition_feasible => b /hs_base_point_pivot.
rewrite in_hs /point_pivot vdotDr vdotNr vdotZr.
have to_rewrite: b.1 = befst b by rewrite lfunE.
by rewrite {2}to_rewrite -/(c b) -ler_subl_addl -opprB -/(r b) ler_opp2.
Qed.

Lemma pivot_feasible:
  (affine <<J>> `<=` P) -> condition_argmax.
Proof.
move/pivot_feasible_condition.
move=> condition k ? ? c_k_leq_0.
rewrite -(ler_nmul2r c_k_leq_0) -!mulrA mulVf ?mulrA ?mulr1.
- exact: condition.
- exact: ltr_neq.
Qed.

Lemma r_j_c_j_le0 :
  condition_feasible -> r j / c j <= 0.
Proof.
move => condition.
have i_in_base: i \in base by apply:(fsubset_incl i_in_I).
have i_notin_J: i \notin (J: {fset _}).
- rewrite !inE eq_refl /= negb_or.
  apply/predD1P; split => //.
  move => h; move: i_in_I j_notin_I; rewrite h => h1 h2.
  by move: (in_fsetD I I j); rewrite {2}h1 h2 /= fsetDv in_fset0.
move: (condition i i_in_base i_notin_J).
rewrite (ker_r i_in_I) {2}/c.
have <-: i.1 = befst i by rewrite lfunE.
rewrite dir_prop_vdot mulr1; apply.
Qed.


Lemma base_pivot_condition:
  condition_feasible -> affine <<J>> `<=` P.
Proof.
move => condition; rewrite P_is_Pbase /=.
rewrite -point_pivot_eq_affine_J // pt_subset.
apply/in_poly_of_baseP => k.
rewrite -(fsetID J base) inE; case/orP.
- rewrite inE; case/andP => _ k_in_J; apply: hs_hp.
  move/memv_span: k_in_J; move: (k:lrel); apply/in_affine.
  by rewrite point_pivot_in_affine_J.
- rewrite inE in_hs; case/andP => k_notin_J k_in_base.
  rewrite /point_pivot vdotDr vdotNr vdotZr.
  have to_rewrite: k.1 = befst k by rewrite lfunE.
  rewrite {2}to_rewrite -/(c k) -ler_subl_addl -opprB -/(r k) ler_opp2.
  by apply: condition.
Qed.


Lemma feasible_pivot:
  condition_argmax -> r j / c j <= 0 ->
  (affine <<J>> `<=` P).
Proof.
rewrite /condition_argmax.
move => condition r_j_c_j; apply: base_pivot_condition.
rewrite /condition_feasible.
move => b b_in_base b_notin_J.
case: (ltrgt0P (c b)).
- move=> c_b_gt0.
  have h1: r j / c j * c b <= 0
    by apply: mulr_le0_ge0 => //; rewrite le0r c_b_gt0 orbT.
  apply: (le_trans h1); exact (r_ge0 b_in_base).
- by move => c_b_lt0; rewrite -ler_ndivr_mulr //; apply: condition.
- by move => ->; rewrite mulr0; apply: (r_ge0 b_in_base).
Qed.



Lemma pivot :
  reflect (c j != 0 /\ (r j > 0 -> (c j < 0) /\ (forall k, k \notin (I : {fset _}) ->
                        c k < 0 -> (r j) / (c j) >= (r k) / (c k))))
          (is_pbasis P J).
Admitted.

End Pivot.

Section Algo.

Lemma basic_point (I : {fsubset base}) :
  is_pbasis I -> is_pbasis_of (ppick (affine << I >>%VS)) I.
Admitted.

Definition check_basis_aux (Q : pred base_t) x I (H : is_pbasis_of x I)
           (i : I) (j : (base `\`I)%fset) :=
  let c := c H (valP i) in
  let r := r I in
  ((c (val j) != 0) && ((r (val j) > 0) ==>
                     [forall k : (base `\` I)%fset, (c (val k) < 0) ==> ((r (val j)) / (c (val j)) >= (r (val k)) / (c (val k)))])) ==> Q ((val j) |` ((I : {fset _}) `\ (val i)))%fset.

Definition check_basis (Q : pred base_t) (I : base_t) :=
  match @idP (I `<=` base)%fset with
  | ReflectT I_sub =>
    match @idP (is_pbasis I%:fsub) with
    | ReflectT H =>
      let H' := basic_point H in
      [forall i : I, [forall j : (base `\`I)%fset, check_basis_aux Q H' i j]]
    | ReflectF _ => false
    end
  | _ => false
  end.

Definition check_basis_all (L : {fset base_t}) :=
  [forall I : L, check_basis (mem L) (val I)].

Theorem check_basis_allP (L : {fset base_t}) :
  check_basis_all L ->
  L =i [fset (FSubset.untag (FSubset.tf x)) | x : {fsubset base} & is_pbasis x]%fset.
Admitted.

End Algo.
End PBasis.
