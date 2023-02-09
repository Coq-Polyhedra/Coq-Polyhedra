From mathcomp Require Import all_ssreflect all_algebra finmap.
From Coq Require Import Uint63 PArray.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx barycenter.
From Polyhedra Require Import lrel polyhedron poly_base simplex.
Require Import enum_algo enum_proof enum_equiv graph high_graph img_graph extra_array extra_int rat_bigQ diameter refinement.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Num.Theory.

Local Notation "a .[ i ]" := (PArray.get a i).

Section LexCorrectness.

Context (m' n' : nat).
Local Notation m := m'.+1. 
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Local Notation b_pert := (Simplex.b_pert b).

Context (G : graph (enum_type m' n')).

Hypothesis enum_h_r : high_enum_algo A b G.
Hypothesis P_compact : forall c, Simplex.bounded A b c.
Hypothesis G_prop0 : G != (graph0 (enum_type m' n')).

Lemma enum_h :
  [forall e : vertices G,
    [&& card_verification (fsval e),
        feas_verification A b (fsval e),
        bas_verification A b (fsval e),
        reg_verification G (fsval e) &
        [forall e' : successors G (fsval e), inter_verification (fsval e) (fsval e')]
    ]
  ].
Proof. by move: enum_h_r; rewrite high_enum_algoE. Qed.

Section ConstructFeasbas.

Context (e : enum_type m' n').
Hypothesis IxG : e \in (vertices G).

Local Notation I := e.1.
Local Notation x := e.2.

Lemma I_prebasis : #|I|==n.
Proof.
move/forallP:enum_h=> /= /(_ [` IxG]).
by case/and5P.
Qed.

Definition prebasis_I := Simplex.Prebasis I_prebasis.
Definition x_inv := -1 *: (row_submx (col' ord0 x)^T I)^T.

Lemma I_basis : Simplex.is_basis A prebasis_I.
Proof.
move/forallP:enum_h=> /= /(_ [` IxG]).
case/and5P=> _ _ + _ _; rewrite /bas_verification /= => /eqP A_Ix.
rewrite /Simplex.is_basis /=; apply/row_freeP.
exists x_inv; rewrite /x_inv -scalemxAr -[X in X *m _]trmxK -trmx_mul tr_col'.
apply/matrixP=> p q; rewrite !mxE.
under eq_bigr => [k _] do rewrite !mxE. 
move: A_Ix=> /matrixP /(_ p (lift ord0 (enum_val q))); rewrite mxE.
under eq_bigr=> [k _] do rewrite mxE GRing.mulrC; move=> ->.
rewrite !mxE; case: splitP.
- move=> j /=; rewrite (ord1_eq0 j) /= => /esym /eqP.
  by rewrite (negPf (neq_bump _ _)).
- move=> k; rewrite lift0 [RHS]add1n => /succn_inj /val_inj <-.
  rewrite !mxE -GRing.mulNrn GRing.Theory.mulrnAr GRing.mulrN1 GRing.opprK.
  congr GRing.natmul; congr nat_of_bool.
  by apply/idP/idP=> [/eqP /enum_val_inj ->|/eqP ->].
Qed.

Definition basis_I := Simplex.Basis I_basis.

Lemma x_point_of_I : x = Simplex.point_of_basis b_pert basis_I.
Proof. 
rewrite -(@Simplex.basis_subset_active_ineq_eq _ _ _ _ _ _ _ x) //=.
apply/subsetP=> i iI; rewrite inE row_mul.
move/forallP:enum_h=> /= /(_ [` IxG]).
case/and5P=> _ _ /eqP I_bas _ _.
by rewrite -[i](enum_rankK_in iI) // -!row_submx_row -I_bas row_mul.
Qed.

Lemma I_feasible : Simplex.is_feasible b_pert basis_I.
Proof.
move/forallP:enum_h=> /= /(_ [` IxG]).
case/and5P=> _ + _ _ _; rewrite /feas_verification /=.
by rewrite x_point_of_I /Simplex.is_feasible.
Qed.

Definition lexbasis_I := Simplex.FeasibleBasis I_feasible.

End ConstructFeasbas.

Lemma I0_def : exists x, x \in vertices G.
Proof. by move/graph0Pn: G_prop0. Qed.

Definition I0 := lexbasis_I (xchooseP I0_def).

Definition to_feas_bas (e : enum_type m' n'):=
  if @idP (e \in vertices G) is ReflectT h then
  lexbasis_I h else I0.

Definition lex_graph := lex_graph A b.

Lemma to_feas_bas_inj : {in vertices G &, injective to_feas_bas}.
Proof.
move=> e e' eG e'G; rewrite /to_feas_bas.
case: {-}_/idP=> // p; case: {-}_/idP=> // p'.
move=> bas_I_eq; rewrite [e]surjective_pairing [e']surjective_pairing.
apply/pair_equal_spec; split.
+ by move: bas_I_eq; do 3! move/(congr1 val).
+ by rewrite !x_point_of_I; move/(congr1 val):bas_I_eq=> /= ->.
Qed.

Lemma to_feas_bas_edges : {in vertices G &,
  forall x y, edges G x y -> 
  edges lex_graph (to_feas_bas x) (to_feas_bas y)}.
Proof.
move=> x y xG yG; rewrite edge_mk_graph ?inE // -in_succE => yx.
rewrite /set_adjacence /=.
move/forallP: enum_h=> /(_ [`xG]) /and5P [_ _ _ _].
move/forallP=> /(_ [`yx]) /=; rewrite /inter_verification.
by rewrite /to_feas_bas; case: {-}_/idP=> // p; case: {-}_/idP.
Qed.

Lemma repr_lex_graph: gisof G lex_graph to_feas_bas.
Proof.
apply/sub_gisof=> //.
- exact: to_feas_bas_inj.
- by apply/fsubsetP=> x; rewrite vtx_mk_graph inE /=.
- exact:to_feas_bas_edges. 
- exact:lex_graph_connected.
- move=> x xG; apply/eqP; rewrite eqEfcard; apply/andP; split.
  + apply/fsubsetP=> y' /imfsetP [/= y].
    rewrite in_succE=> /[dup] /edge_vtxr yG /(to_feas_bas_edges xG yG).
    by rewrite -in_succE => /[swap] ->.
  + rewrite lex_graph_regular ?vtx_mk_graph ?inE // card_in_imfset /=.
    * move/forallP: enum_h=> /(_ [`xG]) /and5P [_ _ _ + _].
      by rewrite /reg_verification=> /eqP ->.
    * move=> p q /(fsubsetP (sub_succ _ _)) + /(fsubsetP (sub_succ _ _)).
      exact:to_feas_bas_inj.
Qed.

End LexCorrectness.

(* --------------------------------------------------------------- *)

Section ImgGraph.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (G_lex : graph (enum_type m' n')) (G_vert : graph [choiceType of 'cV[rat]_n]).

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).

Hypothesis boundA : forall c, Simplex.bounded A b c.
Hypothesis G_lex_verif : high_enum_algo A b G_lex.
Hypothesis G_lex_prop0 : G_lex != graph0 _. 

(* Hypothesis G_vert_img : G_vert = ((@phi m' n') @/ G_lex). *)

Definition base_of_syst (C : 'M[rat]_(m,n) * 'cV[rat]_m) := 
  [fset [<(row i C.1)^T, C.2 i 0>] | i : 'I_m].
Definition poly_of_syst C:= 'P(base_of_syst C).

Local Notation P := (poly_of_syst (A,b)).

Lemma feasA : Simplex.feasible A b.
Proof. exact/feas_bas0/(I0 G_lex_verif G_lex_prop0). Qed.

Lemma relA : rel_mat_Po (base_of_syst (A, b)) (A,b).
Proof. by []. Qed.

Lemma high_img : poly_graph P = 
  ((fun I => Simplex.point_of_basis b I) @/ (lex_graph A b)).
Proof. by exact/(im_lex_graph_vert_graph boundA feasA relA). Qed.

Lemma G_lex_repr : gisof G_lex (lex_graph A b) (to_feas_bas G_lex_verif G_lex_prop0).
Proof. exact/repr_lex_graph. Qed.

Lemma repr_poly_graph :  poly_graph P = ((@phi m' n') @/ G_lex).
Proof.
apply/esym/(gisof_diagram _ G_lex_repr _ high_img); [|exact:erefl].
move=> x xG_lex /=; rewrite Simplex.rel_points_of_basis.
rewrite /to_feas_bas; case: {-}_/idP=> // ?.
by rewrite -x_point_of_I.
Qed.

End ImgGraph.

(* --------------------------------------------------------------- *)

Section BoundPoly.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Context (Y_pos Y_neg : 'M[rat]_(n,m)).

Hypothesis feasA : Simplex.feasible A b. 
Hypothesis bound_h : high_poly_bounded A Y_pos Y_neg.

Definition max_bound_i (i : 'I_n):= 
  (Order.max '[-(row i Y_pos)^T, b] '[-(row i Y_neg)^T,b]).
Definition max_bound := \big[Order.max/0%R]_(i < n) max_bound_i i.

Lemma max_boundP (i : 'I_n):
  max_bound_i i <= max_bound.
Proof.
rewrite /max_bound.
have: i \in index_enum (ordinal_finType n) by rewrite mem_index_enum.
elim: (index_enum _)=> // h t IH.
rewrite in_cons big_cons le_maxr; case/orP.
- by move/eqP=> ->; rewrite lexx.
- by move/IH=> ->; rewrite orbT.
Qed.

Lemma high_poly_boundedP: forall c, Simplex.bounded A b c.
Proof.
move=> c; rewrite -(boundedE (relA A b)); move: c; apply/compactP.
- case/Simplex.feasibleP: feasA=> x x_in; apply/proper0P; exists x.
  by rewrite (feasE (relA A b)).
- apply/compactP_Linfty; exists max_bound=> x.
  rewrite (feasE (relA A b)) inE => x_Ab i.
  case/andP: bound_h=> /forallP /(_ i) + /forallP /(_ i).
  case/andP=> /eqP Y_pos_A Y_pos_pos.
  case/andP=> /eqP Y_neg_A Y_neg_pos.
  move: (vdot_lev Y_pos_pos x_Ab) (vdot_lev Y_neg_pos x_Ab).
  rewrite !vdot_mulmx -!trmx_mul Y_pos_A Y_neg_A.
  rewrite [X in _ <= X]row_vdot mul_scalar_mx GRing.scale1r.
  move=> x_i_ge; rewrite [X in _ <= X]row_vdot mul_scalar_mx GRing.scaleN1r mxE.
  move=> x_i_le; apply/(le_trans _ (max_boundP i)).
  rewrite ler_norml; apply/andP; split.
  + rewrite ler_oppl le_maxr; apply/orP; left.
    by rewrite vdotNl ler_oppl GRing.opprK.
  + rewrite le_maxr; apply/orP; right.
    by rewrite vdotNl ler_oppr.
Qed.

End BoundPoly.

(* --------------------------------------------------------------- *)

Section FullDim.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Context (x0 : 'cV[rat]_n) (s : seq 'cV[rat]_n).

Local Definition base_AB := base_of_syst (A, b).

Hypothesis full_h : 
  [/\ x0 \in (vertex_set 'P(base_AB)), 
    {subset s <= (vertex_set 'P(base_AB))} &
    \dim (span [seq x - x0 | x <- s]) = n].

Lemma high_dim_fullP: \pdim 'P(base_AB) = n.+1.
Proof.
apply/anti_leq/andP; split; first exact:adim_leSn.
case: full_h=> x0_vtx s_vtx {1}<-.
apply/leq_trans; [|apply/(dim_sub_affine (x0:=x0) (X:=s))].
- by rewrite adimN0_eq ?mk_affine_proper0 // dir_mk_affine.
- exact/vertex_set_subset.
- by move=> x /s_vtx; exact/vertex_set_subset.
Qed.

End FullDim.

(* --------------------------------------------------------------- *)

Section HighHirsch.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).

Context (G_lex : graph (enum_type m' n')) (G_vert : graph [choiceType of 'cV[rat]_n]).

Hypothesis enum_h : high_enum_algo A b G_lex.
Hypothesis img_h : G_vert = ((@phi m' n') @/ G_lex).
Hypothesis boundA : forall c : 'cV_n, Simplex.bounded A b c.
Hypothesis G_lex_prop0 : G_lex != graph0 _.
Hypothesis poly_dim : \pdim (poly_of_syst (A, b)) = n.+1.

Hypothesis G_vert_BFS : (diameter G_vert > m - n)%nat.

Lemma poly_facets: (#|` facets (poly_of_syst (A, b))| <= m)%nat.
Proof.
apply/(leq_trans (@facets_le _ _ (base_of_syst (A, b))))/(leq_trans (leq_imfset_card _ _ _)).
by rewrite size_enum_ord leqnn.
Qed.

Theorem high_algo_Hirsch :
  (diameter (poly_graph (poly_of_syst (A,b))) > 
    #|`facets (poly_of_syst (A,b))| - 
      (\pdim (poly_of_syst (A,b))).-1)%nat.
Proof.
have G_vert_poly: poly_graph (poly_of_syst (A,b)) = G_vert.
- rewrite img_h; apply: repr_poly_graph.
  + exact: boundA.
  + exact: enum_h.
  + exact: G_lex_prop0.
rewrite poly_dim /=; apply/(leq_ltn_trans (n:=m - n))=> //;first 
  apply/leq_sub2r/poly_facets.
by rewrite G_vert_poly.
Qed.

End HighHirsch.

(* --------------------------------------------------------------- *)

Section HirschVerification.

Context (Po : Com.polyType).
Hypothesis Po_format : poly_format Po.
Local Notation m' := (Com.m Po).-1.
Local Notation n' := (Com.n Po).-1.

Context (g_lex : graph.graph) (l_lex : Com.lex_mapping).
Hypothesis gl_lex_format : lex_graph_format Po g_lex l_lex.

Context (g_vert : graph.graph) (l_vert : array (array BigQ.bigQ)).
Hypothesis gl_vert_format : vert_graph_format Po g_vert l_vert.

Context (morph morph' : array Uint63.int). 
Context (edge_inv : array (array (Uint63.int * Uint63.int))).

Context (y_pos y_neg : array (array BigQ.bigQ)).
Hypothesis y_pos_format : bound_format Po y_pos.
Hypothesis y_neg_format : bound_format Po y_neg.

Hypothesis enum_h : enum_algo Po g_lex l_lex.
Hypothesis img_h : img_lex_graph morph morph' edge_inv g_lex l_lex g_vert l_vert.
Hypothesis bound_h : @bounded_Po_test Po y_pos y_neg.
Hypothesis graph_h : lex_graph_n0 g_lex.

Local Notation high_poly := (spec_poly m' n' Po).
Local Notation A := high_poly.1.
Local Notation b := high_poly.2.
Local Notation G_lex := (spec_lex_graph m' n' (g_lex,l_lex)).
Local Notation G_vert := (spec_vert_graph n' (g_vert,l_vert)).


Lemma high_enum_h : high_enum_algo A b G_lex.
Proof.
move: (format_poly_precond Po_format) (lex_graph_format_precond Po_format gl_lex_format).
move/spec_func_poly=> + /spec_func_lex_graph.
by move/lex_certif_equiv=> /[apply] /= <-.
Qed.

Lemma high_graph_h : G_lex != graph0 _.
Proof.
move: (lex_graph_format_precond Po_format gl_lex_format).
by move/spec_func_lex_graph/graph_n0_equiv=> <-.
Qed. 

Lemma high_img_h:
  G_vert = ((@phi m' n') @/ G_lex).
Proof.
apply/img_lex_graph_equiv; [| |exact:img_h].
- exact/spec_func_lex_graph/lex_graph_format_precond.
- exact/spec_func_vert_graph/vert_graph_format_precond.
Qed.

Lemma high_bound_h:
  forall c, Simplex.bounded A b c.
Proof.
move: (format_poly_precond Po_format) 
  (bound_format_precond Po_format y_pos_format)
  (bound_format_precond Po_format y_neg_format).
move/spec_func_poly=> + /spec_func_bound + /spec_func_bound.
move/poly_bounded_equiv=> /[apply] /[apply] /eq_imply bound_eq.
apply/high_poly_boundedP;
  [apply/feasA; [exact/high_enum_h|exact/high_graph_h]|exact/bound_eq].
Qed.

Lemma Validation: poly_graph (poly_of_syst high_poly) = G_vert.
Proof.
rewrite high_img_h.
apply/repr_poly_graph; 
  [ exact:high_bound_h|exact:high_enum_h|exact:high_graph_h].
Qed.

Context (origin : Uint63.int) (map_ : array int) (inv : array (array BigQ.bigQ)).
Hypothesis inv_format: inv_format Po inv.

Context (start : Uint63.int).

Hypothesis dim_h : dim_full_test l_vert map_ origin inv Po.
Hypothesis diameter_h : diameter_check g_vert Po start. 


Lemma high_dim_h:
  \pdim (poly_of_syst high_poly) = n'.+2.
Proof.
move: (format_poly_precond Po_format) 
  (inv_format_precond Po_format inv_format)
  (vert_graph_format_precond Po_format gl_vert_format).
move/spec_func_poly=> + /spec_func_inv + /spec_func_vert_graph.
move/dim_full_vtx_graph=> /[apply] /[apply].
case/(_ _ _ dim_h)=> /= x0 [s].
rewrite high_img_h.
rewrite -(repr_poly_graph high_bound_h high_enum_h high_graph_h).
by rewrite vtx_mk_graph=> /high_dim_fullP.
Qed.

Lemma high_diameter_h:
  (diameter G_vert > m'.+1 - n'.+1)%nat.
Proof.
move: (format_poly_precond Po_format)
  (vert_graph_format_precond Po_format gl_vert_format).
move/spec_func_poly=> + /spec_func_vert_graph.
by move/high_diameter_check_equiv=> /[apply] /(_ _ diameter_h).
Qed.

Local Notation P := (poly_of_syst high_poly).

Lemma disprove_Hirsch:
  ((diameter (poly_graph P)) > 
  #|`facets P| - (\pdim P).-1)%nat.
Proof.
apply/high_algo_Hirsch; 
  [ exact:high_enum_h|exact:high_img_h|
    exact:high_bound_h|exact:high_graph_h|
    exact:high_dim_h|exact:high_diameter_h].
Qed.

End HirschVerification.

Section ExactDimension.
Context (Po : Com.polyType).
Hypothesis Po_format : poly_format Po.
Local Notation m' := (Com.m Po).-1.
Local Notation n' := (Com.n Po).-1.
Context (g_lex : graph.graph) (l_lex : Com.lex_mapping).
Hypothesis gl_lex_format : lex_graph_format Po g_lex l_lex.

Context (g_vert : graph.graph) (l_vert : array (array BigQ.bigQ)).
Hypothesis gl_vert_format : vert_graph_format Po g_vert l_vert.

Context (morph morph' : array Uint63.int). 
Context (edge_inv : array (array (Uint63.int * Uint63.int))).

Context (y_pos y_neg : array (array BigQ.bigQ)).
Hypothesis y_pos_format : bound_format Po y_pos.
Hypothesis y_neg_format : bound_format Po y_neg.

Hypothesis enum_h : enum_algo Po g_lex l_lex.
Hypothesis img_h : img_lex_graph morph morph' edge_inv g_lex l_lex g_vert l_vert.
Hypothesis bound_h : @bounded_Po_test Po y_pos y_neg.
Hypothesis graph_h : lex_graph_n0 g_lex.

Local Notation high_poly := (spec_poly m' n' Po).
Local Notation A := high_poly.1.
Local Notation b := high_poly.2.
Local Notation G_lex := (spec_lex_graph m' n' (g_lex,l_lex)).
Local Notation G_vert := (spec_vert_graph n' (g_vert,l_vert)).

Lemma diameter_of_polyXXdimXX k:
  diameter_exact g_vert Po k ->
  diameter (poly_graph (poly_of_syst high_poly)) = int_to_nat k.
Proof.
move=> diameter_h.
have:= (Validation Po_format gl_lex_format gl_vert_format y_pos_format y_neg_format).
move=> /(_ _ _ _ enum_h img_h bound_h graph_h) ->.
move: (vert_graph_format_precond Po_format gl_vert_format).
move/spec_func_vert_graph=> rel_g_vert. 
rewrite -(rel_graph_diameter rel_g_vert) /=.
move: diameter_h=> /eqP diam_h.
apply/nat_to_int_inj; [|exact:int_thresholdP|rewrite int_to_natK //].
rewrite inE.
apply/(@leq_ltn_trans (length g_vert)); last exact/int_thresholdP.
case: rel_g_vert=> -[g' ?] [_ [/= gg' _] _].
rewrite (rel_struct_diameter gg') -(rel_struct_card gg').
apply/bigmax_leqP=> p _; exact: size_path_le.
Qed.

Lemma diameter_of_poly20dim21:
  diameter_exact g_vert Po 21%uint63->
  diameter (poly_graph (poly_of_syst high_poly)) = 21%nat.
Proof. by move/diameter_of_polyXXdimXX=> ->. Qed.

Lemma diameter_of_poly23dim24:
  diameter_exact g_vert Po 24%uint63->
  diameter (poly_graph (poly_of_syst high_poly)) = 24%nat.
Proof. by move/diameter_of_polyXXdimXX=> ->. Qed.

End ExactDimension.

