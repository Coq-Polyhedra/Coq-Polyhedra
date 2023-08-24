Require Import Setoid PArray Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import PArith.BinPos PArith.BinPosDef.
Require Import NArith.BinNat NArith.BinNatDef.
From Bignums Require Import BigQ.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* Open Scope ring_scope. *)

(* --------------------------------------------------------------------------------------------------- *)

Module Common.

(* polyType is the type of the polytope *)
(* It is a pair of a matrix reprsented by lines and a vector b *)
Definition polyType := ((array (array bigQ)) * (array bigQ))%type.
 Definition m (Po : polyType) := length Po.1.
 Definition n (Po : polyType) := length Po.1.[0%uint63].

(* U is the type of perturbed "points" of the lex-graph*) 
(* It is a matrix represented by columns *)
Definition U := array (array bigQ).
Definition lex_label := ((array Uint63.int) * U)%type.
Definition lex_mapping := array lex_label.

Definition bas (lbl : lex_mapping) (i : Uint63.int)  := lbl.[i].1.
Definition point (lbl : lex_mapping) (i : Uint63.int) := lbl.[i].2.
Definition compute_test (G : graph) := IFold.iall^~ (length G).

End Common.

Module Com := Common.

Section CommonEquiv.
Context (G : graph).

Definition compute_test := iall^~ (length G).

Lemma compute_testP f: compute_test f -> forall i, mem_vertex G i -> f i.
Proof.
move/allP=> compu i ig; apply/compu.
by rewrite mem_irangeE le0x.
Qed.

End CommonEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module FormatComputation.

(* Performs all format computation, i.e. correct length of arrays ... *)

Definition poly_format (Po : Com.polyType):=
  [&& (0 <? Com.m Po)%uint63, (0 <? Com.n Po)%uint63,
      PC.pre_length_computation Po.2 (Com.m Po) &
      PC.pre_mx_computation Po.1 (Com.m Po) (Com.n Po)]. 

Definition basis_format (Po : Com.polyType) (x : array Uint63.int):=
  PC.pre_arr_set_computation (fun a b=> (a <? b)%uint63)
    (fun i=> (i <? Com.m Po)%uint63) x.

Definition point_format (Po : Com.polyType) (x : array (array bigQ)):=
  PC.pre_mx_computation x (Uint63.succ (Com.m Po)) (Com.n Po). 
    
Definition lex_vert_format (Po : Com.polyType) (x : Com.lex_label):=
  basis_format Po x.1 && point_format Po x.2.

Definition lex_graph_format (Po : Com.polyType) (g : graph) (l : Com.lex_mapping):=
  PC.pre_graph_computation (fun x y=> PArrayUtils.lt_array_int x.1 y.1)
  (fun x=> lex_vert_format Po x) g l.

Definition lex_graph_n0 (g : graph):= (0 <? length g)%uint63.

Definition vert_graph_format (Po : Com.polyType) 
  (g : graph) (l : array (array bigQ)):=
  PC.pre_graph_computation BigQUtils.BQltx_order 
    (fun x=> (length x =? Com.n Po)%uint63) g l.

Definition bound_format (Po : Com.polyType) (a : array (array bigQ)):=
  PC.pre_mx_computation a (Com.n Po) (Com.m Po).

Definition inv_format (Po : Com.polyType) (a : array (array bigQ)):=
  PC.pre_mx_computation a (Com.n Po) (Com.n Po).

End FormatComputation.

Module FC := FormatComputation.

Section FormatEquiv.

Definition poly_format (Po : Com.polyType):=
  [&& (0 < Com.m Po)%O, (0 < Com.n Po)%O,
    pre_length_computation Po.2 (Com.m Po) &
    pre_mx_computation Po.1 (Com.m Po) (Com.n Po)].

Definition basis_format (Po : Com.polyType) (x : array Uint63.int):=
  pre_arr_set_computation (fun a b=> (a < b)%O)
    (fun i=> (i < Com.m Po)%O) x.

Definition point_format (Po : Com.polyType) (x : array (array bigQ)):=
  pre_mx_computation x (Uint63.succ (Com.m Po)) (Com.n Po). 
    
Definition lex_vert_format (Po : Com.polyType) (x : Com.lex_label):=
  basis_format Po x.1 && point_format Po x.2.

Definition lex_graph_format (Po : Com.polyType) (g : graph) (l : Com.lex_mapping):=
  pre_graph_computation (fun x y=> lt_array_int x.1 y.1)
  (fun x=> lex_vert_format Po x) g l.

Definition lex_graph_n0 (g : graph) := (0 < length g)%O.

Definition vert_graph_format (Po : Com.polyType) 
  (g : graph) (l : array (array bigQ)):=
  pre_graph_computation BQltx_order 
    (fun x=> (length x == Com.n Po)) g l.

Definition bound_format (Po : Com.polyType) (a : array (array bigQ)):=
  pre_mx_computation a (Com.n Po) (Com.m Po).

Definition inv_format (Po : Com.polyType) (a : array (array bigQ)):=
  pre_mx_computation a (Com.n Po) (Com.n Po).

Lemma poly_formatE Po: FC.poly_format Po = poly_format Po.
Proof. by rewrite /FC.poly_format -!ltEint pre_length_computationE pre_mx_computationE.
Qed.

Lemma lex_graph_formatE Po g l:
  FC.lex_graph_format Po g l = lex_graph_format Po g l.
Proof.
rewrite /FC.lex_graph_format pre_graph_computationE; repeat congr andb.
- by rewrite !rel_sortedP; apply/(sorted_rel_equiv)=> //;
  [move => ??; apply/erefl|move=> ???? -> ->; rewrite lt_array_intE].
- apply/eq_all=> ?; congr andb.
  + by rewrite /FC.basis_format pre_arr_set_computationE.
  + by rewrite /FC.point_format pre_mx_computationE.
Qed.

Lemma lex_graph_n0E g:
  FC.lex_graph_n0 g = lex_graph_n0 g.
Proof. by rewrite /FC.lex_graph_n0 -ltEint. Qed.

Lemma vert_graph_formatE Po g l:
  FC.vert_graph_format Po g l = vert_graph_format Po g l.
Proof.
rewrite /FC.vert_graph_format pre_graph_computationE; repeat congr andb.
- by rewrite !rel_sortedP; apply/(sorted_rel_equiv)=> //;
    [move=> ??; apply/erefl|move=> ???? -> ->; rewrite BQltx_orderE].
- by apply/eq_all=> ?; rewrite eqEint.
Qed.

Lemma bound_formatE Po y:
  FC.bound_format Po y = bound_format Po y.
Proof. by rewrite /FC.bound_format pre_mx_computationE. Qed.

Lemma inv_formatE Po y:
  FC.inv_format Po y = inv_format Po y.
Proof. by rewrite /FC.inv_format pre_mx_computationE. Qed.

End FormatEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module PolyBoundedComputation.

(* bounded_Po_test checks that every coordinate is bounded        *)
(* To do so, let y_pos y_neg : array (array bigQ), such that:  *)
(* -> forall i < n, y_pos.[i] *m A = (j == i)_(j < n)                   *)
(* -> forall i < n, y_neg.[i] *m A = - (j == i)_(j < n)                 *)
(* -> forall i < n, y.[i].1 and y.[i].2 are nonnegative               *)


Definition bound_certif_fold
  (Po: Com.polyType) (y : array (array bigQ)) (x : bigQ):=
  IFold.iall (fun i=>
    BigQUtils.eq_array_bigQ 
          (BigQUtils.weighted_lines y.[i] Po.1)
          (BigQUtils.delta_line (Com.n Po) i x)
    && PArrayUtils.all BigQUtils.bigQ_ge0 y.[i]
  ) (length y).


Definition bounded_Po_test (Po : Com.polyType) (y_pos : array (array bigQ)) 
  (y_neg : array (array bigQ)) :=
    bound_certif_fold Po y_pos 1%bigQ &&
    bound_certif_fold Po y_neg (-1)%bigQ.

End PolyBoundedComputation.

Module PBC := PolyBoundedComputation.

Section PolyBoundedEquiv.

Context {Po : Com.polyType}.

Definition bound_certif_fold (y : array (array bigQ)) (x : bigQ):=
  iall (fun i=>
    eq_array_bigQ 
      (weighted_lines y.[i] Po.1)
      (BigQUtils.delta_line (Com.n Po) i x)
    && arr_all BigQUtils.bigQ_ge0 y.[i]
  ) (length y).


Definition bounded_Po_test (y_pos y_neg : array (array bigQ)):=
  bound_certif_fold y_pos 1%bigQ && bound_certif_fold y_neg (-1)%bigQ.

Lemma bound_certif_foldE y x:
  PBC.bound_certif_fold Po y x = bound_certif_fold y x.
Proof.
rewrite /PBC.bound_certif_fold iallE; apply/eq_all=> i.
by rewrite eq_array_bigQE weighted_linesE arr_allE.
Qed.

Lemma bounded_Po_testE y_pos y_neg:
  PBC.bounded_Po_test Po y_pos y_neg = bounded_Po_test y_pos y_neg.
Proof. by congr andb; rewrite bound_certif_foldE. Qed.

End PolyBoundedEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module LexCertifComputation.

(* 
  Verfify that a given graph g_lex : graph.graph and its labeling l_lex : Com.lex_mapping
  is the graph of lexicographic bases of a polyhedron Po : Com.polyType
*)

Section Defs.

Definition sat_ineq (m i : Uint63.int) (a : array bigQ) (b : bigQ) (x : Com.U):=
  if (PArrayUtils.fold_pair
      (fun bv xv acc=> if acc is Eq then (bv ?= (BigQUtils.bigQ_dot a xv))%bigQ else acc)
    (BigQUtils.perturbed_line m i b (-1)%bigQ) x Eq) is Gt 
  then false else true. 

Definition sat_eq (m i : Uint63.int) (a : array bigQ) (b : bigQ) (x : Com.U):=
  BigQUtils.eq_array_bigQ (BigQUtils.bigQ_mul_row_mx a x) 
    (BigQUtils.perturbed_line m i b (-1)%bigQ).

Definition sat_Po (Po : Com.polyType) (x : Com.U) :=
  IFold.iall (fun i => sat_ineq (Com.m Po) i Po.1.[i] Po.2.[i] x) (Com.m Po).

Definition mask_eq (Po : Com.polyType) (m : array Uint63.int) (x : Com.U):=
  IFold.iall (fun i=> sat_eq (Com.m Po) m.[i] Po.1.[m.[i]] Po.2.[m.[i]] x) (length m).

End Defs.

Section Body.
Context (Po : Com.polyType) (G : graph) (lbl : Com.lex_mapping).

(* We test validity of each vertex label*)
Definition sat_test (i : Uint63.int) := sat_Po Po (Com.point lbl i).
Definition bas_eq_test (i : Uint63.int) := mask_eq Po (Com.bas lbl i) (Com.point lbl i).
Definition card_bas_test (i : Uint63.int) := (length (Com.bas lbl i) =? (Com.n Po))%uint63.
Definition vertex_test (i : Uint63.int) := [&& (card_bas_test i), (sat_test i) & (bas_eq_test i)].

Definition vertex_consistent := Com.compute_test G vertex_test.

(* We test the graph structure*)
Definition regularity_test (i : Uint63.int) := (GraphUtils.nb_neighbours G i =? (Com.n Po))%uint63.
Definition basI_test (i : Uint63.int) := GraphUtils.neighbour_all 
  (fun j => 
    ((AIC.array_inter 
      (fun i j=> (i <? j)%uint63) (Com.bas lbl i) (Com.bas lbl j)) =? Uint63.pred (Com.n Po))%uint63)
    G i.

Definition struct_test i :=
    regularity_test i && basI_test i.

Definition struct_consistent :=
  Com.compute_test G struct_test.

Definition enum_algo := vertex_consistent && struct_consistent.

End Body.
End LexCertifComputation.

Module LCA := LexCertifComputation.

Section LexCertifEquiv.
Section Def.

Definition sat_ineq (m i : Uint63.int) (a : array bigQ) (b : bigQ) (x : Com.U):=
  let pert_b := BigQUtils.perturbed_line m i b (-1)%bigQ in 
  let res := arr_fold_pair
    (fun bv xv acc=> if acc is Eq then (bv ?= (BigQUtils.bigQ_dot a xv))%bigQ else acc)
  pert_b x Eq in
  if res is Gt then false else true. 

Definition sat_eq (m i : Uint63.int) (a : array bigQ) (b : bigQ) (x : Com.U):=
  let pert_b := BigQUtils.perturbed_line m i b (-1)%bigQ in 
  eq_array_bigQ (bigQ_mul_row_mx a x) pert_b.

Definition sat_Po (Po : Com.polyType) (x : Com.U) :=
  iall (fun i => sat_ineq (Com.m Po) i Po.1.[i] Po.2.[i] x) (Com.m Po).

Definition mask_eq (Po : Com.polyType) (m : array Uint63.int) (x : Com.U):=
  iall (fun i=> sat_eq (Com.m Po) m.[i] Po.1.[m.[i]] Po.2.[m.[i]] x) (length m).

Context (Po : Com.polyType) (G : graph) (lbl : Com.lex_mapping).

Definition sat_test (i : Uint63.int) := sat_Po Po (Com.point lbl i).
Definition bas_eq_test (i : Uint63.int) := mask_eq Po (Com.bas lbl i) (Com.point lbl i).
Definition card_bas_test (i : Uint63.int) := (length (Com.bas lbl i) == (Com.n Po)).

Definition vertex_test (i : Uint63.int) := [&& (card_bas_test i), (sat_test i) & (bas_eq_test i)].

Definition vertex_consistent := compute_test G vertex_test.

Definition regularity_test (i : Uint63.int) := (nb_neighbours G i == (Com.n Po)).
Definition basI_test (i : Uint63.int) := neighbour_all 
  (fun j => 
    ((array_inter 
      (fun i j=> (i < j)%O) (Com.bas lbl i) (Com.bas lbl j)) == Uint63.pred (Com.n Po)))
    G i.

Definition struct_test i :=
  regularity_test i && basI_test i.
  
Definition struct_consistent :=
  (compute_test G struct_test).

Definition enum_algo := vertex_consistent && struct_consistent.

End Def.
Section Equiv.

Lemma vertex_consistentE Po g lbl:
  LCA.vertex_consistent Po g lbl = vertex_consistent Po g lbl.
Proof.
rewrite /LCA.vertex_consistent /Com.compute_test iallE.
apply/eq_all=> i; congr andb; rewrite /LCA.card_bas_test ?eqEint //.
congr andb.
- rewrite /LCA.sat_test /LCA.sat_Po.
  rewrite iallE; apply/eq_all=> k. 
  rewrite /LCA.sat_ineq arr_fold_pairE.
  rewrite /sat_ineq /arr_fold_pair /Com.point.
  by elim: zip Eq.
- rewrite /LCA.bas_eq_test /LCA.mask_eq.
  rewrite iallE; apply/eq_all=> k.
  rewrite /LCA.sat_eq.
  by rewrite eq_array_bigQE; congr andb; rewrite ?bigQ_mul_row_mxE.
Qed.

Lemma struct_consistentE Po g lbl:
  LCA.struct_consistent Po g lbl = struct_consistent Po g lbl.
Proof.
rewrite /LCA.struct_consistent /Com.compute_test iallE; apply/eq_all=> i.
congr andb; first by rewrite /LCA.regularity_test eqEint.
rewrite /LCA.basI_test neighbour_allE; apply/eq_all=> j.
by rewrite array_interE eqEint.
Qed.

Lemma enum_algoE Po g lbl: 
  LCA.enum_algo Po g lbl = enum_algo Po g lbl.
Proof. by congr andb; rewrite ?vertex_consistentE ?struct_consistentE //. Qed.

End Equiv.
End LexCertifEquiv.

Section LexCertifProofs.

Lemma sat_ineqP (m i : Uint63.int) (a : array bigQ) (b : bigQ) (u : Com.U) :
  length u = Uint63.succ m ->
  sat_ineq m i a b u = 
  BQlex_order (BigQUtils.perturbed_line m i b (-1)%bigQ)
    (bigQ_mul_row_mx a u).
Proof.
move=> len_u.
rewrite /BQlex_order /bigQ_mul_row_mx.
rewrite /lex_array_rel /lex_array_rel_ /arr_fold_pair.
rewrite length_arr_map !length_set length_make -len_u leb_length eqxx /=.
rewrite rAS_map /sat_ineq /arr_fold_pair.
set F := (foldl _ _ _); set F' := (foldl _ _ _).
suff ->: F = F' by [].
rewrite /F /F'.
move/(congr1 int_to_nat): (len_u). 
set pert_b := BigQUtils.perturbed_line _ _ _ _.
rewrite -(size_arr_to_seq u).
have <-: size (arr_to_seq pert_b) = Uint63.succ m by
  rewrite size_arr_to_seq !length_set !length_make -len_u leb_length.
elim/last_ind: (arr_to_seq pert_b) (arr_to_seq u)=> [|t h IH]; elim/last_ind=> [|t' h' _] //.
- by rewrite size_rcons.
- by rewrite size_rcons.
- rewrite !size_rcons => /succn_inj size_tt'.
  rewrite map_rcons !zip_rcons ?size_map // !foldl_rcons /=.
  by move: (IH t' size_tt')=> ->; rewrite !bigQ_dotE.
Qed.

Context {Po : Com.polyType} {g : graph} {lbl : Com.lex_mapping}.

Lemma lex_card_bas i: card_bas_test Po lbl i-> length (Com.bas lbl i) = (Com.n Po).
Proof. by move=> /eqP ->. Qed.


Lemma lex_basI i j: 
  mem_vertex g i -> mem_vertex g j ->
  mem_edge g i j ->
  basI_test Po g lbl i ->
  array_inter (fun i j=> (i < j)%O) 
    (Com.bas lbl i) (Com.bas lbl j) = Uint63.pred (Com.n Po).
Proof.
move=> ig jg ij_g /neighbour_allP.
move/(_ ig); move/neighboursP: ij_g=> /(_ ig jg) [k k_nei j_eq] /(_ k k_nei).
by rewrite j_eq /= => /(_ jg) /eqP ->.
Qed.

Lemma lex_regularity i: regularity_test Po g i -> nb_neighbours g i = (Com.n Po).
Proof. by move=> /eqP. Qed.

Lemma lex_sat_Po k i: (k < Com.m Po)%O ->
  sat_test Po lbl i ->
  sat_ineq (Com.m Po) k Po.1.[k] Po.2.[k] (Com.point lbl i).
Proof. by move=> k_Po /allP; apply; rewrite mem_irangeE le0x k_Po. Qed.

Lemma lex_mask_eq i j: (j < length (Com.bas lbl i))%O -> 
  bas_eq_test Po lbl i ->
  sat_eq (Com.m Po) (Com.bas lbl i).[j]
    Po.1.[(Com.bas lbl i).[j]] Po.2.[(Com.bas lbl i).[j]]
    (Com.point lbl i).
Proof. by move=> j_bas /allP /(_ j); apply; rewrite mem_irangeE le0x j_bas. Qed.
  

End LexCertifProofs.

(* --------------------------------------------------------------- *)

Definition BQlex_label := Com.lex_label.
Definition BQlex_mapping := Com.lex_mapping.

Definition BQvert_label := (array bigQ)%type.
Definition BQvert_mapping := array (BQvert_label).

Module ImgGraphLexComputation.

(* 
  Given two graphs g_lex and g_vert associated with their labels
  l_lex and l_simpl, img_lex_graph verifies the g_vert is the image graph
  of g_lex. It makes uses of three certificates
  (morph morph' : array int) (edge_inv : array (array (int * int))) 
*)

Definition img_lex_graph morph morph' edge_inv 
  g_lex l_lex g_vert l_vert := 
  ILGC.img_label_graph (fun x : BQlex_label => x.2.[0%uint63]) BigQUtils.eq_array_bigQ
  morph morph' edge_inv (g_lex, l_lex) (g_vert, l_vert).

End ImgGraphLexComputation.

Module IGLexC := ImgGraphLexComputation.

Section ImgGraphLexEquiv.

Definition img_lex_graph morph morph' edge_inv 
  g_lex l_lex g_vert l_vert := 
  img_label_graph (fun x : BQlex_label => x.2.[0%uint63]) eq_array_bigQ
  morph morph' edge_inv (g_lex,l_lex) (g_vert,l_vert).

Lemma img_lex_graphE morph morph' edge_inv g_lex l_lex g_vert l_vert:
  IGLexC.img_lex_graph morph morph' edge_inv g_lex l_lex g_vert l_vert =
  img_lex_graph morph morph' edge_inv g_lex l_lex g_vert l_vert.
Proof. 
rewrite /IGLexC.img_lex_graph img_label_graphE; congr andb. 
by rewrite /img_label; apply/eq_all=> i /=; rewrite eq_array_bigQE. 
Qed.

End ImgGraphLexEquiv.

(* -------------------------------------------------------------------- *)

Module DimensionFullComputation.

(* Given an array (lbl : BQvert_mapping) of Q^n points, dim_full_test
  verifies that given n points x_k and one origin x_0,
  the matrix \matrix_k (x_k - x_0)^T is invertible *)

Definition inverse_line_i (lbl : BQvert_mapping) 
  (map_ : array Uint63.int) (origin : Uint63.int) 
  (inv : array (array bigQ)) n i:=
  let: rV_i:= 
    BigQUtils.bigQ_add_rV (lbl.[map_.[i]]) (BigQUtils.bigQ_scal_rV (-1)%bigQ lbl.[origin]) in
  BigQUtils.eq_array_bigQ (BigQUtils.bigQ_mul_row_mx rV_i inv) (BigQUtils.delta_line n i 1%bigQ).

Definition dim_full_test (lbl : BQvert_mapping)
  (map_ : array Uint63.int) (origin : Uint63.int) (inv : array (array bigQ)) 
  (Po : Com.polyType) :=
    [&& 
      (length map_ =? Com.n Po)%uint63,
      PArrayUtils.all (fun x=> (x <? length lbl)%uint63) map_,
      (origin <? length lbl)%uint63 &
      IFold.iall
        (fun i=> inverse_line_i lbl map_ origin inv (Com.n Po) i) 
      (length map_)
    ].


End DimensionFullComputation.

Module DFC := DimensionFullComputation.

Section DimensionFullEquiv.

Definition inverse_line_i (lbl : BQvert_mapping) 
  (map_ : array Uint63.int) (origin : Uint63.int) 
  (inv : array (array bigQ)) n i:=
  let: rV_i:= 
    bigQ_add_rV (lbl.[map_.[i]]) (bigQ_scal_rV (-1)%bigQ lbl.[origin]) in
  eq_array_bigQ (bigQ_mul_row_mx rV_i inv) (BigQUtils.delta_line n i 1%bigQ).

(* Definition inv_format_test (inv : array (array bigQ))
  (Po : Com.polyType):=
  (length inv == (Com.n Po)) &&
  arr_all (fun line=> (length line == (Com.n Po))) inv.

Definition map_test (lbl : BQvert_mapping) (map_ : array Uint63.int) (Po : Com.polyType):=
  [&& (length map_ == (Uint63.succ (Com.n Po))),
      arr_all (fun x=> (x < length lbl)%O) map_ &
      is_lti_sorted map_]. *)

Definition dim_full_test (lbl : BQvert_mapping)
  (map_ : array Uint63.int) (origin : Uint63.int) (inv : array (array bigQ)) 
  (Po : Com.polyType) :=
  [&&
    (length map_ == Com.n Po), 
    arr_all (fun x=> (x < length lbl)%O) map_,
    (origin < length lbl)%O &
    iall
      (fun i=> inverse_line_i lbl map_ origin inv (Com.n Po) i)
    (length map_)
  ].

Lemma dim_full_testE lbl map_ origin inv Po: 
  DFC.dim_full_test lbl map_ origin inv Po = 
  dim_full_test lbl map_ origin inv Po.
Proof.
repeat congr andb; rewrite ?eqEint //.
- by rewrite arr_allE; apply/eq_all=> ?; rewrite ltEint.
- rewrite /DFC.dim_full_test iallE; apply/eq_all=> i.
  rewrite /DFC.inverse_line_i /= eq_array_bigQE. 
  by rewrite bigQ_mul_row_mxE bigQ_add_rVE bigQ_scal_rVE.
Qed.

End DimensionFullEquiv.

(* --------------------------------------------------------------- *)

Module HirschUtils.

(*
  Given a correct witness vertex, 
  this function performs a BFS from this point
  to prove there is a path bigger than 
  the bound defined by the Hirsch Conjecture
*)

Definition diameter_check g (Po : Com.polyType) x :=
  [&& ((Com.n Po) <? (Com.m Po))%uint63, GraphUtils.mem_vertex g x &
      ((Com.m Po) - (Com.n Po) <? nat_to_int (DC.BFS g x))%uint63].

Definition diameter_exact g (Po : Com.polyType) k :=
  (nat_to_int (DC.diameter_BFS g) =? k)%uint63.


End HirschUtils.

Section Hirsch.

Definition diameter_check g (Po : Com.polyType) x :=
  [&& 
    ((Com.n Po) < (Com.m Po))%O, mem_vertex g x &
    (((Com.m Po) - (Com.n Po))%uint63 < nat_to_int (BFS g x))%O
  ].

Definition diameter_exact g (Po : Com.polyType) k :=
  (nat_to_int (diameter_BFS g) == k).

Section Equiv.

Lemma diameter_checkE g (Po : Com.polyType) x:
  HirschUtils.diameter_check g Po x = diameter_check g Po x.
Proof. by rewrite /HirschUtils.diameter_check BFSE mem_vertexE -!ltEint. Qed.

Lemma diameter_exactE g (Po : Com.polyType) k:
  HirschUtils.diameter_exact g Po k = diameter_exact g Po k.
Proof. by rewrite /HirschUtils.diameter_exact eqEint low_diameterE. Qed.

End Equiv.

End Hirsch.
