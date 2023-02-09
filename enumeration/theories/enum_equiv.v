From mathcomp Require Import all_ssreflect all_algebra finmap.
From Coq Require Import Uint63 PArray.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx barycenter.
From Polyhedra Require Import lrel polyhedron poly_base simplex.
Require Import enum_algo enum_proof graph high_graph img_graph extra_array extra_int rat_bigQ array_set diameter refinement.
Require Import NArith.BinNat NArith.BinNatDef.
From Bignums Require Import BigQ.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Num.Theory.

Local Notation "a .[ i ]" := (PArray.get a i).

(* --------------------------------------------------------------- *)

Section Refinement.

Section Relations.

Definition rel_basis (m' : nat) := 
  @rel_arr_set_r _ _ (@rel_int_ord m') (fun x y=> ltn (val x) (val y)).

Definition rel_point (m' n' : nat):=
  @rel_point_mx_col _ [realFieldType of rat] rat_bigQ n' (m'.+1).

Definition rel_lex_vert (m' n' : nat):=
  rel_couple (@rel_basis m') (@rel_point m' n').

Definition rel_lex_lbl_graph (m' n' : nat):=
  @rel_lbl_graph _ _ (@rel_lex_vert m' n').

Definition rel_lex_graph (m' n' : nat):=
  @rel_graph_r _ _ (@rel_lex_vert m' n').

Definition rel_poly (m' n' : nat):= 
  @rel_Po_r _ [realFieldType of rat] rat_bigQ m' n'.

Definition rel_vert (n' : nat):= @rel_point_cV _ _ rat_bigQ n'.

Definition rel_vert_graph (n' : nat):= 
  @rel_graph_r _ _ (@rel_vert n').

Definition rel_bound (m' n' : nat):=
  @rel_point_mx_row _ _ rat_bigQ n' m'.

Definition rel_inv (n' : nat):=
  @rel_point_mx_col _ _ rat_bigQ n' n'.


End Relations.
Section SpecFunc.

Definition spec_basis (m' : nat):=
  arr_to_set \o (arr_map (@int_to_ord m')).

Definition precond_basis (m' : nat) (a : array int):=
  (rel_sorted (fun x y=> (x < y)%O) a) /\
  (precond_array (fun x=> (int_to_nat x < m'.+1)%nat) a).

Lemma spec_func_basis (m' : nat):
  spec_func (@rel_basis m') (@spec_basis m') (@precond_basis m').
Proof. apply/spec_func_arr_to_set_r; [exact/rel_int_ord_lt|exact/spec_func_int_ord]. Qed.

Definition spec_point (m' n' : nat):=
  @arr_to_point_mx_col _ _ n' m'.+1 bigQ2rat_def.

Definition precond_point (m' n' : nat) (a : array (array bigQ)):=
  (precond_mx m'.+1 n' a /\ precond_array (fun x=> precond_array (fun _ => True) x) a).

Lemma spec_func_point (m' n' : nat):
  spec_func (@rel_point m' n') (@spec_point m' n') (@precond_point m' n').
Proof. by apply/spec_func_to_point_mx_col. Qed.

Definition spec_lex_vert (m' n' : nat) x:=
  (@spec_basis m' x.1, @spec_point m' n' x.2).

Definition precond_lex_vert (m' n' : nat) x:=
  @precond_basis m' x.1 /\ @precond_point m' n' x.2.

Lemma spec_func_lex_vert (m' n' : nat):
  spec_func (@rel_lex_vert m' n') (@spec_lex_vert m' n')
    (@precond_lex_vert m' n').
Proof. apply: spec_func_couple; [exact:spec_func_basis|exact:spec_func_point]. Qed.

Definition spec_lex_lbl_graph (m' n' : nat):=
  lbl_graph_to_high_lbl (@spec_lex_vert m' n').

Definition precond_lex_lbl_graph (m' n' : nat) gl:=
  (precond_lbl_graph gl /\ 
    (precond_struct gl.1 /\ 
    precond_array (@precond_lex_vert m' n') gl.2)).

Lemma spec_func_lex_lbl_graph (m' n' : nat):
  spec_func (@rel_lex_lbl_graph m' n') (@spec_lex_lbl_graph m' n')
    (@precond_lex_lbl_graph m' n').
Proof. exact/spec_func_lbl_graph/spec_func_lex_vert. Qed.

Definition spec_lex_graph (m' n' : nat):=
  high_lbl_to_final \o (@spec_lex_lbl_graph m' n').

Definition precond_lex_graph (m' n' : nat) gl:=
  precond_graph (fun x y=> lt_array_int x.1 y.1) 
  (@precond_lex_vert m' n') gl.

Lemma spec_func_lex_graph (m' n' : nat):
  spec_func (@rel_lex_graph m' n') (@spec_lex_graph m' n')
    (@precond_lex_graph m' n').
Proof.
apply/(spec_func_rel_graph_r (eqt:=(fun x y=> eq_array_int x.1 y.1)));
  [ | | |exact:spec_func_lex_vert].
- move=> y x z; apply/lt_array_int_trans.
- move=> x y /spec_func_lex_vert [/= x1X1 _] /spec_func_lex_vert [/= y1Y1 _].
  case/eqP=> /eqP + _; apply/eq_imply/esym/(rel_arr_set_r_eq _ _ _ x1X1 y1Y1).
  + exact/ltnn.
  + apply/ltn_trans.
  + move=> ?? h1 ?? h2; rewrite eqEint; apply/idP/idP.
    * by move/eqP=> /(congr1 int_to_nat); rewrite -h1 -h2=> /val_inj ->.
    * by move/eqP=> /(congr1 val); rewrite h1 h2=> /int_to_nat_inj ->.
- move=> x y /[dup]; rewrite {1}eq_array_intC=> yx xy. 
  split; [move:xy|move:yx]; apply/contraTN/lt_array_int_neq.
Qed.

Definition spec_poly (m' n' : nat) Po:=
  (@arr_to_point_mx_row _ _ m' n' bigQ2rat_def Po.1,
  @arr_to_point_cV _ _ m' bigQ2rat_def Po.2).

Definition precond_poly (m' n' : nat) Po:=
  (@precond_mx BigQ.bigQ m' n' Po.1 /\ precond_array (fun x=> precond_array (fun _ => True) x) Po.1) /\
  (@precond_len BigQ.bigQ m' Po.2 /\ precond_array (fun _ => True) Po.2).

Lemma spec_func_poly (m' n' : nat):
  spec_func (@rel_poly m' n') (@spec_poly m' n') (@precond_poly m' n').
Proof.
move=> x [Px1 Px2]; apply/rel_couple_comp; split=> /=.
- apply/spec_func_to_point_mx_row=> //; exact/Px1.
- apply/spec_func_to_point_cV=> //; exact/Px2.
Qed.

Definition spec_vert (n' : nat):= @arr_to_point_cV _ _ n' bigQ2rat_def.

Definition precond_vert (n' : nat) (a : array bigQ):=
  @precond_len BigQ.bigQ n' a /\ precond_array (fun _ => True) a.

Lemma spec_func_vert (n' : nat):
  spec_func (@rel_vert n') (@spec_vert n') (@precond_vert n').
Proof. exact/spec_func_to_point_cV. Qed.

Definition spec_vert_graph (n' : nat):=
  high_lbl_to_final \o (lbl_graph_to_high_lbl (@spec_vert n')).

Definition precond_vert_graph (n' : nat) gl:=
  precond_graph (BQltx_order) (@precond_vert n') gl.

Lemma spec_func_vert_graph (n' : nat):
  spec_func (@rel_vert_graph n')
  (@spec_vert_graph n') (@precond_vert_graph n').
Proof.
apply/(spec_func_rel_graph_r (eqt:=eq_array_bigQ)).
- exact/BQltx_order_trans.
- move=> x y /spec_func_vert xX /spec_func_vert yY.
  exact/eq_imply2/rel_cV_bqr_eq.
- move=> x y /[dup]; rewrite {1}eq_array_bigQC=> yx xy.
  split; [move: xy|move: yx]; exact/contraTN/BQltx_order_neq. 
- exact/spec_func_vert.
Qed.

Definition spec_bound (m' n' : nat) :=
  @arr_to_point_mx_row _ _ n' m' bigQ2rat_def.

Definition precond_bound (m' n' : nat) (a : array (array bigQ)):=
  (precond_mx n' m' a /\ precond_array (fun x=> precond_array (fun _=> True) x) a).

Lemma spec_func_bound (m' n' : nat):
  spec_func (@rel_bound m' n') (@spec_bound m' n') (@precond_bound m' n').
Proof. exact/spec_func_to_point_mx_row. Qed.

Definition spec_inv (n' : nat):=
  @arr_to_point_mx_col _ _ n' n' bigQ2rat_def.

Definition precond_inv (n' : nat) (a : array (array bigQ)):=
  (precond_mx n' n' a /\ precond_array (fun x=> precond_array (fun _=> True) x) a).

Lemma spec_func_inv (n' : nat):
  spec_func (@rel_inv n') (@spec_inv n') (@precond_inv n').
Proof. exact/spec_func_to_point_mx_col. Qed.

End SpecFunc.
Section AlgoSpec.

Lemma format_poly_mn_ge0 Po: poly_format Po -> 
  (0 < Com.n Po)%nat /\ (0 < Com.m Po)%nat.
Proof. by case/and4P=> ++ _ _; rewrite !ltEint_nat=> ??; split. Qed.

Context (Po : Com.polyType).
Hypothesis Po_format: poly_format Po.
Definition m' := (Com.m Po).-1.
Definition n' := (Com.n Po).-1.
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Lemma format_poly_mn : (m = Com.m Po) * (n = Com.n Po).
Proof. by case: (format_poly_mn_ge0 Po_format)=> ??; rewrite /m' /n' !prednK. Qed.

Lemma format_poly_precond: precond_poly m' n' Po.
Proof.
case/and4P: Po_format => _ _ len_b len_A.
split; split=> //.
- split=> /=; rewrite ?format_poly_mn // => i i_A.
  rewrite /precond_len format_poly_mn.
  by move/all_arr:len_A=> /(_ i i_A)/eqP ->.
- by rewrite /precond_len format_poly_mn; apply/esym/eqP.
Qed.

Section LexGraph.

Lemma lex_graph_format_precond g l: lex_graph_format Po g l ->
  precond_lex_graph m' n' (g,l).
Proof.
apply/precond_graphP=> -[bas pt] /andP /= [bas_format pt_format].
split.
- move:bas_format=> /=; apply:precond_array_setP=> x.
  by rewrite format_poly_mn ltEint_nat.
- split=> //=; move: pt_format; apply/precond_mxP; rewrite ?format_poly_mn //.
  rewrite succ_intE // /Com.m; exact:(length_lt_max Po.1).
Qed.

End LexGraph.

Section VertGraph.

Lemma vert_graph_format_precond g l: vert_graph_format Po g l ->
  precond_vert_graph n' (g,l).
Proof.
apply/precond_graphP=> x len_x; split=> //; rewrite /precond_len.
by rewrite format_poly_mn; apply/esym/eqP.
Qed.   

End VertGraph.

Section Bound.

Lemma bound_format_precond y: bound_format Po y ->
  precond_bound m' n' y.
Proof. by move=> h; split=> //; apply/(precond_mxP _ _ h); rewrite format_poly_mn. Qed.

End Bound.

Section Inv.

Lemma inv_format_precond y: inv_format Po y -> precond_inv n' y.
Proof. by move=> h; split=> //; apply/(precond_mxP _ _ h); rewrite format_poly_mn. Qed.

End Inv.

End AlgoSpec.
End Refinement.

(* --------------------------------------------------------------- *)

Section LexVerification.

Section Def.
Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.
Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Local Notation b_pert := (Simplex.b_pert b).

Definition set_Im : choiceType := [choiceType of {set 'I_m}].
Definition M_n := [choiceType of 'M[rat]_(n,1+m)].
Definition enum_type := [choiceType of (set_Im * M_n)%type].
 
Context (G : graph enum_type).

Definition card_verification (e : enum_type) := #|e.1| == n.
Definition feas_verification (e : enum_type) := e.2 \in Simplex.lex_polyhedron A b_pert.
Definition bas_verification (e : enum_type):= (row_submx A e.1) *m e.2 == row_submx b_pert e.1.
Definition vertex_verification (e : enum_type) := [&& card_verification e, feas_verification e & bas_verification e].

Definition inter_verification (e e': enum_type) := (#|e.1 :&: e'.1| == n').
Definition reg_verification (e : enum_type) := #|` successors G e| == n.
Definition struct_verification (e : enum_type) := reg_verification e && all (inter_verification e) (successors G e).

Definition high_enum_algo := 
  all vertex_verification (vertices G) &&
  all struct_verification (vertices G).

Lemma high_enum_algoE:
  high_enum_algo =
  [forall e : vertices G,
    [&& card_verification (fsval e),
        feas_verification (fsval e),
        bas_verification (fsval e),
        reg_verification (fsval e) &
        [forall e' : successors G (fsval e), inter_verification (fsval e) (fsval e')]
    ]
  ].
Proof.
apply/idP/idP.
- case/andP=> /allP vtx_verif /allP str_verif; apply/forallP=> x.
  move: (vtx_verif _ (fsvalP x)) (str_verif _ (fsvalP x)).
  case/and3P=> -> -> -> /andP [->] /allP int_verif.
  apply/and5P; split=> //; apply/forallP=> y.
  exact:(int_verif _ (fsvalP y)).
- move/forallP=> h; apply/andP; split; apply/allP=> x xG.
  + case/and5P: (h [`xG])=> /= ??? _ _; exact/and3P.
  + case/and5P: (h [`xG])=> /= _ _ _ ? /forallP int_verif.
    apply/andP; split=> //; apply/allP=> y yGx.
    exact:(int_verif [`yGx]).
Qed.
End Def.

Section RelLexGraph.

Context (m' n' : nat).

Lemma rel_lex_vert_bas l V: @rel_lex_vert m' n' l V->
  rel_basis l.1 V.1.
Proof. by case. Qed.

Lemma rel_lex_vert_point l V: @rel_lex_vert m' n' l V->
  rel_point l.2 V.2.
Proof. by case. Qed.

Lemma rel_basis_spec: rel_spec (@rel_basis m') eq.
Proof.
apply/rel_arr_set_r_spec=> x X Y xX xY; apply/val_inj.
by rewrite xX xY.
Qed.

Lemma rel_point_spec: rel_spec (@rel_point m' n') eq.
Proof. apply/rel_point_mx_col_spec/rat_bigQ_injr. Qed.

Lemma rel_lex_vert_spec: rel_spec (@rel_lex_vert m' n') eq.
Proof.
move: (rel_spec_couple rel_basis_spec rel_point_spec)=> h.
move=> x X Y xX xY; move/(_ _ _ _ xX xY): h.
by case: X {xX}=> ??; case: Y {xY}=> ?? [/= -> ->].
Qed.

End RelLexGraph.

Section LexEquivalence.
Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (Po : Com.polyType) (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).

Hypothesis Po_Ab : rel_poly Po (A,b).

Context (g : graph.graph) (l : Com.lex_mapping).
Context (G : high_graph.graph (enum_type m' n')).

Hypothesis gl_G : rel_lex_graph (g, l) G.

Lemma rel_lex_vert_m_max v V: @rel_lex_vert m' n' v V->
  (Com.m Po < max_length)%O.
Proof.
case=> _ /rel_point_mx_col_length; move: (rel_Po_r_m Po_Ab)=> -> Po_len.
apply/(@lt_le_trans _ _ (length v.2)); rewrite ?leEint ?leb_length //.
by rewrite ltEint_nat Po_len leqnn.
Qed.

Lemma card_bas_test_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V ->
  card_bas_test Po l i = card_verification V.
Proof.
move=> ig VG iV; rewrite /card_bas_test /card_verification.
apply/rel_int_eq; [|exact:(rel_Po_r_n Po_Ab)].
move/rel_lex_vert_bas: iV=> /rel_arr_set_r_length; apply. 
- by move=> x /=; rewrite ltnn.
- move=> y x z /=; apply/ltn_trans.
Qed.

Lemma sat_ineq_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V ->
  (rel_int_ord =~> @rel_rV_bqr n' =~> rat_bigQ =~> eq)
    (fun k lA lb=> sat_ineq (Com.m Po) k lA lb (Com.point l i))
    (fun k lA lb=> leqlex (row_mx lb%:M (row k (-1%:M))) (lA *m V.2)).
Proof.
move=> ig VG iV k K kK la LA laLA lb LB lbLB.
rewrite sat_ineqP; last first.
- move/rel_lex_vert_point: iV=> /rel_point_mx_col_length h.
  apply/int_to_nat_inj; rewrite -h (rel_Po_r_m Po_Ab).
  by rewrite length_succ.
- apply/rel_rV_bqr_lex.
  + rewrite -GRing.scaleN1r scale_scalar_mx GRing.mulr1.
    apply/rel_rV_bqr_pertline=> //; last exact/(rel_Po_r_m Po_Ab).
    exact:(rel_lex_vert_m_max iV).
  + apply/rel_mx_bqr_mul_col=> //; exact:rel_lex_vert_point.
Qed.

Lemma sat_test_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V ->
  sat_test Po l i = feas_verification A b V.
Proof.
move=> ig VG iV.
rewrite /sat_test /sat_Po /feas_verification !inE /iall.
under eq_forallb=> k do rewrite /Simplex.b_pert row_row_mx row_cV row_mul.
exact/(rel_Po_r_all_row (sat_ineq_equiv ig VG iV) Po_Ab).
Qed.

Lemma bas_eq_test_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V -> 
  bas_eq_test Po l i = bas_verification A b V.
Proof.
move=> ig VG iV.
rewrite /bas_eq_test /mask_eq /bas_verification.
rewrite -row_submx_mul -row_submx_eq.
apply:(rel_arr_set_r_iall (a:=(Com.bas l i)) (A:=V.1));
  last exact:(rel_lex_vert_bas iV).
move=> k K k_len kK.
apply/rel_point_rV_eq; [exact:rat_bigQ_eq| | ].
- rewrite row_mul; apply/rel_mx_bqr_mul_col;
    [exact:(rel_Po_r_row_A Po_Ab kK)|exact:rel_lex_vert_point].
- rewrite /Simplex.b_pert row_row_mx row_cV -GRing.scaleN1r scale_scalar_mx GRing.mulr1.
  apply/(rel_rV_bqr_pertline _ _ kK)=> //.
  + exact/(rel_lex_vert_m_max)/iV.
  + exact/(rel_Po_r_m Po_Ab).
  + exact:(rel_Po_r_row_b Po_Ab kK).
Qed.


Lemma regularity_test_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V -> regularity_test Po g i = reg_verification G V.
Proof.
move=> ig VG iV.
rewrite /regularity_test /reg_verification (rel_graph_r_succ_card _ gl_G ig) //.
+ by move: (rel_Po_r_n Po_Ab); rewrite /Com.n=> ->.
+ exact:rel_lex_vert_spec.
Qed.

Lemma vertex_consistent_equiv:
  vertex_consistent Po g l = all (vertex_verification A b) (vertices G).
Proof.
apply/(rel_graph_r_all _ gl_G)=> /= i V ig VG iV; do 2? congr andb.
- exact/card_bas_test_equiv.
- exact/sat_test_equiv.
- exact/bas_eq_test_equiv.  
Qed.

Lemma basI_test_equiv i V:
  mem_vertex g i -> V \in vertices G ->
  rel_lex_vert l.[i] V ->
  basI_test Po g l i = all (inter_verification V) (successors G V).
Proof.
move=> ig VG iV. 
apply/(rel_graph_r_nei_all _ _ gl_G ig VG iV).
- exact:rel_lex_vert_spec.
- move=> j W /= jg WG jW; rewrite /inter_verification /Com.n.
  apply/rel_int_eq. 
  + apply:rel_arr_set_r_inter; try exact:rel_lex_vert_bas;
      [exact:rel_int_ord_lt|move=> x /=; exact:ltnn|move=> y x z /=; exact:ltn_trans|].
    by move=> x y /=; rewrite -!leqNgt=> ??; apply/val_inj/anti_leq/andP; split.
  + move: (rel_Po_r_n Po_Ab); rewrite /rel_int pred_intE ?ltEint_nat -?(rel_Po_r_n Po_Ab) //.
Qed.

Lemma struct_consistent_equiv:
  struct_consistent Po g l = all (struct_verification G) (vertices G).
Proof.
apply/(rel_graph_r_all _ gl_G)=> i V /= ig VG iV; congr andb.
- exact: regularity_test_equiv.
- exact: basI_test_equiv.
Qed.

Lemma lex_certif_equiv :
  enum_algo Po g l = high_enum_algo A b G.
Proof. congr andb; [exact: vertex_consistent_equiv|exact: struct_consistent_equiv]. Qed.

End LexEquivalence.
End LexVerification.

(* --------------------------------------------------------------- *)

Section ImgGraphEquivalence.

Context (m' n' : nat).

Context (g_lex : graph.graph) (l_lex : Com.lex_mapping).
Context (G_lex : high_graph.graph (enum_type m' n')).

Hypothesis gG_lex : rel_lex_graph (g_lex, l_lex) G_lex.

Context (g_vert : graph.graph) (l_vert : array (array (BigQ.bigQ))).
Context (G_vert : high_graph.graph ([choiceType of 'cV[rat]_n'.+1])).

Hypothesis gG_vert : rel_vert_graph (g_vert, l_vert) G_vert.

Context (morph morph' : array int) (edge_inv : array (array (int * int))).

Definition phi (e : enum_type m' n') := col 0 e.2.

Lemma img_lex_graph_equiv:
  img_lex_graph morph morph' edge_inv g_lex l_lex g_vert l_vert ->
  G_vert = (phi) @/ G_lex.
Proof.
apply/rel_graph_r_img; [ | |exact:gG_lex|exact:gG_vert].
- apply: (rel_couple_func_snd (f:=(fun x=> x.[0%uint63])) (F:=(fun X=> col 0 X))).
  exact: (rel_point_mx_col_col0).
- exact/rel_point_cV_eq/rat_bigQ_eq.
Qed.
  
End ImgGraphEquivalence.

(* --------------------------------------------------------------- *)

Section PolyBoundedEquivalence.

Context (m' n' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).

Context (Po : Com.polyType) (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Hypothesis Po_Ab : rel_poly Po (A,b).

Context (y_pos y_neg : array (array (BigQ.bigQ))) (Y_pos Y_neg : 'M[rat]_(n,m)).
Hypothesis yY_pos : rel_bound y_pos Y_pos.
Hypothesis yY_neg : rel_bound y_neg Y_neg.

Definition high_certif_func x i r :=
  (r *m A == row i (x%:M)) && (0) <=m (r^T).

Definition high_certif_fold Y x:=
  [forall i : 'I_n, high_certif_func x i (row i Y)]. 

Definition high_poly_bounded:= 
  high_certif_fold Y_pos 1%R && high_certif_fold Y_neg (-1)%R.

Lemma bound_certif_func_equiv:
  (rat_bigQ =~> @rel_int_ord n' =~> @rel_point_rV _ _ rat_bigQ m' =~> eq)
  (fun x i r=> 
    eq_array_bigQ 
      (weighted_lines r Po.1)
      (BigQUtils.delta_line (Com.n Po) i x) &&
      arr_all BigQUtils.bigQ_ge0 r
  ) high_certif_func.
Proof.
move=> x X xX i I iI r R rR; congr andb.
- apply/rel_point_rV_eq; [exact:rat_bigQ_eq| | ].
  + apply/rel_mx_bqr_row_weighted_lines=> //.
    by move: Po_Ab=> /rel_couple_comp [].
  + apply/rel_rV_bqr_delta=> //; rewrite ?leEint ?leb_length //.
    apply/(rel_Po_r_n Po_Ab).
- pose F := fun (i : 'I_m) (r :rat) => (0 <= r)%R.
  pose f := fun (i : int) r => BigQUtils.bigQ_ge0 r.
  have fF: (rel_int_ord =~> rat_bigQ =~> eq) f F by move=> ?? _; exact/rat_bigQ_ge0.
  move: (rel_point_rV_iall fF rR); rewrite /f /F.
  suff ->: [forall j, 0 <= R ord0 j] = (0) <=m (R^T) by
    move=> <-; rewrite /arr_all /iall all_map; by elim: (irange0 (length _)).
  by apply/eq_forallb=> k; rewrite !mxE.
Qed.

Lemma bound_certif_fold_equiv:
  (@rel_bound m' n' =~> rat_bigQ =~> eq)
  (@bound_certif_fold Po) (high_certif_fold).
Proof.
move=> y Y yY x X xX; rewrite /bound_certif_fold /high_certif_fold.
move/rel_point_mx_row_iall: (bound_certif_func_equiv xX).
exact.
Qed.

Lemma poly_bounded_equiv:
  @bounded_Po_test Po y_pos y_neg = high_poly_bounded.
Proof. congr andb; exact/bound_certif_fold_equiv. Qed.


End PolyBoundedEquivalence.

(* --------------------------------------------------------------- *)

Section DimensionFullEquivalence.

Section DimFullLbl.

Context (m' n' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).

Context (Po : Com.polyType) (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Hypothesis Po_Ab: rel_poly Po (A,b).

Definition high_dim_full (V : array 'cV[rat]_n) 
  (Origin : int)
  (Map : array int) (Inv : 'M[rat]_n) :=
  [&&
    (n == length Map),
    arr_all (fun x=> (x < length V)%O) Map,
    (Origin < length V)%O &
    iall
      (fun i=> ((get V (get Map i))^T - (get V Origin)^T) *m Inv == 
      \row_j (int_to_nat i == j)%:R)
    (length Map)
  ].

Context (v : BQvert_mapping) (V : array 'cV[rat]_n).
Hypothesis vV : rel_array (rel_cV_bqr) v V.

Context (origin : Uint63.int) (map_ : array Uint63.int).
Context (inv : array (array bigQ)) (Inv : 'M[rat]_n).
Hypothesis invInv: rel_mx_bqr_col inv Inv.

Lemma dim_full_equivalence:
  dim_full_test v map_ origin inv Po = 
  high_dim_full V origin map_ Inv.
Proof.
rewrite /dim_full_test /high_dim_full /arr_all.
congr andb; first by rewrite (rel_Po_r_n Po_Ab) [RHS]eq_sym.
under eq_all=> x do rewrite (rel_array_length vV).
rewrite (rel_array_length vV) !andbA.
apply/andb_id2l=> /andP [/allP map_in] origin_in.
apply/eq_in_all=> i; rewrite mem_irangeE le0x /= => i_map. 
apply/rel_point_rV_eq; [exact:rat_bigQ_eq| | ].
- apply/rel_mx_bqr_mul_col=> //; apply/rel_rV_bqr_add.
  + move:map_in=> /(_ map_.[i]); rewrite map_f ?mem_irangeE ?i_map ?le0x //.
    move/(_ isT); rewrite -(rel_array_length vV).
    rewrite /rel_rV_bqr=> /(rel_array_r vV); exact/rel_point_rV_tr.
  + rewrite -GRing.scaleN1r; apply/rel_rV_bqr_scal=> //.
    move: origin_in; rewrite -(rel_array_length vV)=> /(rel_array_r vV).
    exact:(rel_point_rV_tr).
- apply:rel_rV_bqr_delta_bis=> //; rewrite ?(rel_Po_r_n Po_Ab) //.
  by rewrite leEint leb_length.
Qed.

End DimFullLbl.

Section DimFullFinalGraph.

Context (m' n' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).

Context (G : high_graph.graph [choiceType of Uint63.int]).
Context (L : array 'cV[rat]_n).
Context (G' : high_graph.graph [choiceType of 'cV[rat]_n]).
Hypothesis GLG' : rel_final_graph (G,L) G'.
Hypothesis GL_length : forall x, x \in vertices G = (x < length L)%O.

Context (origin : Uint63.int) (map_ : array Uint63.int).
Context (Inv : 'M[rat]_n).

Lemma dim_full_vtx_final_graph: 
  high_dim_full L origin map_ Inv ->
  exists x0, exists s : seq 'cV[rat]_n,
  [/\ x0 \in vertices G', {subset s <= vertices G'} &
    \dim (span [seq x - x0 | x <- s]) = n].
Proof.
case/and4P=> /eqP len_map /allP map_in origin_in /allP inv_eq.
exists L.[origin], [seq L.[i] | i <- arr_to_seq map_].
split.
- by rewrite -(gisof_vtx GLG') /=; apply/in_imfset; rewrite GL_length.
- move=> x /mapP [i i_map] ->.
  rewrite -(gisof_vtx GLG') /=; apply/in_imfset; rewrite GL_length.
  exact:map_in.
- set s := [seq _ | _ <- _]. 
  rewrite -[s]in_tupleE span_matrix_cV /=.
  have size_s: n = seq.size s by rewrite !size_map size_irange subn0.
  rewrite {11}size_s -mxrank_tr.
  apply/anti_leq; rewrite rank_leq_row /= row_leq_rank.
  apply/row_freeP; exists (castmx (erefl _, size_s) Inv).
  apply/row_matrixP=> i; rewrite row_mul -tr_col.
  set M := matrix_of_fun _ _.
  have ->: col i M = tnth (in_tuple s) i
    by apply/matrixP=> p q; rewrite /M !mxE ord1.
  rewrite (tnth_nth L.[origin]) /= /s=> [:i_n].
  rewrite (nth_map L.[origin]) ?(nth_map 0%uint63) 
    ?size_map ?size_arr_to_seq ?size_irange ?subn0 -?len_map;
    [ |abstract:i_n; by rewrite {10}size_s ltn_ord|exact:i_n|exact:i_n].
  rewrite nth_irange ?subn0 -?len_map // addn0 trmx_sub.
  move: (inv_eq (nat_to_int i)); rewrite mem_irangeE le0x /=. 
  rewrite ltEint_nat -len_map nat_to_intK ?i_n; 
    last (rewrite inE; apply/(ltn_trans i_n); rewrite len_map; exact/int_thresholdP).
  move=> /(_ isT)/eqP.
  move/(congr1 (castmx ((erefl _), size_s))); rewrite castmx_mul castmx_id.
  by move=> ->; apply/matrixP=> p q; rewrite castmxE !mxE /=.
Qed.

End DimFullFinalGraph.
Section DimFullGraph.

Context (m' n' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).

Context (Po : Com.polyType) (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Hypothesis Po_Ab: rel_poly Po (A,b).

Context (v : BQvert_mapping).
Context (origin : Uint63.int) (map_ : array Uint63.int).
Context (inv : array (array bigQ)) (Inv : 'M[rat]_n).
Hypothesis invInv: rel_inv inv Inv.

Context (g : graph.graph) (l : BQvert_mapping).
Context (G : high_graph.graph [choiceType of 'cV[rat]_n]).
Hypothesis glG : rel_vert_graph (g,l) G.

Lemma dim_full_vtx_graph :
  dim_full_test l map_ origin inv Po ->
  exists x0, exists s : seq 'cV[rat]_n,
  [/\ x0 \in vertices G, {subset s <= vertices G} &
    \dim (span [seq x - x0 | x <- s]) = n].
Proof.
case: glG=> -[G' L'] glGL GL'G.
case: (glGL)=> /= len_gl [/= gG' lL'].
rewrite (dim_full_equivalence Po_Ab lL' _ _ invInv).
apply/(dim_full_vtx_final_graph GL'G)=> i.
by rewrite -(rel_struct_vtx gG') -(rel_array_length lL') -len_gl.
Qed.

End DimFullGraph.

End DimensionFullEquivalence.

(* --------------------------------------------------------------- *)

Section DiameterCheckEquivalence.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (Po : Com.polyType) (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Hypothesis Po_Ab : rel_poly Po (A,b).

Definition high_diameter_check {T : choiceType} (G : graph T) (X : T):=
  [&& (n < m)%nat, (X \in vertices G) & (high_BFS G X > m - n)%nat].

Lemma high_diameter_check_struct x:
  (rel_structure =~> eq) 
    (fun g=> diameter_check g Po x)
    (fun G=> high_diameter_check G x).
Proof.
move=> g G gG; apply/idP/idP.
- case/and3P=> m_n xg m_sub_n; apply/and3P=> [:xG].
  split.
  + by rewrite (rel_Po_r_n Po_Ab) (rel_Po_r_m Po_Ab) -ltEint_nat.
  + abstract: xG; rewrite -?(rel_struct_vtx gG) //.
  + move: m_sub_n; rewrite (rel_struct_BFS gG) // /high_BFS BFSP //.
    rewrite ltEint_nat sub_intE // -(rel_Po_r_m Po_Ab) -(rel_Po_r_n Po_Ab).
    move/leq_trans; apply; exact/nat_to_int_le.
- case/and3P=> m_n xG mn_BFS [:xg m_n_int]; apply/and3P; split.
  + abstract: m_n_int; rewrite ltEint_nat.
    by rewrite -(rel_Po_r_m Po_Ab) -(rel_Po_r_n Po_Ab) //.
  + by abstract: xg; rewrite (rel_struct_vtx gG).
  + rewrite ltEint_nat sub_intE // -(rel_Po_r_m Po_Ab) -(rel_Po_r_n Po_Ab).
    apply/(leq_trans mn_BFS); rewrite (rel_struct_BFS gG) //.
    rewrite nat_to_intK // inE; apply/(@leq_ltn_trans (#|`vertices G|)).
    * rewrite high_BFSE //; apply/bigmax_leqP=> p _; exact/size_path_le.
    * rewrite (rel_struct_card gG); exact/int_thresholdP.
Qed.

Context {g : graph.graph} (l : array (array bigQ)).
Context (G : graph [choiceType of 'cV[rat]_n]).
Hypothesis gG: rel_vert_graph (g,l) G.
Context (x : int).

Lemma high_diameter_check_equiv:
  diameter_check g Po x ->
  (diameter G > m - n)%nat.
Proof.
case: gG=> -[G' L'] [_] [/= gG' _] GLG.
rewrite (high_diameter_check_struct x gG').
case/and3P=> _ ?; rewrite (gisof_high_BFSE GLG) //=.
move/leq_trans; apply; apply/high_BFS_diameter_le.
by rewrite -(gisof_vtx GLG) /=; apply/imfsetP; exists x.
Qed.

End DiameterCheckEquivalence.

(* --------------------------------------------------------------- *)

Section GraphN0.

Context (m' n' : nat).

Lemma graph_n0_equiv: 
  (@rel_lex_graph m' n' =~> eq) 
    (fun g=> lex_graph_n0 g.1) (fun G=> G != graph0 _).
Proof.
case=> g l G [[g' l']] [_] [/= gg' ll'] gl'G.
apply/idP/idP.
- move=> g0; apply/graph0Pn; exists l'.[0%uint63].
  rewrite -(gisof_vtx gl'G) /=; apply/imfsetP; exists 0%uint63=> //=.
  by rewrite -(rel_struct_vtx gg').
- case/graph0Pn=> x; rewrite -(gisof_vtx gl'G) /=.
  case/imfsetP=> k /=; rewrite -(rel_struct_vtx gg')=> + _.
  exact/le_lt_trans/le0x.
Qed.

End GraphN0.

(* Section LowPolyhedron.

Context (Po : Com.polyType).

Hypothesis Po_format : poly_format Po.

Definition m' := (Com.m Po).-1.
Definition n' := (Com.n Po).-1.
Definition m := m'.+1.
Definition n := n'.+1.


Definition A := \matrix_(i < m) (@bigQ_arr_to_rat_cV n Po.1.[nat_to_int i])^T.
Definition b := @bigQ_arr_to_rat_cV m Po.2.

Lemma m'E : m = Com.m Po.
Proof.
rewrite /m /m' prednK //; case/poly_format_ge0: Po_format. 
by rewrite !ltEint_nat. 
Qed.

Lemma n'E : n = Com.n Po.
Proof.
rewrite /n /n' prednK //; case/poly_format_ge0: Po_format.
by rewrite !ltEint_nat. 
Qed.

Lemma m'_max_int: (m < max_int_)%nat.
Proof.
rewrite m'E; rewrite -ltEint_nat; apply/(le_lt_trans (y:=max_length)).
- by rewrite leEint leb_length.
- by rewrite max_length_lt.
Qed.

Lemma m'_max: (Com.m Po < max_int_)%O.
Proof. by rewrite ltEint_nat -m'E m'_max_int. Qed.

Lemma m'_threshold: (m < int_threshold)%nat.
Proof. rewrite m'E; exact/int_thresholdP. Qed.

Lemma int_threshold_ord_m' (i : 'I_m): val i \in gtn int_threshold.
Proof.
rewrite inE; apply/(@ltn_trans m); rewrite ?ltn_ord //.
rewrite m'E; exact/int_thresholdP.
Qed.

Lemma int_threshold_ord_n' (i : 'I_n): val i \in gtn int_threshold.
Proof.
rewrite inE; apply/(@ltn_trans n); rewrite ?ltn_ord //.
rewrite n'E; exact/int_thresholdP.
Qed.

Definition b_pert := Simplex.b_pert b.
Definition splx_type :=
  Simplex.feasible_basis_choiceType A b_pert.


Definition r_Po : Prop :=
  [/\ m = length Po.1, rat_bigQ_cV Po.2 b &
  (forall i : 'I_(m), rat_bigQ_rV Po.1.[nat_to_int i] (row i A))].


Lemma Po_base : r_Po.
Proof.
Admitted.
(* split; rewrite ?m'E //; move=> i; split.
- apply/rat_bigQ_rVP; split.
  + move/dim_Po_testP: Po_format=> /(_ (nat_to_int i)).
    rewrite ltEint_nat -m'E nat_to_intK ?int_threshold_ord_m' // ltn_ord.
    by case/(_ isT)=> ->; rewrite n'E.
  + by move=> j; rewrite !mxE.
- apply/rat_bigQ_rVP; split.
  + move/dim_Po_testP: Po_format=> /(_ (nat_to_int i)).
    rewrite ltEint_nat -m'E nat_to_intK ?ltn_ord ?int_threshold_ord_m' //.
    case/(_ isT)=> _ ->; rewrite add1n m'E succ_intE ?ltEint_nat -?m'E ?m'_max_int //.
  + move=> j; rewrite !mxE.
    case: splitP=> [j' ->|]; rewrite ?(ord1_eq0 j') ?mxE //.
    move=> k ->; rewrite !mxE.
    move/b_pert_testP: Po_format=> /(_ (nat_to_int i) (nat_to_int (1 + k))).
    rewrite !ltEint_nat -m'E nat_to_intK ?int_threshold_ord_m' //.
    move/(_ (ltn_ord _)); rewrite add1n -nat_to_intS.
    rewrite !succ_intE ?ltEint_nat -?m'E ?m'_max_int //; last
      (apply/(@ltn_trans (Com.m Po)); rewrite -?m'E ?m'_max_int // nat_to_intK // int_threshold_ord_m' //).
    rewrite ltnS leq0n /= ltnS nat_to_intK ?int_threshold_ord_m' // ltn_ord=> /(_ isT).
    case/boolP: (i == k)=> /=.
    * move/eqP=> ->; rewrite eqxx=> h; apply/eqP; move: h.
      case: (BigQ.BigQ.eq_equiv)=> _ /[swap] _ /[apply].
      by apply/rat_bigQEl.
    * move=> i_n_k; set S := _ == _.
      suff ->: S = false.
      - move=> h; apply/eqP; move: h.
        case: (BigQ.BigQ.eq_equiv)=> _ /[swap] _ /[apply]; exact/rat_bigQEl.
      apply/negP=> /eqP /(congr1 int_to_nat); rewrite !succ_intE ?ltEint_nat;
        try (apply/(@ltn_trans m'.+1); rewrite ?m'_max_int //?nat_to_intK // int_threshold_ord_m' //).
      move/succn_inj; rewrite !nat_to_intK ?int_threshold_ord_m' //.
      by move/val_inj/eqP; rewrite eq_sym (negPf i_n_k).
Qed. *)

Lemma r_Po_A (i : 'I_m): rat_bigQ_rV Po.1.[nat_to_int i] (row i A).
Proof. by case: Po_base=> _ _ /(_ i). Qed.

Lemma r_Po_b: rat_bigQ_cV Po.2 b.
Proof. by case: Po_base. Qed.

End LowPolyhedron.

Section LexInput.

Context (Po : Com.polyType) (g_lex : graph.graph) (lbl_lex : BQlex_mapping).

Hypothesis Po_format : poly_format Po.
Hypothesis format_h : format_test Po g_lex lbl_lex.

Local Notation m' := (m' Po).
Local Notation n' := (n' Po).
Local Notation m := (m Po).
Local Notation n := (n Po).

Section ConversionFunction.

Context (i : int).
Hypothesis i_g_lex : mem_vertex g_lex i.

Definition bas_i := Com.bas lbl_lex i.
Definition pt_i := Com.point lbl_lex i.

Section Preset.

Definition set_i := @arr_to_set_ord m bas_i.

Lemma bas_i_is_index j: (j < length bas_i)%O -> (bas_i.[j] < m)%nat.
Proof.
move: (lex_format_bas_is_bas format_h)=> /(_ i j i_g_lex).
by rewrite !ltEint_nat m'E.
Qed.

Lemma bas_i_is_sorted: lti_sorted bas_i.
Proof. exact: (lex_format_bas_is_sorted format_h i_g_lex). Qed.

Lemma set_i_rel_bas_i : array_set_ord bas_i set_i.
Proof. apply/arr_to_set_ordP; [exact: m'_threshold | exact: bas_i_is_index]. Qed.

End Preset.
Section Point.

Definition mat_i := @bigQ_mat_to_rat_mat (n) (1+m) pt_i.

Lemma length_pt_i : m.+1 = length pt_i.
Proof.
move: (lex_format_point_cols format_h i_g_lex)=> ->.
rewrite m'E ?succ_intE //. 
exact: (length_lt_max Po.1).
Qed.

Lemma mat_iP: rat_bigQ_mx_col pt_i mat_i.
Proof.
apply/BQ2R_matP_cast=> [|j j_len]; rewrite -?length_pt_i //.
move: (lex_format_point_rows format_h)=> /(_ i i_g_lex) /(_ (nat_to_int j)).
by rewrite int_to_natK=> /(_ j_len) ->; rewrite n'E.
Qed.

End Point.
End ConversionFunction.

Lemma g_lex_0 : mem_vertex g_lex 0%uint63.
Proof. move: (lex_format_prop0 format_h); exact/is_emptyPn. Qed.

Definition G_lex_func i : (enum_type m' n') := (set_i i, mat_i i).

Definition G_lex : (high_graph.graph (enum_type m' n')) := G_lex_func @° (to_graph_struct g_lex).

Lemma G_lex_func_inj: {in vertices (to_graph_struct g_lex) &, injective G_lex_func}.
Proof.
move=> x y; rewrite !to_graph_vtx=> x_g_lex y_g_lex.
move/(congr1 fst)=> /= set_ij.
apply/(lex_format_bas_inj format_h)=> //; apply/array_set_ord_inj; 
  [|..|exact:set_ij]; first [exact:bas_i_is_sorted|exact:set_i_rel_bas_i].
Qed.

Lemma G_lex_vtx:
  G_lex_func @` vertices (to_graph_struct g_lex) = vertices G_lex.
Proof. by rewrite vtx_img_graph. Qed.

Lemma G_lex_edge:
  {in vertices (to_graph_struct g_lex) &, forall x y,
  edges (to_graph_struct g_lex) x y =
  edges G_lex (G_lex_func x) (G_lex_func y)}.
Proof.
move=> i j; rewrite !to_graph_vtx=> i_g_lex j_g_lex.
rewrite to_graph_edge ?to_graph_vtx //.
apply/idP/idP.
- move=> g_lex_ij; apply/edge_img_graph; exists i, j; split; rewrite ?G_lex_funcP //.
  by rewrite to_graph_edge ?to_graph_vtx.
- case/edge_img_graph=> i' [j'] [++ /[dup] g_lex_ij' /edge_vtxlr [i'_g_lex j'_g_lex]].
  move: i'_g_lex j'_g_lex g_lex_ij'; rewrite !to_graph_vtx=> i'_g_lex j'_g_lex. 
  rewrite to_graph_edge ?to_graph_vtx // => g_lex_ij'.
  move/G_lex_func_inj; rewrite !to_graph_vtx => <- //.
  by move/G_lex_func_inj; rewrite !to_graph_vtx => <-.
Qed.


Lemma G_lex_gisof : gisof (to_graph_struct g_lex) G_lex G_lex_func.
Proof.
apply/gisofE; split.
- exact: G_lex_func_inj.
- exact: G_lex_vtx.
- exact: G_lex_edge.
Qed.

Definition rel_G_lex := fun e (E : enum_type m' n') => @array_set_ord m e.1 E.1 /\ @rat_bigQ_mx_col n (1+m) e.2 E.2.

Lemma rel_G_lexP : forall i, mem_vertex g_lex i -> rel_G_lex lbl_lex.[i] (G_lex_func i).
Proof.
move=> i i_g_lex; split.
- exact: set_i_rel_bas_i.
- exact: mat_iP.
Qed.

Lemma correct_lbl_lex : correct_label g_lex lbl_lex.
Proof. exact:(lex_format_correct_label format_h). Qed.

Lemma G_lex_repr_g_lex: repr_graph g_lex lbl_lex G_lex G_lex_func rel_G_lex.
Proof. split; [exact:correct_lbl_lex|exact:G_lex_gisof|exact:rel_G_lexP]. Qed.  


End LexInput.

Section LexCertif.

Context (Po : Com.polyType) (g_lex : graph.graph) (lbl_lex : BQlex_mapping).

Hypothesis Po_format : poly_format Po.
Hypothesis format_h : format_test Po g_lex lbl_lex.

Local Notation m' := (m' Po).
Local Notation n' := (n' Po).
Local Notation m := (m Po).
Local Notation n := (n Po).
Local Notation A := (A Po).
Local Notation b := (b Po).

Context (G : high_graph.graph (enum_type m' n')) (conv : int -> (enum_type m' n')).

Hypothesis g_lex_repr: repr_graph g_lex lbl_lex G conv (@rel_G_lex Po).

Lemma g_lex_repr_bas i: mem_vertex g_lex i->
  array_set_ord (Com.bas lbl_lex i) (conv i).1.
Proof.
move: (repr_graph_rel g_lex_repr)=> /[apply].
by case.
Qed.

Lemma g_lex_repr_point i: mem_vertex g_lex i->
  rat_bigQ_mx_col (Com.point lbl_lex i) (conv i).2.
Proof.
move: (repr_graph_rel g_lex_repr)=> /[apply].
by case.
Qed.

Lemma card_verif i: mem_vertex g_lex i ->
  card_bas_test Po lbl_lex i -> card_verification (conv i).
Proof.
move=> i_g_lex; rewrite /card_bas_test /card_verification /=.
case: (repr_graph_rel g_lex_repr i_g_lex)=> + _.
move/array_set_ord_card=> ->; rewrite ?(lex_format_bas_is_sorted format_h i_g_lex) //.
by move/eqP=> ->; rewrite -n'E.
Qed.

Lemma feas_verif i: mem_vertex g_lex i ->
  sat_test Po lbl_lex i -> feas_verification A b (conv i).
Proof.
Admitted.
(* move=> i_g_lex; rewrite /sat_test /feas_verification inE=> sat_h.
apply/forallP=> k.
have int_k_Po: (nat_to_int k < length Po.1)%O by 
  rewrite ltEint_nat nat_to_intK ?int_threshold_ord_m' -?m'E.
move/(lex_sat_Po int_k_Po): sat_h; rewrite sat_ineqP; last first.
  exact: (lex_format_point_cols format_h).
move: (r_Po_A Po_format k) (g_lex_repr_point i_g_lex).
move/BQR_rV_M_mul=> /[apply]; rewrite row_mul.
move: (r_Po_b Po_format k). /BQR_lex_order /[apply] ->.
Qed. *)

Lemma bas_verif i: mem_vertex g_lex i->
  bas_eq_test Po lbl_lex i -> bas_verification A b (conv i).
Proof.
Admitted.
(* move=> i_g_lex; rewrite /bas_eq_test /bas_verification=> bas_eq_h.
apply/eqP; rewrite -row_submx_mul; apply/row_submx_row_matrixP.
move=> k /(array_set_ord_mem (g_lex_repr_bas i_g_lex)).
case=> j /= j_len j_eq.
move/lex_mask_eq: bas_eq_h=> /(_ j j_len); rewrite /sat_eq.
move: (r_Po_b Po_format k); rewrite -j_eq int_to_natK.
move: (r_Po_A Po_format k) (g_lex_repr_point i_g_lex).
move/BQR_rV_M_mul=> /[apply]; rewrite -j_eq int_to_natK.
by move/BQR_rV_injl=> /[apply] /[apply]; rewrite row_mul.
Qed. *)

Lemma inter_verif i j: 
  mem_vertex g_lex i-> mem_vertex g_lex j->
  mem_edge g_lex i j->
  basI_test Po g_lex lbl_lex i -> inter_verification (conv i) (conv j).
Proof.
move=> i_g_lex j_g_lex g_lex_ij.
move/(lex_basI i_g_lex j_g_lex g_lex_ij).
move: (lex_format_bas_is_sorted format_h i_g_lex).
move: (lex_format_bas_is_sorted format_h j_g_lex).
move: (g_lex_repr_bas i_g_lex) (g_lex_repr_bas j_g_lex).
move/parrayI_final_ord=> /[apply] /[apply] /[apply].
rewrite /inter_verification => -> ->.
by rewrite pred_intE //; case: (poly_format_ge0 Po_format).
Qed.

Lemma reg_verif i: mem_vertex g_lex i->
  regularity_test Po g_lex i -> reg_verification G (conv i).
Proof.
move=> i_g_lex /lex_regularity.
rewrite /reg_verification (repr_graph_card_succ g_lex_repr) //. 
- by (move=> ->; rewrite -n'E).
- move=> j j_g_lex; exact/(lex_format_nei_sort format_h).
- move=> j k j_g_lex; exact/(lex_format_valid_nei format_h).
Qed.

Lemma enum_algo_correct: 
  enum_algo Po g_lex lbl_lex-> high_enum_algo A b G.
Proof.
case/andP=> /compute_testP vtx_h /compute_testP struct_h.
apply/forallP=> x; move: (fsvalP x).
case/(repr_graph_vtx_high g_lex_repr)=> i i_g_lex <-.
case/and3P: (vtx_h i i_g_lex)=> ???.
case/andP: (struct_h i i_g_lex)=> ??.
apply/and5P; split;
  [ exact:card_verif | exact:feas_verif | exact:bas_verif | exact:reg_verif |].
apply/forallP=> y; move: (fsvalP y); rewrite in_succE.
move=> /[dup] /edge_vtxlr [iG yG] /(repr_graph_edge_high g_lex_repr iG yG).
case=> i' [j'] [i'_g_lex j'_g_lex + -> g_lex_ij'].
move/(repr_graph_conv_inj g_lex_repr i_g_lex i'_g_lex)=> i_eq.
by apply/inter_verif=> //; rewrite i_eq.
Qed.

End LexCertif.

Section ImageGraph.

End ImageGraph.


(* Section Validation.

Context (Po : LFC.polyType) (morf morf' : array int) (t : array (array (int * int))).
Context (gl : graph.graph) (lbll : BQlex_mapping).
Context (gr : graph.graph) (lblr : BQvert_mapping).
Context (cert : bound_certificates).
Context (map_ : array Uint63.int) (inv : LFC.U).
Context (start : Uint63.int).

Hypothesis format_h : format_test Po gl lbll.
Hypothesis enum_h : enum_algo Po gl lbll.
Hypothesis quot_h : BQquot gl gr lbll lblr morf morf' t.
Hypothesis Po_format : dim_Po_test Po.
Hypothesis Po_bound: bounded_Po_test Po cert.
Hypothesis Po_b_pert: b_pert_Po_test Po.
Hypothesis Po_dim: dim_full_test lblr map_ inv Po.
Hypothesis hirsch_check : diameter_check gr Po start.

Definition m' := (LFC.m Po).-1.
Definition n' := (LFC.n Po).-1.
Definition m := m'.+1.
Definition n := n'.+1.


Definition A := \matrix_(i < m) (@bigQ_arr_to_rat_cV n Po.[nat_to_int i].1)^T.
Definition b := \col_(i < m) bigQ2rat_def Po.[nat_to_int i].2.[0%uint63].

Lemma m'E : m = LFC.m Po.
Proof. by rewrite /m /m' prednK //; case/dim_Po_testP_ge0: Po_format. Qed.

Lemma n'E : n = LFC.n Po.
Proof. by rewrite /n /n' prednK //; case/dim_Po_testP_ge0: Po_format. Qed.

Lemma m'_max_int: (m < max_int_)%nat.
Proof.
rewrite m'E; rewrite -ltEint_nat; apply/(le_lt_trans (y:=max_length)).
- by rewrite leEint leb_length.
- by rewrite max_length_lt.
Qed.

Lemma m'_max: (LFC.m Po < max_int_)%O.
Proof. by rewrite ltEint_nat -m'E m'_max_int. Qed.

Lemma int_threshold_ord_m' (i : 'I_m): val i \in gtn int_threshold.
Proof.
rewrite inE; apply/(@ltn_trans m); rewrite ?ltn_ord //.
rewrite m'E; exact/int_thresholdP.
Qed.

Lemma int_threshold_ord_n' (i : 'I_n): val i \in gtn int_threshold.
Proof.
rewrite inE; apply/(@ltn_trans n); rewrite ?ltn_ord //.
rewrite n'E; exact/int_thresholdP.
Qed.

Definition b_pert := Simplex.b_pert b.
Definition splx_type :=
  Simplex.feasible_basis_choiceType A b_pert.


Definition r_Po : Prop :=
  m = length Po /\
  (forall i : 'I_(m), 
    [/\
    rat_bigQ_rV Po.[nat_to_int i].1 (row i A) & 
    rat_bigQ_rV Po.[nat_to_int i].2 (row i b_pert)
    ]).


Lemma Po_base : r_Po.
Proof.
split; rewrite ?m'E //; move=> i; split.
- apply/rat_bigQ_rVP; split.
  + move/dim_Po_testP: Po_format=> /(_ (nat_to_int i)).
    rewrite ltEint_nat -m'E nat_to_intK ?int_threshold_ord_m' // ltn_ord.
    by case/(_ isT)=> ->; rewrite n'E.
  + by move=> j; rewrite !mxE.
- apply/rat_bigQ_rVP; split.
  + move/dim_Po_testP: Po_format=> /(_ (nat_to_int i)).
    rewrite ltEint_nat -m'E nat_to_intK ?ltn_ord ?int_threshold_ord_m' //.
    case/(_ isT)=> _ ->; rewrite add1n m'E succ_intE ?ltEint_nat -?m'E ?m'_max_int //.
  + move=> j; rewrite !mxE.
    case: splitP=> [j' ->|]; rewrite ?(ord1_eq0 j') ?mxE //.
    move=> k ->; rewrite !mxE.
    move/b_pert_testP: Po_b_pert=> /(_ (nat_to_int i) (nat_to_int (1 + k))).
    rewrite !ltEint_nat -m'E nat_to_intK ?int_threshold_ord_m' //.
    move/(_ (ltn_ord _)); rewrite add1n -nat_to_intS.
    rewrite !succ_intE ?ltEint_nat -?m'E ?m'_max_int //; last
      (apply/(@ltn_trans (LFC.m Po)); rewrite -?m'E ?m'_max_int // nat_to_intK // int_threshold_ord_m' //).
    rewrite ltnS leq0n /= ltnS nat_to_intK ?int_threshold_ord_m' // ltn_ord=> /(_ isT).
    case/boolP: (i == k)=> /=.
    * move/eqP=> ->; rewrite eqxx=> h; apply/eqP; move: h.
      case: (BigQ.BigQ.eq_equiv)=> _ /[swap] _ /[apply].
      by apply/rat_bigQEl.
    * move=> i_n_k; set S := _ == _.
      suff ->: S = false.
      - move=> h; apply/eqP; move: h.
        case: (BigQ.BigQ.eq_equiv)=> _ /[swap] _ /[apply]; exact/rat_bigQEl.
      apply/negP=> /eqP /(congr1 int_to_nat); rewrite !succ_intE ?ltEint_nat;
        try (apply/(@ltn_trans m'.+1); rewrite ?m'_max_int //?nat_to_intK // int_threshold_ord_m' //).
      move/succn_inj; rewrite !nat_to_intK ?int_threshold_ord_m' //.
      by move/val_inj/eqP; rewrite eq_sym (negPf i_n_k).
Qed.

Section ToEnumType.

Definition arr_to_set_ord (a : array int) : {set 'I_m} := [set j : 'I_m | nat_to_int j \in arr_to_set a].
Definition to_enum_type (e : LFC.algolabel) := (arr_to_set_ord e.1, @bigQ_mat_to_rat_mat n (1+m) e.2).
Context (a : array int).

Hypothesis a_m : forall i, (i < length a)%O -> (a.[i] < m)%nat.

Lemma arr_to_set_ordP : array_set_ord a (arr_to_set_ord a).
Proof.
apply/set_int_ordP; move=> x; apply/idP/idP.
- case/imageP=> j /[swap] ->; rewrite arr_to_setP.
  case/mapP=> i; rewrite mem_irangeE le0x /= => /[dup] i_len /a_m ai_m ->.
  apply/imageP; exists (Ordinal ai_m)=> //.
  rewrite inE int_to_natK arr_to_setP.
  by apply/mapP; exists i=> //; rewrite mem_irangeE le0x i_len.
- case/imageP=> /= j /[swap] ->; rewrite inE=> j_arr2set.
  apply/mapP; exists (nat_to_int j); rewrite ?mem_enum //.
  rewrite nat_to_intK // inE; apply/(@ltn_trans m)=> //.
  rewrite m'E; exact/int_thresholdP.
Qed.

End ToEnumType.

Section LexCertCorrect.

Definition G_lex := (fun i=> to_enum_type lbll.[i]) @° (to_graph_struct gl).

Section Vert.

Context (i : Uint63.int).
Hypothesis ig : mem_vertex gl i.

Definition bas_i := LFC.bas lbll i.
Definition pt_i := LFC.point lbll i.

Lemma set_ord_i_P :
  array_set_ord bas_i (arr_to_set_ord bas_i).
Proof.
apply/arr_to_set_ordP=> j j_len.
rewrite m'E -ltEint_nat.
apply/(enum_bas_is_bas format_h ig).
by rewrite -(enum_card_bas format_h ig).
Qed.

Definition mat_i := @bigQ_mat_to_rat_mat (n) (1+m) pt_i.

Lemma bqr_mat_i : rat_bigQ_mx_col pt_i mat_i.
Proof.
split; last (move=> j; apply/rat_bigQ_cVP; split).
- move: (enum_dim_point format_h)=> /(_ i ig) [-> _].
  rewrite m'E succ_intE // /LFC.m.
  exact: (length_lt_max Po).
- move: (enum_dim_point format_h)=> /(_ i ig) [_ /(_ (nat_to_int j))].
  rewrite ltEint_nat succ_intE ?(length_lt_max Po) //.
  rewrite nat_to_intK ?inE; first move=> ->; rewrite ?n'E //.
  + by rewrite -m'E -[X in (_ <= X)%nat]add1n.
  + apply/(ltn_trans (ltn_ord _)); rewrite add1n m'E -succ_intE ?(length_lt_max Po) //. 
    exact/int_thresholdP.
- by move=> k; rewrite !mxE.
Qed.

Lemma mat_iP : (row_submx A (arr_to_set_ord bas_i)) *m mat_i = row_submx b_pert (arr_to_set_ord bas_i).
Proof.
rewrite -row_submx_mul; apply/row_submx_row_matrixP.
move=> k k_bas_i.
move: (enum_mask_eq enum_h)=> /(_ i ig).
move: k_bas_i; rewrite inE=> /imsetP [j].
case/(nthP (default bas_i))=> k'; rewrite size_arr_to_seq=> k'_lbli.
rewrite nth_arr_to_seq // => <- k_eq.
move/(_ (nat_to_int k')).
rewrite ltEint_nat nat_to_intK ?inE; try exact/(ltn_trans k'_lbli)/int_thresholdP.
move/(_ k'_lbli); rewrite -k_eq /LCA.sat_eq row_mul [Po.[_]]surjective_pairing.
move/BQR_rV_injl; apply; first apply/BQR_rV_M_mul.
- by case: Po_base=> _ /(_ k) [].
- exact: bqr_mat_i.
- by case: Po_base=> _ /(_ k) [].
Qed.

Lemma feas_mat_i: mat_i \in Simplex.lex_polyhedron A b_pert.
Proof.
apply/forallP=> k.
move: (enum_sat_Po enum_h)=> /(_ (nat_to_int k)).
rewrite ltEint_nat ?nat_to_intK ?inE;
  try (apply/(@ltn_trans m)=> //; rewrite r_Po_m; exact/int_thresholdP).
case: Po_base=> <- /(_ k) [bqr_kA bqr_kb] /(_ (ltn_ord _) i ig).
move: (sat_ineqP Po.[nat_to_int k] pt_i).
rewrite row_mul [Po.[_]]surjective_pairing=> ->.
- have:= (BQR_lex_order bqr_kb (BQR_rV_M_mul bqr_kA bqr_mat_i)).
  by move=> ->.
- move: (enum_dim_point format_h)=> /(_ i ig) [-> _].
  move/dim_Po_testP: Po_format=> /(_ (nat_to_int k)).
  rewrite ltEint_nat nat_to_intK ?inE;
    try (apply/(@ltn_trans m)=> //; rewrite r_Po_m; exact/int_thresholdP).
  rewrite -m'E=> /(_ (ltn_ord _)) [_ ->] //.
  + by move: (int_threshold_ord_m' k); rewrite inE.
  + by move: (int_threshold_ord_m' k); rewrite inE.
Qed.

End Vert.

Section Edge.

Lemma to_enum_type_inj i j:
  mem_vertex gl i -> mem_vertex gl j ->
  to_enum_type lbll.[i] = to_enum_type lbll.[j] -> i = j.
Proof.
move=> ig jg [+ _].
move/array_set_ord_inj=> /(_ (LCA.bas lbll i) (LCA.bas lbll j)) h.
apply/(enum_bas_inj format_h ig jg)/h. 
- exact/(enum_bas_is_sorted format_h).
- exact/(enum_bas_is_sorted format_h).
- exact:(set_ord_i_P ig). 
- exact:(set_ord_i_P jg). 
Qed.

End Edge.

Lemma gG_lex : 
  gisof (to_graph_struct gl) G_lex (fun i => to_enum_type lbll.[i]).
Proof.
apply/gisofE; split.
- move=> i j; rewrite vtx_mk_graph !in_fset /= !mem_irangeE !le0x /=.
  rewrite ltEint; exact: to_enum_type_inj.
- by rewrite vtx_img_graph.
- move=> i j; rewrite !to_graph_vtx=> i_gl j_gl.
  rewrite to_graph_edge ?to_graph_vtx //; apply/idP/idP.
  + move=> mem_edge; apply/edge_img_graph; exists i,j.
    by split=> //; rewrite to_graph_edge ?to_graph_vtx.
  + case/edge_img_graph=> i' [j'] [++ edg_ij'].
    move/to_enum_type_inj=> + /to_enum_type_inj.
    move=> <- //; first move=> <- //.
    * move: (edg_ij'); rewrite to_graph_edge //; 
        [exact:(edge_vtxl edg_ij')|exact:(edge_vtxr edg_ij')].
    * by move: (edge_vtxr edg_ij'); rewrite to_graph_vtx.
    * by move: (edge_vtxl edg_ij'); rewrite to_graph_vtx.
Qed.

Lemma G_lex_prop0 : G_lex != graph0 (enum_type m' n').
Proof.
apply/graph0Pn; exists (to_enum_type lbll.[0]).
rewrite -(gisof_bij gG_lex); apply/in_imfset=> /=.
rewrite to_graph_vtx /mem_vertex lt_neqAle le0x andbT.
by move: (enum_prop0 enum_h); rewrite /is_empty eq_sym.
Qed.

Lemma card_verif (e : vertices G_lex) : card_verification (fsval e).
Proof.
move: (fsvalP e); rewrite -{2}(gisof_bij gG_lex).
case/imfsetP=> /= i; rewrite to_graph_vtx=> ig ->.
rewrite /card_verification /=.
move/set_int_ord_card: (set_ord_i_P ig) => <-.
rewrite /arr_to_set card_imset //.
move: (enum_bas_is_sorted format_h)=> /(_ i ig).
move=> /lti_sorted_uniq /card_uniqP ->.
rewrite size_arr_to_seq.
by move: (enum_card_bas format_h)=> /(_ i ig) ->; rewrite -n'E.
Qed.

Lemma bas_verif (e : vertices G_lex) : bas_verification A b (fsval e).
Proof.
move: (fsvalP e); rewrite -{2}(gisof_bij gG_lex).
case/imfsetP=> /= i; rewrite to_graph_vtx=> ig ->.
rewrite /bas_verification /=.
exact/eqP/mat_iP.
Qed.

Lemma feas_verif (e : vertices G_lex) : feas_verification A b (fsval e).
Proof.
move: (fsvalP e); rewrite -{2}(gisof_bij gG_lex).
case/imfsetP=> /= i; rewrite to_graph_vtx=> ig ->.
rewrite /feas_verification /=.
exact: feas_mat_i.
Qed.

Lemma reg_verif (e : vertices G_lex) : reg_verification G_lex (fsval e).
Proof.
rewrite /reg_verification.
move: (fsvalP e); rewrite -{2}(gisof_bij gG_lex).
case/imfsetP=> /= i /[dup] ig /(gisof_succ gG_lex) /[swap] -> ->.
rewrite to_graph_succ_nei // !card_in_imfset //=.
- rewrite to_graph_vtx in ig. 
  move:(enum_regularity enum_h ig)=> /(congr1 int_to_nat).
  rewrite -n'E /n=> <-; rewrite /nb_neighbours -(size_arr_to_seq gl.[i]).
  rewrite -uniq_size_uniq.
  + exact/filter_uniq/enum_uniq.
  + exact/lti_sorted_uniq/(enum_nei_sort format_h ig).
  + move=> x; rewrite mem_filter mem_enum inE andbT.
    case/boolP: (x \in arr_to_seq gl.[i]); rewrite ?andbF //.
    case/mapP=> k; rewrite mem_irangeE le0x andbT /= => /[swap] ->.
    by move/(enum_valid_nei format_h ig)=> ->.
- move=> p q; rewrite !inE /= => /andP [pg _] /andP [qg _].
  exact/to_enum_type_inj.
Qed.

Lemma inter_verif (e : vertices G_lex):
  [forall e' : successors G_lex (fsval e), 
    inter_verification (fsval e) (fsval e')].
Proof.
apply/forallP=> /= e'.
move: (fsvalP e) (fsvalP e'); rewrite -{2}(gisof_bij gG_lex).
case/imfsetP=> /= i /[swap] {2 3}->; rewrite to_graph_vtx=> ig.
rewrite (gisof_succ gG_lex) ?to_graph_vtx //.
case/imfsetP=> /= j' /[swap] ->; rewrite to_graph_succ ?to_graph_vtx //.
case/imfsetP=> /= j /[swap] ->; rewrite inE => /andP [jg ij].
rewrite /inter_verification /=.
move: (set_ord_i_P ig) (set_ord_i_P jg).
move/parrayI_final_ord=> /[apply] ->.
- rewrite (enum_basI enum_h ig jg ij) pred_intE -?n'E //=.
  by rewrite ltEint_nat -n'E.
- exact/(enum_bas_is_sorted format_h).
- exact/(enum_bas_is_sorted format_h).
Qed.

Lemma high_enum_algoE : high_enum_algo A b G_lex.
Proof.
apply/andP; split; try (apply/forallP=> e; apply/and5P; split).
- exact:G_lex_prop0. 
- exact: card_verif.
- exact: feas_verif.
- exact: bas_verif.
- exact: reg_verif.
- exact: inter_verif.
Qed.

End LexCertCorrect.
Section BoundCorrect.

Definition poly := 'P(base_of_mat A b).

Lemma BQR_Po_mul v : m = length v ->
  rat_bigQ_rV (Po_mul v Po) ((@bigQ_arr_to_rat_cV m v)^T *m A).
Proof.
move=> len_v; apply/rat_bigQ_rVP; split.
- rewrite length_Po_mul n'E //.
- move=> i; rewrite Po_mulP ?ltEint_nat ?nat_to_intK -?n'E ?ltn_ord //; last 
    (rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite n'E; exact/int_thresholdP).
  rewrite !mxE /arr_fold_pair zip_map_irange ltin -len_v -m'E ltnn.
  rewrite irange0_iota -m'E.
  rewrite /index_enum unlock_with -enumT -val_enum_ord.
  elim/last_ind: (enum 'I_m)=> /=; rewrite ?big_nil //.
  move=> l a IH; rewrite big_rcons /= !map_rcons foldl_rcons.
  apply/eqP/rat_bigQ_add; apply/eqP=> //; rewrite mxE.
  apply/eqP/rat_bigQ_mul=> /=.
  + by case/rat_bigQ_cVP: (BQ2R_cVP v)=> _; rewrite -len_v=> /(_ a) /eqP <-.
  + case: Po_base=> _ /(_ a) [+ _]; case/rat_bigQ_rVP=> _ /(_ i) /eqP.
    by rewrite mxE=> <-.
Qed.

Definition rat_cert i := ((@bigQ_arr_to_rat_cV m cert.[i].1)^T, (@bigQ_arr_to_rat_cV m cert.[i].2)^T).

Lemma bqr_rat_cert i: (i < LFC.n Po)%O ->
  rat_bigQ_rV cert.[i].1 (rat_cert i).1 /\ rat_bigQ_rV cert.[i].2 (rat_cert i).2.
Proof.
move=> i_n; split; apply/BQR_cV_tr.
- move: (BQ2R_cVP cert.[i].1).
  by case: (bounded_Po_testP_size Po_bound i_n)=> ->; rewrite m'E.
- move: (BQ2R_cVP cert.[i].2).
  by case: (bounded_Po_testP_size Po_bound i_n)=> _ ->; rewrite m'E.
Qed.

Lemma rat_cert_rVE (i : 'I_n):
  (rat_cert (nat_to_int i)).1 *m A = delta_mx ord0 i /\
  (rat_cert (nat_to_int i)).2 *m A = - delta_mx ord0 i.
Proof.
split.
- move: (@bounded_Po_testP_comp _ _ Po_bound (nat_to_int i)).
  rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_n' //.
  rewrite -n'E ltn_ord=> /(_ isT) [+ _].
  move: (@BQR_Po_mul cert.[nat_to_int i].1).
  have:= (bounded_Po_testP_size Po_bound)=> /(_ (nat_to_int i)).
  rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_n' //.
  rewrite -n'E ltn_ord => /(_ isT) [-> _].
  move/(_ m'E)/BQR_rV_injl /[apply]; apply.
  apply/rat_bigQ_rVP; split.
  + by rewrite length_set length_make leb_length n'E.
  + move=> j; case/boolP: (i == j)=> [/eqP ->|/[dup] ij_neq /eqP i_n_j].
    * rewrite get_set_same ?mxE ?eqxx // ltin length_make leb_length.
      by rewrite nat_to_intK ?int_threshold_ord_n' // -n'E ltn_ord.
    * rewrite get_set_other ?get_make ?mxE ?eqxx /=; first by (apply/eqP; rewrite eq_sym (negPf ij_neq)).
      by move/nat_to_int_inj; rewrite !int_threshold_ord_n'=> /(_ isT isT)/val_inj/i_n_j.
- move: (@bounded_Po_testP_comp _ _ Po_bound (nat_to_int i)).
rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_n' //.
rewrite -n'E ltn_ord=> /(_ isT) [_ +].
move: (@BQR_Po_mul cert.[nat_to_int i].2).
have:= (bounded_Po_testP_size Po_bound)=> /(_ (nat_to_int i)).
rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_n' //.
rewrite -n'E ltn_ord => /(_ isT) [_ ->].
move/(_ m'E)/BQR_rV_injl /[apply]; apply.
apply/rat_bigQ_rVP; split.
+ by rewrite length_set length_make leb_length n'E.
+ move=> j; case/boolP: (i == j)=> [/eqP ->|/[dup] ij_neq /eqP i_n_j].
  * rewrite get_set_same ?mxE ?eqxx // ltin length_make leb_length.
    by rewrite nat_to_intK ?int_threshold_ord_n' // -n'E ltn_ord.
  * rewrite get_set_other ?get_make ?mxE ?eqxx /=; first by (apply/eqP; rewrite eq_sym (negPf ij_neq)).
    by move/nat_to_int_inj; rewrite !int_threshold_ord_n'=> /(_ isT isT)/val_inj/i_n_j.
Qed.

Lemma rat_cert_ge0 (i : 'I_n):
  ((rat_cert (nat_to_int i)).1)^T >=m 0 /\ ((rat_cert (nat_to_int i)).2)^T >=m 0.
Proof.
have:= (bounded_Po_testP_ge0 Po_bound)=> /(_ (nat_to_int i)).
rewrite ltEint_nat nat_to_intK ?int_threshold_ord_n' // -n'E ltn_ord.
move/(_ isT)=> cert_ge0.
split; apply/gev0P.
- move=> j; move: (cert_ge0 (nat_to_int j)); rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_m' //.
  rewrite -m'E ltn_ord=> /(_ isT) [+ _].
  case/BigQ.BigQ.le_lteq.
  + move/rat_bigQ_lt=> h; apply/ltW/h=> //.
    by rewrite !mxE.
  + by move/rat_bigQEl=> /(_ 0 rat_bigQ0); rewrite !mxE=> ->.
- move=> j; move: (cert_ge0 (nat_to_int j)); rewrite ltEint_nat ?nat_to_intK ?int_threshold_ord_m' //.
  rewrite -m'E ltn_ord=> /(_ isT) [_ +].
  case/BigQ.BigQ.le_lteq.
  + move/rat_bigQ_lt=> h; apply/ltW/h=> //.
    by rewrite !mxE.
  + by move/rat_bigQEl=> /(_ 0 rat_bigQ0); rewrite !mxE=> ->.
Qed.

Definition max_cert_i i := (Order.max (- '[((rat_cert i).1)^T, b])  (- '[((rat_cert i).2)^T, b])).
Definition max_cert := \big[Order.max/0%R]_(i <- irange0 (LFC.n Po)) max_cert_i i.

Lemma max_cert_iP (i : 'I_n): forall x, b <=m (A *m x) -> `|x i 0| <= max_cert_i (nat_to_int i).
Proof.
move=> x /[dup]; case: (rat_cert_ge0 i)=> cert1_ge0 cert2_ge0.
move/(vdot_lev cert1_ge0)=> + /(vdot_lev cert2_ge0).
rewrite !vdot_mulmx -!trmx_mul.
case: (rat_cert_rVE i)=> -> ->.
rewrite trmxN vdotNl !trmx_delta !vdotl_delta_mx.
move=> x_i_ge x_i_le; apply/ler_normlP; split.
- by rewrite le_maxr; apply/orP; left; rewrite ler_oppr GRing.opprK.
- by rewrite le_maxr; apply/orP; right; rewrite ler_oppr.
Qed.

Lemma boundA: forall c, Simplex.bounded A b c.
Proof.
move=> c; rewrite -(boundedE (relA A b)).
move: c; apply/compactP.
- case/Simplex.feasibleP: (feasA high_enum_algoE)=> x ?; apply/proper0P; exists x.
  by rewrite (feasE (relA A b)).
- apply/compactP_Linfty; exists max_cert=> x.
  rewrite (feasE (relA A b)) inE=> /max_cert_iP h_max.
  move=> i; rewrite /max_cert; apply/(le_trans (h_max i)).
  move: n'E=> /(congr1 nat_to_int); rewrite int_to_natK=> <-.
  move: (mem_irangeE 0%uint63 (nat_to_int n)) (ltn_ord i)=> /(_ (nat_to_int i)).
  rewrite le0x /= ltEint_nat !nat_to_intK ?int_threshold_ord_n' //;
    last (rewrite inE n'E; exact/int_thresholdP).
  move=> <-; rewrite /irange0; elim: (irange _ _); rewrite ?in_nil //.
  move=> a l IH; rewrite big_cons in_cons.
  by case/orP=> [/eqP ->|/IH]; rewrite le_maxr ?lexx // => ->; rewrite orbT.
Qed.

End BoundCorrect.
Section ImgCorrect.

Definition G_vert := (fun i=> @bigQ_arr_to_rat_cV n lblr.[i]) @/ (to_graph_struct gr).

Lemma len_lblr (i : int): mem_vertex gr i ->
  n = length lblr.[i].
Proof.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
case/(quot_graph_morf_complete glr_quot_h)=> i' i'gl ->.
move:(lbl_quot_vert lbl_quot_h)=> /(_ i').
rewrite -(quot_graph_length glr_quot_h).
rewrite ltEint=> /(_ i'gl) /eq_array_relP [ <- _].
case:(enum_dim_point format_h i'gl)=> _ /(_ 0%uint63).
rewrite n'E => <- //; rewrite ltEint_nat succ_intE //.
by rewrite (length_lt_max Po).
Qed.


Lemma phi_rat_bigQ (i : int): mem_vertex gl i ->
  rat_bigQ_cV lbll.[i].2.[0] (phi (to_enum_type lbll.[i])).
Proof.
move=> i_gl; case: (enum_dim_point format_h i_gl).
move/(congr1 int_to_nat); rewrite succ_intE ?(length_lt_max Po) //.
rewrite -m'E -add1n => /esym len_point len_col.
have:= (BQ2R_matP_cast len_point)=> /(_ n).
have h: (forall i0 : int_porderType, 
 (i0 < length (LFC.point lbll i))%O -> n = length (LFC.point lbll i).[i0]).
- move=> j j_len; rewrite n'E len_col // ltEint_nat succ_intE ?(length_lt_max Po) //.
  by rewrite -m'E -[X in (_ <= X)%nat]add1n len_point -ltEint_nat.
by move/(_ h); case=> _ /(_ ord0).
Qed.

Lemma phiE (i : int): mem_vertex gl i ->
  phi (to_enum_type lbll.[i]) = @bigQ_arr_to_rat_cV n lblr.[morf.[i]].
Proof.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
move=> igl; apply/trmx_inj.
move: (lbl_quot_vert lbl_quot_h)=> /(_ i).
rewrite -(quot_graph_length glr_quot_h) ltEint=> /(_ igl).
move=> /[dup] /eq_array_relP [len_eq _].
move/BQR_rV_injl => /(_ n); apply. 
- apply/BQR_cV_tr/(phi_rat_bigQ igl).
- apply/BQR_cV_tr/BQ2R_cVP_cast.
  move:(quot_graph_morf_correct glr_quot_h igl). 
  exact: len_lblr.
Qed.

Lemma G_vert_vtx : vertices G_vert = vertices ((@phi m' n')@/ G_lex).
Proof.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
rewrite !vtx_quot_graph !vtx_img_graph.
apply/fsetP=> x; apply/idP/idP.
- case/imfsetP=> /= ?; rewrite to_graph_vtx.
  case/(quot_graph_morf_complete glr_quot_h)=> i igl -> ->.
  apply/imfsetP=> /=; exists (to_enum_type lbll.[i]); 
    first by (apply/in_imfset; rewrite to_graph_vtx).
  by rewrite phiE.
- case/imfsetP=> /= ? /imfsetP [/= i]; rewrite to_graph_vtx=> igl -> ->.
  apply/imfsetP=> /=; exists morf.[i]; rewrite ?to_graph_vtx ?(quot_graph_morf_correct glr_quot_h) //.
  by rewrite phiE.
Qed.

Lemma G_vert_img : G_vert = ((@phi m' n') @/ G_lex).
Proof.
apply/gisof_idE.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
apply/gisofE; split=> //.
- by rewrite imfset_id G_vert_vtx.
- move=> x y xG_vert yG_vert; apply/idP/idP.
  + case/edge_quot_graph=> /= i [j] [x_eq y_eq x_n_y].
    move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
    rewrite !to_graph_vtx => igr jgr; rewrite to_graph_edge ?to_graph_vtx //.
    case/(quot_graph_edge_morf glr_quot_h igr jgr)=> i_n_j.
    case=> i' [j'] [i'gl j'gl i_eq j_eq gl_ij'].
    apply/edge_quot_graph; exists (to_enum_type lbll.[i']), (to_enum_type lbll.[j']).
    split; rewrite ?phiE // ?i_eq ?j_eq //.
    apply/edge_img_graph; exists i', j'; split=> //.
    by rewrite to_graph_edge ?to_graph_vtx.
  + case/edge_quot_graph=> /= e [e'] [x_eq y_eq x_n_y].
    move=> /[dup] /[dup] /edge_vtxl eG_lex /edge_vtxr e'G_lex.
    case/edge_img_graph=> /= i [j] [e_eq e'_eq].
    move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
    rewrite !to_graph_vtx=> igl jgl; rewrite to_graph_edge ?to_graph_vtx //.
    move=> gl_ij; apply/edge_quot_graph. 
    exists morf.[i], morf.[j]; rewrite x_n_y -x_eq -y_eq -e_eq -e'_eq.
    rewrite !phiE //; split=> //; rewrite to_graph_edge ?to_graph_vtx; try
      exact/(quot_graph_morf_correct glr_quot_h).
    apply/(quot_graph_edge_morf glr_quot_h); try
      exact/(quot_graph_morf_correct glr_quot_h).
    split; last by (exists i, j; split).
    apply/eqP=> morf_eq.
    move: x_n_y; rewrite -x_eq -y_eq -e_eq -e'_eq !phiE //.
    by rewrite morf_eq eqxx.
Qed.

End ImgCorrect.
Section GraphCertification.

Lemma graph_certification : G_vert = (poly_graph A b).
Proof.
apply/repr_poly_graph.
- exact: boundA.
- exact: high_enum_algoE.
- exact: G_vert_img.
Qed.

Lemma in_gr_inj: {in vertices (to_graph_struct gr) &,
  injective (fun x => @bigQ_arr_to_rat_cV n lblr.[x])}.
Proof.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
move=> i j; rewrite !to_graph_vtx=> igr jgr.
move: (BQ2R_cVP_cast (len_lblr igr))=> /(@BQR_cV_tr n lblr.[i]) i_bqr.
move: (BQ2R_cVP_cast (len_lblr jgr))=> /(@BQR_cV_tr n lblr.[j]) j_bqr.
move: (lbl_quot_sort lbl_quot_h); rewrite /sort_check.
move/BQltx_inj; rewrite -(lbl_quot_label lbl_quot_h) ltEint.
move=> /(_ _ _ igr jgr) h_inj /(congr1 trmx) /BQR_rV_injl.
by move/(_ lblr.[i] lblr.[j] i_bqr j_bqr).
Qed.

Lemma graph_verification_low : 
  gisof (to_graph_struct gr) (poly_graph A b) (fun i=> @bigQ_arr_to_rat_cV n lblr.[i]).
Proof.
move/is_lbl_quotP: quot_h=> lbl_quot_h.
move: (lbl_quot_quot lbl_quot_h)=> glr_quot_h.
move/gisof_idE: graph_certification=> h.
apply/(gisof_trans _ h).
apply/gisofE; split.
- exact: in_gr_inj. 
- by rewrite !vtx_mk_graph.
- move=> i j; rewrite !to_graph_vtx=> igr jgr; apply/idP/idP.
  + rewrite to_graph_edge ?to_graph_vtx // => gr_ij.
    apply/edge_quot_graph; exists i, j; split=> //; rewrite ?to_graph_edge ?to_graph_vtx //.
    move/(quot_graph_edge_morf glr_quot_h igr jgr) : gr_ij=> /=.
    case=> + _; apply/contra=> /eqP /in_gr_inj; rewrite !to_graph_vtx.
    by move/(_ igr jgr)=> ->.
  + case/edge_quot_graph=> i' [j'] [++ _ /[dup] /[dup] /edge_vtxl i'gr /edge_vtxr j'gr].
    move/(in_gr_inj i'gr); rewrite to_graph_vtx=> /(_ igr) ->. 
    by move/(in_gr_inj j'gr); rewrite to_graph_vtx=> /(_ jgr) ->.
Qed.
  

End GraphCertification.

Section Dim.

Definition seq_dim_points : seq 'rV[rat]_n := 
  [seq (bigQ_arr_to_rat_cV lblr.[map_.[i]])^T | i <- irange 1 (Uint63.succ (LFC.n Po))].

Definition origin_point : 'rV[rat]_n := (bigQ_arr_to_rat_cV lblr.[map_.[0%uint63]])^T.

Lemma mem_dim_points: 
  origin_point^T \in poly /\ {in seq_dim_points, forall x, x^T \in poly}.
Proof.
move/is_lbl_quotP/lbl_quot_label: (quot_h)=> lbl_len.
split.
- move/fsetP: (gisof_bij graph_verification_low)=> /(_ origin_point^T).
  rewrite trmxK in_imfset ?vtx_mk_graph; first by move/esym/vertex_set_subset.
  rewrite inE mem_irangeE le0x /= /graph_length lbl_len.
  case: (dim_full_testP_map Po_dim)=> _ /(_ 0%uint63); apply. 
  rewrite ltEint_nat succ_intE //; exact: (length_lt_max Po.[0%uint63].1).
- move=> x /mapP [y] /=; rewrite mem_irangeE=> /andP [_] y_len ->.
  rewrite trmxK; move/fsetP: (gisof_bij graph_verification_low).
  move/(_ (@bigQ_arr_to_rat_cV n lblr.[map_.[y]])); rewrite !vtx_mk_graph=> h.
  apply/vertex_set_subset; rewrite -h; apply/in_imfset; rewrite inE /=.
  rewrite mem_irangeE le0x /= /graph_length lbl_len.
  by case: (dim_full_testP_map Po_dim)=> _ /(_ _ y_len). 
Qed.

Lemma size_dim_points: seq.size seq_dim_points = n.
Proof.
rewrite size_map size_irange succ_intE ?subSS ?subn0 ?n'E //.
exact: (length_lt_max Po.[0%uint63].1).
Qed.

Lemma map_lblr_length i: (i < Uint63.succ (LFC.n Po))%O -> n = length lblr.[map_.[i]].
Proof.
case: (dim_full_testP_map Po_dim)=> <- /[apply].
case/is_lbl_quotP: quot_h=> gl_gr <- + _ mapi_gr.
move: (quot_graph_morf_complete gl_gr)=> /(_ _ mapi_gr).
case=> j j_gl -> /(_ j); rewrite -(quot_graph_length gl_gr).
move/(_ j_gl); case/andP=> /eqP <- _.
case: (enum_dim_point format_h j_gl)=> _ /(_ 0%uint63) ->; rewrite ?n'E //.
rewrite ltEint_nat succ_intE ?ltn0Sn //; exact: (length_lt_max Po).
Qed. 

Lemma adim_dim_points:
  adim [affine (span [seq (x - origin_point)^T%R | x <- seq_dim_points]) & origin_point^T] = n.+1.
Proof.
rewrite adimN0_eq ?mk_affine_proper0 // dir_mk_affine; congr S.
set S := map _ _; have ->: span S = span (in_tuple S) by [].
have size_S: seq.size S = n by rewrite size_map size_dim_points.
rewrite span_matrix_cV -mxrank_tr; set M:= matrix_of_fun _ _.
have ->: M^T = \matrix_i S`_i ^T by apply/matrixP=> i j; rewrite !mxE (tnth_nth 0) /=.
rewrite -(rank_castmx size_S).
apply/anti_leq/andP; split; first by apply: rank_leq_row.
rewrite row_leq_rank row_free_castmx; apply/row_freeP.
exists (bigQ_mat_to_rat_mat inv); apply/row_matrixP=> i.
rewrite row_mul rowK (nth_map 0) ?size_dim_points -?{2}size_S //.
rewrite (nth_map 0%uint63) ?size_irange ?succ_intE ?subSS ?subn0 -?n'E -?{2}size_S //;
  last exact: (length_lt_max Po.[0%uint63].1).
rewrite nth_irange ?succ_intE ?subSS ?subn0 -?n'E -?{2}size_S //;
  last exact: (length_lt_max Po.[0%uint63].1).
rewrite addn1 !trmx_sub !trmxK.
move: (dim_full_testP_inv Po_dim)=> /(_ (nat_to_int i.+1)) /=.
rewrite !ltEint_nat !nat_to_intK ?inE; last
  (apply/(leq_ltn_trans (ltn_ord _)); rewrite size_S n'E; exact/int_thresholdP).
rewrite ltn0Sn /= succ_intE; last exact: (length_lt_max Po.[0%uint63].1).
rewrite ltnS -n'E -{2}size_S ltn_ord=> /(_ isT).
apply/(elimT (BQR_rV_injl _ _)); first apply/BQR_rV_M_mul.
- apply/BQR_arr_rV; rewrite -?GRing.scaleN1r; last apply/BQR_scal_rV=> //.
  + apply/BQR_cV_tr/BQ2R_cVP_cast.
    rewrite -(@map_lblr_length (nat_to_int i.+1)) //.
    rewrite ltEint_nat -nat_to_intS !succ_intE ?ltnS; try exact: (length_lt_max Po.[0%uint63].1).
    * rewrite nat_to_intK -?n'E -?{2}size_S ?ltn_ord //.
      rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite size_S n'E; exact/int_thresholdP.
    * rewrite ltEint_nat nat_to_intK ?inE; last by 
        (apply/(ltn_trans (ltn_ord _)); rewrite size_S n'E; exact/int_thresholdP).
      apply/(ltn_trans (ltn_ord _)); rewrite size_S n'E -ltEint_nat; exact: (length_lt_max Po.[0%uint63].1).
  + apply/BQR_cV_tr/BQ2R_cVP_cast; rewrite (@map_lblr_length 0%uint63) //.
    rewrite ltEint_nat succ_intE ?ltn0Sn //; exact: (length_lt_max Po.[0%uint63].1).
- case: (dim_full_testP_format Po_dim)=> len_inv form_inv.
  apply/BQ2R_matP_cast; rewrite ?size_S ?len_inv ?n'E //.
  by move=> k /form_inv ->.
- apply/rat_bigQ_rVP; rewrite {1}size_S length_set length_make leb_length {1}n'E.
  split=> // j; rewrite !mxE -nat_to_intS pred_succ.
  case/boolP: (i == j)=> /=.
  + move/eqP=> ->; rewrite get_set_same // length_make leb_length.
    rewrite ltin nat_to_intK -?n'E -?{2}size_S ?ltn_ord //.
    rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite size_S n'E.
    exact/int_thresholdP.
  + move=> /eqP i_n_j; rewrite get_set_other ?get_make //.
    move/nat_to_int_inj=> h; apply/i_n_j/val_inj/h; 
      rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite size_S n'E; exact/int_thresholdP. 
Qed.

Lemma poly_dimension: \pdim poly = n.+1.
Proof.
(* rewrite dimN0_eq; last by (apply/proper0P; exists origin_point^T; case: mem_dim_points). *)
apply/anti_leq/andP; split; first exact: adim_leSn.
move: adim_dim_points=> <-; case: mem_dim_points=> x0P xkP.
pose S := [seq x^T | x <- seq_dim_points].
have xkPS: {in S, forall x, x \in poly} by move=> x /mapP [x'] /xkP + ->.
have:= (dim_sub_affine x0P xkPS); set M := map _ _; set M' := map _ _.
suff ->: M = M' by [].
by rewrite /M /S -map_comp; apply/eq_map=> x /=; rewrite trmx_sub.
Qed.

End Dim.

Section Start.

Lemma g_start : mem_vertex gr start.
Proof. by case/diameter_checkP: hirsch_check. Qed.

End Start.

Section BFS.

Lemma start_G_vert : (@bigQ_arr_to_rat_cV n lblr.[start]) \in vertices G_vert.
Proof.
rewrite graph_certification. 
by rewrite -(gisof_bij graph_verification_low) in_imfset // to_graph_vtx g_start.
Qed.

Lemma poly_BFS: exists2 x, x \in vertices G_vert &
  (HBFS G_vert x (succ_vert G_vert) > m - n)%nat.
Proof.
exists (@bigQ_arr_to_rat_cV n lblr.[start]).
- exact: start_G_vert. 
- case/diameter_checkP: hirsch_check=> g_start.
  rewrite -m'E -n'E (repr_graph_BFS graph_verification_low g_start).
  move/gisof_idE: graph_certification=> h.
  rewrite -(gisof_BFSP h (@succ_vert_h _ G_vert) 
    (succ_gGP graph_verification_low)).
  + move/leq_trans; apply; exact: nat_to_int_le.
  + exact: start_G_vert.
Qed.

End BFS.

Section Hirsch.

Theorem Hirsch_Conjecture_is_false :
  (high_diameter (poly_graph A b) > 
  #|`facets 'P(base_of_mat A b)| - (\pdim 'P(base_of_mat A b)).-1)%nat.
Proof.
apply/Hirsch_was_wrong.
- exact: high_enum_algoE. 
- exact: G_vert_img.
- exact: boundA.
- exact: poly_BFS.
- exact:poly_dimension. 
Qed.

End Hirsch.
End Validation. *) *)