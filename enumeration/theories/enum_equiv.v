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
- by apply/precond_mxP; [| |exact:len_A]; rewrite format_poly_mn.
- by apply/precond_lengthP; [|exact:len_b]; rewrite format_poly_mn.
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

Definition dim_full_array (V : array 'cV[rat]_n) 
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
  dim_full_array V origin map_ Inv.
Proof.
rewrite /dim_full_test /dim_full_array /arr_all.
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

Definition high_dim_full (x0 : 'cV[rat]_n) (s : 'M[rat]_n) :=
  [&& x0 \in vertices G',
    [forall i, col i s \in vertices G'] &
    let X := \matrix_(i < n) ((col i s)^T - (x0)^T) in X *m Inv == 1%:M
  ].

Lemma dim_full_vtx_final_graph: 
  dim_full_array L origin map_ Inv ->
  exists x0, exists s, high_dim_full x0 s.
Proof.
case/and4P=> /eqP len_map /allP map_in origin_in /allP inv_eq.
exists L.[origin].
set s_seq := [seq L.[i] | i <- arr_to_seq map_].
have s_seq_n: seq.size s_seq == n by rewrite size_map size_arr_to_seq len_map.
set s_tuple := Tuple s_seq_n.
have s_tuple_tnth: forall i, tnth s_tuple i = L.[map_.[nat_to_int i]].
- by move=> i; rewrite (tnth_nth 0) /= (nth_map (default map_)) ?nth_arr_to_seq // ?size_arr_to_seq -?len_map //.
set s := (\matrix_(i < n) (tnth s_tuple i)^T)^T.
exists s; move=> [:i_thre]. 
apply/and3P; split.
- rewrite -(gisof_vtx GLG') /= in_imfset //=.
  by rewrite GL_length.
- apply/forallP; move=> i; rewrite /s -tr_row rowK trmxK s_tuple_tnth.
  rewrite -(gisof_vtx GLG') /= in_imfset //=.
  rewrite GL_length; apply/map_in/map_f.
  rewrite /irange0 mem_irangeE le0x /=.
  rewrite ltEint_nat -len_map nat_to_intK //.
  by abstract: i_thre i; apply:(int_threshold_length (a:=map_)); rewrite -len_map.
- apply/eqP/row_matrixP=> i; rewrite row_mul.
  rewrite rowK -tr_row rowK trmxK s_tuple_tnth.
  have ->: row i 1%:M = \row_j (i == j)%:R by
    move=> t; apply/matrixP=> p q; rewrite !mxE.
  apply/eqP; move: (inv_eq (nat_to_int i)); rewrite nat_to_intK //.
  apply; rewrite mem_irangeE le0x ltEint_nat -len_map /=.
  by rewrite nat_to_intK.
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
  exists x0, exists s, high_dim_full G Inv x0 s.
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

