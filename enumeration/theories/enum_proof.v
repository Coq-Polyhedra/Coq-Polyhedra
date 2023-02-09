From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx.
From Polyhedra Require Import lrel polyhedron poly_base.
From Polyhedra Require Import simplex fsetmin.
Require Import enum_algo graph high_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.
Open Scope polyh_scope.

Section Simplex.

Context (R : realFieldType) (n m : nat).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (c : 'cV[R]_n).
Context (bas0 : Simplex.lex_feasible_basis A b).
Hypothesis (bnd_c : Simplex.bounded A b c).

Lemma unpt_pt_is_feas (bas1 : Simplex.lex_feasible_basis A b):
  Simplex.point_of_basis b bas1 \in Simplex.polyhedron A b.
Proof.
rewrite inE Simplex.rel_points_of_basis -col_mul.
move: (Simplex.feasible_basis_is_feasible bas1).
rewrite /Simplex.is_feasible inE.
move/forallP=> lex_feas_bas1; apply/forallP => i.
move/lex_ord0: (lex_feas_bas1 i).
by rewrite !mxE /=; case: splitP => //= j; rewrite (ord1_eq0 j).
Qed.
  

Lemma feas_bas0 : Simplex.feasible A b.
Proof.
apply/Simplex.feasibleP.
exists (Simplex.point_of_basis b bas0).
exact: unpt_pt_is_feas.
Qed.

Definition simplex_lex_basis := Simplex.phase2_res c bas0.
Definition simplex_lex_point := Simplex.point_of_basis b simplex_lex_basis.
Definition simplex_lex_ppoint := Simplex.point_of_basis (Simplex.b_pert b) simplex_lex_basis.


Lemma simplex_bas0 : Simplex.phase2 c bas0 = Simplex.Phase2_res_optimal_basis (Simplex.phase2_res c bas0).
Proof.
move: (@Simplex.phase2_resP _ _ _ _ _ c bas0).
case: (Simplex.phase2P c bas0).
- move=> bas1 i [red_cost_lt0 i_feas].
  suff: False by case.
  case/(Simplex.boundedP_lower_bound _ feas_bas0) : bnd_c => K K_opt.
  case: (Simplex.unbounded_cert_on_basis K i_feas red_cost_lt0 (unpt_pt_is_feas bas1)).
  move=> x [x_feas].
  by rewrite real_ltNge ?num_real // (K_opt _ x_feas).
- move=> bas1 _ h.
  by rewrite (h (Simplex.Phase2_res_optimal_basis bas1)).
Qed.

Lemma simplex_lex_reduced_cost : (Simplex.reduced_cost_of_basis c simplex_lex_basis) >=m 0.
Proof.
rewrite /simplex_lex_basis; move: simplex_bas0.
by case: (Simplex.phase2P c bas0 ) => // bas h [] <-.
Qed.

Lemma simplex_lex_feas : simplex_lex_ppoint \in Simplex.lex_polyhedron A (Simplex.b_pert b).
Proof. exact: Simplex.feasible_basis_is_feasible. Qed.

Lemma simplex_feas : simplex_lex_point \in Simplex.polyhedron A b.
Proof. exact: unpt_pt_is_feas. Qed.

Lemma simplex_lex_opt x : x \in Simplex.lex_polyhedron A (Simplex.b_pert b) ->
  (c^T *m simplex_lex_ppoint) <=lex (c^T *m x).
Proof.
move: simplex_lex_reduced_cost.
rewrite /Simplex.reduced_cost_of_basis.
rewrite /simplex_lex_point /Simplex.point_of_basis /= inE.
set A_I := row_submx.row_submx A _.
set A_I_inv := qinvmx _ _.
move=> red_cost_ge0 /forallP x_inP.
have -> : (c^T *m x) = (c^T *m (A_I_inv *m A_I) *m x).
- rewrite qmulVmx ?mulmx1 //.
  move: (Simplex.basis_trmx_row_free simplex_lex_basis).
  by rewrite -!row_leq_rank mxrank_tr {2}Simplex.prebasis_card.
rewrite !mulmxA -[c^T *m A_I_inv]trmxK trmx_mul trmxK -mulmxA.
apply/lev_mul_lex; rewrite ?trmxK //.
by move=> i; rewrite row_mul !row_submx.row_submx_row -row_mul x_inP.
Qed.

Lemma simplex_opt x : x \in Simplex.polyhedron A b ->
  '[c, simplex_lex_point] <= '[c, x].
Proof.
move=> x_feas.
pose X := row_mx x 0 : 'M_(n, 1 + m).
have/simplex_lex_opt: X \in Simplex.lex_polyhedron A (Simplex.b_pert b).
- rewrite inE; apply/forallP=> i.
  apply/lex_lev=> j; rewrite row_mul -matrix_vdot row_id !mxE.
  case: splitP'.
  + move=> k; rewrite (ord1_eq0 k)=> ->; rewrite colKl col_id.
    move: x_feas; rewrite inE=> /forallP /(_ i).
    by rewrite -matrix_vdot col_id.
  + move=> k ->; rewrite colKr col0 vdot0r !mxE.
    by case: (i == k); rewrite /= ?mulr1n ?mulr0n ?lerN10 ?oppr0.
move/lex_ord0; rewrite -!matrix_vdot row_id trmxK -Simplex.rel_points_of_basis.
suff ->: col 0 X = x by [].
apply/matrixP=> i j; rewrite !mxE (ord1_eq0 j).
by case: splitP=> // k _; rewrite (ord1_eq0 k).
Qed.

Definition simplex_lex_exec := Simplex.phase2_exec c bas0.

Lemma last_simplex_lex_exec: last bas0 simplex_lex_exec = simplex_lex_basis.
Proof. by []. Qed. 

End Simplex.

Section QuotientGraph.

Context (R : realFieldType) (n' m' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).
Context (base : base_t[R,n]).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).
Hypothesis P_compact: forall c, Simplex.bounded A b c.
Hypothesis P_feasible: Simplex.feasible A b.

Local Notation P := 'P(base).

Definition rel_mat_Po (base : base_t[R,n]) (C : 'M[R]_(m,n) * 'cV[R]_m):=
  [fset [<(row i C.1)^T, C.2 i ord0>] | i : 'I_m] = base.
  
Hypothesis r_Ab_base : rel_mat_Po base (A, b).
(* Hypothesis A_inj : injective (fun i=> row i A). *)

(* Hypothesis size_base : #|`base| = m.
Definition A_ := (\matrix_(i < #|`base|%fset) ((fnth i).1)^T).
Definition b_ := (\col_(i < #|`base|%fset) (fnth i).2).
Definition base_tuple_ := [tuple (tnth [tuple of base] i) | i < #|`base|].
Definition A := (castmx (size_base, erefl) A_).
Definition b := (castmx (size_base, erefl) b_).
Definition base_tuple := (tcast size_base base_tuple_).
Hypothesis P_compact : compact 'P(base). *)

(* Lemma size_base: #|` base| = m.
Proof.
Admitted.

Lemma base_inj (i j : 'I_m): base`_i = base`_j -> i = j.
Proof.
suff: {in gtn (size base) &, injective (nth 0 base)} by
  move=> h base_eq; apply/val_inj/h=> //=; rewrite inE size_base.
exact/uniqP.
Qed. *)


(* Lemma row_A i : row i A = ((base`_i).1)^T.
Proof.
rewrite row_castmx castmx_id rowK.
by rewrite /fnth (tnth_nth 0).
Qed. *)

(* Lemma row_b i : row i b = ((base`_i).2)%:M.
Proof.
rewrite row_castmx castmx_id /b_.
apply/matrixP=> p q.
rewrite !mxE (ord1_eq0 p) (ord1_eq0 q) eqxx mulr1n.
by rewrite /fnth (tnth_nth 0).
Qed. *)


(* Lemma b_i i : b i 0 = (base`_i).2.
Proof. by move/matrixP: (row_b i)=> /(_ 0 0); rewrite !mxE eqxx mulr1n. Qed. *)

(* Lemma base_nth (i : 'I_m) : base`_i = base_tuple`_i.
Proof. by rewrite -tnth_nth tcastE tnth_mktuple (tnth_nth 0) /=. Qed. *)

Lemma feasE x : x \in P = (x \in Simplex.polyhedron A b).
Proof.
apply/idP/idP.
- move/in_poly_of_baseP=> x_poly; rewrite inE.
  apply/forallP=> /= i; rewrite -row_vdot.
  move/fsetP: r_Ab_base=> /(_ [<(row i A)^T, b i 0>]).
  rewrite in_imfset //= => /esym /x_poly.
  by rewrite in_hs /=.
- rewrite inE; move/forallP=> /= x_poly.
  apply/in_poly_of_baseP=> e.
  move/fsetP: r_Ab_base=> /(_ e) /[swap] ->.
  case/imfsetP=> /= i _ ->; rewrite in_hs /=.
  rewrite row_vdot; apply: x_poly.
Qed.

Lemma boundedE c : bounded P c = Simplex.bounded A b c.
Proof.
apply/idP/idP.
- case/boundedP=> x /[dup] x_feas; rewrite feasE=> x_splx_feas.
  move/poly_subset_hsP=> Pbase_bnd.
  apply/Simplex.boundedP_lower_bound; first by (apply/Simplex.feasibleP; exists x).
  by exists '[c,x]; move=> y; rewrite -feasE=> /Pbase_bnd /=.
- case/Simplex.boundedP=> -[x [+ <-]].
  rewrite -feasE=> x_feas poly_bnd.
  apply/boundedP; exists x=> //; apply/poly_subset_hsP=> y.
  by rewrite feasE=> /poly_bnd.
Qed.

Lemma pointedE : pointed P = Simplex.pointed A.
Proof.
case/Simplex.feasibleP: P_feasible=> y=> /forallP y_base. 
apply/idP/idP; apply/contraTT.
- case/Simplex.pointedPn=> d /= [dn0 d_feas nd_feas].
  apply/pointedPn; exists y; exists d=> //.
  apply/poly_leP=> x; rewrite affE=> /in_lineP [mu ->].
  rewrite feasE; apply/forallP=> i.
  rewrite mulmxDr -scalemxAr.
  suff ->: A *m d = 0 by rewrite scaler0 addr0; exact: y_base.
  apply: lev_antisym; rewrite d_feas andbT.
  by rewrite -oppv_ge0 -mulmxN.
- case/pointedPn=> x [d] dn0 /poly_leP line_sub.
  apply/Simplex.pointedPn; exists d=> /=.
  have: x \in P by
    apply/line_sub; rewrite affE; apply/in_lineP; exists 0; rewrite scale0r addr0.
  rewrite feasE inE -subv_ge0=> /gev0P x_feas.
  suff Ad0: (A *m d) = 0 by rewrite mulmxN Ad0 oppr0 lev_refl dn0.
  apply/eqP/contraT; case/matrix0Pn=> i [j]; rewrite (ord1_eq0 j).
  set S := (A *m x - b) i 0.
  set D := (A *m d) i 0.
  case: ltrgt0P=> // /[dup] Ad0 + _.
  + set mu := - (S / D) - 1.
    have: x + mu *: d \in P by apply/line_sub; rewrite affE; apply/in_lineP; exists mu.
    rewrite feasE inE -subv_ge0 mulmxDr addrAC -scalemxAr.
    move/gev0P/(_ i); rewrite mxE -/S mxE -/D /mu mulrDl mulNr -mulrA mulVr ?(unitf_gt0 Ad0) //.
    rewrite mulr1 addrA subrr add0r mulNr mul1r oppr_ge0.
    by case: ltrgt0P.
  + set mu := - (S / D) + 1.
    have: x + mu *: d \in P by apply/line_sub; rewrite affE; apply/in_lineP; exists mu.
    rewrite feasE inE -subv_ge0 mulmxDr addrAC -scalemxAr.
    move/gev0P/(_ i); rewrite mxE -/S mxE -/D /mu mulrDl mulNr -mulrA mulVr ?(unitf_lt0 Ad0) //.
    rewrite mulr1 addrA subrr add0r mul1r.
    by case: ltrgt0P.
Qed.

Lemma compactE : compact P.
Proof.
apply/compactP; last (move=> c; rewrite boundedE; exact/P_compact). 
apply/proper0P; case/Simplex.feasibleP: P_feasible=> x.
by rewrite -feasE=> ?; exists x.
Qed.

Lemma feas_to_lexfeas x :
  x \in Simplex.polyhedron A b ->
  row_mx x 0 \in Simplex.lex_polyhedron A (Simplex.b_pert b).
Proof.
rewrite !inE; move/forallP=> /= x_poly.
apply/forallP=> /= i; rewrite row_row_mx row_mul.
apply/lex_lev=> j. rewrite -matrix_vdot row_id.
case: (splitP' j)=> k ->.
- rewrite row_mxEl colKl col_id (ord1_eq0 k) mxE row_vdot.
  exact: x_poly.
- rewrite row_mxEr colKr col0 vdot0r !mxE.
  by case: (i == k); rewrite ?mulr1n ?mulr0n ?lerN10 ?oppr_le0.
Qed.

Lemma lexfeas_to_feas x :
  x \in Simplex.lex_polyhedron A (Simplex.b_pert b) ->
  col 0 x \in Simplex.polyhedron A b.
Proof.
rewrite !inE; move/forallP=> /= x_feaslex.
apply/forallP=> i; rewrite -col_mul mxE.
move/(_ i): x_feaslex=> /lex_ord0; rewrite /Simplex.b_pert 2!mxE.
by case: splitP=> //= j _; rewrite (ord1_eq0 j) !mxE.
Qed.

Lemma Pbase_prop0 (I : Simplex.lex_feasible_basis A b): P `>` [poly0].
Proof. by apply/proper0P; exists (Simplex.point_of_basis b I); rewrite feasE unpt_pt_is_feas. Qed.

Lemma unpt_pt_is_eq (bas1 : Simplex.lex_feasible_basis A b):
  forall k, k \in bas1 -> row k A *m Simplex.point_of_basis b bas1 = row k b.
Proof.
move=> k; rewrite Simplex.active_ineq_pert_exact inE=> /eqP.
move/(congr1 (col 0)); rewrite Simplex.rel_points_of_basis.
rewrite -!col_mul -row_mul=> ->.
apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) !mxE.
by case: splitP=> // j _; rewrite (ord1_eq0 j).
Qed.

Section EquivGraphLexi.

Definition set_adjacence := fun I I' : {set 'I_m} =>  #| I :&: I' | == n.-1.

Definition lex_graph := mk_graph [fset x | x : Simplex.lex_feasible_basis A b] set_adjacence.

Lemma splx_adj_sym I J: set_adjacence I J -> set_adjacence J I.
Proof. by rewrite /set_adjacence setIC. Qed.

Section SplxGraphConnected.

Context (I J: Simplex.lex_feasible_basis A b).
Definition obj_conn := \sum_(i < #|J|) (row i (row_submx A J)).

Lemma obj_connE: 
  obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) J =
  \sum_(i < #|J|) (row i (row_submx (Simplex.b_pert b) J)).
Proof.
rewrite mulmx_suml /=; apply/eq_big=> //= i _.
by rewrite -row_mul Simplex.row_submx_point_of_basis.
Qed.

Lemma obj_conn_opt:
  forall K : Simplex.lex_feasible_basis A b, K != J ->
  (obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) J) <lex
  (obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) K).
Proof.
move=> K K_n_J; rewrite obj_connE mulmx_suml /=.
apply/ltrlex_sum.
- move=> i; move: (Simplex.feasible_basis_is_feasible K).
  by rewrite !row_submx_row -row_mul /Simplex.is_feasible inE=> /forallP /(_ (enum_val i)).
- have: (J != K :> {set _}) by rewrite eq_sym.
  rewrite eqEcard [X in (X <= _)%N]Simplex.prebasis_card [X in (_ <= X)%N]Simplex.prebasis_card leqnn andbT.
  case/subsetPn=> j jJ j_n_K; exists (enum_rank_in jJ j); rewrite !row_submx_row -row_mul enum_rankK_in //.
  rewrite /ltrlex; move: (Simplex.feasible_basis_is_feasible K).
  rewrite /Simplex.is_feasible inE=> /forallP /(_ j) ->; rewrite andbT.
  by move: j_n_K; rewrite Simplex.active_ineq_pert_exact inE eq_sym.
Qed.

Lemma opt_is_J : simplex_lex_basis (obj_conn^T) I = J.
Proof.
apply/eqP/contraT=> /obj_conn_opt; rewrite lex_ltrNge.
rewrite -/simplex_lex_ppoint.
have ->: Simplex.point_of_basis (Simplex.b_pert b) (simplex_lex_basis obj_conn^T I) = simplex_lex_ppoint (obj_conn^T) I by [].
have h_J: Simplex.point_of_basis (Simplex.b_pert b) J \in Simplex.lex_polyhedron A (Simplex.b_pert b) by
  exact/(Simplex.feasible_basis_is_feasible J).
by rewrite -{-2}[obj_conn]trmxK simplex_lex_opt.
Qed.

Lemma path_to_J: path (edges lex_graph) I (Simplex.phase2_exec obj_conn^T I).
Proof.
move: (Simplex.phase2_exec_adj (obj_conn^T) I).
set f := (fun _ => _); suff eq_rel_edge: f =2 edges lex_graph by rewrite (eq_path eq_rel_edge).
by move=> x y; rewrite edge_mk_graph ?in_fsetE.
Qed.

Program Definition conn_splx_gpath := @GPath _ lex_graph I J (shorten I (Simplex.phase2_exec (obj_conn^T) I)) _ _ _.
Next Obligation. by rewrite vtx_mk_graph in_fsetE. Qed.
Next Obligation. by case/shortenP: path_to_J. Qed.
Next Obligation. by rewrite -opt_is_J /simplex_lex_basis /Simplex.phase2_res; case/shortenP : path_to_J. Qed.


Program Definition conn_splx_epath := @EPath _ _ conn_splx_gpath _.
Next Obligation. by case/shortenP: path_to_J. Qed.

End SplxGraphConnected.

Section SplxGraphRegular.

Context (I : Simplex.lex_feasible_basis A b).
Section MkNeigh.

Context (i : 'I_#|I|).
Definition obj_reg :=
  (\sum_(j < #|I| | (enum_val j) != (enum_val i)) row j (row_submx A I)) -
  row i (row_submx A I).

Lemma red_cost_reg :
  (Simplex.reduced_cost_of_basis (obj_reg^T) I) = const_mx 1%:R - 2%:R *: (delta_mx i 0).
Proof.
rewrite /Simplex.reduced_cost_of_basis -trmx_mul.
rewrite /obj_reg mulmxBl mulmx_suml -row_mul qmulmxV ?row1; last exact/Simplex.basis_is_basis.
apply/matrixP=> p q; rewrite (ord1_eq0 q) !mxE eqxx andbT /=.
rewrite summxE.
under eq_bigr=> j ?.
- rewrite -row_mul qmulmxV; last exact/Simplex.basis_is_basis.
  rewrite row1 mxE eqxx /=.
over.
case/boolP: (p == i)=> /= [/eqP p_i | /negPf p_n_i].
- rewrite mulr1 -mulrnBl !mulr1n opprD addNKr.
  apply/subr0_eq/eqP; rewrite opprK -addrA addNr addr0.
  have h: forall j, enum_val j != enum_val i -> (p == j) = false by 
    move=> j; apply/contra_neqF=> /eqP/(congr1 enum_val) <-; rewrite p_i.
  under eq_bigr=> j j_n_i do rewrite (h _ j_n_i).
  by rewrite sumr_const /= mul0rn.
- rewrite mulr0n mulr0 !subr0.
  rewrite (bigD1_ord p) /=; last first.
  + apply/contraT; rewrite negbK=> /eqP h; move: p_n_i.
    by move/enum_val_inj: h=> ->; rewrite eqxx.
  rewrite eqxx /=; apply/eqP; rewrite -subr_eq0 addrC mulr1n addKr.
  under eq_bigr=> j ? do rewrite eq_liftF.
  by rewrite sumr_const mul0rn.
Qed.

Lemma pick_reg : 
  [pick i0 | Simplex.reduced_cost_of_basis obj_reg^T I i0 0 < 0 ] = Some i.
Proof.
rewrite red_cost_reg.
have pick_h: forall x, (1%:R - 2%:R * (x == i)%:R < 0) = (x == i) by
  move=> ? x; case: (_ == _); rewrite /= ?mulr0n ?mulr0 ?subr0 ?ltr10 ?mulr1n ?mulr1 ?subr_lt0 ?ltr1n.
under eq_pick=> j do rewrite !mxE eqxx andbT pick_h.
case: pickP=> /=; last by (move/(_  i); rewrite eqxx).
by move=> ? /eqP ->.
Qed.

Lemma reg_infeas_dir : ~~ Simplex.feasible_dir A (Simplex.direction i).
Proof.
rewrite /Simplex.feasible_dir /=; apply/contraT; rewrite negbK.
move/(Simplex.unbounded_cert_on_basis (b:=b) (c:=obj_reg^T)).
move: pick_reg; case: pickP=> // j /[swap]; case=> -> ->.
rewrite unpt_pt_is_feas.
move: P_compact=> /(_ (obj_reg^T)).
move/Simplex.boundedP_lower_bound=> /(_ (feas_bas0 I)) [K] h /(_ K isT isT).
by case=> x [x_poly]; rewrite ltNge h.
Qed.

Definition neigh_reg := Simplex.lex_rule_fbasis reg_infeas_dir.

Lemma neigh_regE : exists2 j, j \notin I & neigh_reg = j |: (I :\ enum_val i) :> {set _}.
Proof.
rewrite /neigh_reg /Simplex.lex_rule_fbasis //=.
set j := Simplex.argmin_gap _ _ _; exists j=> //.
exact/Simplex.lex_ent_var_not_in_basis.
Qed.

Lemma neigh_reg_adj : set_adjacence I neigh_reg.
Proof.
rewrite /set_adjacence; case: neigh_regE=> j j_n_I ->.
rewrite setIUr setIDA setIid disjoint_setI0 1?disjoint_sym ?disjoints1 //.
rewrite set0U cardsD (elimT setIidPr) ?sub1set ?enum_valP //.
by rewrite Simplex.prebasis_card cards1 subn1.
Qed.

End MkNeigh.
Section MkSucc.

Lemma splx_adj_witness (J : Simplex.lex_feasible_basis A b):
  set_adjacence I J -> exists i j,
  [/\ i \in I, j \notin I & (J  = j |: (I :\ i) :> {set _})].
Proof.
move/eqP=> adjIJ.
have/properP [_]: I :&: J \proper I by
  rewrite properEcard subsetIl Simplex.prebasis_card adjIJ /=.
have/properP [_]: I :&: J \proper J by
  rewrite properEcard subsetIr Simplex.prebasis_card adjIJ /=.
case=> j jJ j_nIJ [i iI i_nIJ].
have I_eq: i |: (I :&: J) = I:> {set _}.
- apply/eqP; rewrite eqEcard Simplex.prebasis_card.
  rewrite inE iI /= in i_nIJ.
  rewrite cardsU1 adjIJ inE iI i_nIJ leqnn andbT.
  by rewrite subUset subsetIl sub1set iI.
have J_eq: j |: (I :&: J) = J:> {set _}.
- apply/eqP; rewrite eqEcard Simplex.prebasis_card.
  rewrite inE jJ /= in j_nIJ.
  rewrite cardsU1 adjIJ inE jJ j_nIJ leqnn andbT.
  by rewrite subUset subsetIr sub1set jJ.
have i_n_j: i != j.
- apply/contraT; rewrite negbK=> /eqP h.
  by move: i_nIJ; rewrite inE iI h jJ.
exists i; exists j; split; rewrite ?inE ?eqxx // ?jJ ?andbT.
  by move: j_nIJ; rewrite inE jJ andbT.
by rewrite -J_eq; congr setU; rewrite -[in RHS]I_eq setU1K.
Qed.

Definition neigh_reg_fset := [fset neigh_reg i | i in 'I_#|I|].

Lemma neigh_reg_surj (J : Simplex.lex_feasible_basis A b): set_adjacence I J ->
  exists i, J = neigh_reg i.
Proof.
case/splx_adj_witness=> i' [j] [i'I j_nI J_eq].
set i := (enum_rank_in i'I i').
have J_eq_val: J = j |: (I :\ enum_val i) :> {set _} by
  rewrite enum_rankK_in.
rewrite (Simplex.edge_lex_ruleE j_nI J_eq_val).
exists i; case: (neigh_regE i)=> k k_nI reg_eq.
rewrite (Simplex.edge_lex_ruleE k_nI reg_eq).
congr Simplex.lex_rule_fbasis; exact/eq_irrelevance.
Qed.


Lemma succ_reg :
  successors lex_graph I = neigh_reg_fset.
Proof.
apply/fsetP=> J; rewrite ?succ_mk_graph ?in_fsetE !inE //=.
apply/idP/idP.
- case/neigh_reg_surj=> i ->; exact/in_imfset.
- case/imfsetP=> /= i _ ->; exact/neigh_reg_adj.
Qed.
End MkSucc.

End SplxGraphRegular.

Lemma lex_graph_connected : connected lex_graph.
Proof. by move=> I J _ _; exists (conn_splx_epath I J). Qed.

Lemma lex_graph_regular : regular lex_graph n.
Proof.
move=> I _; rewrite succ_reg card_imfset ?size_enum_ord ?Simplex.prebasis_card //.
move=> i j reg_eq.
have: neigh_reg i = neigh_reg j :> {set _} by rewrite reg_eq.
case: (neigh_regE i)=> i' i'_nI ->.
case: (neigh_regE j)=> j' j'_nI -> reg_eq_val.
have ij': i' = j'.
- move/setP/(_ j'): reg_eq_val.
  by rewrite !inE (negPf j'_nI) !andbF !orbF eqxx eq_sym=> /eqP.
move/setP/(_ (enum_val i)): reg_eq_val.
rewrite ij' !inE eqxx ?enum_valP /= ?orbF ?andbT.
have/negPf -> /=: (enum_val i != j') by
  apply/contraT; rewrite negbK=> /eqP; move: j'_nI=> /[swap] <-; rewrite enum_valP.
by move/esym/negbFE/eqP/enum_val_inj.
Qed.

End EquivGraphLexi.

Section Quotient.
 
Section VertexQuotient.

Definition fset_active (bas : {set 'I_m}) :=
  [fset [<(row i A)^T, b i 0>] | i : 'I_m in bas].

Lemma fset_active_sub (bas : Simplex.prebasis m n) :
  (fset_active bas `<=` base)%fset.
Proof.
apply/fsubsetP=> e /imfsetP /= [i i_bas ->].
by rewrite -r_Ab_base in_imfset.
Qed.

Lemma fset_active_befst (bas : Simplex.basis A) :
  (befst @` (fset_active bas)) = [fset (row i A)^T | i in bas].
Proof.
apply/fsetP=> x; apply/idP/idP.
- case/imfsetP=> /= e /imfsetP [/= i i_bas ->] ->.
  rewrite lfunE /=; exact/in_imfset.
- case/imfsetP=> /= i i_bas ->.
  apply/imfsetP; exists [<(row i A)^T, b i 0>]; rewrite ?lfunE //=.
  exact/in_imfset.
Qed.
    

Lemma fset_active_free (bas : Simplex.basis A) :
  free (befst @`fset_active bas).
Proof.
rewrite fset_active_befst.
move: (Simplex.basis_is_basis bas); rewrite /Simplex.is_basis row_free_free_submx.
rewrite -free_tr_rV; set S := [seq _ | _ in _].
move=> free_S.
rewrite (perm_free (Y:=S)) //; apply/uniq_perm; rewrite ?fset_uniq ?free_uniq //.
move=> x; apply/idP/idP.
- case/imfsetP=> /= i i_bas ->; exact/image_f.
- case/imageP=> /= i i_bas ->; exact/in_imfset.
Qed.

Lemma A_inj_bas (bas : Simplex.basis A) : {in bas &, injective (fun i=> row i A)}.
Proof.
move=> i j i_bas j_bas; move: (Simplex.basis_is_basis bas).
rewrite /Simplex.is_basis /= row_free_free_submx /image_mem=> /free_uniq /uniq_map_inj.
by apply; rewrite mem_enum.
Qed.

Lemma fset_active_card_befst (bas:Simplex.basis A) :
  #|` befst @` (fset_active bas)| = n.
Proof.
rewrite fset_active_befst card_in_imfset -?cardE ?Simplex.prebasis_card //.
move=> i j i_bas j_bas /trmx_inj; exact/(@A_inj_bas bas).
Qed.

Lemma fset_active_befst_inj (bas: Simplex.basis A):
  {in fset_active bas &, injective befst}.
Proof.
move=> x y /imfsetP [/= i i_bas ->] /imfsetP [/= j j_bas ->].
by rewrite !lfunE=> /= /trmx_inj /(@A_inj_bas bas) ->.
Qed.

Lemma fset_active_feas (bas : Simplex.lex_feasible_basis A b) :
  [pt Simplex.point_of_basis b bas]%:PH =
  'P^=(base; fset_active bas).
Proof.
apply/poly_eqP=> x.
rewrite in_pt in_polyEq feasE /=.
apply/idP/idP.
- move/eqP=> ->; rewrite unpt_pt_is_feas andbT.
  apply/forallP=> e; rewrite in_hp.
  case/imfsetP: (fsvalP e)=> /= i i_bas -> /=.
  move: (Simplex.row_submx_point_of_basis b bas); rewrite -row_submx_mul.
  move/row_submx_row_matrixP=> /(_ _ i_bas).
  rewrite row_mul.
  move/matrixP/(_ ord0 ord0); rewrite -matrix_vdot row_id col_id mxE.
  by move=> ->.
- case/andP=> /forallP bas_active x_feas; apply/eqP/Simplex.basis_subset_active_ineq_eq/subsetP.
  move=> i; rewrite inE /= => i_bas; apply/eqP/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q).
  have ei_active: [< (row i A)^T , b i 0 >] \in (fset_active bas) by rewrite /fset_active; exact/in_imfset.
  by move: (bas_active [`ei_active]); rewrite in_hp /==> /eqP; rewrite row_vdot !mxE.
Qed.

Lemma vertex_quotient_fset :
  vertex_set P =
  [fset Simplex.point_of_basis b (Simplex.basis_of_feasible_basis x) |
    x : Simplex.lex_feasible_basis A b].
Proof.
apply/fsetP=> x; apply/idP/idP.
+ move/[dup]/vertex_set_subset; rewrite feasE=> x_feas. 
  rewrite in_vertex_setP=> /face_argmin /(_ (pt_proper0 _)).
  case=> c _ x_opt_c.
  move/compact_pointed: compactE; rewrite pointedE=> A_pointed.
  move: (Simplex.build_lex_feasible_basis A_pointed x_feas)=> bas0.
  apply/imfsetP; exists (simplex_lex_basis c bas0)=> //=.
  suff: simplex_lex_point c bas0 \in argmin P c.
    - by rewrite -x_opt_c in_pt=> /eqP <-.
  apply/(argmin_mem (x:=x)); rewrite ?simplex_opt ?feasE ?simplex_feas //.
  by rewrite -x_opt_c in_pt.
+ case/imfsetP=> /= bas _ ->; rewrite in_vertex_setP.
  apply/face_active_free_fset; rewrite ?pt_proper0 //.
  exists (fset_active bas); split; rewrite ?fset_active_sub ?fset_active_free //.
  - exact: fset_active_feas.
  - by rewrite fset_active_card_befst dim_pt subSS subn0.
Qed.

Lemma lexbas_vtx (bas : Simplex.lex_feasible_basis A b) :
  Simplex.point_of_basis b bas \in vertex_set P.
Proof. by rewrite vertex_quotient_fset; apply/imfsetP; exists bas. Qed.

End VertexQuotient.

Section EdgesQuotient.

Lemma fset_active_edge_sub_base (I J: Simplex.prebasis m n) :
  (fset_active I `&` fset_active J `<=` base)%fset.
Proof. exact/(fsubset_trans (fsubsetIl _ _))/fset_active_sub. Qed.

Definition fset_active_edge_free (I J : Simplex.basis A) :
  free (befst @` (fset_active I `&` fset_active J))%fset.
Proof.
apply: (@free_subset _ _ _ (befst @` fset_active I)).
- move=> x /imfsetP [/= e e_IJ] ->; apply/in_imfset.
  move: e e_IJ; exact/fsubsetP/fsubsetIl.
- exact:fset_active_free.
- exact: fset_uniq.
Qed.

Section EdgeActive.

Context (I J : Simplex.lex_feasible_basis A b).
Hypothesis edge_IJ: set_adjacence I J.
Local Definition x := Simplex.point_of_basis b I.
Local Definition y := Simplex.point_of_basis b J.
Hypothesis x_n_y: x != y.

Lemma active_inj_edge i j:
  i \in I -> j \in J -> row i A = row j A -> b i 0 = b j 0 ->
  i = j.
Proof.
case: (splx_adj_witness edge_IJ)=> p [q] [pI qnI J_eq].
have I_eq: I = p |: J :\ q :> {set _}.
- rewrite J_eq; apply/setP=> x; rewrite !inE.
  case/boolP: (x == p)=> [/eqP ->|_] //=; rewrite ?pI.
  by case/boolP: (x == q)=> [/eqP ->|_] //=; rewrite (negPf qnI).
rewrite I_eq !inE=> /orP [/eqP ->|/andP [_] /(@A_inj_bas J) /[apply]/[apply] //].
rewrite J_eq !inE=> /orP [/eqP ->|/andP [_] /(A_inj_bas pI) /[apply] //].
move=> row_pq b_pq.
suff/eqP: x = y by rewrite (negPf x_n_y).
rewrite /y; apply/Simplex.is_point_of_basis_pert_active.
move=> k; move/setP: (J_eq)=> ->; rewrite !inE; case/orP.
- move/eqP=> ->; rewrite /x row_mul -row_pq.
  move/unpt_pt_is_eq: (pI)=> ->; apply/matrixP=> ? y; rewrite !mxE.
  by rewrite (ord1_eq0 y).
- by case/andP=> _ /unpt_pt_is_eq; rewrite row_mul.
Qed.

Lemma fset_active_edge_eq : 
  (fset_active I `&` fset_active J)%fset = fset_active (I :&: J).
Proof.
apply/fsetP=> e; apply/idP/idP.
- rewrite inE=> /andP [] /imfsetP [/= i iI ->].
  case/imfsetP=> /= j jJ [/trmx_inj].
  move/active_inj_edge=> /(_ iI jJ) /[apply] ij_eq.
  by apply/imfsetP; exists i=> //=; rewrite !inE iI ij_eq jJ.
- case/imfsetP=> /= i; rewrite inE => /andP [iI iJ ->].
  by rewrite inE; apply/andP; split; apply/imfsetP; exists i.
Qed.

Lemma fset_active_edge_card_befst:
  #|` befst @` (fset_active I `&` fset_active J)|%fset = n.-1.
Proof.
rewrite fset_active_edge_eq card_in_imfset /=.
- rewrite card_in_imfset /= -?cardE; first by move/eqP: edge_IJ.
  move=> i j; rewrite !inE=> /andP [iI _] /andP [jI _]. 
  by case=> /trmx_inj /(A_inj_bas iI jI).
- move=> e f /imfsetP /= [i + ->] /imfsetP /= [j + ->].
  rewrite !inE=> /andP [iI _] /andP [jI _].
  by rewrite !lfunE /= => /trmx_inj /(A_inj_bas iI jI) ->.
Qed.

Lemma A_IJ_rank : \rank (row_submx A (I :&: J)) = n.-1.
Proof.
apply/anti_leq; move/eqP: edge_IJ=> <-.
rewrite rank_leq_row row_leq_rank /=.
rewrite row_free_free_submx -free_tr.
rewrite (perm_free (Y:=(befst @` (fset_active I `&` fset_active J))%fset)) ?fset_active_edge_free //.
rewrite fset_active_edge_eq; apply/uniq_perm; rewrite ?fset_uniq //.
- rewrite map_inj_in_uniq ?enum_uniq //.
  move=> i j; rewrite !mem_enum !inE=> /andP [iI _] /andP [jI _].
  by move/trmx_inj/(A_inj_bas iI jI).
- move=> x; apply/idP/idP.
  + case/imageP=> /= i iIJ ->; apply/imfsetP.
    exists [<(row i A)^T, b i 0>]; rewrite ?lfunE //.
    by apply/imfsetP; exists i.
  + case/imfsetP=> /= [e /imfsetP [/= i iIJ ->] ->].
    by rewrite lfunE /=; apply/imageP; exists i.
Qed.

Lemma A_IJ_xy z: z \in [fset x; y] ->
  (row_submx A (I :&: J)) *m z = row_submx b (I :&: J).
Proof.
move=> z_xy; rewrite -row_submx_mul.
apply/row_submx_row_matrixP=> i iIJ; rewrite row_mul.
move: (iIJ); rewrite !inE=> /andP [iI iJ].
move/subsetP: (Simplex.basis_subset_of_active_ineq b I)=> /(_ _ iI).
move/subsetP: (Simplex.basis_subset_of_active_ineq b J)=> /(_ _ iJ).
rewrite !inE !row_mul => /eqP + /eqP.
by move: z_xy; rewrite !inE=> /orP [] /eqP ->.
Qed.

Lemma A_I_y: (row_submx A I) *m y != row_submx b I.
Proof.
move: x_n_y; apply/contra=> h; rewrite eq_sym; apply/eqP/Simplex.basis_subset_active_ineq_eq.
apply/subsetP=> i iI; rewrite inE.
by move/eqP: h; rewrite -row_submx_mul=> /row_submx_row_matrixP /(_ _ iI) ->.
Qed.

Lemma A_J_x: (row_submx A J) *m x != row_submx b J.
Proof.
move: x_n_y; apply/contra=> h; apply/eqP/Simplex.basis_subset_active_ineq_eq.
apply/subsetP=> i iI; rewrite inE.
by move/eqP: h; rewrite -row_submx_mul=> /row_submx_row_matrixP /(_ _ iI) ->.
Qed.

Lemma x_eq_base: exists2 i, ((row i A) *m x) 0 0 = b i 0 & ((row i A) *m y) 0 0 > b i 0.
Proof.
case: (splx_adj_witness edge_IJ)=> i [j] [iI jnI J_eq].
exists i.
- move/subsetP: (Simplex.basis_subset_of_active_ineq b I)=> /(_ _ iI).
  by rewrite inE row_mul=> /eqP ->; rewrite mxE.
- move: (A_IJ_xy (fset22 _ _)) A_I_y.
  rewrite -row_submx_mul=> /row_submx_row_matrixP h.
  apply/contraR; rewrite -leNgt -row_submx_mul -row_mul mxE => Aiy_le_b.
  apply/eqP/row_submx_row_matrixP=> k kI.
  case/boolP: (k \in J).
  + move=> kJ; move: (h k); rewrite inE kI kJ; exact.
  + rewrite J_eq !inE kI andbT negb_or negbK=> /andP [_ /eqP ->].
    apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) mxE [RHS]mxE.
    apply/le_anti; rewrite Aiy_le_b /=.
    move: (Simplex.lex_feasible_basis_is_feasible J); rewrite inE.
    by move/forallP=> /(_ i).
Qed.

Lemma y_eq_base: exists2 j, ((row j A) *m y) 0 0 = b j 0 & ((row j A) *m x) 0 0 > b j 0.
Proof.
case: (splx_adj_witness (splx_adj_sym edge_IJ))=> j [i] [jJ inJ I_eq].
exists j.
- move/subsetP: (Simplex.basis_subset_of_active_ineq b J)=> /(_ _ jJ).
  by rewrite inE row_mul=> /eqP ->; rewrite mxE.
- move: (A_IJ_xy (fset21 _ _)) A_J_x.
  rewrite -row_submx_mul=> /row_submx_row_matrixP h.
  apply/contraR; rewrite -leNgt -row_submx_mul -row_mul mxE => Ajx_le_b.
  apply/eqP/row_submx_row_matrixP=> k kI.
  case/boolP: (k \in I).
  + move=> kJ; move: (h k); rewrite inE kI kJ; exact.
  + rewrite I_eq !inE kI andbT negb_or negbK=> /andP [_ /eqP ->].
    apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) mxE [RHS]mxE.
    apply/le_anti; rewrite Ajx_le_b /=.
    move: (Simplex.lex_feasible_basis_is_feasible I); rewrite inE.
    by move/forallP=> /(_ j).
Qed.
 
  
Lemma fset_active_edge_to_lambda z:
  z \in 'P^=(base; fset_active I `&` fset_active J) -> 
  exists lambda, z = lambda *: x + (1 - lambda) *: y.
Proof.
case/in_polyEqP=> eq_IJ z_feas.
have A_IJ_z: row_submx A (I :&: J) *m z = row_submx b (I :&: J).
- apply/matrixP=> i j.
  rewrite (ord1_eq0 j) -row_vdot row_submx_mxE row_submx_row.
  apply/eqP.
  move: (eq_IJ ([<(row (enum_val i) A)^T, b (enum_val i) 0>])).
  rewrite fset_active_edge_eq in_hp /= row_vdot; apply.
  apply/imfsetP; exists (enum_val i)=> //=; exact: enum_valP.
have A_IJ_x := (A_IJ_xy (fset21 _ _)).
have A_IJ_y := (A_IJ_xy (fset22 _ _)).
move: (f_equal2 (@GRing.add _) A_IJ_x (f_equal (@GRing.opp _) A_IJ_y)).
move: (f_equal2 (@GRing.add _) A_IJ_x (f_equal (@GRing.opp _) A_IJ_z)).
rewrite subrr -!mulmxBr => /(congr1 trmx) + /(congr1 trmx).
rewrite trmx0 !trmx_mul=> /rank1_ker /[apply].
rewrite corank1_kermx // ?A_IJ_rank // => /(_ (erefl _)).
case=> [/eqP|]; rewrite ?trmx_eq0 ?subr_eq0; [move=> h|].
  by move: x_n_y; rewrite h.
case=> lambda /(congr1 trmx); rewrite trmxK trmx_mul trmxK.
rewrite mulmx_sum_col big_ord1 col_id mxE.
move/(congr1 (@GRing.opp _))/eqP; rewrite opprB subr_eq.
move/eqP=> ->; exists (1 - lambda 0 0).
rewrite !scalerBl !scalerBr !scale1r addrC -[in RHS]addrA. 
congr (_ + _); rewrite opprB opprD opprK; congr (_ + _).
by rewrite addrC -addrA addNr addr0.
Qed.
    


Lemma fset_active_edge_to_segm z:
  z \in 'P^=(base; fset_active I `&` fset_active J) -> 
  z \in [segm x & y].
Proof.
move=> /[dup] /fset_active_edge_to_lambda [lambda ->].
move/in_polyEqP=> [in_hp_z z_base].
apply/in_segmP; exists (1 - lambda); 
  last by (congr (_ + _); congr (_ *: _); rewrite opprB addrC -addrA addNr addr0).
move: z_base; rewrite feasE inE mulmxDr -!scalemxAr=> /forallP h.
case: (x_eq_base)=> i Aix Aiy; case: (y_eq_base)=> j Ajy Ajx.
rewrite subr_ge0 ler_subl_addl ler_addr; apply/andP; split.
- move: (h i); rewrite 2!mxE [X in _ + X]mxE.
  move: Aix; rewrite -row_mul mxE=> ->; rewrite -ler_subl_addl.
  rewrite -{1}[b i 0]mul1r -mulrBl -subr_ge0 -mulrBr.
  rewrite pmulr_lge0 ?subr_ge0 // subr_gt0; move: Aiy.
  by rewrite -row_mul mxE.
- move: (h j); rewrite 2!mxE [X in _ + X]mxE.
  move: Ajy; rewrite -row_mul mxE=> ->; rewrite -ler_subl_addr.
  rewrite -{1}[b j 0]mul1r -mulrBl opprB addrCA addrN addr0.
  rewrite -subr_ge0 -mulrBr pmulr_lge0 //; move: Ajx.
  by rewrite -row_mul mxE subr_gt0.
Qed.

Lemma fset_active_edge_feas:
  [segm x & y] =
  'P^=(base; fset_active I `&` fset_active J).
Proof.
apply/poly_eqP=> z; apply/idP/idP.
- case/in_segmP=> mu /andP [mu0 mu1] ->.
  apply/in_polyEqP; split.
  + move=> e; rewrite fset_active_edge_eq=> /imfsetP [/= i iIJ ->].
    rewrite in_hp /= vdotDr !vdotZr !row_vdot.
    move: (A_IJ_xy (fset21 _ _)) (A_IJ_xy (fset22 _ _)).
    rewrite -!row_submx_mul=> /row_submx_matrixP /(_ _ iIJ 0) ->.
    move/row_submx_matrixP/(_ _ iIJ 0)=> ->.
    by rewrite -mulrDl -addrA addNr addr0 mul1r.
  + rewrite feasE inE; apply/forallP=> i.
    rewrite mulmxDr -!scalemxAr 2!mxE [X in _ + X]mxE.
    move: (Simplex.lex_feasible_basis_is_feasible J); rewrite inE=> /forallP /(_ i).
    move: (Simplex.lex_feasible_basis_is_feasible I); rewrite inE=> /forallP /(_ i).
    move: mu1; rewrite -subr_ge0=> mu1.
    move=> /(ler_wpmul2l mu1) + /(ler_wpmul2l mu0); move=> /ler_add /[apply].
    by rewrite -mulrDl -addrA addNr addr0 mul1r.
- exact: fset_active_edge_to_segm. 
Qed.

Lemma adj_xy: adj P x y.
Proof.
rewrite /adj /= x_n_y /=.
apply/face_active_free_fset; rewrite ?segm_prop0 //.
exists (fset_active I `&` fset_active J)%fset; split.
- exact: fset_active_edge_sub_base.
- exact: fset_active_edge_feas.
- by rewrite fset_active_edge_card_befst dim_segm x_n_y /= !subSS subn0.
- exact: fset_active_edge_free.
Qed.

End EdgeActive.

Section EdgeSimplexExec.

Context (x y : 'cV[R]_n) (I : Simplex.lex_feasible_basis A b).
Hypothesis edge_xy : adj P x y.
Hypothesis bas_I_x : Simplex.point_of_basis b I = x.

Lemma c_def : exists c, [segm x & y] == argmin P c.
Proof.
case/andP: edge_xy=> _ /face_argmin.
by case/(_ (segm_prop0 _ _))=> c _ ->; exists c.
Qed.

Lemma c'_def : exists c', [pt y]%:PH == argmin P c'.
Proof.
move/adj_vtxr: edge_xy; rewrite in_vertex_setP.
by case/face_argmin/(_ (pt_proper0 _))=> c' _ ->; exists c'.
Qed.

Definition c := xchoose c_def.
Definition c' := xchoose c'_def.
Definition obj_func (epsilon : R) : 'cV_n := c + epsilon *: c'.
Definition exec_adj (epsilon : R) := simplex_lex_exec (obj_func epsilon) I.

Definition gap z := '[c, x - z] / '[c', z - x]. 
Definition fset_gap := [fset gap z | z in vertex_set P & ('[c', z - x] < 0) && (z != y)].
Definition min_epsilon := (fset_min 1%R fset_gap) / 2%:R.

Lemma fset_gap_gt0 G: G \in fset_gap -> 0 < G.
Proof.
case/imfsetP=> /= z; rewrite inE=> /andP [z_vtx /andP [c'_xz zny] ->].
rewrite /gap.
rewrite ltr_ndivl_mulr // mul0r vdotDr vdotNr subr_lt0.
apply/(argmin_sep (P:=P)).
- by move: (P_compact c); rewrite boundedE.
- by move/eqP: (xchooseP c_def)=> <-; rewrite in_segml.
- move: zny; apply/contra.
  move: (P_compact c); rewrite -boundedE=> /argmin_in_face_set/vertex_set_of_face.
  move=> /[apply] /(_ z_vtx).
  move/eqP: (xchooseP c_def)=> <-; rewrite vertex_set_segm !inE. 
  by case/orP=> // /eqP zx; move: c'_xz; rewrite zx subrr vdot0r ltxx.
- exact: vertex_set_subset.
Qed.

Lemma min_epsilon_gt0: min_epsilon > 0.
Proof.
rewrite /min_epsilon; case/boolP: (fset_gap == fset0).
- move/eqP=> ->; rewrite fset_min0 ?divr_gt0 ?ltr01 ?ltr0Sn //.
- by case/(fset_minP 1)=> /fset_gap_gt0 ? _; rewrite divr_gt0 ?ltr0Sn.
Qed.

Lemma min_epsilon_ltgap z: z \in vertex_set P ->
  '[c', z - x] < 0 -> z != y ->
  min_epsilon < '[c, x - z] / '[c', z - x].
Proof.
move=> z_vtx c'_xz zny; rewrite /min_epsilon.
have fset_gap_n0: fset_gap != fset0 by
  apply/fset0Pn; exists (gap z); apply/in_imfset=> /=; rewrite !inE z_vtx c'_xz zny.
move/(fset_minP 1): fset_gap_n0; move: min_epsilon_gt0; rewrite /min_epsilon.
set F := fset_min _ _.
rewrite ltr_pdivl_mulr ?ltr0Sn // mul0r => F_gt0.
case=> F_in /(_ (gap z)); rewrite in_imfset ?inE ?z_vtx ?c'_xz ?zny //.
move/(_ isT); rewrite -ltr_pdivl_mulr ?invr_gt0 ?ltr0Sn // invrK.
move/le_lt_trans; apply; rewrite ltr_pmulr ?fset_gap_gt0 ?in_imfset ?inE ?z_vtx ?c'_xz ?zny //.
by rewrite ltr1n.
Qed.

Lemma obj_func_min_xy: '[obj_func (min_epsilon), y] < '[obj_func (min_epsilon), x].
Proof.
rewrite /obj_func !vdotDl !vdotZl; apply/ler_lt_add.
- apply/(argmin_lower_bound (P:=P)); last exact/vertex_set_subset/(adj_vtxl edge_xy).
  move/eqP: (xchooseP c_def)=> <-; exact: in_segmr.
- rewrite (ltr_pmul2l min_epsilon_gt0).
  apply/(argmin_sep (P:=P)).
  + by move: (P_compact c'); rewrite boundedE.
  + by move/eqP: (xchooseP c'_def)=> <-; rewrite in_pt.
  + by move/eqP: (xchooseP c'_def)=> <-; rewrite in_pt; case/andP: edge_xy.
  + exact/vertex_set_subset/(adj_vtxl edge_xy).
Qed.

Lemma obj_func_min_out z: z \in vertex_set P -> z \notin [fset x; y] ->
  '[obj_func (min_epsilon), x] < '[obj_func (min_epsilon), z].
Proof.
move=> z_vtx; rewrite !inE negb_or=> /andP [znx zny].
rewrite /obj_func !vdotDl !vdotZl.
rewrite -ltr_subr_addr -addrA -mulrBr -ltr_subl_addl.
rewrite -!vdotBr; case: (ger0P '[c', z - x]).
- rewrite -(pmulr_rge0 _ min_epsilon_gt0)=> /lt_le_trans; apply.
  rewrite vdotBr subr_lt0; apply/(argmin_sep (P:=P)).
  + by rewrite boundedE.
  + move/eqP: (xchooseP c_def)=> <-; exact: in_segml.
  + case/andP: edge_xy=> _ /(vertex_set_of_face z_vtx) h.
    apply/contraT; rewrite negbK.
    move/eqP: (xchooseP c_def)=> <- /h.
    by rewrite vertex_set_segm !inE (negbTE znx) (negbTE zny).
  + exact/vertex_set_subset.
  (*TODO:same proof as in fset_gap_gt0*)
- move=> c'_zx; rewrite -ltr_ndivl_mulr //.
  exact/min_epsilon_ltgap.
Qed.

Lemma exec_adj_xy J: J \in (exec_adj min_epsilon) -> 
  Simplex.point_of_basis b J \in [fset x; y]. 
Proof.
rewrite /exec_adj /simplex_lex_exec.
move: (Simplex.phase2_exec_opt (obj_func min_epsilon) I).
elim: (Simplex.phase2_exec _ _) J=> //= h t IH. 
move=> J /andP [hI path_ht]; rewrite inE; case/orP.
- move/eqP=> ->; move: hI; rewrite bas_I_x.
  exact/contra_leT/obj_func_min_out/lexbas_vtx.
- apply/IH; move: path_ht hI.
  elim: t {IH}=> //= h' t' IH' /andP [hh' ??].
  apply/andP; split=> //; exact/(le_trans hh').
Qed.

Lemma exec_adj_last: simplex_lex_point (obj_func min_epsilon) I = y.
Proof.
apply/eqP/contraT=> splx_pt_Iy.
have splx_pt_Ix: simplex_lex_point (obj_func min_epsilon) I = x.
- rewrite /simplex_lex_point -last_simplex_lex_exec.
  move: (mem_last I (exec_adj min_epsilon)); rewrite inE.
  case/orP=> [/eqP -> //|/exec_adj_xy]; rewrite !inE (negPf splx_pt_Iy) orbF.
  by move/eqP=> ->.
have := (simplex_opt I)=> /(_ (obj_func min_epsilon) (P_compact _)).
move/(_ y); rewrite -feasE vertex_set_subset ?(adj_vtxr edge_xy) //.
by move/(_ isT); rewrite splx_pt_Ix leNgt obj_func_min_xy.
Qed.

Lemma adj_I_to_J: exists P Q: Simplex.lex_feasible_basis A b,
  [/\ set_adjacence P Q, Simplex.point_of_basis b P = x
    & Simplex.point_of_basis b Q = y].
Proof.
have:=foobar=> /(_ _ _ _ _ I (exec_adj min_epsilon)).
move=> /(_ set_adjacence) /(_ (fun K=> Simplex.point_of_basis b K = x)).
move=> /(_ (fun K=> Simplex.point_of_basis b K = y)).
case.
- exact/Simplex.phase2_exec_adj.
- by move=> K /exec_adj_xy; rewrite !inE=> /orP [] /eqP ->; [left|right].
- exact: bas_I_x.
- exact: exec_adj_last.
- move: exec_adj_last; rewrite /simplex_lex_point -last_simplex_lex_exec.
  rewrite /exec_adj; case: (simplex_lex_exec _ _)=> //=.
  rewrite bas_I_x; apply/contra_eqT=> _.
  by case/andP: edge_xy.
- move=> P [Q] [_ _ ? <- <-]; exists P, Q; split=> //.
Qed.

End EdgeSimplexExec. 

Lemma adj_IJ x y: adj P x y -> exists I J : Simplex.lex_feasible_basis A b,
  [/\ set_adjacence I J, Simplex.point_of_basis b I = x & 
  Simplex.point_of_basis b J = y].
Proof.
move=> edge_xy; have:= adj_vtxl edge_xy.
rewrite vertex_quotient_fset=> /imfsetP [/= K _ /esym bas_K_x].
exact/(adj_I_to_J _ bas_K_x).
Qed.

End EdgesQuotient.

Definition poly_graph {k : nat} {K : realFieldType}
  (P : 'poly[K]_k):= 
  mk_graph (vertex_set P) (adj P).

Lemma im_lex_graph_vert_graph :
  poly_graph P = ((Simplex.point_of_basis b) @/ lex_graph).
Proof.
apply/gisof_idE/gisofE; split => //=; rewrite !vtx_mk_graph.
- rewrite vertex_quotient_fset /=; apply/fsetP=> x.
  rewrite !inE /=; apply/idP/idP=> /imfsetP [x' /= _ ->]; apply/in_imfset=> //.
  exact/in_imfset.
- move=> x y x_vtx y_vtx; apply/idP/idP.
  + rewrite edge_mk_graph=> // /[dup] edge_xy.
    move/adj_IJ=> [I] [J] [splx_adj_IJ splx_pt_Ix splx_pt_Jy].
    apply/edge_quot_graph; exists I, J; split=> //; first by case/andP: edge_xy.
    rewrite edge_mk_graph //; exact/in_imfset.
  + case/edge_quot_graph=> I [J] [splx_pt_Ix splx_pt_Jy x_n_y].
    rewrite edge_mk_graph ?in_imfset //.
    move/adj_xy; rewrite /Quotient.x /Quotient.y splx_pt_Ix splx_pt_Jy.
    by move/(_ x_n_y)=> ?; rewrite edge_mk_graph.
Qed.

End Quotient.

End QuotientGraph.
