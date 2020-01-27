(*
Section Graph.

Context {R : realFieldType} {n : nat} (P : 'poly[R]_n).

Definition adj :=
  [rel v w : 'cV[R]_n | (v != w) && ([segm v & w] \in face_set P)].

Lemma adj_sym v w : adj v w = adj w v. (*symmetric adj.*)
Proof.
by rewrite /= eq_sym fsetUC.
Qed.

Lemma adj_vtxl (v w : 'cV[R]_n) : adj v w -> v \in vertex_set P.
Proof.
by move/andP => [_] segm_face; apply/(fsubsetP (vertex_setS segm_face));
   rewrite vertex_set_segm; rewrite !inE eq_refl.
Qed.

Lemma adj_vtxr (v w : 'cV[R]_n) : adj v w -> w \in vertex_set P.
Proof.
by rewrite adj_sym; apply/adj_vtxl.
Qed.

Hypothesis P_compact : compact P.

Lemma vertex_set_slice_dim1 v : v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       forall F, F \in face_set P -> (v \in F) -> (dim F >= 1)%N -> (slice e F `>` [poly0]).
Admitted.

Lemma vertex_set_slice v : v \in vertex_set P ->
  forall e, [e separates v from ((vertex_set P) `\ v)%fset] ->
       vertex_set (slice e P) =
       [fset ppick (slice e F) | F in face_set P & ((v \in F) && (dim F == 2%N))]%fset.
Admitted.

Definition improve c :=
  [rel v w | (adj v w) && ('[c,w] < '[c,v])].

Lemma sub_improve_adj c: subrel (improve c) adj.
Proof.
by move => ??/andP [].
Qed.

Lemma improving_neighbor (c v : 'cV[R]_n) :
  v \in vertex_set P -> v \notin argmin P c -> exists w, improve c v w.
Proof.
move => v_vtx v_notin.
have P_prop0 : P `>` [poly0] by apply/proper0P; exists v; apply/vertex_set_subset.
suff /existsP: [exists w : vertex_set P, adj v (fsval w) &&  ('[c,fsval w] < '[c,v])]
  by move => [w ?]; exists (fsval w).
move: v_notin; apply/contraR; rewrite negb_exists => /forallP adj_vert.
have {}adj_vert: forall w, adj v w -> '[c,w] >= '[c,v].
- move => w adj; move/adj_vtxr: (adj) => w_vtx.
  by move/(_ [` w_vtx]%fset): adj_vert; rewrite adj /= leNgt.
have c_bounded : bounded P c by apply/compactP.
rewrite in_argmin vertex_set_subset //=.
rewrite [P]conv_vertex_set //; apply/conv_subset.
move => w; case/altP : (w =P v) => [ -> _| w_neq_v w_vtx]; first by rewrite in_hs.
pose sep := conv_sep_hp (sep_vertex P_compact v_vtx).
pose e := xchoose sep.
pose sep_v := (sep_hpP (xchooseP sep)).1.
pose sep_other := (sep_hpP (xchooseP sep)).2.
have w_in_hs : w \in [hs e].
  by apply/hsN_subset/sep_other/in_conv; rewrite !inE w_neq_v /=.
move: (hp_itv w_in_hs sep_v) => [α α01].
set x := _ + _ => x_in_hp.
have {x_in_hp} x_in_slice : x \in slice e P
  by rewrite in_polyI x_in_hp /= mem_poly_convex ?ltW_le ?vertex_set_subset.
suff: x \in [hs [<c, '[ c, v]>]].
- rewrite !in_hs /= /x combine2C combine2_line vdotDr ler_addl.
  rewrite vdotZr vdotBr pmulr_rge0 ?subr_ge0 //.
  by rewrite subr_cp0; move/andP: α01 => [].
- move: x_in_slice; rewrite [slice _ _]conv_vertex_set;
    last by apply/(subset_compact P_compact)/poly_subsetIr.
  rewrite (vertex_set_slice v_vtx) ?(xchooseP sep) // => /in_convP [ω ω_supp ->].
  apply/convexW; first apply/mem_poly_convex.
  move => z /(fsubsetP ω_supp)/imfsetP => [[F] /and3P [F_face v_in_F /eqP dimF2] ->].
  have : v \in vertex_set F by rewrite (vertex_set_face F_face) in_imfset // inE ?v_vtx.
  move: (F_face).
  move/(dim2P (face_compact P_compact F_face)): dimF2 => [y [y' -> y_neq_y' yy'_face]].
  have adj_y_y': adj y y' by rewrite inE yy'_face y_neq_y'.
  move/vertex_setS: (yy'_face); rewrite vertex_set_segm => /fsubsetP sub_vtx v_in.
  have slice_prop0 : slice e [segm y & y'] `>` [poly0].
  - apply/(vertex_set_slice_dim1 v_vtx) => //; first by apply/(xchooseP sep).
    + by apply/in_conv.
    + by rewrite dim_segm y_neq_y'.
  suff: slice e [segm y & y'] `<=` [hs [<c, '[ c, v]>]]
    by move/poly_subsetP/(_ _ (ppickP slice_prop0)).
  apply/(poly_subset_trans (poly_subsetIr _ _))/conv_subset.
  move: v_in adj_y_y' => /fset2P; case => <-;
    by move => adj_v u /fset2P; case => ->; rewrite in_hs // adj_vert // adj_sym.
Qed.

End Graph.

Section MkPath.

Context {R : realFieldType} {n : nat} (P : 'poly[R]_n).
Hypothesis P_compact : compact P.

Variable c : 'cV[R]_n.

Definition height (v : 'cV[R]_n) :=
  #|` [fset w in vertex_set P | '[c,w] <= '[c,v]] |%fset.

Definition mk_improve (v : 'cV[R]_n) :=
  match @idP (v \in vertex_set P) with
  | ReflectT v_vtx =>
    match @idPn (v \in argmin P c) with
    | ReflectT v_notin => xchoose (improving_neighbor P_compact v_vtx v_notin)
    | _ => v
    end
  | _ => v
  end.

Lemma mk_improveE (v : 'cV[R]_n) (v_vtx : v \in vertex_set P) (v_notin : v \notin argmin P c) :
  let w := mk_improve v in improve P c v w.
Proof.
rewrite /mk_improve.
case: {-}_/idP => [h|]; rewrite ?v_vtx //.
case: {-}_/idPn => [h'|]; rewrite ?v_notin //.
by apply/(xchooseP (improving_neighbor _ _ _)).
Qed.

Lemma mk_improve_in_vertex_set (v : 'cV[R]_n) :
  v \in vertex_set P -> mk_improve v \in vertex_set P.
Proof.
move => v_vtx; rewrite /mk_improve.
case: {-}_/idP => [h|]; rewrite ?v_vtx //.
case: {-}_/idPn => [h'| //].
by move: (xchooseP (improving_neighbor P_compact h h')) => /andP [/adj_vtxr ? _].
Qed.

Function mk_path (v : 'cV[R]_n) {measure height v} :=
  if (v \in vertex_set P) && (v \notin argmin P c) then
    let w := mk_improve v in
    w :: mk_path w
  else [::].
Proof.
move => v /andP [v_vtx v_notin].
set w := mk_improve v; apply/ssrnat.leP.
suff w_lt_v: '[c,w] < '[c,v].
- rewrite /height.
  set S_w := [fset _ | _ in _ & _]%fset; set S_v := [fset _ | _ in _ & _]%fset.
  apply/fproper_ltn_card/fproperP; split.
  + move => x; rewrite !inE /= => /andP [-> /=].
    by move/le_lt_trans/(_ w_lt_v)/ltW.
  + by exists v; rewrite !inE v_vtx //= -?ltNge.
- by rewrite /w; move/andP : (mk_improveE v_vtx v_notin) => [_].
Qed.

Lemma mk_pathP :
  forall v, path (improve P c) v (mk_path v).
Proof.
apply/(@mk_path_rect (path (improve P c))) => [v /andP [v_vtx v_notin] w | //=].
suff: improve P c v w by rewrite /= => -> ->.
by rewrite /w; apply: mk_improveE.
Qed.

Lemma mk_path_argmin :
  forall v, v \in vertex_set P -> (last v (mk_path v)) \in argmin P c.
Proof.
pose P' v s := v \in vertex_set P -> (last v s) \in argmin P c.
apply/(@mk_path_rect P') => [v _| v ? <-].
- by rewrite /P' /= => h ?; apply/h/mk_improve_in_vertex_set.
- case: ifP => [// | /negbT]; rewrite negb_and => /orP; case; rewrite /P' /=.
  + by move/negP.
  + by rewrite negbK.
Qed.

End MkPath.

Section Connectness.

Context {R : realFieldType} {n : nat}.

Lemma connected_graph (P: 'poly[R]_n) v w :
  compact P -> v \in vertex_set P -> w \in vertex_set P ->
    exists2 p, (path (adj P) v p) & w = last v p.
Proof.
move => P_compact v_vtx; rewrite in_vertex_setP.
move/face_argmin/(_ (pt_proper0 _)) => [c c_bouned argmin_eq].
exists (mk_path P_compact c v); first by apply/(sub_path (@sub_improve_adj _ _ _ _))/mk_pathP.
by move: (mk_path_argmin P_compact c v_vtx); rewrite -argmin_eq in_pt => /eqP.
Qed.

Hypothesis n_gt0 : (n > 0)%N.

Definition disjoint_path (V : {fset 'cV[R]_n}) (p : seq 'cV[R]_n) := [forall v : V, fsval v \notin p].

Lemma disjoint_pathP V p :
  reflect (forall v, v \in V -> v \notin p) (disjoint_path V p).
Admitted.

Lemma foo (P : 'poly[R]_n) c v :
  compact P -> v \in vertex_set P -> exists p, [/\ path (adj P) v p, last v p \in argmin P c & (forall w, w \in p -> '[c,w] < '[c,v])].
Proof.
move => P_compact v_vtx; exists (mk_path P_compact c v); split.
- by apply/(sub_path (@sub_improve_adj _ _ _ _))/mk_pathP.
- exact: mk_path_argmin.
- set p := mk_path _ _ _.
Admitted.

Lemma balinski P V v w :
  compact P -> dim P = n.+1%N -> (V `<=` vertex_set P)%fset -> #|` V | = n.-1%N ->
    v \in (vertex_set P `\` V)%fset -> w \in (vertex_set P `\` V)%fset ->
      exists p, [/\ (path (adj P) v p), w = last v p & disjoint_path V p].
Proof.
set S := (_ `\` _)%fset.
move => P_compact dimP V_sub V_card v_in_S w_in_S.
have S_sub: (S `<=` vertex_set P)%fset by admit.
have v_vtx := (fsubsetP S_sub _ v_in_S).
have w_vtx := (fsubsetP S_sub _ w_in_S).
pose V' := (v |` V)%fset.
have: (0 < #|` V' | <= n)%N by admit.
move/subset_hp => [e]; rewrite -[e]beE /=.
set c := e.1; set α := e.2 => c_neq0 sub.
case: (ltP '[c,w] α) => [c_w_lt| c_w_ge].
- set F := argmin P c.
  have c_bounded : bounded P c by admit.
  have F_compact : compact F by admit.
  pose p1 := mk_path P_compact c v.
  pose p2 := mk_path P_compact c w.
  (*pose p3 := connected_graph F_compact *)
Admitted.

(*
Lemma other_vtx : exists2 w, w \in vertex_set P & w \notin V.
Proof.
suff: (vertex_set P `\` V)%fset != fset0
  by move/fset0Pn => [w /fsetDP [??]]; exists w.
rewrite -cardfs_gt0 cardfsDS ?subn_gt0 ?card_V ?prednK //.
by apply/ltnW/card_vertex_set; rewrite ?dimP.
Qed.
*)
End Connectness.
*)
