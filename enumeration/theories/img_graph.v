From mathcomp Require Import all_ssreflect all_algebra finmap.
From Coq Require Import Uint63 PArray.
From Polyhedra Require Import extra_misc.
Require Import graph high_graph extra_array extra_int refinement.
Require Import NArith.BinNat NArith.BinNatDef.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "a .[ i ]" := (PArray.get a i).

Import Order.Theory.

(* Module ImgGraphFormatComputation.

Definition length_morph_check (morph morph' : array int) (gl gr : graph.graph):= 
  (length gl =? length morph)%uint63 && (length gr =? length morph')%uint63.
  
Definition length_edge_inv_check (edge_inv : array (array (int * int))) (gr : graph.graph):= 
  (length gr =? length edge_inv)%uint63 && 
  (IFold.iall (fun i => ((length edge_inv.[i]) =? GraphUtils.nb_neighbours gr i)%uint63) (length edge_inv)).

Definition length_format_check morph morph' edge_inv gl gr:=
    length_morph_check morph morph' gl gr && length_edge_inv_check edge_inv gr.

(* Definition length_label_check {T1 T2 : Type} (gl gr : graph.graph) (lbll : array T1) (lblr : array T2):=
  (correct_label gl lbll) && (correct_label gr lblr). *)

(* Definition global_length_check 
  {T1 T2 : Type} gl gr 
  (lbll : array T1) (lblr : array T2) 
  morph morph' edge_inv:=
  [&& length_morph_check gl gr morph morph',
      length_edge_inv_check gr edge_inv &
      length_label_check gl gr lbll lblr]. *)

Definition valid_nei_check gl:= 
  IFold.iall (fun i=>
    PArrayUtils.all 
      (fun j=> GraphUtils.mem_vertex gl j)
    (neighbours gl i))
  (length gl).

(* Definition is_sort_check {T2 : Type} (lblr : array T2) 
  (r_sort : T2 -> T2 -> bool):= 
  PArrayUtils.is_sorted_rel r_sort lblr. *)

Definition img_graph_format morph morph' edge_inv gl gr :=
  length_format_check morph morph' edge_inv gl gr &&
  valid_nei_check gl.

End ImgGraphFormatComputation.

Module IGFC := ImgGraphFormatComputation.

Section ImgGraphFormatEquiv.

Definition length_morph_check (morph morph' : array int) (gl gr : graph.graph) := 
  (length gl == length morph)%O && (length gr == length morph')%O.
  
Definition length_edge_inv_check (edge_inv : array (array (int * int))) (gr : graph.graph):= 
  (length gr == length edge_inv) && 
  (iall (fun i => ((length edge_inv.[i]) == nb_neighbours gr i)%O) (length edge_inv)).

Definition length_format_check morph morph' edge_inv gl gr :=
    length_morph_check morph morph' gl gr && length_edge_inv_check edge_inv gr.

  (* 
Definition length_label_check {T1 T2 : Type} (gl gr : graph.graph) (lbll : array T1) (lblr : array T2):=
  (correct_label gl lbll) && (correct_label gr lblr). *)

(* Definition global_length_check 
  {T1 T2 : Type} gl gr 
  (lbll : array T1) (lblr : array T2) 
  morph morph' edge_inv:=
  [&& length_morph_check gl gr morph morph',
      length_edge_inv_check gr edge_inv &
      length_label_check gl gr lbll lblr]. *)

Definition valid_nei_check gl:= 
  iall (fun i=>
    arr_all 
      (fun j=> mem_vertex gl j)
    (neighbours gl i))
  (length gl).

(* Definition is_sort_check {T2 : Type} (lblr : array T2) 
  (r_sort : T2 -> T2 -> bool):= 
  is_sorted_rel r_sort lblr. *)

Definition img_graph_format morph morph' edge_inv gl gr :=
  length_format_check morph morph' edge_inv gl gr && valid_nei_check gl.

Section Proofs.

Lemma img_graph_formatE morph morph' edge_inv gl gr :
  IGFC.img_graph_format morph morph' edge_inv gl gr =
  img_graph_format morph morph' edge_inv gl gr.
Proof.
repeat congr andb; rewrite ?eqEint //.
- by rewrite iallE; apply/eq_all=> i; rewrite eqEint nb_neighboursE.
- by rewrite /IGFC.valid_nei_check iallE; apply/eq_all=> i; rewrite arr_allE.
Qed.

End Proofs.

End ImgGraphFormatEquiv.

Section ImgGraphFormatProofs.

Context (gl gr : graph.graph).
Context (morph morph' : array int) (edge_inv : array (array (int * int))).

Local Notation format_h := (img_graph_format morph morph' edge_inv gl gr).

Lemma img_graph_format_length: format_h ->
  (length gl = length morph) * (length gr = length morph') * (length gr = length edge_inv).
Proof. by case/andP=> /andP [/andP [/eqP <- /eqP <-] /andP [/eqP <-]]. Qed.

Lemma img_graph_format_edge_length: format_h ->
  forall i, mem_vertex gr i -> length edge_inv.[i] = nb_neighbours gr i.
Proof.
move=> /[dup] form_h.
case/andP=> /andP [_ /andP] [_ h] _ i i_gr.
move/allP: h=> /(_ i); rewrite mem_irangeE le0x /=.
by rewrite -(img_graph_format_length form_h)=> /(_ i_gr)/eqP.
Qed.

Lemma img_graph_format_valid_nei: format_h-> forall i,
  mem_vertex gl i -> forall k, (k < nb_neighbours gl i)%O->
  mem_vertex gl (neighbours gl i).[k].
Proof.
move=> /[dup] form_h.
case/andP=> _ /allP h i i_gl k k_nei.
move: (h i); rewrite mem_irangeE le0x /= => /(_ i_gl) /allP /(_ (neighbours gl i).[k]); apply.
by apply map_f; rewrite mem_irangeE le0x.
Qed.


End ImgGraphFormatProofs. *)

Module ImgGraphComputation.

Definition vertex_morph_check morph (gl gr : graph.graph):=
  (IFold.iall (fun k=> GraphUtils.mem_vertex gr morph.[k]) (length gl)).

Definition vertex_inv_check morph morph' (gl gr : graph.graph) := 
  IFold.iall 
    (fun i=> (GraphUtils.mem_vertex gl morph'.[i]) && 
    (morph.[morph'.[i]] =? i)%uint63) 
  (length gr).

(* Definition vertex_label_check {T1 T2 : Type} (f : T1 -> T2) (r_eq : rel T2)
  (lbll : array T1) (lblr : array T2)
  (morph : array int) := 
  IFold.iall (fun i => r_eq (f lbll.[i]) lblr.[morph.[i]]) (length morph). *)

Definition img_vertex morph morph' gl gr :=
    vertex_morph_check morph gl gr && vertex_inv_check morph morph' gl gr.

Definition nei_check morph gl gr:=
  IFold.iall (fun i=>
    GraphUtils.neighbour_all 
      (fun j=>
        ~~ (morph.[i] =? morph.[j])%uint63 ==> 
        GraphUtils.mem_vertex gr morph.[i] &&
        GraphUtils.mem_edge gr morph.[i] morph.[j]) 
    gl i)
  (length gl).

Definition no_loop_check morph (gl gr : graph.graph):=
  IFold.iall (fun i=>
    GraphUtils.mem_vertex gr morph.[i] &&
    ~~(GraphUtils.mem_edge gr morph.[i] morph.[i]))
  (length gl).

Definition edge_inv_check morph edge_inv gl gr := 
  IFold.iall (fun i=>
    IFold.iall (fun j=>
      let: (a,b) := edge_inv.[i].[j] in 
      [&& (GraphUtils.mem_vertex gl a), 
          (GraphUtils.mem_vertex gl b),
          (morph.[a] =? i)%uint63,
          (morph.[b] =? (GraphUtils.neighbours gr i).[j])%uint63 &
          GraphUtils.mem_edge gl a b]
    ) (length (GraphUtils.neighbours gr i)) 
  ) (length gr).

Definition img_edge morph edge_inv gl gr :=
  [&& nei_check morph gl gr, no_loop_check morph gl gr & edge_inv_check morph edge_inv gl gr].

Definition img_graph morph morph' edge_inv gl gr :=
  img_vertex morph morph' gl gr &&
  img_edge morph edge_inv gl gr.

End ImgGraphComputation.

Module IGC := ImgGraphComputation.

Section ImgGraphEquiv.

Definition vertex_morph_check morph (gl gr : graph.graph):=
  (iall (fun k=> mem_vertex gr morph.[k]) (length gl)).

Definition vertex_inv_check morph morph' (gl gr : graph.graph) := 
  iall 
    (fun i=> (mem_vertex gl morph'.[i]) && 
    (morph.[morph'.[i]] == i)%O) 
  (length gr).

(* Definition vertex_label_check {T1 T2 : Type} (f : T1 -> T2) (r_eq : rel T2)
  (lbll : array T1) (lblr : array T2)
  (morph : array int) := 
  iall (fun i => r_eq (f lbll.[i]) lblr.[morph.[i]]) (length morph). *)

Definition img_vertex morph morph' gl gr :=
  vertex_morph_check morph gl gr && vertex_inv_check morph morph' gl gr.

Definition nei_check morph gl gr:=
  iall (fun i=>
    neighbour_all 
      (fun j=>
        ~~ (morph.[i] == morph.[j])%O ==>
        mem_vertex gr morph.[i] &&
        mem_edge gr morph.[i] morph.[j]) 
    gl i)
  (length gl).

Definition no_loop_check morph (gl gr : graph.graph):=
  iall (fun i=>
    mem_vertex gr morph.[i] &&
    ~~(mem_edge gr morph.[i] morph.[i]))
  (length gl).

Definition edge_inv_check morph edge_inv  gl gr:= 
  iall (fun i=>
    iall (fun j=>
      let: (a,b) := edge_inv.[i].[j] in 
      [&& (mem_vertex gl a), 
          (mem_vertex gl b),
          (morph.[a] == i), 
          (morph.[b] == (neighbours gr i).[j]) &
          mem_edge gl a b]
    ) (length (neighbours gr i))
  ) (length gr).

Definition img_edge morph edge_inv gl gr :=
  [&& nei_check morph gl gr, no_loop_check morph gl gr & edge_inv_check morph edge_inv gl gr].

Definition img_graph morph morph' edge_inv gl gr:=
    img_vertex morph morph' gl gr &&
    img_edge morph edge_inv gl gr.

Section Proofs.

Lemma img_vertexE morph morph' gl gr:
  IGC.img_vertex morph morph' gl gr =
  img_vertex morph morph' gl gr.
Proof.
congr andb.
- by rewrite /IGC.vertex_morph_check iallE; apply/eq_all=> i; rewrite mem_vertexE.
- by rewrite /IGC.vertex_inv_check iallE; apply/eq_all=> i; rewrite mem_vertexE eqEint.
Qed.

Lemma img_edgeE morph edge_inv gl gr:
  IGC.img_edge morph edge_inv gl gr = img_edge morph edge_inv gl gr.
Proof.
repeat congr andb.
- rewrite /IGC.nei_check iallE; apply/eq_all=> i.
  rewrite neighbour_allE; apply/eq_all=> j.
  by rewrite eqEint mem_edgeE.
- rewrite /IGC.no_loop_check iallE; apply/eq_all=> i.
  by rewrite mem_edgeE.
- rewrite /IGC.edge_inv_check iallE; apply/eq_all=> i.
  rewrite iallE; apply/eq_all=> j; case: (edge_inv.[i].[j])=> ??.
  by rewrite !mem_vertexE !eqEint !mem_edgeE.
Qed.

Lemma img_graphE morph morph' edge_inv gl gr:
  IGC.img_graph morph morph' edge_inv gl gr =
  img_graph morph morph' edge_inv gl gr.
Proof. by rewrite /IGC.img_graph img_vertexE img_edgeE. Qed.

End Proofs.
End ImgGraphEquiv.

Section ImageGraphStructure.

(* Local Definition format_h morph morph' edge_inv gl gr := img_graph_format morph morph' edge_inv gl gr. *)

Definition high_vtx_morph morph (Gl Gr : graph [choiceType of int]) := all (fun x=> morph.[x] \in vertices Gr) (vertices Gl).

Lemma vtx_morph_check_struct morph: 
  (rel_structure =~> rel_structure =~> eq)
  (vertex_morph_check morph) (high_vtx_morph morph).
Proof.
move=> gl Gl glGl gr Gr grGr; rewrite /vertex_morph_check (@rel_struct_all _ _ _ glGl).
by apply/eq_all=> i; rewrite (rel_struct_vtx grGr).
Qed.

Definition high_vtx_inv morph morph' (Gl Gr : graph [choiceType of int]) :=
  all (fun x=> (morph'.[x] \in vertices Gl) && (morph.[morph'.[x]] == x)) (vertices Gr).

Lemma vtx_inv_check_struct morph morph':
  (rel_structure =~> rel_structure =~> eq)
  (vertex_inv_check morph morph') (high_vtx_inv morph morph').
Proof.
move=> gl Gl glGl gr Gr grGr; rewrite /vertex_inv_check (rel_struct_all _ grGr); apply/eq_all=> i.
by congr andb; rewrite (rel_struct_vtx glGl).
Qed.

Definition high_img_vtx morph morph' Gl Gr := high_vtx_morph morph Gl Gr && high_vtx_inv morph morph' Gl Gr.

Lemma vtx_check_struct morph morph':
  (rel_structure =~> rel_structure =~> eq)
  (img_vertex morph morph') (high_img_vtx morph morph').
Proof. move=> ??????; congr andb; [exact:vtx_morph_check_struct|exact:vtx_inv_check_struct]. Qed.

Lemma high_img_vtxP morph morph' Gl Gr: high_img_vtx morph morph' Gl Gr -> vertices Gr = (fun i=> morph.[i]) @` (vertices Gl).
Proof.
case/andP=> /allP morph_in /allP morph_surj; apply/fsetP=> z; apply/idP/idP.
- case/morph_surj/andP=> ? /eqP <-; exact/in_imfset.
- by case/imfsetP=> z' /= /morph_in ? ->.
Qed.

Definition high_nei (morph : array int) (Gl Gr : graph [choiceType of int]) := 
  all (fun x=> 
    all (fun y=> (morph.[x] != morph.[y]) ==> (edges Gr morph.[x] morph.[y])) (successors Gl x))
  (vertices Gl).

Lemma nei_check_struct morph:
  (rel_structure =~> rel_structure =~> eq)
  (nei_check morph) (high_nei morph).
Proof.
move=> gl Gl glGl gr Gr grGr; rewrite /nei_check (rel_struct_all _ glGl).
apply/eq_in_all=> i; rewrite -(rel_struct_vtx glGl)=> igl. 
rewrite (rel_struct_nei_all _ glGl igl); apply/eq_in_all=> j j_succ.
congr implb; apply/idP/idP. 
- by case/andP=> moigr; rewrite (rel_struct_edge grGr).
- move=> /[dup] /edge_vtxl; rewrite -(rel_struct_vtx grGr)=> moigr.
  by rewrite -(rel_struct_edge grGr) // moigr.
Qed.

Definition high_no_loop (morph : array int) (Gl Gr : graph [choiceType of int]):=
  all (fun x=> (morph.[x] \in vertices Gr) &&
    ~~ (edges Gr morph.[x] morph.[x])) (vertices Gl).

Lemma no_loop_check_struct morph:
  (rel_structure =~> rel_structure =~> eq)
  (no_loop_check morph) (high_no_loop morph).
Proof.
move=> gl Gl glGl gr Gr grGr; rewrite /no_loop_check (rel_struct_all _ glGl).
apply/eq_all=> i; apply/idP/idP. 
- case/andP=> moigr; rewrite (rel_struct_edge grGr) // -(rel_struct_vtx grGr).
  by move=> ->; rewrite moigr.
- case/andP; rewrite -(rel_struct_vtx grGr)=> moigr.
  by rewrite -(rel_struct_edge grGr) // moigr.
Qed.

Definition high_edge_inv morph edge_inv Gl gr Gr:=
  all (fun x=> all (fun y=> let: (a,b):= edge_inv.[x].[y] in
    [&& morph.[a] == x, morph.[b] == (neighbours gr x).[y] & 
      edges Gl a b])
    (irange0 (length (neighbours gr x)))) 
  (vertices Gr).

Lemma edge_inv_check_struct morph edge_inv gl Gl gr Gr:
  rel_structure gl Gl -> rel_structure gr Gr -> 
  (edge_inv_check morph edge_inv gl gr) = 
  (high_edge_inv morph edge_inv Gl gr Gr).
Proof.
move=> glGl grGr.
rewrite /edge_inv_check (rel_struct_all _ grGr); apply/eq_in_all=> x.
rewrite -(rel_struct_vtx grGr)=> xgr.
apply/eq_in_all=> y y_succ.
case: (edge_inv.[x].[y])=> a b.
apply/idP/idP=> [/and5P [?? -> ->] //|/and3P [-> -> /=]].
- by rewrite (rel_struct_edge glGl).
- move=> /[dup] /edge_vtxlr [aGl bGl]. 
  by rewrite (rel_struct_edge glGl) !(rel_struct_vtx glGl) ?aGl ?bGl.
Qed.

Definition high_img_edge morph edge_inv Gl gr Gr:=
  [&& high_nei morph Gl Gr, high_no_loop morph Gl Gr & high_edge_inv morph edge_inv Gl gr Gr].

Lemma edge_check_struct morph edge_inv gl Gl gr Gr:
  rel_structure gl Gl -> rel_structure gr Gr ->
  img_edge morph edge_inv gl gr = high_img_edge morph edge_inv Gl gr Gr.
Proof.
move=> ??; repeat congr andb;
  [exact:nei_check_struct|exact:no_loop_check_struct|exact:edge_inv_check_struct].
Qed.

Definition high_img_graph morph morph' edge_inv Gl gr Gr:=
    high_img_vtx morph morph' Gl Gr && high_img_edge morph edge_inv Gl gr Gr.

Lemma img_graph_struct morph morph' edge_inv gl Gl gr Gr:
  rel_structure gl Gl -> rel_structure gr Gr -> 
  (img_graph morph morph' edge_inv gl gr) =
  (high_img_graph morph morph' edge_inv Gl gr Gr).
Proof. by move=> glGl grGr; congr andb; [exact:vtx_check_struct|exact:edge_check_struct]. Qed.

Lemma high_img_graphP morph morph' edge_inv Gl gr Gr:
  rel_structure gr Gr ->
  high_img_graph morph morph' edge_inv Gl gr Gr ->
  Gr = (fun i=> morph.[i]) @/ Gl.
Proof.
move=> grGr.
case/andP=> vtx_h edge_h; apply/graphE.
rewrite vtx_quot_graph (high_img_vtxP vtx_h); split=> // i j.
apply/idP/idP.
- case/and3P: edge_h=> _ no_loop_h /allP/(_ i) h /[dup] /edge_vtxlr [iGr jGr] /[dup] ijGr. 
  rewrite -(rel_struct_edge grGr) ?(rel_struct_vtx grGr) //.
  move/neighboursP; rewrite !(rel_struct_vtx grGr).
  move=> /(_ iGr jGr) [k k_nei j_eq].
  move/allP: (h iGr)=> /(_ k); rewrite mem_irangeE le0x /=.
  move/(_ k_nei); case: (edge_inv.[i].[k])=> a b /and3P [/eqP a_i /eqP b_k a_b].
  apply/edge_quot_graph; exists a, b; split=> //; rewrite -?j_eq //.
  rewrite -b_k -a_i; apply/negP=> /eqP morph_eq.
  move/allP: no_loop_h=> /(_ _ (edge_vtxl a_b)).
  by case/andP=> _; rewrite {2}morph_eq a_i b_k j_eq ijGr.
- case/edge_quot_graph=> a [b] [i_eq j_eq i_n_j abGl].
  case/and3P: edge_h=> /allP /(_ _ (edge_vtxl abGl)) /allP /(_ b).
  by rewrite in_succE => /(_ abGl); rewrite i_eq j_eq i_n_j.
Qed.

End ImageGraphStructure.

Module ImgLabelGraphComputation.

Definition img_label {T1 T2 : Type} (f : T1 -> T2) (r_eq : rel T2) morph
  lbll lblr :=
  IFold.iall (fun i=> r_eq (f lbll.[i]) lblr.[morph.[i]]) (length lbll).

(* Definition img_label_sort_check {T2 : Type} (r_sort : rel T2) lblr:=
  PArrayUtils.is_sorted_rel r_sort lblr. *)

Definition img_label_graph {T1 T2} (f : T1 -> T2) r_eq morph morph' edge_inv
  gll grl := 
  IGC.img_graph morph morph' edge_inv gll.1 grl.1 && img_label f r_eq morph gll.2 grl.2. 

End ImgLabelGraphComputation.

Module ILGC := ImgLabelGraphComputation.

Section ImgLabelGraphEquiv.

Definition img_label {T1 T2 : Type} (f : T1 -> T2) (r_eq : rel T2) morph
  lbll lblr :=
  iall (fun i=> r_eq (f lbll.[i]) lblr.[morph.[i]]) (length lbll).

(* Definition img_label_sort_check {T2 : Type} (r_sort : rel T2) lblr:=
  rel_sorted r_sort lblr. *)


Definition img_label_graph {T1 T2} (f : T1 -> T2) r_eq morph morph' edge_inv
  gll grl := 
  img_graph morph morph' edge_inv gll.1 grl.1 && img_label f r_eq morph gll.2 grl.2. 

Lemma img_labelE {T1 T2 : Type} (f : T1 -> T2) r_eq morph lbll lblr:
  ILGC.img_label f r_eq morph lbll lblr =
  img_label f r_eq morph lbll lblr.
Proof. by rewrite /ILGC.img_label iallE. Qed.

Lemma img_label_graphE {T1 T2 : Type} (f : T1 -> T2) r_eq morph morph' edge_inv gll grl:
  ILGC.img_label_graph f r_eq morph morph' edge_inv gll grl =
  img_label_graph f r_eq morph morph' edge_inv gll grl.
Proof. by congr andb; rewrite ?img_graphE ?img_labelE. Qed.

End ImgLabelGraphEquiv.

Section ImgLabelRel.
Section Def.

Context {T1 T2 : Type} (f : T1 -> T2) (r_eq: rel T2).
Context (morph morph' : array int) (edge_inv : array (array (int * int))).

Definition high_img_label Gl lbll lblr := all (fun x=> r_eq (f lbll.[x]) lblr.[morph.[x]]) (vertices Gl).
Definition high_img_label_graph Gll gr Grl :=
  high_img_graph morph morph' edge_inv Gll.1 gr Grl.1 && high_img_label Gll.1 Gll.2 Grl.2.
End Def.

Section RelLabelGraph.

Context {t1 t2 : Type} {T1 T2: choiceType} (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop) (f : t1 -> t2) (F : T1 -> T2).
Context (eq_t2 : rel t2) (eq_T2 : rel T2).
Context (morph morph' : array int) (edge_inv : array (array (int * int))).  

Lemma rel_label_graph_img gl Gl gr Gr ll Ll lr Lr:
  (r1 =~> r2) f F->
  (r2 =~> r2 =~> eq) eq_t2 eq_T2->
  @rel_lbl_graph _ _ r1 (gl,ll) (Gl,Ll) ->
  @rel_lbl_graph _ _ r2 (gr,lr) (Gr,Lr) -> 
  img_label_graph f eq_t2 morph morph' edge_inv (gl,ll) (gr,lr) = 
  high_img_label_graph F eq_T2 morph morph' edge_inv (Gl,Ll) gr (Gr,Lr).
Proof.
move=> fF eq_tT2 [/= len_gll [ /=glGl llLl]] [/= len_grl [ /= grGr lrLr]].
rewrite /img_label_graph /high_img_label_graph /= (img_graph_struct _ _ _ glGl grGr).
apply/andb_id2l=> /andP [mor_vtx mor_edge]; rewrite /img_label /high_img_label.
rewrite -len_gll; rewrite (rel_struct_all _ glGl); apply/eq_in_all=> i iGl.
apply/eq_tT2.
- by apply/fF/(rel_array_r llLl); rewrite -len_gll; move: iGl; rewrite -(rel_struct_vtx glGl).
- apply/(rel_array_r lrLr); case/andP: mor_vtx=> /allP/(_ i iGl).
  by rewrite -(rel_struct_vtx grGr) -len_grl.
Qed.

End RelLabelGraph.

Section RelFinalGraph.

Context {T1 T2 : choiceType} (f : T1 -> T2).
Context (morph morph' : array int) (edge_inv : array (array (int * int))).

Lemma rel_final_graph_img gl (ll : array T1) Gl gr (lr : array T2) Gr g:
  rel_structure g gr->
  rel_final_graph (gl, ll) Gl -> rel_final_graph (gr,lr) Gr ->
  high_img_label_graph f (@eq_op _) morph morph' edge_inv (gl, ll) g (gr, lr) ->
  Gr = f @/ Gl.
Proof.
move=> ggr glGl grGr /andP [] /= /(high_img_graphP ggr)=> gr_eq.
move: grGr; rewrite gr_eq=> final_g /allP h.
apply/graphE; split.
- rewrite -(gisof_vtx final_g) !vtx_quot_graph /= -(gisof_vtx glGl) /=.
  apply/fsetP=> z; apply/idP/idP.
  + case/imfsetP=> ? /imfsetP [/= i igl -> ->].
    by move/eqP: (h _ igl)=> <-; apply/in_imfset/in_imfset.
  + case/imfsetP=> ? /imfsetP /= [i igl -> ->].
    move/eqP: (h _ igl)=> ->; apply/in_imfset=> /=. 
    by apply/imfsetP; exists i.
- move=> x y; apply/idP/idP.
  + move=> /[dup] /edge_vtxlr [xGr yGr].
    move: (xGr) (yGr); rewrite -(gisof_vtx final_g) /=.
    case/imfsetP=> /= ? ++ /imfsetP [?] /=.
    rewrite vtx_quot_graph=> /imfsetP /= [i igl ->] ->.
    case/imfsetP=> j /= jgl -> ->.
    rewrite -(gisof_edge final_g) /= ?(vtx_quot_graph); 
      [|by apply/imfsetP; exists i|by apply/imfsetP; exists j].
    case/edge_quot_graph=> i' [j'] [<- <- ij' /[dup]].
    case/edge_vtxlr=> i'gl j'gl ij'gl.
    move: (h _ i'gl) (h _ j'gl)=> /eqP <- /eqP <-.
    apply/edge_quot_graph; exists ll.[i'], ll.[j'].
    split=> //; last by rewrite -(gisof_edge glGl).
    apply/negP=> /eqP; rewrite (eqP (h _ i'gl)) (eqP (h _ j'gl)).
    move/(gisof_inj final_g)=> /=; rewrite vtx_quot_graph.
    rewrite (in_imfset _ _ i'gl) (in_imfset _ _ j'gl)=> /(_ isT isT).
    by move/eqP; rewrite (negPf ij').
  + case/edge_quot_graph=> x' [y'] [<- <- f_xy'] /[dup].
    case/edge_vtxlr; rewrite -(gisof_vtx glGl) /=.
    case/imfsetP=> /= i igl x'_eq /imfsetP [/= j jgl y'_eq].
    rewrite x'_eq y'_eq -(gisof_edge glGl) //= => ijgl.
    rewrite (eqP (h _ igl)) (eqP (h _ jgl)).
    rewrite -(gisof_edge final_g) ?vtx_quot_graph ?(in_imfset _ _ igl) ?(in_imfset _ _ jgl) //.
    apply/edge_quot_graph; exists i,j; split=> //.
    apply/negP=> /eqP /(congr1 (fun x=> lr.[x])).
    rewrite -(eqP (h _ igl)) -(eqP (h _ jgl)) -x'_eq -y'_eq.
    by move/eqP; rewrite (negPf f_xy').
Qed.
 
End RelFinalGraph.
Section RelGraphR.

Context {t1 t2 : Type} {T1 T2: choiceType} (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop).
Context (f : t1 -> t2) (F : T1 -> T2).
Context (eq_t2 : rel t2).
Context (morph morph' : array int) (edge_inv : array (array (int * int))).  

Lemma rel_graph_r_img gl ll gr lr Gl Gr:
  (r1 =~> r2) f F->
  (r2 =~> r2 =~> eq) eq_t2 (@eq_op _)->
  @rel_graph_r _ _ r1 (gl,ll) Gl -> @rel_graph_r _ _ r2 (gr,lr) Gr ->
  img_label_graph f eq_t2 morph morph' edge_inv (gl,ll) (gr,lr) ->
  Gr = F @/ Gl.
Proof.
move=> fF eq_tT2 [[gl' ll'] glgl' gl'Gl] [[gr' lr'] grgr' gr'Gr].
rewrite (rel_label_graph_img _ _ _ fF eq_tT2 glgl' grgr').
apply/rel_final_graph_img=> //; by case: grgr'=> _ [].
Qed.

End RelGraphR.

End ImgLabelRel.

(* Section GraphStruct.

Definition to_graph_struct (g : graph.graph) : high_graph.graph [choiceType of int] :=
  mk_graph [fset i | i in irange0 (graph_length g)] (mem_edge g).

Lemma to_graph_vtx (g : graph.graph) x: 
  x \in vertices (to_graph_struct g) = mem_vertex g x.
Proof. by rewrite vtx_mk_graph inE /= mem_irangeE le0x /= ltEint. Qed.

Lemma to_graph_edge (g : graph.graph) i j: mem_vertex g i ->
  mem_vertex g j -> edges (to_graph_struct g) i j = mem_edge g i j.
Proof.
move=> ig jg.
by rewrite edge_mk_graph ?inE /= ?mem_irangeE ?le0x ?ltEint.
Qed.

Lemma to_graph_succ (g : graph.graph) i:
  mem_vertex g i ->
  successors (to_graph_struct g) i = [fset j : int| (mem_vertex g j && mem_edge g i j)].
Proof.
move=> ig.
rewrite succ_mk_graph ?inE /= ?mem_irangeE ?le0x ?ltEint //.
by apply/fsetP=> y; rewrite !inE /= ?mem_irangeE le0x ltEint /=.
Qed.

Lemma to_graph_succ_nei (g : graph.graph) i:
  mem_vertex g i ->
  successors (to_graph_struct g) i = [fset j : int | (mem_vertex g j) && (j \in arr_to_seq (neighbours g i))].
Proof.
move=> ig; rewrite to_graph_succ //; apply/fsetP=> y.
rewrite !inE /=; apply/idP/idP.
- case/andP=> yg /neighboursP; rewrite yg ig.
  case/(_ isT isT)=> k k_nei <-.
  apply/(nthP (default (neighbours g i))).
  by exists (int_to_nat k); rewrite ?size_arr_to_seq ?nth_arr_to_seq -?ltEint_nat // int_to_natK.
- case/andP=> yg.
  case/(nthP (default (neighbours g i)))=> k; rewrite size_arr_to_seq=> k_len.
  rewrite nth_arr_to_seq // => y_eq; apply/andP; split=> //.
  apply/neighboursP; rewrite ?yg ?xg //; exists (nat_to_int k)=> //.
  rewrite ltEint_nat nat_to_intK // inE.
  exact/(ltn_trans k_len)/int_thresholdP.
Qed.

(* Section Quotient.

Context (gl gr : graph.graph) (morf morf' : array int) (t : array (array (int * int))).

Hypothesis quot_h : graph.quot_graph gl gr morf morf' t.

Lemma to_graph_quot :
  (to_graph_struct gr) = ((fun i => morf.[i]) @/ (to_graph_struct gl)).
Proof.
apply/gisof_idE/gisofE; split=> //.
- apply/fsetP=> x; rewrite vtx_quot_graph !inE /= to_graph_vtx.
  apply/idP/idP.
  + case/(quot_graph_morf_complete quot_h)=> x' x'gl ->.
    by apply/in_imfset=> /=; rewrite to_graph_vtx.
  + case/imfsetP=> /= x'; rewrite to_graph_vtx=> x'gl ->.
    exact/(quot_graph_morf_correct quot_h).
- move=> x y; rewrite !to_graph_vtx=> xgr ygr.
  rewrite to_graph_edge ?to_graph_vtx //.
  apply/idP/idP.
  + case/(quot_graph_edge_morf quot_h xgr ygr)=> /[swap].
    case=> x' [y'] [x'gl y'gl <- <- gl_xy'] ?. 
    apply/edge_quot_graph; exists x'; exists y'; split=> //=.
    by rewrite to_graph_edge ?to_graph_vtx.
  + case/edge_quot_graph=> x' [y'] [x_eq y_eq ?].
    move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
    rewrite !to_graph_vtx=> x'gl y'gl.
    rewrite to_graph_edge ?to_graph_vtx // => gl_xy'.
    apply/(quot_graph_edge_morf quot_h xgr ygr); split=> //.
    by exists x', y'; split.
Qed.

End Quotient. *)
End GraphStruct.

(* Section LabelEquiv.

Definition label_equiv {T T' : Type} (a : array T) (b : array T') (r : T -> T' -> bool):=
  length a = length b /\ forall i, (i < length a)%O -> r a.[i] b.[i]. 

Lemma label_equiv_get {T T' : Type} (a : array T) (b : array T') (r : T -> T' -> bool):
  label_equiv a b r -> forall i, (i < length a)%O -> r a.[i] b.[i].
Proof. by case. Qed.

Lemma label_equiv_length {T T' : Type} (a : array T) (b : array T') (r : T -> T' -> bool):
  label_equiv a b r -> length a = length b.
Proof. by case. Qed.

Lemma lbl_eq_arr_to_seq {T T' : Type} (a : array T) (b : array T') (r : T -> T' -> bool):
  label_equiv a b r <-> (length a = length b :> nat) /\ (forall i, (i < length a)%nat ->
    r (nth (default a) (arr_to_seq a) i) (nth (default b) (arr_to_seq b) i)).
Proof.
split.
- case=> eq_len h; split; rewrite eq_len //.
  move=> i i_len; rewrite !nth_arr_to_seq ?eq_len //.
  apply: h; rewrite eq_len ltEint_nat nat_to_intK //.
  apply/(ltn_trans i_len)/int_thresholdP.
- case=> /int_to_nat_inj eq_len h; split=> //= i.
  rewrite ltEint_nat=> /[dup] ? /h; rewrite !nth_arr_to_seq -?eq_len //.
  by rewrite int_to_natK.
Qed.

Lemma label_equiv_inj {T T' : Type} (a : array T) (b : array T') (r : T -> T' -> bool)
  (e : T -> T -> bool) (e' : T' -> T' -> bool):
  label_equiv a b r -> 
  (forall i j, (i < length a)%O -> (j < length a)%O -> e a.[i] a.[j] -> i = j) ->
  (forall i j i' j', (i < length a)%O -> (i' < length b)%O -> (j < length a)%O -> (j' < length b)%O ->
    r a.[i] b.[i'] -> r a.[j] b.[j'] -> e a.[i] a.[j] <-> e' b.[i'] b.[j']) ->
  forall i j, (i < length b)%O -> (j < length b)%O -> e' b.[i] b.[j] -> i = j.
Proof.
case=> len_eq r_ab a_inj r_equiv i j ib jb.
move: (r_ab i) (r_ab j); rewrite len_eq ib jb => /(_ isT) + /(_ isT).
move/r_equiv=> /[apply] /[apply]; rewrite len_eq ib jb=> /(_ isT isT isT isT).
by apply/a_inj; rewrite len_eq.
Qed.

Lemma label_equiv_sort {T T' : Type} (a : array T) (b : array T')
  (r : T -> T' -> bool) (r_sort : rel T) (r_sort' : rel T'):
  label_equiv a b r ->
  (forall x y x' y', r x x' -> r y y' -> r_sort x y = r_sort' x' y') ->
  rel_sorted a r_sort = rel_sorted b r_sort'.
Proof.
case=> len_eq r_get r_sort_sort'; rewrite /rel_sorted.
apply/(sorted_rel_pair (r:=r) (x:=(default a)) (x':=(default b)))=> //.
- by rewrite !size_arr_to_seq len_eq.
- move=> k; rewrite size_arr_to_seq=> k_len; rewrite !nth_arr_to_seq -?len_eq //.
  apply/r_get; rewrite ltEint_nat nat_to_intK //.
  apply/(ltn_trans k_len)/int_thresholdP.
Qed.

Section Quotient.

Context {T1 T2 T1' T2': Type}.
Context (g1 g2 : graph.graph). 
Context (lbl1 : array T1) (lbl2 : array T2) (lbl1' : array T1') (lbl2' : array T2').
Context (r_lbl : T1 -> T2 -> bool) (r_lbl' : T1' -> T2' -> bool).
Context (r_sort : rel T2) (r_sort' : rel T2').
Context (r1 : T1 -> T1' -> bool) (r2 : T2 -> T2' -> bool).
Context (morf morf': array int) (t : array (array (int * int))).

Hypothesis g1g2 : graph.lbl_quot g1 g2 morf morf' t lbl1 lbl2 r_lbl r_sort.
Hypothesis lbl_equiv1 : label_equiv lbl1 lbl1' r1.
Hypothesis lbl_equiv2 : label_equiv lbl2 lbl2' r2.
Hypothesis r2_h : forall x y x' y', r2 x x' -> r2 y y' -> r_sort x y = r_sort' x' y'.
Hypothesis r1212'_h : forall i j, (i < length lbl1)%O -> (j < length lbl2)%O -> r_lbl lbl1.[i] lbl2.[j] <-> r_lbl' lbl1'.[i] lbl2'.[j].

Lemma label_equiv_quot: graph.lbl_quot g1 g2 morf morf' t lbl1' lbl2' r_lbl' r_sort'.
Proof.
case: g1g2=> quot_g1g2 lbl12 vert_lbl12 sort_lbl2.
split=> //.
- rewrite /label_check !(lbl_quot_label g1g2) (label_equiv_length lbl_equiv1).
  by rewrite (label_equiv_length lbl_equiv2).
- rewrite /vert_check=> i ig1.
  apply/r1212'_h; try apply/vert_lbl12=> //.
  + by rewrite -lbl12 (quot_graph_length quot_g1g2).
  + move: (quot_graph_morf_correct quot_g1g2); rewrite -lbl12.
    by apply; rewrite /mem_vertex (quot_graph_length quot_g1g2). 
- by rewrite /sort_check -(label_equiv_sort lbl_equiv2 r2_h).
Qed.

End Quotient.
End LabelEquiv. *)

Section GraphRepr.

Context (t : Type) (T : choiceType) (g : graph.graph) (lbl : array t) (G : high_graph.graph T).
Context (conv : int -> T) (rel_t : t -> T -> Prop).

Definition repr_graph := [/\
  correct_label g lbl,
  gisof (to_graph_struct g) G conv &
  forall i, mem_vertex g i -> rel_t lbl.[i] (conv i)].

Lemma repr_graph_correct : repr_graph -> correct_label g lbl.
Proof. by case. Qed. 

Lemma repr_graph_conv_inj : repr_graph -> 
  forall i j, mem_vertex g i -> mem_vertex g j -> conv i = conv j -> i = j.
Proof. by case=> _ /gisof_inj conv_inj _ i j ig jg /conv_inj; apply; rewrite to_graph_vtx. Qed.

Lemma repr_graph_vtx_low: repr_graph -> forall i,
  mem_vertex g i -> conv i \in vertices G.
Proof.
case=> _ gisof_repr _ i ig; rewrite -(gisof_vtx gisof_repr); apply/in_imfset=> /=.
by rewrite to_graph_vtx.
Qed.

Lemma repr_graph_vtx_high: repr_graph ->
  forall x : T, x \in vertices G -> exists2 i, mem_vertex g i & conv i = x.
Proof.
case=> _ gisof_repr _ x; rewrite -(gisof_vtx gisof_repr).
case/imfsetP=> /= i; rewrite to_graph_vtx => ig ->.
by exists i.
Qed.

Lemma repr_graph_edge_low: repr_graph -> forall i j,
  mem_vertex g i -> mem_vertex g j ->
  mem_edge g i j -> edges G (conv i) (conv j).
Proof.
case=> _ repr_gisof _ i j ig jg g_ij.
by rewrite -(gisof_edge repr_gisof) ?to_graph_vtx // to_graph_edge.
Qed.

Lemma repr_graph_edge_high: repr_graph ->
  {in vertices G&, forall x y, edges G x y ->
  exists i, (exists j, 
    [/\ mem_vertex g i, mem_vertex g j, 
    x = (conv i), y = (conv j) & 
    mem_edge g i j])}.
Proof.
move=> /[dup] rep [_ repr_gisof _] x y.
case/(repr_graph_vtx_high rep)=> i ig <-.
case/(repr_graph_vtx_high rep)=> j jg <-.
rewrite -(gisof_edge repr_gisof) ?to_graph_vtx // to_graph_edge //.
by move=> g_ij; exists i,j; split.
Qed.

Lemma repr_graph_succ: repr_graph->
  forall i, mem_vertex g i->
  successors G (conv i) = conv @` [fset j : int | (mem_vertex g j) && (j \in arr_to_seq (neighbours g i))].
Proof.
case=> _ /gisof_succ + _ i ig.
move/(_ i); rewrite to_graph_vtx=> /(_ ig) ->.
by rewrite to_graph_succ_nei.
Qed.

Lemma repr_graph_card_succ: repr_graph->
  (forall i, mem_vertex g i -> lti_sorted (neighbours g i))->
  (forall i j, mem_vertex g i -> (j < nb_neighbours g i)%O -> mem_vertex g (neighbours g i).[j])->
  forall i, mem_vertex g i-> #|` successors G (conv i)| = nb_neighbours g i.
Proof.
move=> gG stt_h nei_h i ig.
rewrite (repr_graph_succ gG ig) card_in_imfset /=; last first.
  move=> x y; rewrite !inE /= => /andP [+ _] /andP [+ _]; exact: (repr_graph_conv_inj gG).
rewrite card_imfset //=.
set S := [seq _ <- _ | _ & _]; suff: perm_eq S (arr_to_seq (neighbours g i)) by
  move/perm_size=> ->; rewrite size_arr_to_seq.
apply/uniq_perm; [ exact/filter_uniq/enum_uniq | exact/lti_sorted_uniq/stt_h | ].
move=> x; rewrite mem_filter mem_enum inE andbT.
apply/andb_idl; case/mapP=> k; rewrite mem_irangeE le0x /=.
move=> k_nei ->; exact/(nei_h i k ig).
Qed.

Lemma repr_graph_rel: repr_graph->
  forall i, mem_vertex g i -> rel_t lbl.[i] (conv i).
Proof. by case. Qed.

End GraphRepr.



(* Section GraphRepr. 

Context {T : choiceType} (g : graph.graph) (lbl : array T) (G : high_graph.graph T).

Definition repr_graph := correct_label g lbl /\ gisof (to_graph_struct g) G (fun i => lbl.[i]).

Lemma repr_lbl_inj: 
  repr_graph -> 
  {in vertices (to_graph_struct g) &, injective (fun i => lbl.[i])}.
Proof. by case=> ? []. Qed.

Lemma repr_vtx:
  repr_graph -> forall x,
  x \in vertices G = [exists i, mem_vertex g i && (lbl.[i] == x)].
Proof.
case=> _ /gisofE [_ <- _].
move=> x; apply/idP/idP.
- case/imfsetP=> x' /=; rewrite to_graph_vtx=> ? ->.
  by apply/existsP; exists x'; rewrite eqxx andbT.
- case/existsP=> x' /andP [? /eqP <-]; apply/in_imfset=> /=.
  by rewrite to_graph_vtx.
Qed.

Lemma repr_vtx_lbl:
  repr_graph -> forall i, mem_vertex g i -> lbl.[i] \in vertices G.
Proof. by move=> ? i gi; rewrite repr_vtx //; apply/existsP; exists i; rewrite gi eqxx. Qed.

Lemma repr_vtx_fset:
  repr_graph -> vertices G = [fset lbl.[i] | i : int & mem_vertex g i].
Proof.
move=> repr_g; apply/fsetP=> x; rewrite (repr_vtx repr_g).
apply/idP/idP.
- case/existsP=> x' /andP [x'g /eqP <-]; exact: in_imfset.
- case/imfsetP=> /= x'; rewrite inE=> x'g ->; apply/existsP; exists x'.
  by rewrite x'g eqxx.
Qed.

Lemma repr_vtx_card: repr_graph -> #|` vertices G| = length g.
Proof.
move=> /[dup] gG /repr_vtx_fset ->; rewrite card_in_imfset /=.
- rewrite (@perm_size _ _ (irange0 (length g))) ?size_irange0 //.
  apply/uniq_perm; rewrite ?filter_uniq -?enumT ?enum_uniq ?uniq_irange //.
  by move=> y; rewrite mem_filter mem_irangeE le0x mem_enum inE ltEint andbT.
- by move=> ????; apply/(repr_lbl_inj gG); rewrite to_graph_vtx.
Qed.

Lemma repr_edge:
  repr_graph -> forall x y,
    edges G x y = [exists i, [exists j, 
    [&& mem_vertex g i, mem_vertex g j,
    lbl.[i] == x, lbl.[j] == y & mem_edge g i j]]].
Proof.
move=> gG x y.
case: (gG)=> /eqb_spec g_lbl gG_gisof.
apply/idP/idP.
- move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
  rewrite !(repr_vtx gG)=> /existsP [i] /andP [ig /eqP <-].
  case/existsP=> j /andP [jg /eqP <-].
  rewrite -(gisof_morph gG_gisof) ?to_graph_edge ?to_graph_vtx //.
  move=> ?; apply/existsP; exists i; apply/existsP; exists j.
  by rewrite ig jg !eqxx.
- case/existsP=> i /existsP [j] /and5P [ig jg /eqP <- /eqP <- g_ij].
  by rewrite -(gisof_morph gG_gisof) ?to_graph_edge ?to_graph_vtx.
Qed.

Lemma repr_succ x:
  repr_graph -> mem_vertex g x ->
  successors G lbl.[x] = 
  [fset lbl.[y] | y : int & ((mem_vertex g y) && (mem_edge g x y))].
Proof.
move=> gG xg; apply/fsetP=> z; apply/idP/idP.
- rewrite in_succE (repr_edge gG).
  case/existsP=> i /existsP [j] /and5P [ig jg].
  move/eqP/(repr_lbl_inj gG); rewrite !to_graph_vtx ig xg=> -> //.
  move/eqP=> <- xjg; apply/in_imfset; rewrite inE.
  by apply/and3P; split.
- case/imfsetP=> /= j; rewrite inE=> /andP [jg xjg] ->.
  rewrite in_succE (repr_edge gG).
  by apply/existsP; exists x; apply/existsP; exists j; apply/and5P; split.
Qed.

End GraphRepr.

Section Giso.

Context {T : choiceType} (g : graph.graph) (lbl : array T).

Lemma repr_graph_giso_id (G G' : high_graph.graph T):
  G = G' -> repr_graph g lbl G' -> repr_graph g lbl G.
Proof. by move=> ->. Qed.

(*TODO : need some lemmas on gisof*)
End Giso.

(* Section GraphRepr.

Context {T : Type} {T' : choiceType} (r : T -> T' -> Prop).
Context (g : graph.graph) (lbl: array T) (G : high_graph.graph T').

Definition repr_graph := exists2 lbl' : array T', 
  label_equiv lbl lbl' r & repr_graph_base g lbl' G.

End GraphRepr. *)

Section Quotient.

Context {T1 T2 : choiceType}.
Context (g1 g2: graph.graph) (lbl1 : array T1) (lbl2 : array T2).
Context (G1 : high_graph.graph T1).

Hypothesis g1G1 : repr_graph g1 lbl1 G1.

Context (morf morf': PArray.array int) (t : array (array (int * int))) (F : T1 -> T2) (r_sort : rel T2).
Hypothesis g1g2 : lbl_quot g1 g2 morf morf' t lbl1 lbl2
  (fun t1 t2=> F t1 == t2) r_sort.
Hypothesis r_sort_irr : irreflexive r_sort.
Hypothesis r_sort_trans : transitive r_sort.

Lemma repr_quot_inj: 
  {in vertices ([eta get morf] @/ to_graph_struct g1) &, injective (get lbl2)}.
Proof.
move=> i j; rewrite vtx_quot_graph.
case/imfsetP => /= [x'] + -> /imfsetP /= [y'] + ->.
rewrite !to_graph_vtx => x'g1 y'g1.
move: (lbl_quot_sort g1g2)=> /(sorted_rel_inj r_sort_irr r_sort_trans).
apply; rewrite ltEint -(lbl_quot_label g1g2);
  exact: (quot_graph_morf_correct (lbl_quot_quot g1g2)).
Qed.

Lemma repr_quot_vtx:
  get lbl2 @` vertices ([eta get morf] @/ to_graph_struct g1) =
  vertices (F @/ G1).
Proof.
apply/fsetP=> x; apply/idP/idP.
- case/imfsetP=> /= x'; rewrite vtx_quot_graph.
  case/imfsetP=> /= x''; rewrite to_graph_vtx.
  move=> x''g1 -> ->; rewrite vtx_quot_graph.
  apply/imfsetP=> /=; exists lbl1.[x'']; rewrite ?(lbl_quot_vert g1g2).
  + by rewrite (repr_vtx g1G1); apply/existsP; exists x''; rewrite eqxx x''g1.
  + case: g1g2=> quot_h _ vert_h _; apply/eqP; rewrite eq_sym. 
    by apply: vert_h; rewrite -(quot_graph_length quot_h). 
- rewrite !vtx_quot_graph; case/imfsetP=> /= x'.
  rewrite (repr_vtx g1G1); case/existsP=> x'' /andP [x''g1 /eqP <-] ->.
  move:(lbl_quot_vert g1g2)=> /(_ x'').
  rewrite -(quot_graph_length (lbl_quot_quot g1g2))=> /(_ x''g1)/eqP ->.
  apply/in_imfset=> /=.
  by apply/in_imfset=> /=; rewrite to_graph_vtx.
Qed.

Lemma repr_quot_edge: 
  {in vertices ([eta get morf] @/ to_graph_struct g1) &,
  forall x y : int_choiceType,
  edges ([eta get morf] @/ to_graph_struct g1) x y =
  edges (F @/ G1) lbl2.[x] lbl2.[y]}.
Proof.
move=> x y xG1 yG1.
apply/idP/idP.
- case/edge_quot_graph=> /= x' [y'].
  case=> x_eq y_eq x_n_y /[dup] /[dup] /edge_vtxl + /edge_vtxr.
  rewrite !to_graph_vtx => x'g1 y'g1; rewrite to_graph_edge ?to_graph_vtx //.
  move=> g1_xy'; apply/edge_quot_graph; exists lbl1.[x'], lbl1.[y'].
  rewrite (repr_edge g1G1). 
  move:(lbl_quot_vert g1g2)=> vert_g1g2. 
  move: (vert_g1g2 x') (vert_g1g2 y').
  rewrite -(quot_graph_length (lbl_quot_quot g1g2))=> /(_ x'g1)/eqP ->.
  move/(_ y'g1)/eqP=> ->; rewrite x_eq y_eq.
  split=> //.
  + move: x_n_y; apply: contra_neq=> /repr_quot_inj.
    apply; rewrite vtx_quot_graph; apply/imfsetP=> /=.
    * by exists x'; rewrite ?to_graph_vtx ?x_eq.
    * by exists y'; rewrite ?to_graph_vtx ?y_eq.
  + by apply/existsP; exists x'; apply/existsP; exists y'; apply/and5P; split.
- case/edge_quot_graph=> x' [y'] [Fx' Fy' lbl2_xy].
  rewrite (repr_edge g1G1)=> /existsP [x''] /existsP [y''].
  case/and5P=> x''g1 y''g1 /eqP lbl1x'' /eqP lbl1y'' g1_xy''.
  apply/edge_quot_graph; exists x'', y''; split.
  + move: Fx'; rewrite -lbl1x''. 
    move:(lbl_quot_vert g1g2)=> /(_ x'').
    rewrite -(quot_graph_length (lbl_quot_quot g1g2))=> /(_ x''g1)/eqP ->.
    move/(repr_quot_inj _ xG1); apply; rewrite vtx_quot_graph.
    by apply/in_imfset; rewrite to_graph_vtx.
  + move: Fy'; rewrite -lbl1y''. 
    move:(lbl_quot_vert g1g2)=> /(_ y'').
    rewrite -(quot_graph_length (lbl_quot_quot g1g2))=> /(_ y''g1)/eqP ->.
    move/(repr_quot_inj _ yG1); apply; rewrite vtx_quot_graph.
    by apply/in_imfset; rewrite to_graph_vtx.
  + by move: lbl2_xy; apply/contra_neq=> ->.
  + by rewrite to_graph_edge ?to_graph_vtx.
Qed.


Lemma repr_graph_quot: repr_graph g2 lbl2 (F @/ G1).
Proof.
split.
- by rewrite /correct_label -(lbl_quot_label g1g2) eqb_refl.
- move: (lbl_quot_quot g1g2)=> /to_graph_quot/gisof_idE/gisof_trans; apply.
  apply/gisofE; split.
  + exact: repr_quot_inj.
  + exact: repr_quot_vtx.
  + exact: repr_quot_edge.
Qed.

End Quotient. *)

 *)
