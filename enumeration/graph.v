(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From Coq Require Import PArray Uint63.
Require Import PArith.BinPos PArith.BinPosDef.
Require Import NArith.BinNat NArith.BinNatDef.
From Polyhedra Require Import extra_misc.
Require Import extra_int extra_array.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.Theory.

(* -------------------------------------------------------------------- *)
Definition graph := array (array int).

Module GraphUtils.

Definition is_empty (g : graph) := (length g =? 0)%uint63.

Definition graph_length (g : graph) := length g.

Definition mem_vertex (g : graph) (x : int):= (x <? length g)%uint63.

Definition neighbours (g : graph) (x : int) := g.[x].

Definition nb_neighbours (g : graph) (x : int) := length g.[x].

Definition neighbour_fold {A : Type} (f : int -> A -> A) (a : A) (g : graph) (i : int):=
  PArrayUtils.fold (fun i a'=> if mem_vertex g i then f i a' else a') g.[i] a.
    
Definition neighbour_all (f : int -> bool) (g : graph) (i : int):=
  PArrayUtils.all (fun j=> if mem_vertex g j then f j else true) g.[i].

Definition mem_edge (g : graph) (x y : int) :=
  neighbour_fold (fun j acc=> acc || (j =? y)%uint63) false g x.

End GraphUtils.

Section Defs.

Definition is_empty (g : graph) := length g == 0%uint63.

Definition graph_length (g : graph) := length g.

Definition mem_vertex (g : graph) (x : int):= (x < length g)%O.

Definition neighbours (g : graph) (x : int) := g.[x].

Definition nb_neighbours (g : graph) (x : int) := length g.[x].

Definition neighbour_fold {A : Type} (f : int -> A -> A) (a : A) (g : graph) (i : int):=
  arr_fold (fun i a'=> if mem_vertex g i then f i a' else a') g.[i] a.
    
Definition neighbour_all (f : int -> bool) (g : graph) (i : int):=
  arr_all (fun j=> if mem_vertex g j then f j else true) g.[i].

Definition mem_edge (g : graph) (x y : int) :=
  neighbour_fold (fun j acc=> acc || (j =? y)%uint63) false g x.

Section Equiv.

Lemma is_emptyE (g : graph): GraphUtils.is_empty g = is_empty g.
Proof. by rewrite /GraphUtils.is_empty /is_empty eqEint. Qed.

Lemma graph_lengthE (g : graph): 
  GraphUtils.graph_length g = graph_length g.
Proof. by []. Qed.

Lemma mem_vertexE (g : graph) (x : int):
  GraphUtils.mem_vertex g x = mem_vertex g x.
Proof. by rewrite /GraphUtils.mem_vertex -ltEint. Qed.

Lemma neighboursE (g : graph) (x : int):
  GraphUtils.neighbours g x = neighbours g x.
Proof. by []. Qed.

Lemma nb_neighboursE (g : graph) (x : int):
  GraphUtils.nb_neighbours g x = nb_neighbours g x.
Proof. by []. Qed.

Lemma neighbour_foldE {A : Type} (f : int -> A -> A) (a : A) (g : graph) (i : int):
  GraphUtils.neighbour_fold f a g i = neighbour_fold f a g i.
Proof. by rewrite /GraphUtils.neighbour_fold arr_foldE. Qed.

Lemma neighbour_allE (f : int -> bool) (g : graph) (i : int):
  GraphUtils.neighbour_all f g i = neighbour_all f g i.
Proof. by rewrite /GraphUtils.neighbour_all arr_allE. Qed.

Lemma mem_edgeE (g : graph) (x y : int):
  GraphUtils.mem_edge g x y = mem_edge g x y.
Proof. by rewrite /GraphUtils.mem_edge neighbour_foldE. Qed.

End Equiv.
End Defs.

Section Proofs.

Section Base.
Context (g : graph).

Lemma is_emptyPn: ~~ is_empty g -> mem_vertex g 0%uint63.
Proof.
rewrite /is_empty /mem_vertex lt_neqAle le0x andbT.
by rewrite eq_sym.
Qed.

Lemma wB_nat_graph x: mem_vertex g x -> 
  int_to_nat x \in gtn int_threshold.
Proof.
rewrite /mem_vertex ltEint_nat inE; move/ltn_trans; apply; exact/int_thresholdP.
Qed.

Lemma wB_nat_graph_length (x : 'I_(graph_length g)): val x \in gtn int_threshold.
Proof.
rewrite inE; apply/(@ltn_trans (graph_length g))=> //=; exact/int_thresholdP.
Qed.

Lemma mem_vertex_ord (i : 'I_(graph_length g)) : mem_vertex g (nat_to_int i).
Proof.
by rewrite /mem_vertex ltEint_nat nat_to_intK ?wB_nat_graph_length.
Qed.

Lemma neighbour_foldP (T : Type) f (x : T) i:
  mem_vertex g i ->
  neighbour_fold f x g i = 
  foldl (fun a j=> f j a) x [seq j <- (arr_to_seq (neighbours g i)) | mem_vertex g j].
Proof.
move=> ig; rewrite /neighbour_fold /arr_fold.
elim/last_ind: (arr_to_seq _)=> //= t h IH.
rewrite filter_rcons.
by case: ifP=> hg; rewrite !foldl_rcons hg IH.
Qed. 

Lemma mem_edgeP (i j : int): mem_vertex g i ->
  mem_edge g i j = (j \in [seq y <- arr_to_seq (neighbours g i) | mem_vertex g y]).
Proof.
move=> ig.
rewrite /mem_edge neighbour_foldP //.
elim/last_ind: (arr_to_seq _)=> //= t h IH.
rewrite !filter_rcons.
case: ifP=> // hg; rewrite foldl_rcons mem_rcons inE IH.
rewrite orbC; congr orb; apply/idP/idP=> [/eqb_spec ->|/eqP ->] //.
exact/eqb_refl.
Qed.

Lemma neighboursP i j: mem_vertex g i -> mem_vertex g j ->
  reflect (exists2 k, (k < nb_neighbours g i)%O & (neighbours g i).[k] = j)
  (mem_edge g i j).
Proof.
move=> ig jg; rewrite mem_edgeP //; apply/(iffP idP).
- rewrite mem_filter=> /andP [_].
  case/(nthP (default (neighbours g i)))=> k.
  rewrite size_arr_to_seq=> k_len; rewrite nth_arr_to_seq // => <-.
  exists (nat_to_int k)=> //; rewrite ltEint_nat nat_to_intK //.
  rewrite inE; exact/(ltn_trans k_len)/int_thresholdP.
- case=> k k_len j_eq; rewrite mem_filter jg /=.
  apply/(nthP (default (neighbours g i))); exists k.
  + by rewrite size_arr_to_seq -ltEint_nat.
  + by rewrite nth_arr_to_seq -?ltEint_nat ?int_to_natK.
Qed.

Lemma neighbour_allP (f : int -> bool) (i : int):
  mem_vertex g i ->
  reflect (forall k, (k < nb_neighbours g i)%O ->
  let n := (neighbours g i).[k] in
  mem_vertex g n -> f n)
  (neighbour_all f g i).
Proof.
move=> ig; apply/(iffP idP).
- rewrite /neighbour_all; move/all_arr=> + k.
  move=> /[apply]; rewrite /neighbours.
  by case: ifP.
- move=> h; apply/all_arr=> k k_len; case: ifP=> //.
  move: (h k k_len); exact.
Qed.

End Base.

End Proofs.

(*For now, labeled graphs are just given by a graph and a map int -> T*)
Section LabeledGraph.

Definition correct_label {T : Type} (g : graph) (lbl : array T):=
  (graph_length g =? length lbl)%uint63.

Lemma correct_label_mem {T : Type} (g : graph) (lbl : array T):
  correct_label g lbl -> forall x, mem_vertex g x = (x < length lbl)%O.
Proof. by move/eqb_spec=> <- x; rewrite ltEint. Qed.

End LabeledGraph.



(* Lemma quot_graph_morf_correct: forall i, mem_vertex gl i ->
  mem_vertex gr morph.[i].
Proof.
case/and5P: quot_h=> _ + _ _ _; rewrite /vertex_morf_check. 
move/all_arr.
by rewrite -quot_graph_length.
Qed. *)




(* Lemma quot_graph_morf_complete: forall j, mem_vertex gr j ->
  exists2 i, mem_vertex gl i & (j = morph.[i]). 
Proof.
move=> j j_gr.
case/and5P: quot_h=> len_h _ _ + _.
move/allP=> /(_ j); rewrite mem_irangeE le0x /=.
case/andP: len_h=> /andP [_ /eqP] <- _; rewrite ltEint. 
by case/(_ j_gr)/andP=> ? /eqP ?; exists morph'.[j].
Qed.

Lemma quot_graph_nei_correct: forall i, mem_vertex gl i ->
  forall j, (j < length (neighbours gl i))%O -> mem_vertex gl (neighbours gl i).[j].
Proof.
move=> i igl j j_nei.
case/and5P: quot_h=> /andP [/andP [/eqP len_gl _] _] _ /allP + _ _.
move/(_ i); rewrite mem_irangeE le0x -len_gl /= ltEint.
by case/(_ igl)/and3P=> _ _ /all_arr /(_ j j_nei).
Qed.

Lemma quot_graph_edge_morf i j: mem_vertex gr i -> mem_vertex gr j ->
  reflect 
  ((i != j) /\ (exists i', exists j', [/\ mem_vertex gl i', mem_vertex gl j', morph.[i'] = i, morph.[j'] = j & mem_edge gl i' j']))
  (mem_edge gr i j).
Proof.
move=> igr jgr; case/and5P: quot_h=> /andP [/andP [/eqP len_gl /eqP len_gr]]. 
move=> len_t _ edge_h _ /allP t_h.
apply/(iffP idP).
- move=> /[dup] ij_gr /(neighboursP igr jgr) [k k_nei j_eq].
  split.
  + apply/eqP=> ij; move: ij_gr; rewrite ij.
    case: (quot_graph_morf_complete jgr)=> j' j'gl ->.
    move/allP: edge_h=> /(_ j'); rewrite -len_gl mem_irangeE le0x /= ltEint.
    by case/(_ j'gl)/and3P=> _ /negPf ->.
  + move: (t_h i); rewrite mem_irangeE le0x /= ltEint.
    move/(_ igr)/allP=> /(_ k); rewrite mem_irangeE le0x k_nei.
    move/(_ isT); case: (t.[i].[k])=> i' k' /and4P [i'gl k'nei /eqP i'_eq /eqP nei'_eq].
    exists i', ((neighbours gl i').[k']); split=> //; rewrite -?j_eq //.
    * apply/quot_graph_nei_correct=> //.
    * apply/neighboursP=> //; last exists k'=> //; exact/quot_graph_nei_correct.
- case=> i_n_j -[i'] [j'] [i'gl j'gl i_eq j_eq ij'_gl].
  rewrite -i_eq -j_eq; move/allP: edge_h; rewrite -len_gl.
  move/(_ i'); rewrite mem_irangeE le0x /= ltEint.
  case/(_ i'gl)/and3P=> /(neighbour_allP _ i'gl).
  case/(neighboursP i'gl j'gl): ij'_gl=> k k_len j'_eq /(_ k k_len) /=.
  by rewrite j'_eq i_eq j_eq => /(_ j'gl) /implyP /(_ i_n_j).
Qed. *)

(* End Proofs.

End QuotientGraph.

Module LabelQuotientUtils.

(* Context (gl gr : graph) (morph morph': array int) (t : array (array (int * int))).
Context {T1 T2 : Type} (lbll : array T1) (lblr : array T2).
Context (r_lbl : T1 -> T2 -> bool) (r_sort : T2 -> T2 -> bool). *)

Definition is_label_check {T1 T2 : Type} (gl gr : graph) (lbll : array T1) (lblr : array T2):=
  (correct_label gl lbll) && (correct_label gr lblr).

Definition is_vert_check {T1 T2 : Type} (morph : array int) (lbll : array T1) 
  (lblr : array T2) (r_lbl : T1 -> T2 -> bool):= 
  IFold.iall (fun i => r_lbl lbll.[i] lblr.[morph.[i]]) (length morph).

Definition is_sort_check {T2 : Type} (lblr : array T2) 
  (r_sort : T2 -> T2 -> bool):= 
  PArrayUtils.is_sorted_rel lblr r_sort.

Definition is_lbl_quot (gl gr : graph) (morph morph' : array int)
  (t : array (array (int * int))) {T1 T2 : Type} (lbll : array T1)
  (lblr : array T2) (r_lbl : T1 -> T2 -> bool) 
  (r_sort : T2 -> T2 -> bool) := 
  [&& ImgGraph.quot_graph gl gr morph morph' t, 
      is_label_check gl gr lbll lblr,
      is_vert_check morph lbll lblr r_lbl & 
      is_sort_check lblr r_sort].

End LabelQuotientUtils.

Section LabelQuotient.

Context (gl gr : graph) (morph morph': array int) (t : array (array (int * int))).
Context {T1 T2 : Type} (lbll : array T1) (lblr : array T2).
Context (r_lbl : T1 -> T2 -> bool) (r_sort : T2 -> T2 -> bool).

Definition is_label_check:=
  (correct_label gl lbll) && (correct_label gr lblr).

Definition is_vert_check:= 
  iall (fun i => r_lbl lbll.[i] lblr.[morph.[i]]) (length morph).

Definition is_sort_check:= 
  is_sorted_rel lblr r_sort.

Definition is_lbl_quot:= 
  [&& quot_graph gl gr morph morph' t, 
      is_label_check,
      is_vert_check& 
      is_sort_check].

Definition vert_check := forall i, (i < length morph)%O -> r_lbl lbll.[i] lblr.[morph.[i]].
Definition label_check := ((length gl = length lbll) * (length gr = length lblr))%type.
Definition sort_check := rel_sorted lblr r_sort.
Definition lbl_quot :=
  [/\ quot_graph gl gr morph morph' t, label_check, 
  vert_check & sort_check].

Section Equiv.

Lemma is_lbl_quotE: 
  LabelQuotientUtils.is_lbl_quot gl gr morph morph' t lbll lblr r_lbl r_sort =
  is_lbl_quot.
Proof.
rewrite /LabelQuotientUtils.is_lbl_quot quot_graphE.
rewrite /LabelQuotientUtils.is_vert_check iallE.
by rewrite /LabelQuotientUtils.is_sort_check is_sorted_relE.
Qed.

End Equiv.

Section Proofs.

Hypothesis lbl_quot_h : lbl_quot.

Lemma lbl_quot_quot: quot_graph gl gr morph morph' t.
Proof. by case: lbl_quot_h. Qed.

Lemma lbl_quot_vert: vert_check.
Proof. by case: lbl_quot_h. Qed.
  
Lemma lbl_quot_label: label_check.
Proof. by case: lbl_quot_h. Qed.

Lemma lbl_quot_sort: sort_check.
Proof. by case: lbl_quot_h. Qed.
  
End Proofs.

End LabelQuotient.

Section QuotientGraphProofs.

Context (gl gr : graph) (morph morph' : array int) (t : array (array (int * int))).
Context {T1 T2 : Type} (lbll : array T1) (lblr : array T2).
Context (r_lbl : T1 -> T2 -> bool) (r_sort : T2 -> T2 -> bool).

Lemma label_checkP: 
  reflect 
    (label_check gl gr lbll lblr) 
    (is_label_check gl gr lbll lblr).
Proof.
apply/(iffP idP).
- by case/andP=> /eqb_spec ? /eqb_spec ?; split.
- by case=> ??; apply/andP; split; apply/eqb_spec.
Qed.

Lemma vert_checkP:
  reflect
    (vert_check morph lbll lblr r_lbl)
    (is_vert_check morph lbll lblr r_lbl).
Proof.
apply/(iffP idP).
- by move/allP=> h i i_morf; apply/h; rewrite mem_irangeE le0int.
- move=> h; apply/allP=> i; rewrite mem_irangeE le0int /=.
  exact: h.
Qed.

Lemma sort_checkP:
  reflect
    (sort_check lblr r_sort)
    (is_sort_check lblr r_sort).
Proof. rewrite /is_sort_check /sort_check rel_sortedP; exact: idP. Qed.

Lemma is_lbl_quotP:
  reflect
    (lbl_quot gl gr morph morph' t lbll lblr r_lbl r_sort)
    (is_lbl_quot gl gr morph morph' t lbll lblr r_lbl r_sort). 
Proof.
apply/(iffP idP).
- case/and4P=> ? /label_checkP ? /vert_checkP ? /sort_checkP ?. 
  by split.
- case=> ? /label_checkP ? /vert_checkP ? /sort_checkP ?.
  by apply/and4P; split.
Qed.

End QuotientGraphProofs.

(* -------------------------------------------------------------------- *)
 *)
