(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import fsetmin extra_misc.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset.

(* -------------------------------------------------------------------- *)
Section FsFun.
Context (K : choiceType) (V : eqType) (d : K -> V).

Fact fsfun_udp_key : unit. Proof. exact: tt. Qed.

Definition fsfun_upd (f : fsfun d) (k : K) (v : V) : fsfun d :=
  [fsfun[fsfun_udp_key]
     x in k |` finsupp f => if x == k then v else f x].

Definition fsfun_dupd (f : fsfun d) (k : K) (v : V) : fsfun d :=
  if k \in finsupp f then f else fsfun_upd f k v.
End FsFun.

Notation "f .[ k <- v ]" := (fsfun_upd f k v) : fun_scope.
Notation "f .[ k <-? v ]" := (fsfun_dupd f k v)
  (at level 2, format "f .[ k  <-?  v ]") : fun_scope.

(* -------------------------------------------------------------------- *)
Section GraphDef.
Context (T : choiceType).

Implicit Type (fs : {fsfun T -> option {fset T} with None}).

Definition codom_sub fs :=
  [forall x : finsupp fs, (odflt fset0 (fs (val x))) `<=` finsupp fs].

Lemma codom_subP fs :
  reflect {in (finsupp fs), forall x, odflt fset0 (fs x) `<=` finsupp fs}
		(codom_sub fs).
Proof.
apply/(iffP idP).
- by move/forallP=> H x xfs; move: (H [` xfs]).
- move=> H; apply/forallP=> x; exact/H/valP.
Qed.

Record graph :=
  Graph { fs : {fsfun T -> option {fset T} with None};
          _  : codom_sub fs}.

Coercion graph_val (G : graph) := let: Graph g _ := G in g.

Canonical graph_subType := Eval hnf in [subType for graph_val].

Definition graph_eqMixin :=
  Eval hnf in [eqMixin of graph by <:].
Canonical graph_eqType :=
  Eval hnf in EqType graph graph_eqMixin.
Definition graph_choiceMixin :=
  [choiceMixin of graph by <:].
Canonical graph_choiceType :=
  Eval hnf in ChoiceType graph graph_choiceMixin.

Definition graph_of of phant T := graph.
Identity Coercion type_graph_of : graph_of >-> graph.
End GraphDef.

(* -------------------------------------------------------------------- *)
Notation "{ 'graph' T }" := (graph_of (Phant T)) (at level 0).

Section GraphOf.
Context (T : choiceType).

Canonical graph_of_subType    := Eval hnf in [subType    of {graph T}].
Canonical graph_of_eqType     := Eval hnf in [eqType     of {graph T}].
Canonical graph_of_choiceType := Eval hnf in [choiceType of {graph T}].
End GraphOf.

(* -------------------------------------------------------------------- *)
Section GraphBasics.
Context (T : choiceType).

Program Definition graph0 : graph T := @Graph _ [fsfun] _.
Next Obligation. apply/codom_subP => x; by rewrite finsupp0 inE. Qed.

(*Definition add_vertex (g : graph T) (v : T) :=
  Graph g.[v <-? Some fset0].

Definition add_edge (g : graph T) (v1 v2 : T) :=
  let g' := Graph g.[v1 <- Some (v2 |` odflt fset0 (g v1))] in
  Graph g'.[v2 <- Some (v1 |` odflt fset0 (g' v2))].*)

Definition successors (g : graph T) (v : T) : {fset T} :=
  odflt fset0 (g v).

Definition vertices (g : graph T) : {fset T} :=
  finsupp g.

Definition edges (g : graph T) : rel T :=
  [rel x y | y \in successors g x].

(* Definition predecessors (g : graph T) (v : T) : {fset T} :=
  [fset x in vertices g | edges g x v]. *)

(* Introduce notation *)
(* create_graph -> mk_graph *)

Program Definition mk_graph (V : {fset T}) (E : rel T) : graph T :=
  @Graph _ [fsfun v in V => Some [fset w | w in V & E v w] | None] _.
Next Obligation.
apply/codom_subP=> x x_in.
rewrite fsfunE ifT /=; last by move: x_in; apply/fsubsetP/finsupp_sub.
apply/fsubsetP=> y; rewrite !inE /= =>/andP [y_in] _.
by rewrite mem_finsupp fsfunE y_in.
Qed.

Section Lemmas.

Lemma graphE (G1 G2 : graph T): G1 = G2 <-> vertices G1 = vertices G2 /\ edges G1 =2 edges G2.
Proof.
split; first by move=> ->.
case: G1=> f; case: G2=> g hg hf /= [] vtxE edgeE; apply/eqP; rewrite -val_eqE /=.  
apply/eqP/fsfunP=> x.
move: (edgeE x); rewrite /edges /successors /=.
move: vtxE; rewrite /vertices /=; move/fsetP/(_ x).
rewrite !mem_finsupp.
by case: (f x); case: (g x)=> //= ?? _ /fsetP ->.
Qed.

Lemma vtx0 : vertices graph0 = fset0.
Proof. exact: finsupp0. Qed.

Lemma edge0 (x y : T) : edges graph0 x y = false.
Proof. by rewrite /edges /successors /= fsfun0E /=. Qed.

Lemma vtx_prop0 (G : graph T) : vertices G != fset0 <-> G != graph0.
Proof.
split; apply/contra_neq.
- by move=> ->; rewrite vtx0.
- move=> vtx_eq0; apply/graphE; rewrite vtx0; split=> //.
	move=> x y; rewrite edge0 /edges /successors /=.
	move: vtx_eq0; rewrite /vertices; move/fsetP/(_ x); rewrite in_fset0.
	by case: finsuppP.
Qed.

Lemma graph0Pn (G : graph T) : reflect (exists x : T, x \in vertices G) (G != graph0).
Proof.
apply/(iffP idP).
- by move/vtx_prop0/fset0Pn.
- by move=> ?; apply/vtx_prop0/fset0Pn.
Qed.


Lemma in_succE (G : graph T) (x y : T) :
  y \in successors G x = edges G x y.
Proof. by []. Qed.

Lemma edge_vtxl (G : graph T) (x y : T) :
  edges G x y -> x \in vertices G.
Proof.
rewrite /vertices -in_succE /successors.
by case : (finsuppP G).
Qed.

Lemma edge_vtxr (G : graph T) (x y : T) :
  edges G x y -> y \in vertices G.
Proof.
move/[dup] => /edge_vtxl.
case: G=> f; rewrite /edges /vertices /successors /=.
move/codom_subP => /(_ x) codom_f /codom_f /fsubsetP; exact.
Qed.

Lemma edge_vtxlr (G : graph T) (x y : T):
  edges G x y -> x \in vertices G /\ y \in vertices G.
Proof. by move=> /[dup] /edge_vtxl -> /edge_vtxr ->. Qed.


Lemma sub_succ (G : graph T) (x : T) :
  successors G x `<=` vertices G.
Proof. apply/fsubsetP=> y; rewrite in_succE; exact: edge_vtxr. Qed.

Section MkGraph.
Context (V : {fset T}) (E : rel T).

Lemma vtx_mk_graph : vertices (mk_graph V E) = V.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
- exact: finsupp_sub.
- by apply/fsubsetP=> x; rewrite mem_finsupp fsfunE => ->.
Qed.

Lemma edge_mk_graph : {in V&, forall x y, edges (mk_graph V E) x y = E x y}.
Proof.
by move=> x y xV yV; rewrite -in_succE /successors /= fsfunE xV /= !inE yV.
Qed.

Lemma succ_mk_graph : {in V, forall x,
  successors (mk_graph V E) x = [fset y in V | E x y]}.
Proof.
move=> x xV; apply/fsetP=> y; rewrite in_succE !inE /=.
apply/idP/idP.
- move=> /[dup] /edge_vtxr; rewrite vtx_mk_graph=> yV.
  by rewrite edge_mk_graph // yV.
- by case/andP => /= yV xEy; rewrite edge_mk_graph.
Qed.

End MkGraph.
End Lemmas.

End GraphBasics.
Section Connected.
Context (T : choiceType) (G : graph T).

Record gpath := GPath {
  src  : T;
  dst  : T;
  walk : seq T;
  _ : src \in vertices G;
  _ : path (edges G) src walk;
  _ : last src walk == dst
}.

Record epath := EPath {
  p :> gpath;
  _ : uniq (src p :: walk p)
}.

Definition is_path (p : epath) (x y : T) := src p = x /\ dst p = y.
Definition has_path (x y : T) := exists p : epath, is_path p x y.
Definition size_path (p : epath) := size (walk p).
Definition is_npath (n : nat) (p : epath) (x y : T) :=
  is_path p x y /\ size_path p = n.
Definition has_npath (n : nat) (x y : T) := exists p : epath, is_npath n p x y.
Definition connected := {in (vertices G) &, forall x y : T, has_path x y}.

Lemma mem_src (p : epath) : src p \in vertices G. Proof. by case: p => -[]. Qed.
Lemma path_walk (p : epath) : path (edges G) (src p) (walk p). Proof. by case: p => -[]. Qed.
Lemma last_dst (p : epath) : last (src p) (walk p) = (dst p). Proof. by case: p => -[????? /= /eqP]. Qed.
Lemma uniq_walk (p : epath) : uniq (src p :: walk p). Proof. by case: p. Qed.

Lemma mem_walk (p : epath) : forall x, x \in walk p -> x \in vertices G.
Proof.
move: (path_walk p); elim: (walk p) (src p) (mem_src p)=> //= h t IH.
move=> s s_vtx /andP [/edge_vtxr h_vtx] /(IH _ h_vtx) IH2.
by move=> x; rewrite inE; case/orP=> [/eqP ->|/IH2].
Qed.

Lemma size_path_le (p : epath) : size_path p <= #|` vertices G|.
Proof. by apply/uniq_leq_size; [by case/andP:(@uniq_walk p)|exact:mem_walk]. Qed.


Lemma mem_dst (p : epath) : dst p \in vertices G.
Proof. 
rewrite -last_dst; case E: (walk p)=> [|h t]; rewrite ?mem_src //.
by apply/(@mem_walk p); rewrite E /= mem_last.
Qed.

Lemma edge_dst (p : epath): size_path p > 0 -> 
  edges G (last (src p) (behead (belast (src p) (walk p)))) (dst p).
Proof.
rewrite /size_path.
move/(pathP (src p)): (path_walk p)=> /(_ (size (walk p)).-1).
rewrite -last_dst; case: (walk p)=> //=.
move=> a l /= /(_ (leqnn _)) + _.
rewrite !(last_nth (src p)) size_belast.
suff ->: nth (src p) [:: src p, a & l] (size l) = nth (src p) (src p :: belast a l) (size l) by [].
by move: {1 3}(src p); move: (src p) a; elim: l=> //=.
Qed.


Section FinType.

Definition walk_of (x : gpath) := (src x, dst x, walk x).
Definition of_walk (x : T * T * seq T) :=
  let: (s, d, w) := x in
  if @idP (s \in vertices G) is ReflectT Hs then
  if @idP (path (edges G) s w) is ReflectT Hpath then
  if @idP (last s w == d) is ReflectT Hd then
  Some (@GPath s d w Hs Hpath Hd)
  else None else None else None.
  
Lemma walk_of_can: pcancel walk_of of_walk.
Proof.
move=> x; rewrite /walk_of /of_walk.
case: x=> s d w /= sG pathG last_eq.
case: {-}_/idP; rewrite ?sG // => sG'.
case: {-}_/idP; rewrite ?pathG // => pathG'.
case: {-}_/idP; rewrite ?last_eq // => last_eq'.
rewrite (bool_irrelevance sG sG') (bool_irrelevance pathG pathG').
by rewrite (bool_irrelevance last_eq last_eq').
Qed.

Definition gpath_eqMixin := PcanEqMixin walk_of_can.
Canonical gpath_eqType := Equality.Pack gpath_eqMixin.

Definition gpath_choiceMixin := PcanChoiceMixin walk_of_can.
Canonical gpath_choiceType := ChoiceType _ gpath_choiceMixin.

Canonical epath_subType := Eval hnf in [subType for p].
Definition epath_eqMixin := Eval hnf in [eqMixin of epath by <:].
Canonical epath_eqType := Eval hnf in EqType epath epath_eqMixin.
Definition epath_choiceMixin := Eval hnf in [choiceMixin of epath by <:].
Canonical epath_choiceType := Eval hnf in ChoiceType epath epath_choiceMixin.

Definition U (P : 'I_#|` vertices G|) :=  P.-tuple (vertices G).
Definition foo := {P : 'I_#|` vertices G| & U P}.
Definition foo2 := ((vertices G) * foo)%type.
Definition walk_of_foo (x : foo) := [seq val i | i <- (tagged x)].
Definition gpath_prop (x : foo2) :=
  path (edges G) (val x.1) (walk_of_foo x.2).
Definition epath_prop (x : foo2) :=
  uniq ((val x.1) :: (walk_of_foo x.2)).
Definition foo3 := {x : foo2 | gpath_prop x && epath_prop x}.

Program Definition gpath_make (x : foo3) := 
  @GPath (val x.1) (last (val x.1) (walk_of_foo x.2)) (walk_of_foo x.2) _ _ _.
Next Obligation. by case: x=> /= ? /andP []. Qed.

Program Definition epath_make (x : foo3) :=
  @EPath (gpath_make x) _.
Next Obligation. by case: x=> /= ? /andP []. Qed.

Fixpoint walk_vtx (w : seq T) := match w with
  |[::] => [::]
  |h::t=> if @idP (h \in (vertices G)) is ReflectT h_vtx then
    [` h_vtx] :: (walk_vtx t) else (walk_vtx t)
end.

Lemma walk_vtxP (x : epath): [seq val i | i <- walk_vtx (walk x)] = walk x.
Proof.
have:= (@mem_walk x).
elim: (walk x)=> //= h t IH in_ht.
move: (in_ht h); rewrite !inE eq_refl /= => /(_ isT) h_vtx.
case: {-}_/idP=> [|/(_ h_vtx)] //= h_vtx2.
by rewrite IH // => y yt; apply/in_ht; rewrite inE yt orbT.
Qed.


Lemma size_epath_vtx (x : epath): size (walk_vtx (walk x)) < #|` vertices G|.
Proof.
have ->: size (walk_vtx (walk x)) = size (walk x) by
  move/(congr1 size): (walk_vtxP x); rewrite size_map.
have:= (uniq_size_ltn (uniq_walk x) (fset_uniq (vertices G)))=> /=.
apply=> i; rewrite inE; case/orP=> [/eqP ->|]; rewrite ?mem_src //.
by move/mem_walk.
Qed.
Program Definition epath_tuple (x : epath) := 
  @Tuple (Ordinal (size_epath_vtx x)) _ (walk_vtx (walk x)) _.

Program Definition epath_foo (x : epath) : foo := Tagged _ (epath_tuple x).
Definition epath_foo2 (x : epath) : foo2 := ([`mem_src x], epath_foo x).
Program Definition epath_foo3 (x : epath) : foo3 :=
  @exist _ _ (epath_foo2 x) _.
Next Obligation. apply/andP; split.
- rewrite /gpath_prop /= /walk_of_foo /= walk_vtxP.
  exact: path_walk.
- rewrite /epath_prop /walk_of_foo walk_vtxP /=.
  exact: uniq_walk.
Qed.

Lemma gpath_inj (x y : gpath): x = y <-> 
  [/\ src x = src y, dst x = dst y & walk x = walk y].
Proof.
split; first by move=> ->.
case: x=> sx dx wx; case: y=> sy dy wy /=.
move=> ++++++ [s_eq d_eq w_eq]; rewrite s_eq d_eq w_eq.
move=> sP wP dP sP2 wP2 dP2.
by rewrite (bool_irrelevance sP sP2) (bool_irrelevance dP dP2) (bool_irrelevance wP wP2).
Qed.

Lemma epath_inj (x y : epath): x = y <-> p x = p y.
Proof.
split; first by move/(congr1 p).
case: x=> px px_uniq; case: y=> py py_uniq /= p_xy.
move: py_uniq; rewrite -p_xy=> px_uniq2.
by rewrite (bool_irrelevance px_uniq px_uniq2).
Qed.

Lemma can_epath_foo3: cancel (epath_foo3 : epath -> [finType of foo3]) epath_make.
Proof.
move=> x; apply/epath_inj/gpath_inj=> /=; split=> //.
- by rewrite /walk_of_foo /= walk_vtxP last_dst.
- rewrite /walk_of_foo /=; exact/walk_vtxP.
Qed.

Definition epath_countMixin := CanCountMixin can_epath_foo3.
Canonical epath_countType := (CountType epath epath_countMixin).
Definition epath_finMixin := CanFinMixin can_epath_foo3.
Canonical epath_finType := FinType epath epath_finMixin.

End FinType.

Section NilPath.
Context {x : T}.
Hypothesis xG : x \in vertices G.
Program Definition nil_path := @EPath (@GPath x x [::] _ _ _) _.
End NilPath.

Lemma size_path0 (p : epath) : size_path p = 0 <-> src p = dst p.
Proof.
split.
- by move/size0nil; case: p=> -[/= ??? _ _ + _]; move/[swap]; move=> -> /= /eqP.
- move=> h; apply/eqP; rewrite size_eq0; apply/eqP; move: h.
  case: p=> -[/= ?? s _ _ /eqP <- /andP [+ _]].
  by move/[swap] => ->; case: s=> //= ??; rewrite mem_last.
Qed.

Lemma has_npath0 x : x \in vertices G -> has_npath 0 x x.
Proof. by move=> xG; exists (nil_path xG). Qed.

Lemma has_npath0P (x y : T) : has_npath 0 x y <-> x = y /\ y \in vertices G.
Proof.
split=> [|[->]]; last exact/has_npath0.
case=> -[p /= ?] [[<- <-]] /size_path0 <-; split=> //.
exact: mem_src.
Qed.

Lemma has_pathP (x y : T): has_path x y <-> exists n, has_npath n x y.
Proof.
split.
- by case=> p ?; exists (size (walk p)); exists p; split.
- by case=> ? [p []]; exists p.
Qed.

Lemma has_pathxx x : x \in vertices G -> has_path x x.
Proof. move=> xG; apply/has_pathP; exists 0; exact: (has_npath0 xG). Qed.

Lemma epath_vtx (p : epath) : dst p \in vertices G.
Proof.
case: p=> -[x y s /= +++ _]; elim: s x y => /= [|a l IH].
- by move=> x y ? _ /eqP <-.
- move=> x y xG /andP [edge_a]; apply/IH.
  exact: (edge_vtxr edge_a).
Qed.

Lemma has_path_vtx (x y : T): has_path x y -> y \in vertices G.
Proof. case=> p [_ <-]; exact: epath_vtx. Qed.

Lemma has_npath_vtx n x y: has_npath n x y -> y \in vertices G.
Proof. case=> p [[_ <-]] _; exact: epath_vtx. Qed.

Section EdgePath.
Context {x y : T}.
Hypothesis xGy : edges G x y.
Hypothesis xny : x != y.

Program Definition edge_path := @EPath (@GPath x y [:: y] _ _ _) _.
Next Obligation. exact: (edge_vtxl xGy). Defined.
Next Obligation. by rewrite xGy. Defined.
Next Obligation. by rewrite inE xny. Defined.
End EdgePath.

Lemma has_path_edge x y : edges G x y -> has_path x y.
Proof.
move=> xGy; case/boolP: (x == y).
- move/eqP => ->; exact/has_pathxx/(edge_vtxr xGy).
- by move=> xny; exists (edge_path xGy xny).
Qed.

Section TransPath.
Context {p p' : epath}.
Hypothesis junction : (dst p) = (src p').

(*TODO : créer un lemme d'existence d'un chemin sans cycle : gpath => epath*)
(*TODO : partir d'un gpath qui convient*)

Program Definition trans_path :=
  @EPath (@GPath (src p) (dst p') (shorten (src p) ((walk p) ++ (walk p'))) _ _ _) _.
Next Obligation. by case: p=> -[]. Defined.
Next Obligation.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP.
Defined.
Next Obligation.
have: last (src p) (walk p ++ walk p') = dst p' by rewrite last_cat last_dst junction last_dst.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP=> ? _ _ _ ->.
Defined.
Next Obligation.
have: path (edges G) (src p) (walk p ++ walk p') by rewrite cat_path last_dst junction !path_walk.
by case/shortenP.
Defined.

Lemma src_trans_path : src trans_path = src p.
Proof. by []. Qed.

Lemma dst_trans_path : dst trans_path = dst p'.
Proof. by []. Qed.

Lemma all_trans_path (P : pred T) :
  all P (src p :: walk p) -> all P (walk p') ->
  all P (src trans_path :: walk trans_path).
Proof.
rewrite /=; case/andP=> -> /=.
have: path (edges G) (src p) (walk p ++ walk p')
  by rewrite cat_path last_dst junction !path_walk.
case/shortenP=> w _ _ sub_w /allP all_p /allP all_p'.
apply/allP=> z /sub_w; rewrite /= mem_cat.
by case/orP=> [/all_p |/all_p'].
Qed.

End TransPath.

Lemma has_path_trans x y z : has_path x y -> has_path y z -> has_path x z.
Proof. by case => [p [? +]] [p' [+ ?]]; move=> <- /esym junc_y; exists (trans_path junc_y); split. Qed.

Section BelastPath.
Context (p : epath).
Let bwalk := (behead (belast (src p) (walk p))).

Program Definition belast_path :=
  @EPath (@GPath (src p) (last (src p) bwalk) bwalk _ _ _) _.
Next Obligation. exact: mem_src. Defined.
Next Obligation.
  move: (path_walk p); rewrite /bwalk. elim/last_ind: (walk p)=> //= l a _.
  by rewrite belast_rcons /= rcons_path=> /andP [].
Defined.
Next Obligation.
  move: (uniq_walk p); rewrite /= /bwalk; elim/last_ind: (walk p) => // l a _.
  rewrite belast_rcons /= rcons_uniq mem_rcons inE negb_or -!andbA.
  by case/and4P => _ -> _ ->.
Defined.

Lemma dst_blpath : dst belast_path = last (src p) (bwalk).
Proof. by []. Qed.

Lemma blpath_edge_last : walk p != [::] ->
  edges G (dst belast_path) (dst p).
Proof.
rewrite dst_blpath /bwalk; move: (last_dst p) (path_walk p).
elim/last_ind: (walk p)=> //= l a _.
by rewrite last_rcons rcons_path belast_rcons /=; move=> -> /andP [].
Qed.

Lemma src_blpath : src belast_path = src p. Proof. by []. Qed.

Lemma size_blpath : size_path belast_path = (size_path p).-1.
Proof.
rewrite /size_path /= /bwalk.
by elim/last_ind: (walk p)=> //= l a _; rewrite belast_rcons size_rcons /=.
Qed.

End BelastPath.

Lemma has_npathSP (n : nat) (x y : T):
  has_npath (S n) x y -> exists2 z, y \in successors G z & has_npath n x z.
Proof.
case=> p [[<- <-]] size_p; set bp := (belast_path p).
exists (dst bp).
+ apply: blpath_edge_last; apply/negP; rewrite -size_eq0.
  by rewrite /size_path in size_p; rewrite size_p. (* TODO : ugly *)
+ by exists bp; split; first split=> //; rewrite size_blpath size_p.
Qed.

Section ConsPath.

Context {x y : T} {p' : epath}.
Hypothesis xGy : edges G x y.
Hypothesis xny : x != y.
Hypothesis junction: y = src p'.

Definition cons_path := @trans_path (edge_path xGy xny) p' junction.
End ConsPath.

Section RConsPath.

Context {y : T} {p : epath}.
Hypothesis pGy : edges G (dst p) y.
Hypothesis y_new : y \notin (src p) :: (walk p).

Program Definition rcons_epath := 
  @EPath (@GPath (src p) y (rcons (walk p) y) _ _ _) _.
Next Obligation. exact: mem_src. Qed.
Next Obligation. by rewrite rcons_path path_walk last_dst. Qed.
Next Obligation. by rewrite last_rcons. Qed.
Next Obligation.
move: y_new; rewrite mem_rcons !inE !negb_or eq_sym.
case/andP=> -> y_n_walk /=; case/andP: (uniq_walk p)=> -> /=.
by rewrite rcons_uniq y_n_walk /=.
Qed.

End RConsPath.

Section SubPath.

Context {p : epath} {w : seq T}.
Hypothesis sub_w: prefix_seq w (walk p).

Program Definition sub_epath:= @EPath (@GPath (src p) (last (src p) w) w _ _ _) _.
Next Obligation. by rewrite mem_src. Qed.
Next Obligation. apply/(prefix_seq_path sub_w)/(path_walk). Qed.
Next Obligation. by move: (uniq_walk p)=> /= /andP [/(prefix_seq_notin sub_w) -> /(prefix_seq_uniq sub_w) ->]. Qed.

End SubPath.

Section InOutPath.
Context {p : epath} (pr : pred T).
Hypothesis src_in : pr (src p).
Hypothesis dst_out : ~~ pr (dst p).

Lemma last_out : ~~ pr (last (src p) (walk p)).
Proof. by rewrite last_dst. Qed.

Program Definition in_out_epath := @sub_epath p (xchoose (prefix_seq_in_out src_in last_out)) _.
Next Obligation. by case/and3P: (xchooseP (prefix_seq_in_out src_in last_out)). Qed.

Lemma in_out_epath_in : all pr (belast (src p) (walk in_out_epath)).
Proof. by case/and3P: (xchooseP (prefix_seq_in_out src_in last_out)). Qed.

Lemma in_out_epath_out : ~~ pr (dst in_out_epath).
Proof. by case/and3P: (xchooseP (prefix_seq_in_out src_in last_out)). Qed.

End InOutPath.

Section Ind.

Lemma has_pathW (P : T -> Prop) (x0 : T) :
  P x0
  -> (forall (S : T -> Prop) x,
      (forall x, S x -> P x)
      -> (forall x, S x -> x \in vertices G)
      -> S x -> forall y, y \in successors G x -> P y)
  -> forall y, has_path x0 y -> P y.
Proof.
move=> Px0 PS y /has_pathP[n]; elim: n y => [|n ih] y.
- by move/has_npath0P=> [<-].
case/has_npathSP=> x x0_p_x /[dup] px /ih Px.
apply: (PS (fun y => has_npath n x0 y) x) => //.
exact: has_npath_vtx.
Qed.

End Ind.
End Connected.

Section Regular.
Context {T : choiceType} (G : graph T) (n : nat).

Definition regular := forall v : T, v \in vertices G -> #|` successors G v| = n.

End Regular.

Section ImageGraph.
Context {T1 T2 : choiceType} (G : graph T1) (f : T1 -> T2).
Let V := vertices G.
Let E := edges G.

Definition img_graph := mk_graph (f @` V)
  [rel x y | [exists v : V, [exists w : V,
  [&& f (val v) == x, f (val w) == y & E (val v) (val w)]]]].

Lemma vtx_img_graph : vertices img_graph = f @` V.
Proof. by rewrite vtx_mk_graph. Qed.

Lemma edge_img_graph x y : reflect
  (exists v, (exists w, [/\ f v = x, f w = y & (E v w)]))
  (edges img_graph x y).
Proof.
apply/(iffP idP).
- move/[dup]/[dup] => /edge_vtxl + /edge_vtxr.
  rewrite vtx_img_graph=> xV2 yV2; rewrite edge_mk_graph //=.
	+ case/existsP=> x'; case/existsP=> y'; case/and3P => /eqP <- /eqP <- ?.
		by exists (fsval x'); exists (fsval y'); split.
- case=> x' [y'] [<- <- /[dup] /[dup] /edge_vtxl x'V /edge_vtxr y'V x'Gy'].
	rewrite edge_mk_graph ?in_imfset //=.
	apply/existsP; exists [` x'V]; apply/existsP; exists [` y'V].
	by rewrite !eq_refl x'Gy'.
Qed.

End ImageGraph.

Notation "f '@°' G" := (img_graph G f) (at level 24, format "f  '@°'  G").

Section ImgTheory.
Lemma img_graph0 {T1 T2 : choiceType} (f : T1 -> T2): f @° (graph0 T1) = graph0 T2.
Proof.
apply/graphE; split.
- rewrite vtx_img_graph !vtx0; apply/fsetP=> x; apply/idP/idP/negP.
  by case/imfsetP.
- move=> x y; rewrite edge0.
  apply/(introF (edge_img_graph (graph0 T1) f x y)).
  by case=> ? [? []]; rewrite edge0.
Qed.

Lemma comp_img_graph {T1 T2 T3: choiceType} (f : T1 -> T2) (g : T2 -> T3) (G : graph T1) : (g \o f) @° G = g @° (f @° G).
Proof.
apply/graphE; split.
- rewrite !vtx_img_graph; apply/fsetP=> x; apply/idP/idP.
  + by case/imfsetP=> /= x0 x0G ->; apply/in_imfset/in_imfset.
  + case/imfsetP=> /= x0 /imfsetP [/= x1 x1G -> ->]; apply/imfsetP.
    by exists x1.
- move=> x y; apply/idP/idP.
  + case/edge_img_graph => x' [y' [<- <- x'Gy']]; apply/edge_img_graph.
    exists (f x')=> //; exists (f y')=> //; split=> //; apply/edge_img_graph.
    by exists x'=> //; exists y'.
  + case/edge_img_graph => x' [y' [<- <- /edge_img_graph]].
		case=> x'' [y'' [<- <- xGy'']]; apply/edge_img_graph.
		by exists x''; exists y''.
Qed.

Lemma cancel_img_graph {T1 T2 : choiceType} (f : T1 -> T2) (g : T2 -> T1) (G : graph T1):
  {in vertices G, cancel f g} -> (g \o f) @° G = G.
Proof.
move=> can_fg; apply/graphE; split; first (apply/fsetP=> x; apply/idP/idP).
- rewrite !vtx_img_graph=> /imfsetP [ /= x' x'G ->].
  by rewrite can_fg.
- move=> xG; rewrite vtx_img_graph; apply/imfsetP=> /=; exists x; rewrite ?can_fg //.
- move=> x y; apply/idP/idP.
  + case/edge_img_graph=> /= x' [y'] [<- <-].
    move=> /[dup] /[dup] /edge_vtxl x'G /edge_vtxr y'G.
    by rewrite !can_fg.
  + move=> /[dup] /[dup] /edge_vtxl xG /edge_vtxr yG ?.
    by apply/edge_img_graph; exists x; exists y=> /=; rewrite !can_fg //; split.
Qed.


End ImgTheory.

Section QuotientGraph.

Context {T1 T2 : choiceType} (G : graph T1) (f : T1 -> T2).
Let V := vertices G.
Let E := edges G.

Definition quot_graph := mk_graph (f @` V)
  [rel x y | [exists v : V, [exists w : V,
  [&& f (val v) == x, f (val w) == y, x != y & E (val v) (val w)]]]].

Lemma vtx_quot_graph : vertices quot_graph = f @` V.
Proof. by rewrite vtx_mk_graph. Qed.

Lemma edge_quot_graph x y : reflect
  (exists v, (exists w, [/\ f v = x, f w = y, x != y & (E v w)]))
  (edges quot_graph x y).
Proof.
apply/(iffP idP).
- move/[dup]/[dup] => /edge_vtxl + /edge_vtxr.
  rewrite vtx_quot_graph=> /imfsetP /= [v vV ->] /imfsetP /= [w wV ->].
  rewrite edge_mk_graph ?in_imfset //=.
  case/existsP=> v' /existsP [w'] /and4P [/eqP <- /eqP <- ??].
  by exists (fsval v'); exists (fsval w'); split.
- case=> x' [y'] [<- <- ?].
  move/[dup]/[dup] => /edge_vtxl x'V /edge_vtxr y'V ?.
  rewrite edge_mk_graph ?in_imfset //=.
  apply/existsP; exists [` x'V]; apply/existsP; exists [`y'V].
  by apply/and4P; split.
Qed.

Lemma edge_quot_graph_xx x: ~~ (edges quot_graph x x).
Proof. by apply/contraT; rewrite negbK; case/edge_quot_graph=> ? [?] []; rewrite eq_refl. Qed.

End QuotientGraph.

Notation "f @/ G" := (quot_graph G f) (at level 24, format "f  '@/'  G").

Section GIsomorphism.

Context {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2).
Let V1 := vertices G1.
Let V2 := vertices G2.
Let E1 := edges G1.
Let E2 := edges G2.

Definition gisof f := {in V1&, injective f} /\ f @° G1 = G2.
Definition giso := exists f, gisof f.

Section IsoProofs.

Lemma gisof_inj f : gisof f -> {in V1&, injective f}.
Proof. by case. Qed.

Lemma gisof_edge f : gisof f -> {in V1&, forall x y, E1 x y = E2 (f x) (f y)}.
Proof.
case=> f_inj f_G1 x y xV1 yV1; rewrite /E2 -f_G1; apply/idP/idP.
- move=> xG1y; apply/edge_img_graph.
  by exists x => //; exists y.
- case/edge_img_graph => x' [y' [+ + /[dup] /[dup] /edge_vtxl x'V1 /edge_vtxr y'V1]].
	by move/f_inj=> -> // /f_inj ->.
Qed.

Lemma gisof_vtx f : gisof f -> f @` V1 = V2.
Proof. by rewrite /V2; case=> _ <-; rewrite vtx_img_graph. Qed.

Lemma gisofE f:
  gisof f <-> [/\ {in V1&, injective f}, (f @` V1 = V2) &
    {in V1&, forall x y, E1 x y = E2 (f x) (f y)}].
Proof.
split.
- move=> gisoff; split; [by case: gisoff|exact:gisof_vtx|exact:gisof_edge].
- case=> f_inj f_bij f_morph; split=> //.
  apply/graphE; rewrite vtx_img_graph f_bij; split=> // x y.
  apply/idP/idP.
  + case/edge_img_graph=> x' [y' [<- <-]].
		move=> /[dup] /[dup] /edge_vtxl x'V1 /edge_vtxr y'V1.
		by rewrite -/E1 (f_morph _ _ x'V1 y'V1).
	+ move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
		rewrite -/V1 -/V2 -f_bij.
		case/imfsetP=> /= x' x'V1 -> /imfsetP [/= y' y'V1 ->].
		rewrite -/E2 -f_morph // => x'G1y'.
		by apply/edge_img_graph; exists x'; exists y'.
Qed.

Lemma gisoE: giso <-> exists f,
  [/\ {in V1&, injective f}, (f @` V1 = V2) &
  {in V1&, forall x y, E1 x y = E2 (f x) (f y)}].
Proof. split; by case=> f /gisofE ?; exists f. Qed.

Section SubGraphIso.
Context {f : T1 -> T2}.
Hypothesis f_inj : {in V1&, injective f}.
Hypothesis f_leq : (f @` V1) `<=` V2.
Hypothesis f_morph : {in V1&, forall x y, E1 x y -> E2 (f x) (f y)}.
Hypothesis G2_connected : connected G2.
Hypothesis G_succ : {in V1, forall x, f @` (successors G1 x) = successors G2 (f x)}.
Hypothesis G1_neq0 : G1 != (graph0 T1).

Lemma sub_has_path : {in V1, forall x, forall y, has_path G2 (f x) y -> y \in f @` V1}.
Proof.
move=> x xV1 y; elim/has_pathW; first exact: in_imfset.
move=> S x0 S_im S_vtx Sx0 y0; case/imfsetP: (S_im _ Sx0) => /= xO' x0'V1 ->.
rewrite -G_succ //; move: y0; exact/fsubsetP/subset_imfset/fsubsetP/sub_succ.
Qed.

Lemma sub_vertices : V2 `<=` f @` V1.
Proof.
apply/fsubsetP=> x xV2; case/graph0Pn : G1_neq0=> y yV1.
apply/(sub_has_path yV1)/G2_connected=> //.
by move/fsubsetP: f_leq; apply; rewrite in_imfset.
Qed.

Lemma sub_edges : {in V1&, forall x y, E2 (f x) (f y) -> E1 x y}.
Proof.
move=> x y xV1 yV1; rewrite -[E2 _ _]in_succE -G_succ // -[E1 _ _]in_succE.
case/imfsetP => y' /= y'_succ /f_inj -> //.
exact: (edge_vtxr y'_succ).
Qed.

Lemma sub_gisof : gisof f.
Proof.
apply/gisofE; split=> //; first by (apply/eqP; rewrite eqEfsubset f_leq sub_vertices).
move=> x y xV1 yV1; apply/idP/idP; first exact: f_morph.
exact: sub_edges.
Qed.

End SubGraphIso.
End IsoProofs.
End GIsomorphism.

Module XFinmap.
Section XFinmap.
Context {T1 T2: choiceType} (f : T1 -> T2) (S1 : {fset T1}) (x0 : T1).
Let S2 := f @` S1.
Hypothesis f_inj : {in S1&, injective f}.

Section EmptyS1.
Hypothesis S1_eq0: S1 = fset0.
Lemma emptyS2 : S2 = fset0.
Proof.
apply/fsetP=> x; rewrite in_fset0 /S2.
by apply/(introF (imfsetP _ f _ _))=> -[/= x']; rewrite S1_eq0.
Qed.

Definition g_empty := fun _ : T2 => x0.
Lemma g_emptyK : {in S1, cancel f g_empty}.
Proof. by move=> x; rewrite S1_eq0. Qed.
Lemma g_emptyKd : {in S2, cancel g_empty f}.
Proof. by move=> x; rewrite emptyS2. Qed.

End EmptyS1.
Section NotEmpty.
Hypothesis S1_neq0 : S1 != fset0.
Let x1 := [` xchooseP (fset0Pn _ S1_neq0) ].


Lemma tmp : f (val x1) \in S2. Proof. exact/in_imfset/valP. Qed.
Definition fS : S1 -> S2 := fun x=> insubd [` tmp] (f (val x)).
Lemma has_inv (y : S2) : exists x, fS x == y.
Proof.
case/imfsetP: (valP y)=> /= x xS1 y_eq; exists [` xS1].
by rewrite -val_eqE val_insubd /= in_imfset ?y_eq.
Qed.
Definition fS_inv (y : S2) := xchoose (has_inv y).
Definition f_inv (y : T2) := val (fS_inv (insubd [`tmp ] y)).

Lemma fS_inj : injective fS.
Proof.
move=> x y /(congr1 val); rewrite !insubdK ?in_imfset ?(valP x) ?(valP y) //.
move/f_inj=> /(_ (valP x) (valP y)); exact: val_inj.
Qed.

Lemma fSK : cancel fS fS_inv.
Proof.
move=> x.
move/eqP : (xchooseP (has_inv (fS x))); exact: fS_inj.
Qed.

Lemma fSKd : cancel fS_inv fS.
Proof.
move=> x; exact/eqP/(xchooseP (has_inv x)).
Qed.

Lemma fK : {in S1, cancel f f_inv}.
Proof.
move=> x xS1.
have ->: x = val [`xS1] by []; congr val.
exact/fSK.
Qed.

Lemma fKd : {in S2, cancel f_inv f}.
Proof. by move=> x /imfsetP [/= y yS1 ->]; rewrite fK. Qed.

End NotEmpty.
End XFinmap.
End XFinmap.

Section Bijections.

Context {T1 T2: choiceType} (f : T1 -> T2) (S1 : {fset T1}) (x0 : T1).
Hypothesis f_inj : {in S1 &, injective f}.
Let S2 := f @` S1.

Lemma in_bij : exists2 g, {in S1, cancel f g} & {in S2, cancel g f}.
Proof.
case/boolP: (S1 == fset0).
- move/eqP => S1_eq0; exists (XFinmap.g_empty x0).
  + exact: XFinmap.g_emptyK.
  + exact: XFinmap.g_emptyKd.
- move=> S1_neq0; exists (XFinmap.f_inv f S1_neq0).
  + exact: (XFinmap.fK).
  + exact: (XFinmap.fKd).
Qed.

Lemma in_inv : exists2 g, {in S2 &, injective g} & g @` S2 = S1.
Proof.
case: in_bij=> g can_fg can_gf; exists g.
- move=> x y /imfsetP [/= x' x'S1 ->] /imfsetP [/= y' y'S1 ->].
  by rewrite !can_fg // => ->.
- apply/fsetP=> x; apply/idP/idP.
  + case/imfsetP=> /= x' /imfsetP [/= x'' x''S1 ->] ->.
    by rewrite can_fg.
  + by move=> xS1; apply/imfsetP=> /=; exists (f x); rewrite ?in_imfset ?can_fg.
Qed.

End Bijections.

Section GisoTheory.

Lemma gisof_idE {T : choiceType} (G1 G2 : graph T): gisof G1 G2 id <-> G1 = G2.
Proof.
split.
- case/gisofE=> _; rewrite imfset_id=> V1V2 E1E2.
  apply/graphE; split=> // x y; apply/idP/idP.
  + move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
    by move/E1E2=> /[apply] ->.
  + move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
    by rewrite -V1V2=> /E1E2 /[apply] ->.
- by move=> ->; apply/gisofE; split=> //; rewrite imfset_id.
Qed.

Lemma gisogg {T : choiceType} (G : graph T) : giso G G.
Proof. by apply/gisoE; exists id; split=> //; apply/fsetP=> ?; rewrite in_fsetE. Qed.

Lemma giso0n {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) :
  giso G1 G2 -> G1 != (graph0 T1) -> G2 != (graph0 T2).
Proof.
case=> f [f_inj] => <-.
case/graph0Pn=> x xV1; apply/graph0Pn; exists (f x).
by rewrite vtx_img_graph in_imfset.
Qed.

Lemma giso00 {T1 T2 : choiceType} (f: T1 -> T2) : giso (graph0 T1) (graph0 T2).
Proof. by exists f; split; rewrite ?img_graph0 //; move=> x y; rewrite vtx0. Qed.

Lemma giso_sym {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) (x0 : T1):
  giso G1 G2 -> giso G2 G1.
Proof.
move=> /gisoE [f [f_inj f_surj f_morph]].
apply/gisoE; case: (in_bij x0 f_inj)=> g can_fg can_gf.
exists g; split; rewrite -f_surj.
- move=> x y /imfsetP [/= x' x'V1 ->] /imfsetP [/= y' y'V1 ->].
  by rewrite !can_fg // => ->.
- apply/fsetP=> x; apply/idP/idP.
  + by case/imfsetP=> /= x' /imfsetP [/= x'' ? -> ->]; rewrite can_fg.
  + by move=> xV1; apply/imfsetP; exists (f x); rewrite ?in_imfset ?can_fg.
- move=> x y /imfsetP [/= x' x'V1 ->] /imfsetP [/= y' y'V1 ->].
  by rewrite !can_fg -?f_morph.
Qed.

Lemma gisof_sym {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2)
  (f : T1 -> T2) (g : T2 -> T1):
  {in vertices G1, cancel f g} ->
  gisof G1 G2 f -> gisof G2 G1 g.
Proof.
move=> can_gf /gisofE [f_inj f_vtx f_edge].
apply/gisofE; split.
- move=> x y; rewrite -f_vtx=> /imfsetP [/= x' x'G1 ->].
  by case/imfsetP=> /= y' y'G1 ->; rewrite !can_gf // => ->.
- rewrite -f_vtx; apply/fsetP=> x; apply/idP/idP.
  + case/imfsetP=> /= ? /imfsetP [/= ? memG1 ->] ->.
    by rewrite can_gf.
  + move=> xG1; apply/imfsetP=> /=; exists (f x); rewrite ?can_gf //.
    by apply/imfsetP; exists x.
- move=> x y; rewrite -f_vtx.
  case/imfsetP=> /= x' x'G -> /imfsetP [/= y' y'G ->].
  by rewrite !can_gf // f_edge.
Qed.

Lemma gisof_trans {T1 T2 T3 : choiceType} 
  (G1 : graph T1) (G2 : graph T2) (G3 : graph T3)
  (f : T1 -> T2) (g : T2 -> T3):
  gisof G1 G2 f -> gisof G2 G3 g -> gisof G1 G3 (g \o f).
Proof.
case=> f_inj <- [g_inj <-]; split.
- move=> x y xG1 yG1 /= /g_inj; rewrite vtx_img_graph !in_imfset //=.
  move/(_ isT isT)/f_inj; exact.
- by rewrite comp_img_graph.
Qed.

Lemma giso_trans {T1 T2 T3 : choiceType}
  (G1 : graph T1) (G2 : graph T2) (G3 : graph T3) :
  giso G1 G2 -> giso G2 G3 -> giso G1 G3.
Proof.
case=> f + [g]; move/gisof_trans=> /[apply] ?.
by exists (g \o f).
Qed.

Lemma gisof_has_path {T1 T2 : choiceType}
  (G1 : graph T1) (G2 : graph T2) f x y :
  gisof G1 G2 f -> x \in vertices G1 ->
  has_path G1 x y -> has_path G2 (f x) (f y).
Proof.
case => f_inj <- xG1.
elim/has_pathW.
- by apply/has_pathxx; rewrite vtx_img_graph in_imfset.
- move=> S x0 S_path S_vtx /[dup] /S_path xG_x0 /S_vtx x0G y0 x0Gy0.
  apply/(has_path_trans xG_x0)/has_path_edge.
  + by apply/edge_img_graph; exists x0=> //; exists y0.
Qed.

Lemma giso_connected {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) :
  giso G1 G2 -> connected G1 -> connected G2.
Proof.
case=> f /[dup] -[f_inj <-] /gisof_has_path Hpath G1_conn x y.
rewrite vtx_img_graph=> /imfsetP [/= x' x'G1 ->] /imfsetP [/= y' y'G1 ->].
apply/Hpath=> //; exact/G1_conn.
Qed.

Lemma gisof_succ {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) f x:
  gisof G1 G2 f -> x \in vertices G1 ->
  successors G2 (f x) = f @` (successors G1 x).
Proof.
case=> f_inj <- xG1; apply/fsetP=> y; rewrite in_succE; apply/idP/idP.
- case/edge_img_graph=> x' [y'] [+ <- /[dup] /edge_vtxl x'G1].
  by move/f_inj=> <- // ?; apply/in_imfset.
- case/imfsetP=> /= y' xGy' ->; apply/edge_img_graph.
  by exists x; exists y'.
Qed.

Lemma giso_regular {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) n :
  giso G1 G2 -> regular G1 n -> regular G2 n.
Proof.
case=> f /[dup] -[f_inj <-] /gisof_succ Hsucc G1_reg x.
rewrite vtx_img_graph=> /imfsetP [/= x' x'G1 ->].
rewrite Hsucc // card_in_imfset /= ?(G1_reg x') //.
move=> v w; rewrite !in_succE; move/edge_vtxr=> + /edge_vtxr.
exact: f_inj.
Qed.

Lemma gisof_diagram {T1 T2 T3 : choiceType}
  (G1 : graph T1) (G2 : graph T2) (G3 G4 : graph T3)
  (f : T1 -> T2) (g : T1 -> T3) (h : T2 -> T3):
  {in vertices G1, forall x, (g x) = h (f x)} ->
  gisof G1 G2 f -> G3 = (g @/ G1) -> G4 = (h @/ G2) ->
  G3 = G4.
Proof.
move=> fghC G1_G2 G3_img_G1 G4_img_G2.
have vtx_G3G4: vertices G3 = vertices G4.
- rewrite G3_img_G1 G4_img_G2.
  rewrite !vtx_quot_graph -(gisof_vtx G1_G2).
  apply/fsetP=> x; apply/idP/idP.
  + case/imfsetP=> /= x' x'G1 ->; rewrite fghC //.
    by apply/imfsetP; exists (f x')=> //; apply/imfsetP; exists x'.
  + case/imfsetP=> ? /imfsetP [x' ? -> ->].
    by rewrite -fghC //; apply/imfsetP; exists x'.
apply/graphE; split=> //.
move=> x y; rewrite G3_img_G1 G4_img_G2.
apply/idP/idP.
- case/edge_quot_graph=> x' [y'] [<- <-] /[swap].
  move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr; move=> x'G1 y'G1.
  move=> G1_xy'; rewrite !fghC // => hf_xy'.
  apply/edge_quot_graph; exists (f x'), (f y'); split=> //.
  by rewrite -(gisof_edge G1_G2).
- case/edge_quot_graph=> ? [?] [<- <- /[swap]].
  move=> /[dup] /[dup] /edge_vtxl + /edge_vtxr.
  rewrite -(gisof_vtx G1_G2)=> /imfsetP [/= x' x'G1 ->] /imfsetP [/= y' y'G1 ->].
  rewrite -(gisof_edge G1_G2) // -!fghC // => G1_xy' g_xy'.
  by apply/edge_quot_graph; exists x',y'; split.
Qed.


Section GisofPath.

Context {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) (f : T1 -> T2).
Hypothesis (G1G2 : gisof G1 G2 f).
Context (p : epath G1).

Lemma gisof_src : f (src p) \in vertices G2.
Proof. by rewrite -(gisof_vtx G1G2) in_imfset //= mem_src. Qed.

Lemma gisof_walk : path (edges G2) (f (src p)) [seq f x | x <- walk p].
Proof.
move: (path_walk p); elim: (walk p) (src p)=> //= h t IH x /andP [].
move=> G1_xh /IH ->; rewrite andbT -(gisof_edge G1G2) //;
  [exact:(edge_vtxl G1_xh)|exact:(edge_vtxr G1_xh)].
Qed.

Lemma gisof_dst : last (f (src p)) [seq f x | x <- walk p] == f (dst p).
Proof. by rewrite -(last_dst p) last_map. Qed.

Definition gisof_gpath := GPath gisof_src gisof_walk gisof_dst.

Lemma gisof_epath_uniq : uniq (src gisof_gpath :: walk gisof_gpath).
Proof.
move: (uniq_walk p)=> /= /andP [src_walk uniq_walk].
apply/andP; split.
- apply/negP=> /mapP [y] /[dup] y_walk /mem_walk yG1.
  case/gisofE: G1G2=> f_inj _ _; move/f_inj.
  move/(_ (mem_src _) yG1); move: y_walk=> /[swap] <-.
  by rewrite (negPf src_walk).
- rewrite map_inj_in_uniq //.
  move=> x y /mem_walk + /mem_walk.
  case/gisofE: G1G2=> + _ _; apply.
Qed.

Definition gisof_epath := EPath gisof_epath_uniq.
End GisofPath.

Lemma gisof_epath_bij {T1 T2 : choiceType}
  (G1 : graph T1) (G2 : graph T2) (f : T1 -> T2)
  (fp : epath G2) (G1G2 :gisof G1 G2 f) :
  exists (p1 : epath G1),
  gisof_epath G1G2 p1 = fp.
Proof.
move:(mem_src fp); rewrite -(gisof_vtx G1G2).
case/imfsetP=> /= srx srx_G1 srx_eq.
case/gisofE: {1}G1G2=> f_inj _ _.
case: (in_bij srx f_inj)=> g fg_can gf_can.
move: (gisof_sym fg_can G1G2)=> G2G1.
exists (gisof_epath G2G1 fp); apply/epath_inj/gpath_inj; split.
- by rewrite /= gf_can // srx_eq in_imfset.
- by rewrite /= gf_can // (gisof_vtx G1G2) mem_dst.
- rewrite /=; move: (@mem_walk _ _ fp).
  elim: (walk fp)=> //= h t IH mem_ht.
  rewrite gf_can ?IH //.
  + by move=> z zt; apply/mem_ht; rewrite inE zt orbT.
  + by rewrite (gisof_vtx G1G2); apply/mem_ht; rewrite inE eqxx.
Qed.

Lemma size_epath_gisof {T1 T2 : choiceType}
  (G1 : graph T1) (G2 : graph T2) (f : T1 -> T2)
  (G1G2 : gisof G1 G2 f) (p1 : epath G1):
  size_path p1 = size_path (gisof_epath G1G2 p1).
Proof. by rewrite /size_path /= size_map. Qed. 


End GisoTheory.



(*
Context {T : choiceType} (G : graph T).
Local Notation V := (vertices G).
Section BFS.

Program Definition new_unmark_succ (S1 : {fset V}) : {fset V} :=
  let S2 := (\bigcup_(v <- S1) successors G (fsval v)) `|` [fsetval x in S1] in
  [fset [` _ : fsval v \in V] | v : S2].
Next Obligation.
move: (fsvalP v); rewrite in_fsetE; case/orP. 
- by case/bigfcupP=> x _; move/(fsubsetP (sub_succ G (fsval x))).
- case/imfsetP=> /= x _ ->; exact: fsvalP.
Qed.

Lemma unmark_subset (S : {fset V}) : S `<=` new_unmark_succ S.
Proof.
rewrite /new_unmark_succ; apply/fsubsetP=> x xS /=.
apply/imfsetP=> /=.
have xS2: fsval x \in \bigcup_(v <- S) successors G (fsval v) `|` [fset fsval x0 | x0 in S].
- by rewrite in_fsetE; apply/orP; right; apply/in_imfset.
exists [` xS2] => //=; exact/val_inj.
Qed.

Definition mes (S : {fset V}) := #|`V| - #|` S|.

Function BFS_rank (marked : {fset V}) (n : nat) {measure mes marked}:=
  let new := new_unmark_succ marked in
  if marked == new then n else BFS_rank new n.+1.
Proof.
move=> marked _ marked_sub.
have marked_lt: marked `<` new_unmark_succ marked by
  rewrite fproperEneq unmark_subset andbT; apply/negPf.
apply/leP/ltn_sub2l; last exact: fproper_ltn_card.
have ->: #|` V| = #|` [fset x | x : V]| by
  rewrite card_imfset //= -cardE cardfE.
apply/fproper_ltn_card/(fproper_sub_trans marked_lt).
by apply/fsubsetP=> x _; apply/in_imfset.
Qed.

Definition BFS_vertex (x : V) := BFS_rank [fset x] 0.

End BFS.

Section ShortestPaths.

Definition is_path_supp (p : epath G) (S : {fset V}) := all (fun y=> y \in [fsetval z in S]) ((src p)::(walk p)).

Lemma path_supp_sub (p : epath G) (S S' : {fset V}) : S `<=` S' -> is_path_supp p S -> is_path_supp p S'.
Proof.
move/fsubsetP=> subSS' /allP supp_S; apply/allP=> x x_p.
by move: (supp_S x x_p); case/imfsetP=> /= x' /subSS' ? ->; rewrite in_imfset.
Qed.

Definition is_shortest_ (p : epath G) (S : {fset V}) :=
  [forall p' : epath G,
  (src p == src p') ==> (dst p == dst p') ==> (is_path_supp p' S) ==>
  (size_path p <= size_path p')].

Definition is_shortest (p : epath G) (S : {fset V}) := is_shortest_ p S && is_path_supp p S.

Definition limited_access (x : V) (k : nat) (S : {fset V}) :=
  forall p : epath G, src p = fsval x -> is_shortest p S ->
  size_path p <= k.

Definition connected_access (x : V) (S : {fset V}) :=
  forall y, y \in S -> 
  exists p : epath G, [/\ src p = fsval x, dst p = fsval y & is_shortest p S].

Lemma limited_access0 (x : V) : limited_access x 0 [fset x].
Proof.
Admitted.
(* move=> p src_x [_] /allP all_x; rewrite leqn0; apply/eqP/size_path0.
move: (all_x (last (src p) (walk p)))=> /(_ (mem_last _ _)).
by rewrite -last_dst src_x; case/imfsetP=> /= x'; rewrite in_fsetE=> /eqP -> ->.
Qed. *)

Lemma limited_access_succ (x : V) (k : nat) (S : {fset V}):
  limited_access x k S -> connected_access x S -> limited_access x k.+1 (new_unmark_succ S).
Proof.
Admitted.
(* move=> lim_S conn_S p src_x [short_p supp_p].
have: dst p \in [fsetval z in (new_unmark_succ S)] by
  move/allP: supp_p=> /(_ (dst p)); rewrite -last_dst mem_last; exact.
rewrite /new_unmark_succ; case/imfsetP=> /= d /imfsetP [/= d' _].
move/(congr1 val)=> /= dd'; rewrite dd'=> dst_eq.
move: (fsvalP d'); rewrite in_fsetE -dst_eq.
have dst_p_S: forall y, y \in S -> dst p = fsval y -> size_path p <= k.+1.
- move=> y yS dst_y.
  case: (conn_S y yS)=> p' [src_p' dst_p' short_p'].
  move: (lim_S p' src_p' short_p')=> size_p'.
  suff: size_path p <= k by exact: leqW.
  apply/(leq_trans _ size_p')/short_p; rewrite ?src_x ?src_p' ?dst_y ?dst_p' //.
  by apply/(path_supp_sub (unmark_subset S)); case: short_p'.
case/orP.
- case/bigfcupP=> /= y /andP [yS _]; rewrite in_succE=> dst_succ.
  case: (conn_S y yS)=> p' [src_p' dst_p' /[dup] -[short_p' supp_p'] short_p'_].
  move: (lim_S p' src_p' short_p'_)=> path_p'_k.
  case/boolP: (dst p \in (src p') :: (walk p')).
    case/(allP supp_p')/imfsetP; exact: dst_p_S.
  move=> dst_n_p'; rewrite -dst_p' in dst_succ.
  set pr := rcons_epath dst_succ dst_n_p'.
  apply/(@leq_trans (size_path pr)).
  + apply/short_p; rewrite ?src_p' //=.
    apply/allP=> z /=; rewrite !(inE, mem_rcons).
    case/or3P=> [/eqP ->| |h];
      try apply: (allP (path_supp_sub (unmark_subset S) supp_p'));
      rewrite ?mem_head ?inE ?h ?orbT //.
    move/eqP=> ->; apply/imfsetP; exists d; rewrite ?dd' //=.
    apply/imfsetP; exists d'=> //=; exact: val_inj.
  + by rewrite /size_path size_rcons ltnS.
- case/imfsetP=> /=; exact: dst_p_S.
Qed. *)

Lemma BFS_vertexP (x : V) (p : epath G): 
  limited_access x (BFS_vertex x) [fset x | x : V].
Proof.
Admitted.

End ShortestPaths.


Lemma xV : ~(V = fset0) -> {x : T & x \in V}.
Proof. 
move/eqP/fset0Pn=> h; have := (xchooseP h)=> a.
by apply (existT _ (xchoose h)).
Qed.

Definition arg_diameter (p0 : epath G) :=
  [arg max_(p > p0 | is_shortest p [fset x | x : V]) size_path p].

Definition diameter :=
  if V =P fset0 is ReflectF h
  then size_path (arg_diameter (nil_path (tagged (xV h))))
  else 0.

End Diameter.
*)
