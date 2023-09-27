From mathcomp Require Import all_ssreflect finmap.
From Coq Require Import PArray Uint63.
Require Import PArith.BinPos PArith.BinPosDef.
Require Import NArith.BinNat NArith.BinNatDef.
From Polyhedra Require Import extra_misc.
Require Import extra_array extra_int graph high_graph refinement.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.Theory.

Module Queue.
Section Queue.

Context {T : Type}.

Record queue := Queue { front : seq T; back : seq T; }.

Implicit Types (q : queue) (x : T) (xs : seq T).

Definition empty := Queue [::] [::].

Definition isempty q :=
  if q is Queue [::] [::] then true else false.

Definition enqueue q x :=
  Queue q.(front) (x :: q.(back)).

Definition pull q :=
  if   q is Queue [::] back
  then Queue (rev back) [::] 
  else q.

Definition dequeue q :=
  if   pull q is Queue (x :: front) back
  then Some (x, Queue front back)
  else None.

Definition relqueue q xs :=
  q.(front) ++ rev q.(back) = xs.

Notation "q <+> xs" := (relqueue q xs)
  (at level 70, no associativity).

Lemma rq0 : relqueue empty [::].
Proof. by []. Qed.

Lemma rq_enqueue q xs x :
  q <+> xs -> enqueue q x <+> rcons xs x.
Proof. by move=> <-; rewrite rcons_cat -rev_cons. Qed.

Lemma rq_enqueue_witness q xs x :
  enqueue q x <+> xs -> exists2 hs, xs = rcons hs x & q <+> hs.
Proof.
rewrite /enqueue /relqueue /= rev_cons -rcons_cat.
by move=> <-; exists (front q ++ rev (back q)).
Qed.

Lemma rq_pull q xs : q <+> xs -> pull q <+> xs.
Proof. 
move=> <-; case: q=> [front back]; case: front=> //=.
(* TODO : why unfolding is mandatory ? *)
by rewrite /relqueue /rev /= cats0.
Qed.

Lemma rq_dequeue_nil q : q <+> [::] -> Queue.dequeue q = None.
Proof.
move=> /rq_pull; rewrite /dequeue; case: (pull q)=> front back.
by case: front.
Qed.

Lemma rq_dequeue_cons q x xs :
  q <+> x :: xs ->
    exists2 q', Queue.dequeue q = Some (x, q') & q' <+> xs.
Proof.
move=> /rq_pull; rewrite /dequeue /pull; case: q=> [front back].
case: front=> [|h t].
- elim/last_ind: back=> // back' x' _; rewrite rev_rcons.
  case=> ->; rewrite /rev cats0=> ->; exists (Queue xs [::])=> //.
  by rewrite /relqueue /rev cats0.
- rewrite /relqueue cat_cons; case=> -> <-.
  by exists (Queue t back).
Qed.

Lemma rq_witness q: exists s, q <+> s.
Proof. by exists (q.(front) ++ rev q.(back)). Qed.

End Queue.

Definition mem_queue {T : eqType} (x : T) (q : @queue T):= 
  forall rs, relqueue q rs -> x \in rs.

Lemma mem_queue0 {T : eqType} (x : T):
  ~ mem_queue x (empty).
Proof.
by move=> /(_ [::]) /(_ (erefl _)) /=.
Qed.

Lemma mem_enqueue {T : eqType} (x y : T) (q : @queue T):
  mem_queue x (enqueue q y) -> x = y \/ mem_queue x q.
Proof.
case: (rq_witness q)=> s rq_s /(_ (rcons s y)).
rewrite /relqueue /= rev_cons -rcons_cat rq_s.
move/(_ (erefl _)); rewrite mem_rcons in_cons.
case/orP=> [/eqP ->|xs]; [by left|right].
by move=> s'; rewrite /relqueue rq_s => <-.
Qed.

Lemma mem_queue_cons {T : eqType} (h x: T) (t : seq T) (q q': @queue T):
  relqueue q (h :: t) -> relqueue q' t -> 
  mem_queue x q <-> x = h \/ mem_queue x q'.
Proof.
move=> rq_ht rq'_t; split.
- move/(_ _ rq_ht); rewrite in_cons; case/orP=> [/eqP ->|]; [by left|].
  by move=> xt; right=> rs'; rewrite /relqueue rq'_t => <-.
- by case=> [-> rs'|/(_ _ rq'_t) xt rs']; 
    rewrite /relqueue rq_ht => <-; rewrite in_cons ?eq_refl // xt orbT.
Qed.

End Queue.

Arguments Queue.queue T : clear implicits.
Arguments Queue.empty T : clear implicits.

Module DiameterComputation.

Definition bfsqueue := Queue.queue (int * N)%type.
Definition marks    := array bool.

Record state := State {
  maxpath  : N;
  visited  : marks;
  queue    : bfsqueue;
}.

Module State.
  Definition mk (n : int) (y : int) :=
    {| maxpath  := 0%N;
       visited  := (PArray.make n false).[y <- true]; 
       queue    := Queue.empty _; |}.

  Definition mark (st : state) (y : int) (k : N) :=
    if st.(visited).[y] then st else
      {| maxpath := N.max k st.(maxpath);
         visited := st.(visited).[y <- true]; 
         queue   := Queue.enqueue st.(queue) (y, k); |}.

  Definition dequeue (st : state) :=
    if Queue.dequeue st.(queue) is Some ((y, k), q) then
      let st := {|
        maxpath := st.(maxpath);
        visited := st.(visited);
        queue   := q;
      |} in Some (st, y, k)
    else None.
End State.

Section Diameter.
Definition BFS_step (g : graph.graph) (st : state * int * N) :=
  let: (st, x, k) := st in

  let: st :=
    GraphUtils.neighbour_fold
      (fun y st => State.mark st y (N.succ k))
      st g x in

  match State.dequeue st with
  | Some st => inl st
  | None    => inr st
  end.

Definition BFS_ (g : graph.graph) (x : int) :=
  let: out := BFS_step g (State.mk (PArray.length g) x, x, 0%N) in
  let: out := IFold.iofold
    (fun _ s => BFS_step g s)
    (length g)%uint63
    out in
  if out is inr v then Some v else None.

Definition BFS (g : graph.graph) (x : int) :=
  odflt 0%N (omap (fun x => x.(maxpath)) (BFS_ g x)).

Definition diameter_BFS (g : graph.graph) :=
  IFold.ifold (fun i v=> N.max v (BFS g i)) (length g) 0%N.

End Diameter.
End DiameterComputation.

Module DC := DiameterComputation.

Section DiameterEquiv.
Definition BFS_step (g : graph.graph) (st : DC.state * int * N) :=
  let: (st, x, k) := st in

  let: st :=
    neighbour_fold
      (fun y st => DC.State.mark st y (N.succ k))
      st g x in

  match DC.State.dequeue st with
  | Some st => inl st
  | None    => inr st
  end.

Definition BFS_ (g : graph.graph) (x : int) :=
  let: out := BFS_step g (DC.State.mk (PArray.length g) x, x, 0%N) in
   let: out := iofold
      (fun _ s => BFS_step g s)
      (length g)%uint63
      out in
    if out is inr v then Some v else None.

Definition BFS (g : graph.graph) (x : int) :=
  odflt 0%N (omap (fun x => x.(DC.maxpath)) (BFS_ g x)).

Definition diameter_BFS (g : graph.graph) :=
  ifold (fun i v=> N.max v (BFS g i)) (length g) 0%N.

Section Equiv.

Lemma BFSE (g : graph.graph) x:
  DC.BFS g x = BFS g x.
Proof.
rewrite /DC.BFS /BFS.
congr odflt; congr omap.
rewrite /DC.BFS_ /BFS_ iofoldE.
set IO := iofold _ _ _; set IO' := iofold _ _ _.
suff ->: IO = IO' by [].
rewrite /IO /IO' /iofold /DC.BFS_step neighbour_foldE.
apply/eq_foldl=> + j; case=> // -[[]] ??? /=.
by rewrite neighbour_foldE.
Qed.

Lemma low_diameterE (g : graph.graph):
  DC.diameter_BFS g = diameter_BFS g.
Proof.
rewrite /DC.diameter_BFS /diameter_BFS.
rewrite ifoldE; apply/eq_foldl=> x y.
by congr N.max; rewrite BFSE.
Qed.

End Equiv.
End DiameterEquiv.

Section HighDiameter.
Section Def.

Context {T : choiceType} (G : graph T).

Definition is_shortest (p : gpath G) :=
  forall p' : gpath G, (src p = src p') -> dst p = dst p' ->
  size_path p <= size_path p'.

Definition is_shortest_epath (p : epath G) :=
  [forall p' : epath G, (src p == src p') ==> (dst p == dst p') ==> 
  (size_path p <= size_path p')].

Lemma is_shortestP (p : epath G): reflect
  (is_shortest p)
  (is_shortest_epath p).
Proof.
apply/(iffP idP).
- move=> h p' /eqP src_eq /eqP dst_eq.
  move/forallP: h=> /(_ (@gpath_epath _ _ p')).
  rewrite gpath_epath_src gpath_epath_dst src_eq dst_eq.
  move/leq_trans; apply; exact:size_gpath_epath.
- move=> h; apply/forallP=> p'; apply/implyP=> /eqP src_eq.
  by apply/implyP=> /eqP dst_eq; apply: h.
Qed.

Definition eccentricity x:=
  \max_(p : epath G | is_shortest_epath p && (src p == x)) size_path p.

Definition diameter := \max_(p : epath G | is_shortest_epath p) size_path p.

Lemma eccentricity_epathP x: forall p : epath G, 
  src p = x -> is_shortest_epath p ->
  size_path p <= eccentricity x.
Proof.
move=> p src_p is_shtt_p.
by apply/(bigmax_sup p)=> //; rewrite is_shtt_p src_p eqxx.
Qed.

Lemma eccentricityP x: forall p : gpath G, src p = x ->
  is_shortest p -> size_path p <= eccentricity x.
Proof.
move=> p src_p is_shtt_p.
set p' := (@gpath_epath _ _ p).
apply/leq_trans; first apply/(is_shtt_p p');
  [exact:gpath_epath_src|exact:gpath_epath_dst|].
apply/eccentricity_epathP; rewrite ?gpath_epath_src //. 
apply/is_shortestP=> p'' src_p'' dst_p''.
apply/leq_trans; [exact:size_gpath_epath|apply:is_shtt_p].
- by rewrite -gpath_epath_src. 
- by rewrite -gpath_epath_dst.
Qed.


Lemma diameter_epathP: forall p : epath G, is_shortest_epath p -> size_path p <= diameter.
Proof.
move=> p is_shtt_p; rewrite /diameter.
exact/(bigmax_sup p).
Qed.

Lemma diameter0:
  G = graph0 T -> diameter = 0.
Proof.
move=> G0; rewrite /diameter.
case: (big_enumP is_shortest_epath)=> /= e <- _ [] _.
set P := [pred _ | _].
suff: #|P| = 0 by 
  move=> -> /size0nil ->; rewrite big_nil.
move: {e} P (max_card P) => /=.
by rewrite G0 epath0=> P; rewrite leqn0=> /eqP.
Qed.


Lemma diameterP: G != graph0 T ->
(exists2 p : gpath G, is_shortest p & size_path p = diameter) /\ 
(forall p : gpath G, is_shortest p -> size_path p <= diameter).
Proof.
case/graph0Pn=> x xG.
split.
+ move=> [:H]. 
  rewrite /diameter (bigmax_eq_arg (nil_path xG)).
  - abstract: H. 
    apply/is_shortestP=> p' _ _; rewrite /size_path /=.
    exact: leq0n.
  - set p := arg_max _ _ _; exists p=> //.
    apply/is_shortestP; rewrite /p.
    by case: (arg_maxnP (fun p : epath G => size_path p) H).
+ move=> p is_shtt_p.
  set p' := (@gpath_epath _ _ p).
  apply/leq_trans; first apply/(is_shtt_p p');
    [exact:gpath_epath_src|exact:gpath_epath_dst|].
  apply/diameter_epathP/is_shortestP=> p'' src_p'' dst_p''.
  apply/leq_trans; [exact:size_gpath_epath|apply:is_shtt_p].
  - by rewrite -gpath_epath_src. 
  - by rewrite -gpath_epath_dst.
Qed.

End Def.
Section BFSDef.

Context {T : choiceType} (G : graph T).
Context {dataType : Type}.
Notation data_queue := (Queue.queue (T * dataType)%type).
Context {collectType : Type}.

Record state := State
  {
    collect : collectType;
    visited : {fset T};
    queue : data_queue;
  }.

Definition mk (y : T) (d : collectType):=
  {|
    collect := d;
    visited := [fset y];
    queue := Queue.empty _; 
  |}.

Definition mark (st : state) (y : T) (k : dataType) 
  (coll : state -> dataType -> collectType):=
  if y \in st.(visited) then st else
  {|
    collect := coll st k;
    visited := y |` st.(visited);
    queue := Queue.enqueue st.(queue) (y,k) 
  |}.

Definition dequeue (st : state) :=
  if Queue.dequeue st.(queue) is Some ((y,k), q) then
    let st := 
    {|
      collect := st.(collect);
      visited := st.(visited);
      queue := q;
    |} in Some (st, y, k)
  else None.

Definition param_BFS_step (st : state * T * dataType)
  (updt : T -> dataType -> T -> dataType)
  coll 
  (succ : T -> seq T) :=
  let: (st, x, k) := st in
  let: st := foldl (fun s y=> mark s y (updt x k y) coll) st (succ x) in
  match dequeue st with
  | Some st => inl st
  | None    => inr st
  end.

Definition param_BFS_iter (y : T) (d : dataType) (c : collectType) updt coll succ:=
  iter #|` vertices G|.+1
  (oapply (fun x=> param_BFS_step x updt coll succ)) 
  (inl ((mk y c), y, d)).

Definition param_BFS_ (y : T) (d : dataType) (c : collectType) updt coll succ:=
  match param_BFS_iter y d c updt coll succ with
  |inl _ => None
  |inr v => Some v
  end.

Definition param_BFS y d c updt coll succ := 
  odflt c (omap collect (param_BFS_ y d c updt coll succ)).

End BFSDef.

Section HBFS.

Context {T : choiceType} (G : graph T).

Definition Hstate := @state T nat nat.
Definition Hmk (y : T) : Hstate := mk y 0%nat.
Definition Hmark (st : Hstate) (y : T) (k : nat) :=
  mark st y k (fun s k=> maxn s.(collect) k).
Definition Hdequeue (st : Hstate) := dequeue st.  
Definition HBFS_step (y : Hstate * T * nat) succ :=
  param_BFS_step y (fun _ k _=> k.+1) (fun s k=> maxn s.(collect) k) succ.
Definition HBFS_iter (y : T) succ := 
  param_BFS_iter G y 0%nat 0%nat (fun _ k _=> k.+1) (fun s k=> maxn s.(collect) k) succ.
Definition HBFS_ (y : T) succ := 
  param_BFS_ G y 0%nat 0%nat (fun _ k _=> k.+1) (fun s k=> maxn s.(collect) k) succ.
Definition HBFS (y : T) succ := 
  param_BFS G y 0%nat 0%nat (fun _ k _=> k.+1) (fun s k=> maxn s.(collect) k) succ.
Definition Hdiameter_BFS succ := \max_(i <- vertices G) HBFS i succ.

End HBFS.

End HighDiameter.

Section RelStruct.

Context (g : graph.graph) (G : high_graph.graph [choiceType of Uint63.int]).
Hypothesis gG : rel_structure g G.

Section RelDef.

Definition rel_queue (q : Queue.queue (int * N)) (Q : Queue.queue (Uint63.int * nat)):=
  forall rs rS, Queue.relqueue q rs -> Queue.relqueue Q rS ->
  (forall x, x \in rs -> mem_vertex g x.1) /\
  [seq (i.1, nat_of_bin i.2) | i <- rs] = rS.

Definition rel_state (s : DC.state) (S : state):= [/\
  s.(DC.maxpath) = S.(collect) :> nat, length (DC.visited s) = length g,
  (forall i, mem_vertex g i -> s.(DC.visited).[i] = (i \in S.(visited))) &
  rel_queue s.(DC.queue) S.(queue)].

Lemma rel_state_mk (y : int): mem_vertex g y -> rel_state (DC.State.mk (length g) y) (mk y 0).
Proof.
move=> yg; split=> //=; last by move=> rs rS <- <-.
  by rewrite length_set length_make leb_length.
move=> i ig; case/boolP: (i == y).
+ by move/eqP=> <-; rewrite get_set_same ?length_make ?leb_length ?ig // inE eq_refl.
+ rewrite eq_sym; move/eqP=> i_n_y; rewrite get_set_other // get_make; apply/esym.
  rewrite inE; move/eqP: i_n_y; rewrite eq_sym.
  by apply/contra_neqF=> /eqP. 
Qed.

Definition rel_pair {P Q P' Q' : Type} (rP : P -> P' -> Prop) (rQ : Q -> Q' -> Prop) (x : P + Q) (y : P' + Q'):=
  match x, y with
  |inl x_, inl y_ => rP x_ y_
  |inr x_, inr y_ => rQ x_ y_
  |_, _ => False
  end.

Definition rel_continue (s : DC.state * int * N) (S : state * int * nat):=
  let: (st,i,n) := s in
  let: (St, t, k) := S in
  [/\ rel_state st St, (mem_vertex g i), i = t & (nat_of_bin n = k)].

Definition rel_step (s : DC.state * int * N + DC.state) (S : state * int * nat + state):=
  rel_pair rel_continue rel_state s S.

Lemma rel_step_mk (y : int): mem_vertex g y-> 
  rel_step (inl (DC.State.mk (PArray.length g) y, y, 0%N)) (inl (mk y 0, y, 0)). 
Proof. move=> yg /=; split=> //; exact/rel_state_mk. Qed.

Definition rel_option {A B : Type} (r : A -> B -> Prop) (x : option A) (y : option B):=
  match x, y with
  |Some x', Some y'=> r x' y'
  |None, None=> True
  |_, _=> False
  end.

Definition succ x := arr_to_seq (neighbours g x).

(* Lemma succ_neiE (x : T):
  (x \in vertices G) -> perm_eq (successors G x) (succ x).
Proof.
move=> /[dup] /foo=> -[i] /andP [ig /eqP x_i_eq] xG.
rewrite -x_i_eq (repr_succ gG) // /succ.
case: {-}_/idP; last rewrite x_i_eq //. 
move => xG'.
have ->: xchoose (foo xG') = i by
  apply/(repr_lbl_inj gG); rewrite ?to_graph_vtx //; 
  case/andP: (xchooseP (foo xG'))=> // _ /eqP.
apply/(perm_trans (enum_imfset _ _))=> /=.
- move=> p q /andP [? _] /andP [? _].
  by apply/(repr_lbl_inj gG); rewrite to_graph_vtx.
apply/perm_map/uniq_perm; 
  try apply/filter_uniq; rewrite ?enum_uniq ?uniq_irange //.
move=> k /=; rewrite !mem_filter /= -?enumT mem_enum /= inE andbT andbC.
by rewrite mem_irangeE le0x /= ltEint.
Qed. *)

End RelDef.

Section ReprGraphBFS.

Lemma repr_graph_BFS_dequeue s S:
  rel_state s S -> rel_option rel_continue
    (DC.State.dequeue s) (dequeue S).
Proof.
case=> max_eq len_vis_eq vis_eq.
case: (Queue.rq_witness (DC.queue s))=> rs rq_rs.
case: (Queue.rq_witness (queue S))=> rS rq_rS.
move/(_ rs rS rq_rs rq_rS)=> [].
rewrite /DC.State.dequeue /dequeue /=.
case: rs rq_rs=> [/Queue.rq_dequeue_nil ->|].
  by move: rq_rS=> /[swap] _ /[swap] /= <- /Queue.rq_dequeue_nil ->.
case=> i k l rq_s_ikl.
case: rS rq_rS=> // -[Y K] L rq_S_YKL.
case: (Queue.rq_dequeue_cons rq_s_ikl)=> s' ->.
case: (Queue.rq_dequeue_cons rq_S_YKL)=> S' -> /=.
move=> rq_S' rq_s' ikl_g [Y_eq K_eq L_eq].
split=> //; last (move: (ikl_g (i, k)); rewrite ?inE ?eq_refl /=; exact).
split=> //= l' L'; rewrite /Queue.relqueue rq_S' rq_s' => <- <-.
by split=> // x xl; apply/ikl_g; rewrite in_cons xl orbT.
Qed.

Lemma repr_graph_BFS_mark y s S n : mem_vertex g y -> 
  rel_state s S ->
  rel_state (DC.State.mark s y n) (mark S y n (fun s k=> maxn s.(collect) k)).
Proof.
move=> yg sS; rewrite /DC.State.mark /mark.
case: sS=> eq_max eq_len_vis eq_vis eq_queue.
rewrite (eq_vis _ yg); case: ifP=> //.
move=> y_n_vis; split=> //=.
- by rewrite N_maxE eq_max maxnC.
- by rewrite length_set.
- move=> i ig; case/boolP: (i == y).
  + by move/eqP=> ->; rewrite get_set_same ?eq_len_vis // !inE eq_refl.
  + move=> /[dup] /eqP ? i_n_y; rewrite get_set_other; first by move/esym.
    by rewrite eq_vis //; rewrite !inE (negPf i_n_y) /=.
- move=> rs rS /= rq_rs rq_rS.
  case: (Queue.rq_enqueue_witness rq_rS)=> rS' rS_eq.
  case: (Queue.rq_enqueue_witness rq_rs)=> rs' rs_eq.
  move/eq_queue=> /[apply] /= -[rs'_g rs'_eq].
  rewrite rs_eq rS_eq; split.
  + by move=> x; rewrite mem_rcons inE; case/orP=> [/eqP ->|/rs'_g].
  + by rewrite map_rcons; congr rcons.
Qed.

Lemma repr_graph_BFS_mark_fold y s S n: mem_vertex g y -> rel_state s S ->
  rel_state 
    (neighbour_fold (fun i st=> (DC.State.mark st i (N.succ n))) s g y)
    (foldl (fun St x=> mark St x (nat_of_bin n).+1 (fun s k=> maxn s.(collect) k)) S (succ y)).
Proof.
move=> yg sS; rewrite neighbour_foldP // /succ.
rewrite -{2}(rel_struct_nei_mem gG) //.
elim/last_ind: (arr_to_seq _)=> // t h IH.
rewrite !filter_rcons; case: ifP=> // hg.
rewrite !foldl_rcons; move: IH.
suff ->: n.+1 = (N.succ n) by exact/repr_graph_BFS_mark.
by elim: n=> //= n; rewrite nat_of_succ_pos.
Qed.

Lemma repr_graph_BFS_step (y : int) (s : DC.state) (S : state) (n : N):
  mem_vertex g y -> rel_state s S -> 
  rel_step (BFS_step g (s, y, n)) (HBFS_step (S, y, nat_of_bin n) succ).
Proof.
move=> yg sS.
rewrite /BFS_step /HBFS_step /param_BFS_step.
move: (repr_graph_BFS_mark_fold n yg sS)=> /[dup] + /repr_graph_BFS_dequeue.
by case: (dequeue _)=> //=; case: (DC.State.dequeue _).
Qed.

Lemma repr_graph_BFS_iter (s : DC.state * int * N + DC.state) (S : state * int * nat + state) (n : int):
  rel_step s S -> rel_step (iofold (fun _=> BFS_step g) n s) (iter n (oapply (HBFS_step^~ succ)) S).
Proof.
rewrite /iofold irange0_iota.
elim: (int_to_nat n)=> // k.
rewrite iotaS_rcons add0n map_rcons foldl_rcons /=.
set F := foldl _ _ _; set I := iter _ _ _.
move=> /[apply]; case: F; case: I=> //=.
case=> -[St Y P] [[st y] p] [] /[swap] ++ <- <-.
exact/repr_graph_BFS_step.
Qed.

Lemma repr_graph_BFS_ (y : int): mem_vertex g y ->
  rel_option rel_state (BFS_ g y) (HBFS_ G y succ).
Proof. 
move=> yg; rewrite /BFS_ /HBFS_ /param_BFS_ /param_BFS_iter iterSr.
move/(repr_graph_BFS_step 0 yg): (rel_state_mk yg).
move/(repr_graph_BFS_iter (length g)).
rewrite /HBFS_step (rel_struct_card gG).
set I := iofold _ _ _; set I' := iter _ _ _.
by case: I; case: I'.
Qed.
 
Lemma repr_graph_BFS (y : int): mem_vertex g y->
  BFS g y = HBFS G y succ :> nat.
Proof.
move=> yg; rewrite /BFS /HBFS /param_BFS.
move: (repr_graph_BFS_ yg); rewrite /HBFS_.
case: (BFS_ _ _); case: (param_BFS_ _ _ _)=> //=.
by move=> ?? [].
Qed.

Lemma repr_graph_diameter : diameter_BFS g = Hdiameter_BFS G succ :> nat.
Proof.
rewrite /diameter_BFS /Hdiameter_BFS /ifold.
rewrite (rel_struct_vtx_set gG) big_imfset //= undup_id ?uniq_irange //.
rewrite (perm_big (irange0 (length g))).
- apply/uniq_perm=> //; try exact/uniq_irange.
have: (forall x, x \in irange0 (length g) -> mem_vertex g x) by move=> ?; rewrite mem_irangeE le0x ltEint.
elim/last_ind: (irange0 _)=> /=; first by (move=> _; rewrite big_nil).
move=> t h IH mem_th; rewrite foldl_rcons big_rcons.
rewrite -repr_graph_BFS; first by (apply/mem_th; rewrite mem_rcons inE eq_refl).
rewrite -IH /=; first by (move=> x xt; apply/mem_th; rewrite mem_rcons in_cons xt orbT).
by rewrite N_maxE.
Qed.

End ReprGraphBFS.

End RelStruct.

Section DiameterProof.

Context {T : choiceType} (G : graph T).
Context (succ : T -> seq T).
Hypothesis succG : forall x, x \in vertices G -> succ x =i successors G x.

Section BFS.

Context (x:T).
Hypothesis xG : x \in vertices G.

Section Utils.

Definition supp_shortest (p : epath G) (S : {fset T}):=
  [&& (src p == x), (dst p \in S) & is_shortest_epath p].

Definition target_shortest (p : epath G) (y : T):=
  [&& (src p == x), (dst p == y) & is_shortest_epath p].

Lemma supp_shortestP (p : epath G) S: reflect
  ([/\ src p = x, dst p \in S & is_shortest p])
  (supp_shortest p S).
Proof.
apply/(iffP idP).
- by case/and3P=> /eqP -> -> /is_shortestP.
- by case=> src_p dst_p /is_shortestP is_sht; apply/and3P; rewrite src_p dst_p is_sht.
Qed.

Lemma target_shortestP (p : epath G) y: reflect
  ([/\ src p = x, dst p = y & is_shortest p])
  (target_shortest p y).
Proof.
apply/(iffP idP).
- by case/and3P=> /eqP -> /eqP -> /is_shortestP.
- by case=> src_p dst_p /is_shortestP is_sht; apply/and3P; rewrite src_p dst_p is_sht.
Qed.

Lemma supp_shortest1 p: supp_shortest p [fset x] -> p = nil_path xG.
Proof.
case/supp_shortestP=> src_p /fset1P dst_p is_sht.
apply/epath_inj/gpath_inj=> /=; split=> //.
move: (is_sht (nil_path xG))=> /= /(_ src_p dst_p).
by rewrite /size_path /= leqn0 size_eq0 => /eqP.
Qed.

Lemma target_shortest_witness (p : epath G) (z : T):
  src p = x -> dst p = z -> exists p', target_shortest p' z.
Proof.
move=> src_p dst_p.
pose P := fun p' : epath G => (src p' == x) && (dst p' == z).
have P0: P p by apply/andP; split; exact/eqP.
case/(arg_minnP (fun p : epath G => size_path p)): P0=> p' /andP [/eqP src_p' /eqP dst_p'] min_p'.
exists p'; apply/target_shortestP; split=> // p''.
rewrite src_p' dst_p' => src_p'' dst_p''. 
apply/leq_trans; [|exact:size_gpath_epath].
apply/min_p'.
by rewrite /P -src_p'' -dst_p'' !eq_refl.
Qed.

Lemma target_shortest_by_size (p : epath G) (z : T) (n : nat):
  (forall p', target_shortest p' z -> size_path p' = n) ->
  src p = x -> dst p = z -> size_path p = n -> target_shortest p z.
Proof.
move=> size_prop src_p dst_p size_p; apply/target_shortestP; split=> //p'. 
rewrite src_p dst_p size_p => src_p' dst_p'.
case: (target_shortest_witness src_p dst_p)=> p_min /[dup] /size_prop <-.
by case/target_shortestP=> ??; apply; rewrite -?src_p' -?dst_p'.
Qed.

(* Lemma target_supp_shortest p y: target_shortest p y S -> supp_shortest p S.
Proof. by case/target_shortestP=> ? dst_p ??; apply/supp_shortestP; rewrite ?dst_p. Qed. *)

Definition join_epath (p : epath G) y : epath G:=
  if @idP (edges G (dst p) y) is ReflectT h_py then
  if @idP (y \notin src p :: walk p) is ReflectT h_ynp then
  rcons_epath h_py h_ynp else p else p.

Lemma join_epath_supp (p : epath G) v (S : {fset T}):
  {subset src p :: walk p <= S} -> edges G (dst p) v -> v \notin S -> 
  [/\ src (join_epath p v) = src p, dst (join_epath p v) = v & 
  walk (join_epath p v) = rcons (walk p) v].
Proof.
move=> sub_p edge_pv v_nS; rewrite /join_epath.
case: {-}_/idP=> //.
have h_v_np: v \notin src p :: walk p by move: v_nS; exact/contra/sub_p.
by case: {-}_/idP.
Qed.

Definition frontier_epath (p : epath G) (S : {fset T}): epath G :=
    if @idP (src p \in S) is ReflectT h_src then
    if @idP (dst p \notin S) is ReflectT h_dst then
    in_out_epath h_src h_dst else p else p.

Lemma frontier_epathP (p : epath G) (S : {fset T}):
  src p \in S -> dst p \notin S ->
  let: fp := frontier_epath p S in
  {subset belast (src fp) (walk fp) <= S} /\ dst fp \notin S.
Proof.
move=> src_p dst_p; rewrite /frontier_epath.
case: {-}_/idP=> //; case: {-}_/idP=> // dst_p' src_p'.
split=> /=.
- move/allP: (in_out_epath_in src_p' dst_p'); exact.
- exact: (in_out_epath_out src_p' dst_p').
Qed.

Lemma frontier_epath_src (p : epath G) (S : {fset T}):
  src (frontier_epath p S) = src p.
Proof. by rewrite /frontier_epath; case: {-}_/idP=> //; case: {-}_/idP. Qed.

Lemma frontier_epath_n0 (p : epath G) (S : {fset T}):
  src p \in S -> dst p \notin S ->
  size_path (frontier_epath p S) > 0.
Proof.
move=> src_p dst_p; case: (frontier_epathP src_p dst_p).
case/boolP: (size_path (frontier_epath p S) == 0); rewrite ?lt0n //.
by move/eqP/size_path0=> <-; rewrite frontier_epath_src src_p.
Qed.

Lemma frontier_epath_prefix (p : epath G) (S : {fset T}):
  src p \in S -> dst p \notin S ->
  prefix_seq (walk (frontier_epath p S)) (walk p).
Proof.
move=> src_p dst_p; rewrite /frontier_epath.
case: {-}_/idP=> //; case: {-}_/idP=> // dst_p' src_p'.
by case/andP: (xchooseP (prefix_seq_in_out src_p' (last_out dst_p'))).
Qed.

Definition fp_in (p : epath G) (S : {fset T}):= 
  last (src p) (behead (belast (src p) (walk (frontier_epath p S)))).

Lemma fp_inP (p : epath G) (S : {fset T}):
  src p \in S -> dst p \notin S ->
  fp_in p S \in S /\ edges G (fp_in p S) (dst (frontier_epath p S)).
Proof.
move=> src_p dst_p; split.
- case: (frontier_epathP src_p dst_p)=> + _; apply.
  move: (frontier_epath_n0 src_p dst_p); rewrite /size_path /fp_in.
  case/lastP: (walk _)=> // t h _; rewrite !belast_rcons /=.
  by rewrite frontier_epath_src mem_last.
- rewrite /fp_in -(frontier_epath_src p S).
  exact/edge_dst/frontier_epath_n0.
Qed.

Definition in_frontier_epath (p : epath G) (S : {fset T}):=
  sub_epath (prefix_seq_belast (walk (frontier_epath p S)) (src p)).

Lemma in_frontier_epath_ext (p : epath G) (S : {fset T}):
  dst (in_frontier_epath p S) = fp_in p S /\
  src (in_frontier_epath p S) = src p.
Proof. by rewrite -last_dst frontier_epath_src. Qed.

Lemma frontier_epath_size (p : epath G) (S : {fset T}):
  src p \in S -> dst p \notin S ->
  size_path (frontier_epath p S) =
  (size_path (in_frontier_epath p S)).+1.
Proof.
move=> src_p dst_p; rewrite /size_path /= size_behead size_belast.
rewrite prednK //; exact/frontier_epath_n0.
Qed.



End Utils.

Section Invariant.

Definition inv_collect (s : Hstate) := s.(collect) = 
  \max_(p : epath G | supp_shortest p s.(visited)) size_path p.

Definition inv_queue_vis (s : @Hstate T) y k := 
  forall y' k', (y',k') = (y,k) \/ Queue.mem_queue (y',k') s.(queue) -> 
  y' \in s.(visited).

Definition inv_queue_paths (s : @Hstate T) y k :=
  forall y' k', (y', k') = (y,k) \/ Queue.mem_queue (y',k') s.(queue) ->
  exists p : epath G, [/\ target_shortest p y', {subset src p :: walk p <= s.(visited)} & size_path p = k'].
  
Definition inv_edge (s : @Hstate T) (y : T) (k : nat):=
  forall u v, u \in s.(visited) -> v \notin s.(visited) ->
  edges G u v ->
  u = y \/ exists k', Queue.mem_queue (u,k') s.(queue).

Definition inv_queue_sort (s : @Hstate T) (y : T) (k : nat):=
  forall rs, Queue.relqueue s.(queue) rs ->
  exists l r : seq (T * nat), [/\ (y,k) :: rs = l ++ r, all (fun z=> z.2 == k) l & all (fun z=> z.2 == k.+1) r].

Definition inv_x_vis (s : Hstate):= x \in s.(visited).
Definition inv_vis_vtx (s : Hstate) := s.(visited) `<=` vertices G.

Definition inv_state (s : Hstate):= [/\ inv_collect s, inv_x_vis s & inv_vis_vtx s].

Definition inv_step (S : Hstate * T * nat):=
  let: (s, y, k):= S in
  [/\ 
    inv_state s,
    inv_edge s y k,
    inv_queue_vis s y k,
    inv_queue_paths s y k &
    inv_queue_sort s y k
  ].

Definition inv_step_sum (S : Hstate * T * nat + Hstate):=
  match S with
  |inl Sl => inv_step Sl
  |inr Sr => inv_state Sr
  end.

End Invariant.
Section Proofs.

Section Init.

Lemma Hmk_collect: inv_collect (Hmk x).
Proof.
rewrite /inv_collect /=; apply/anti_leq; rewrite leq0n /=.
by apply/bigmax_leqP=> p /supp_shortest1 ->.
Qed.


Lemma Hmk_step: inv_step ((Hmk x), x, 0).
Proof.
split; first split.
- rewrite /inv_collect /=; apply/anti_leq; rewrite leq0n /=.
  by apply/bigmax_leqP=> p /supp_shortest1 ->; rewrite /size_path.
- by rewrite /inv_x_vis /= fset11.
- by rewrite /inv_vis_vtx /= fsub1set.
- move=> u v /= /fset1P -> _ _; by left.
- move=> y' k'; case=> [[-> /= _]|]; [exact: fset11|].
  by move/Queue.mem_queue0.
- move=> y' k'; case=> [[-> ->]|/Queue.mem_queue0] //.
  exists (nil_path xG)=> /=; split=> //; last move=> z; rewrite ?inE //.
  by apply/target_shortestP.
- by move=> rs /= <- /=; exists [:: (x,0)], [::].
Qed.

End Init.
Section HMark.
Definition Hmark_fold (s : Hstate) y k:= 
  foldl (fun (s0 : state) (y0 : T) =>
    mark s0 y0 k.+1 (fun s1 : Hstate=> maxn s1.(collect))) 
    s (succ y).

Lemma Hmark_foldE s y k:
  has (fun z=> z \notin s.(visited)) (succ y) ->
  Hmark_fold s y k = 
  State  (maxn s.(collect) k.+1) 
          (s.(visited) `|` [fset z | z in succ y]) 
          (foldl Queue.enqueue s.(queue) 
            [seq (z, k.+1) | z <- undup' (succ y) & z \notin s.(visited)]).
Proof.
rewrite /Hmark_fold.
elim: (succ y) s=> //= h t IH s.
case/boolP: (h \in visited s).
- move=> h_vis /= /IH; rewrite /mark h_vis=> ->.
  congr State.
  + apply/fsetP=> z; rewrite !inE /=.
    by case/boolP: (z == h)=> [/eqP ->|]; rewrite ?h_vis.
  + elim: (undup' t) (queue s)=> //= a l IH2 q.
    case: ifP.
    * move=> a_visF; suff ->: a != h by rewrite /= a_visF /= IH2.
      by move: a_visF; apply/contraNneq=> ->.
    * by move=> a_vis; case: ifP; rewrite //= ?a_vis.
- move=> /negPf h_visF _; rewrite /mark h_visF.
  set s' := {|collect := _; visited := _; queue:= _|}.
  case/boolP: (has (fun z=> z \notin visited s') t).
  + move/IH=> -> /=; congr State; rewrite -?maxnA ?maxnn //.
    * apply/fsetP=> z; rewrite !inE /= !orbA; congr orb; rewrite orbC //.
    * elim: (undup' t) (Queue.enqueue _ _)=> //= a l IH2 q.
      case: ifP; rewrite ?inE ?negb_or; first case/andP=> -> /= -> //=.
      by case: ifP=> //= ? ->.
  + rewrite -all_predC /= => all_t.
    set F := foldl _ _ _; have ->: F = s'.
    * rewrite /F; elim: t all_t {IH F}=> //= a l IH /andP [].
      by rewrite negbK => ->.
    congr State.
    * apply/fsetP=> z; rewrite !inE /= orbC.
      case/boolP: (z \in t); rewrite ?orbF //.
      by move/allP: all_t=> /[apply] /=; rewrite negbK !inE orbC !orbT => ->.
    * set S := [seq _ | _ <- _ & _]; suff ->: S = [::] by [].
      rewrite /S.
      have /=: all (fun z=> z \in h |` visited s) (undup' t) by
        apply/allP=> z; rewrite mem_undup'; move/allP: all_t=> /[apply] /=; rewrite negbK.
      elim: (undup' t)=> //= a l IH2 /andP [+ /IH2 <-].
      rewrite !inE; case/orP=> [/eqP ->|]; rewrite ?eq_refl //=.
      by move=> a_vis; case: ifP=> /=; rewrite ?a_vis /=.
Qed.

Lemma Hmark_foldF s y k:
  ~~ has (fun z=> z \notin s.(visited)) (succ y) ->
  Hmark_fold s y k = s.
Proof.
rewrite /Hmark_fold -all_predC => /allP.
elim: (succ y) s=> //= h t IH s ht_vis.
move: (ht_vis h (mem_head _ _)); rewrite negbK /mark => ->.
by apply/IH=> z zt; apply/ht_vis; rewrite in_cons zt orbT.
Qed.


Lemma Hmark_fold_explored (s : Hstate) y k:
  forall v, edges G y v -> 
  v \in visited (Hmark_fold s y k).
Proof.
move=> v yGv.
case/boolP: (has (fun z=> z \notin s.(visited)) (succ y))=> y_vis.
+ rewrite (Hmark_foldE _ y_vis) /= inE; apply/orP; right.
  rewrite mem_imfset //= succG ?in_succE //.
  by move/edge_vtxl: yGv.
+ rewrite (Hmark_foldF _ y_vis).
  move: y_vis; rewrite -all_predC=> /allP /(_ v).
  rewrite succG ?(edge_vtxl yGv) // in_succE => /(_ yGv) /=.
  by rewrite negbK.
Qed.

Lemma Hmark_fold_queue (s : Hstate) y (k : nat):
  forall rs, Queue.relqueue (queue s) rs ->
  Queue.relqueue (queue (Hmark_fold s y k))
  (rs ++ [seq (z, k.+1) | z <- undup' (succ y) & z \notin visited s]).
Proof.
move=> rs rq_rs.
case/boolP: (has (fun z=> z \notin s.(visited)) (succ y))=> y_vis.
- rewrite (Hmark_foldE _ y_vis) /=.
  set S := [seq _ | _ <- _ & _]; elim/last_ind: S; rewrite ?cats0 //=.
  move=> t h IH; rewrite foldl_rcons -?rcons_cat -IH //=.
  by rewrite /Queue.relqueue /= rev_cons rcons_cat.
- rewrite (Hmark_foldF _ y_vis).
  set S := [seq _ | _ <- _ & _]; suff ->: S = [::] by rewrite cats0.
  rewrite /S; elim: (succ y) y_vis=> //= h t IH.
  rewrite negb_or negbK=> /andP [/[dup] h_vis -> /= /IH] <-.
  elim: (undup' t)=> //= a l IH2. 
  case: ifP=> /=; first by (case: ifP=> //=; rewrite IH2).
  by move/eqP=> ->; rewrite h_vis /=.
Qed.

Lemma Hmark_fold_mem_queue (s : Hstate) y k:
  forall y' k', (y', k') = (y, k) \/ Queue.mem_queue (y', k') (queue (Hmark_fold s y k)) ->
  ((y',k') = (y, k) \/ Queue.mem_queue (y', k') (queue s)) \/ 
  (y',k') \in [seq (z, k.+1) | z <- undup' (succ y) & z \notin visited s].
Proof.
move=> y' k'; case=> [->|]; first by left; left.
case: (Queue.rq_witness s.(queue))=> rs rq_rs.
move: (Hmark_fold_queue y k rq_rs)=> rq_Hmark /(_ _ rq_Hmark).
rewrite mem_cat; case/orP.
- by move=> yk'_rs; left; right => rs'; rewrite /Queue.relqueue rq_rs => <-.
- by right.
Qed.

Lemma Hmark_fold_mem_enqueue s y k y' k':
  Queue.mem_queue (y', k') (queue s) -> 
  Queue.mem_queue (y', k') (queue (Hmark_fold s y k)).
Proof.
case: (Queue.rq_witness (queue s))=> rs rq_rs /(_ _ rq_rs) yk'_rs.
move: (Hmark_fold_queue y k rq_rs)=> rq_Hmark rs'.
by rewrite /Queue.relqueue rq_Hmark => <-; rewrite mem_cat yk'_rs.
Qed.

Lemma Hmark_fold_collect (s : Hstate) y k:
  collect (Hmark_fold s y k) = if [seq z <- succ y | z \notin visited s] is [::] then collect s else maxn (collect s) k.+1.
Proof.
case/boolP: (has (fun z=> z \notin s.(visited)) (succ y))=> y_vis.
- rewrite (Hmark_foldE _ y_vis) /=.
  by move: y_vis; rewrite has_filter; case: [seq _ <- _ | _].
- rewrite (Hmark_foldF _ y_vis).
  by move: y_vis; rewrite has_filter negbK => /eqP ->.
Qed.

Lemma Hmark_fold_visited (s : Hstate) y k:
  visited (Hmark_fold s y k) = visited s `|` [fset z | z in succ y].
Proof.
case/boolP: (has (fun z=> z \notin s.(visited)) (succ y))=> y_vis.
- by rewrite (Hmark_foldE _ y_vis) /=.
- rewrite (Hmark_foldF _ y_vis); apply/esym/fsetUidPl/fsubsetP=> z.
  rewrite mem_imfset //=; move: y_vis; rewrite -all_predC=> /allP /[apply] /=.
  by rewrite negbK.
Qed.

Lemma Hmark_fold_minimal (s : Hstate) y k z:
  inv_step (s, y, k) -> z \in succ y -> z \notin s.(visited) ->
  forall p : epath G, target_shortest p z -> size_path p = k.+1.
Proof.
case=> -[_ x_vis _] edge_syk vis_syk path_syk sort_syk.
move=> yGz z_visF p /target_shortestP [src_p dst_p min_p].
apply/anti_leq/andP; split.
- case: (path_syk y k (or_introl (erefl _)))=> p' [].
  case/target_shortestP=> src_p' dst_p' _ supp_p' size_p'.
  move: yGz; rewrite succG -?dst_p' ?mem_dst // in_succE => p'Gz.
  case: (join_epath_supp supp_p' p'Gz z_visF)=> src_join dst_join /(congr1 seq.size).
  rewrite size_rcons; move: size_p'; rewrite /size_path=> -> <-.
  by apply/min_p; rewrite ?src_p ?src_join ?src_p' ?dst_p ?dst_join.
- move: (x_vis); rewrite /inv_x_vis -src_p=> src_p_vis.
  move: (z_visF); rewrite -dst_p => dst_p_visF.
  apply/(@leq_trans (size_path (frontier_epath p s.(visited)))); 
    last exact/prefix_seq_size/frontier_epath_prefix.
  case: (fp_inP src_p_vis dst_p_visF)=> /= fp_in_vis edge_fp_in.
  case: (frontier_epathP src_p_vis dst_p_visF)=> _ dst_fp.
  rewrite (frontier_epath_size) // ltnS.
  case: (in_frontier_epath_ext p s.(visited))=> dst_in_fp src_in_fp.
  move: (edge_syk _ _ fp_in_vis dst_fp edge_fp_in).
  case.
  + move=> fp_in_eq; case: (path_syk y k (or_introl (erefl _)))=> p'.
    case=> /target_shortestP [src_p' dst_p'] + _ <-.
    by apply; rewrite ?src_p' ?src_in_fp ?src_p ?dst_p' ?dst_in_fp ?fp_in_eq.
  + case=> k'; case: (Queue.rq_witness s.(queue))=> rs rq_rs fp_memq.
    have k'_eq: k' \in [fset k; k.+1].
    * case/(_ _ rq_rs): sort_syk=> l [r] [rs_eq l_all r_all]. 
      move/(_ _ rq_rs): fp_memq=> /(mem_body (y,k)); rewrite rs_eq.
      by rewrite mem_cat; case/orP; 
        [move: l_all|move: r_all]; move=> /allP/[apply]/eqP /= ->; 
        rewrite !inE eq_refl ?orbT.
    case: (path_syk _ _ (or_intror fp_memq))=> p'.
    case=> /target_shortestP [src_p' dst_p' min_p'] _.
    move: k'_eq; rewrite !inE; case/orP=> /eqP ->.
    * by move=> <-; apply/min_p'; rewrite ?src_p' ?src_in_fp ?src_p ?dst_p' ?dst_in_fp.
    * move=> size_p'; apply/ltnW; rewrite -size_p'.
      by apply/min_p'; rewrite ?src_p' ?src_in_fp ?src_p ?dst_p' ?dst_in_fp.
Qed.

Lemma Hmark_fold_inv (s : Hstate) y k:
  inv_step (s, y, k) -> 
  inv_step (Hmark_fold s y k, y, k).
Proof.
case/boolP: (has (fun z=> z \notin s.(visited)) (succ y))=> y_vis;
  last by rewrite (Hmark_foldF _ y_vis).
move=> /[dup] inv_syk [[coll_s x_vis_s vis_vtx_s] edge_syk vis_syk path_syk sort_syk]; split; first split.
- rewrite /inv_collect /= Hmark_fold_collect Hmark_fold_visited.
  set S:= [seq _ <- _ | _].
  have ->: visited s `|` [fset z | z in succ y] = visited s `|` [fset z | z in S] by
    apply/fsetP=> z; rewrite !inE /= mem_filter; case: (z \in visited s).
  case E: S=> [|a l]; rewrite ?fset_nil ?fsetU0 coll_s // -E /S.
  case: (path_syk y k (or_introl (erefl _)))=> py [/target_shortestP [src_py dst_py min_py] supp_py size_py].
  move: (mem_dst py); rewrite dst_py=> y_vtx.
  apply/anti_leq/andP; split; rewrite ?geq_max; first (apply/andP; split).
  + apply/bigmax_leqP=> p /supp_shortestP [? dst_p ?]; apply/(bigmax_sup p)=> //.
    by apply/supp_shortestP; split=> //; rewrite !inE dst_p.
  + move: (mem_head a l); rewrite -E mem_filter => /andP [a_visF a_succ].
    move: (Hmark_fold_minimal inv_syk a_succ a_visF).
    have:= (join_epath_supp supp_py _ a_visF); rewrite -in_succE -succG ?dst_py // a_succ.
    case/(_ isT); rewrite src_py => src_join dst_join walk_join.
    case: (target_shortest_witness src_join dst_join)=> pa /[dup] target_pa /target_shortestP [src_pa dst_pa min_pa].
    move/(_ _ target_pa)=> <-; apply/(bigmax_sup pa)=> //; apply/supp_shortestP; split=> //.
    by rewrite dst_pa !inE /= mem_filter a_succ a_visF orbT.
  + apply/bigmax_leqP=> p /supp_shortestP [src_p + min_p]; rewrite !inE /= mem_filter.
    case/orP.
    * move=> dst_p; rewrite leq_max; apply/orP; left; apply/(bigmax_sup p)=> //.
      by apply/supp_shortestP; split.
    * case/andP=> dst_p_visF dst_p_succ; rewrite leq_max; apply/orP; right.
      rewrite leq_eqVlt; apply/orP; left.
      apply/eqP/(Hmark_fold_minimal inv_syk dst_p_succ dst_p_visF).
      by apply/target_shortestP; split.
- by move: x_vis_s; rewrite /inv_x_vis Hmark_fold_visited inE => ->.
- rewrite /inv_vis_vtx Hmark_fold_visited fsubUset. 
  move: (vis_vtx_s); rewrite /inv_vis_vtx => -> /=. 
  apply/fsubsetP=> z; rewrite !inE /= succG ?in_succE; try exact: edge_vtxr.
  move: (vis_syk y k (or_introl (erefl _))); move/fsubsetP: vis_vtx_s; exact.
- move=> u v; rewrite Hmark_fold_visited !inE negb_or /= => + /andP [v_visF v_succF].
  case/boolP: (u == y)=> [/eqP ->|]; first by left.
  move=> u_n_y; case/boolP: (u \in visited s)=> [/edge_syk /(_ v_visF) + _|].
  + move=> /[apply]; case; first by left. 
    case=> k' /(@Hmark_fold_mem_enqueue _ y k).
    by right; exists k'.
  + move=> u_visF /= u_succ uGv; right; exists k.+1.
    case: (Queue.rq_witness s.(queue))=> rs rq_rs.
    move: (Hmark_fold_queue y k rq_rs)=> rq_Hmark rs'.
    rewrite /Queue.relqueue rq_Hmark => <-; rewrite mem_cat.
    apply/orP; right; apply/mapP; exists u=> //.
    by rewrite mem_filter u_visF mem_undup' u_succ. 
- move=> y' k' /Hmark_fold_mem_queue [/vis_syk|]; rewrite Hmark_fold_visited !inE.
    by move=> ->.
  case/mapP=> y'' /=; rewrite mem_filter mem_undup' => /andP [y''_visF y''_succ [-> _]].
  by rewrite y''_succ orbT.
- move=> y' k' /Hmark_fold_mem_queue [/path_syk|].
    by case=> p [? supp_p ?]; exists p; split=> // z /supp_p; rewrite Hmark_fold_visited !inE => ->.
  case/mapP=> z; rewrite mem_filter mem_undup' => /andP [z_visF z_succ] [-> ->].
  move: (Hmark_fold_minimal inv_syk z_succ z_visF)=> min_by_size.
  case: (path_syk y k); first by left. 
  move=> p_y [/target_shortestP [src_py dst_py _] supp_py size_py]; exists (join_epath p_y z).
  move: (z_succ); rewrite succG -?dst_py ?mem_dst // in_succE => pyGz.
  case: (join_epath_supp supp_py pyGz z_visF)=> src_join dst_join walk_join.
  move/(congr1 seq.size): (walk_join); rewrite /size_path size_rcons.
  move: (size_py); rewrite /size_path => -> size_join.
  split=> //; first by (apply/(target_shortest_by_size min_by_size); rewrite -?src_py).
  move=> w; rewrite src_join walk_join -rcons_cons mem_rcons in_cons Hmark_fold_visited dst_py.
  by case/orP=> [/eqP ->|/supp_py]; rewrite !inE ?z_succ ?orbT //=; move=> ->.
- move=> rs'; case: (Queue.rq_witness s.(queue))=> rs rq_rs.
  move: (Hmark_fold_queue y k rq_rs); rewrite /Queue.relqueue => -> <-.
  set r' := [seq _ | _ <- _ & _].
  case: (sort_syk _ rq_rs)=> l [r] [lr_eq l_k r_Sk]; exists l, (r ++ r').
  split; rewrite ?catA -?lr_eq ?cat_cons // all_cat r_Sk /=.
  by apply/allP=> z /mapP [z' _] -> /=.
Qed.

End HMark.
Section HStep.

Lemma Hdequeue_inv (s : Hstate) y k:
  inv_step (s, y, k) -> 
  (forall v, edges G y v -> v \in s.(visited)) ->
  inv_step_sum 
    match dequeue s with
    |Some st => inl st
    |None => inr s
    end.
Proof.
move=> syk y_expl; rewrite /dequeue.
case: (Queue.rq_witness (queue s))=> rs.
case: rs=> [|[y' k'] t rq_rs].
- move/Queue.rq_dequeue_nil=> -> /=; by case: syk.
- case: syk=> coll_s edge_syk vis_syk paths_syk sort_syk.
  case: (Queue.rq_dequeue_cons rq_rs)=> q' -> /= rq'.
  split=> //.
  + move=> u v /= u_vis v_visF uGv.
    move: (edge_syk _ _ u_vis v_visF uGv).
    case; first by (move=> uy; move: uGv v_visF; rewrite uy => /y_expl ->).
    case=> k'' /(_ _ rq_rs); rewrite !inE.
    case/orP=> [/eqP [-> _]|u_t]; [by left|right].
    by exists k'' => rs'; rewrite /Queue.relqueue rq' => <-.
  + move=> y'' k'' /= yk''_q'; apply: (@vis_syk _ k''); right.
    case: (Queue.mem_queue_cons (y'', k'') rq_rs rq')=> _; exact.
  + move=> y'' k'' /= yk''_q'; apply: paths_syk; right.
    case: (Queue.mem_queue_cons (y'', k'') rq_rs rq')=> _; exact.
  + move=> ? /=; rewrite /Queue.relqueue rq' => <-.
    case: (sort_syk _ rq_rs)=> l [r] [lr_eq /allP l_k /allP r_Sk].
    have head_l: l = (y,k) :: behead l.
    * case: l lr_eq l_k=> /= [r_eq|a l] /=; last case=> -> //.
      move: r_Sk=> /(_ (y,k)); rewrite -r_eq !inE eq_refl /= => /(_ isT).
      by rewrite (ltn_eqF (ltnSn k)).
    move: lr_eq l_k; rewrite head_l /=; case.
    case E: (behead l)=> [|v w].
    * move=> /= r_eq.
      exists r, [::]; split=> //=; rewrite ?cats0 //.
      apply/allP=> z; move: r_Sk; rewrite -r_eq.
      move/[dup]/(_ (y',k') (mem_head _ _))/eqP=> /= ->.
      by move=> /[apply].
    * case=> v_eq t_eq /[dup] vw_in /(_ v).
      rewrite !inE eq_refl orbT -v_eq=> /(_ isT) /= /eqP k'_eq.
      exists (v :: w), r; rewrite ?v_eq ?t_eq ?k'_eq; split=> //; try apply/allP=> //.
      by move=> z z_vw; apply/vw_in; rewrite inE z_vw orbT.
Qed.

Lemma Hstep_inv (s : Hstate) y k:
  inv_step (s,y,k) -> inv_step_sum (HBFS_step (s, y, k) succ).
Proof.
move=> inv_syk; rewrite /HBFS_step /BFS_step.
apply/(@Hdequeue_inv _ y k).
- exact: Hmark_fold_inv.
- exact: Hmark_fold_explored.
Qed.

Lemma Hstep_inv_end (s : Hstate) y k:
  inv_step (s,y,k) ->
  if (HBFS_step (s,y,k) succ) is inr Sr then
  (forall p : epath G, src p = x -> dst p \in visited Sr) else True.
Proof.
move=> inv_syk; rewrite /HBFS_step /param_BFS_step.
case/boolP: (has (fun z => z \notin visited s) (succ y))=> succ_vis.
- have:= (Hmark_foldE k succ_vis); rewrite /Hmark_fold => ->.
  rewrite /dequeue /=.
  case: (Queue.rq_witness (queue s))=> rs rq_rs.
  set F := [seq _ | _ <- _ & _].
  have: Queue.relqueue (foldl Queue.enqueue (queue s) F) (rs ++ F).
  + elim/last_ind: F=> //= [|t h IH]; rewrite ?cats0 //.
    rewrite foldl_rcons -rcons_cat; exact/Queue.rq_enqueue.
  have: rs ++ F != [::].
  + rewrite -size_eq0 size_cat addn_eq0 negb_and size_map. 
    by rewrite !size_eq0 -has_filter -has_undup' succ_vis orbT.
  case: (rs ++ F)=> // a l _ rq_al.
  case: (Queue.rq_dequeue_cons rq_al)=> q' -> _; by case: a {rq_al}.
- have:= (Hmark_foldF k succ_vis); rewrite /Hmark_fold /dequeue => ->.
  move: succ_vis; rewrite -all_predC=> /allP succ_vis.
  case: inv_syk=> -[coll_s x_vis vis_vtx] edge_syk vis_syk path_syk sort_syk.
  case: (Queue.rq_witness (queue s)); case;
    last by (move=> [??] l rq_al; case: (Queue.rq_dequeue_cons rq_al)=> ? ->).
  move=> queue_nil; move: (Queue.rq_dequeue_nil queue_nil)=> ->.
  move=> p src_p; case/boolP: (dst p \in visited s)=> // dst_p.
  move: x_vis; rewrite /inv_x_vis -src_p => src_p_vis.
  case: (fp_inP src_p_vis dst_p)=> fp_vis fp_edge.
  case: (frontier_epathP src_p_vis dst_p)=> _ fp_dst.
  case: (edge_syk _ _ fp_vis fp_dst fp_edge); last by case=> ? /(_ _ queue_nil).
  move=> fp_eq; move: fp_edge; rewrite fp_eq=> /[dup] /edge_vtxl /succG.
  by rewrite -in_succE => <- /succ_vis /=; rewrite fp_dst.
Qed.

End HStep.

Section HIter.

Definition HIter n :=
  iter n
  (oapply (fun y=> HBFS_step y succ)) 
  (inl ((mk x 0), x, 0)).

Lemma HIter_inv n: inv_step_sum (HIter n).
Proof.
elim: n=> /=; first exact: Hmk_step.
move=> n; case: (HIter n)=> //=. 
case=> -[] ???; exact: Hstep_inv.
Qed.

Lemma HIter_nE n: if HIter n is inl Sl then
  let: (s, y, k) := Sl in
  forall rs, Queue.relqueue s.(queue) rs ->
  [/\ uniq (unzip1 rs),
  {subset unzip1 rs <= s.(visited)} &
  n <= #|`[fset y | y in s.(visited) & (y \notin unzip1 rs)]|]
  else True.
Proof.
elim: n=> /= [? <-|n]; rewrite ?leq0n //=.
case: (HIter n)=> //= -[[]] s y k IHn /=.
case: (Queue.rq_witness s.(queue))=> rs rq_rs.
case/boolP: (has (fun z => z \notin visited s) (succ y))=> succ_vis.
- move: (Hmark_fold_queue y k rq_rs).
  rewrite /dequeue /=.
  have: rs ++ [seq (z, k.+1) | z <- undup' (succ y) & z \notin visited s] != [::].
  + rewrite -size_eq0 ?size_cat addn_eq0 size_map !size_eq0. 
    by rewrite negb_and -has_filter -has_undup' succ_vis orbT.
  case E: (rs ++ _)=> [|a l] //.
  case: a E=> y' k' rs_eq _; rewrite /Hmark_fold => rq_al.
  case: (Queue.rq_dequeue_cons rq_al)=> q' -> rq' /= ?.
  rewrite /Queue.relqueue rq' => <-; move: (IHn _ rq_rs).
  rewrite Hmark_fold_visited => -[uniq_rs rs_sub n_leq].
  split.
  + suff: uniq (unzip1 ((y',k') :: l)) by case/andP.
    rewrite -rs_eq /unzip1 map_cat cat_uniq uniq_rs -filter_undup' -map_undup'; first by move=> ?? [].
    rewrite -map_in_undup' ?undup'_uniq ?andbT /=; first by move=> ?? /mapP [? _ ->] /mapP [? _ ->] ->. 
    rewrite -all_predC; apply/allP=> z; rewrite mem_undup' /= => /mapP [z'].
    case/mapP=> z''; rewrite mem_filter => /andP [+ _] -> ->; apply/contra.
    exact: rs_sub.
  + move=> z /(mem_body y'); have ->: y' :: unzip1 l = unzip1 ((y', k') :: l) by [].
    rewrite -rs_eq /unzip1 map_cat mem_cat !inE; case/orP=> [/rs_sub ->|] //.
    case/mapP=> c /mapP [z']; rewrite mem_filter mem_undup' => /andP [_ z'_eq -> ->].
    by rewrite z'_eq orbT.
  + apply/(leq_ltn_trans n_leq)/fproper_ltn_card/fproperP; split.
    * move=> z; rewrite !inE /= => /andP [z_vis z_rsF].
      have: z \notin unzip1 ((y',k') :: l).
      - rewrite -rs_eq /unzip1 map_cat mem_cat negb_or z_rsF /=.
        apply/negP; case/mapP=> -[z' p'] /mapP [z'']; rewrite mem_filter.
        by move=> /[swap] -[<- _] /[swap] /= <-; rewrite z_vis.
      by rewrite negb_or z_vis => /andP [_ ->].
    * case: rs rs_eq rs_sub uniq_rs {rq_rs n_leq}=> /=.
      - rewrite -filter_undup' -map_undup'; first by move=> ?? [].
        move=> /= yk'_l_eq _.
        have /andP [yk'_lF uniq_l]: uniq (unzip1 ((y', k') :: l)) by 
          rewrite -yk'_l_eq /unzip1 -map_in_undup' ?undup'_uniq // => ?? /mapP [? _ ->] /mapP [? _ ->] ->.
        move: (mem_head (y', k') l); rewrite -yk'_l_eq mem_undup'.
        case/mapP=> y''; rewrite mem_filter=> /andP [y''_visF y''_succ] [y''_eq].
        exists y'; rewrite !inE /= ?andbT ?y''_eq ?y''_visF ?y''_succ ?orbT //=.
        apply/negP; rewrite -y''_eq => /mapP [[y_abs k_abs]].
        by move=> /[swap] /= <- /(map_f fst) /=; rewrite (negPf yk'_lF).
      - move=> h t /= [-> l_eq] /(_ y' (mem_head _ _)) y'_vis /andP [yk'_tF uniq_t].
        exists y'; rewrite !inE /= ?negb_and ?negbK ?eq_refl ?orbT // y'_vis /=.
        rewrite -l_eq /unzip1 map_cat mem_cat ?negb_or yk'_tF /=.
        apply/negP=> /mapP [c] /mapP [y''] + -> /=; move=> /[swap] <-.
        by rewrite mem_filter y'_vis.
- have:= (Hmark_foldF k succ_vis); rewrite /Hmark_fold /dequeue => ->.
  case: rs rq_rs=> [rq_nil|[y' k'] l]; first by (move: (Queue.rq_dequeue_nil rq_nil)=> ->).
  move=> rq_al; case: (Queue.rq_dequeue_cons rq_al)=> q' -> rq' /= ?.
  rewrite /Queue.relqueue rq' => <-; case: (IHn _ rq_al)=> /= /andP [y'_lF uniq_l sub_y'l n_leq].
  split=> //; first by (move=> z zl; apply/sub_y'l; rewrite in_cons zl orbT).
  apply/(leq_ltn_trans n_leq)/fproper_ltn_card/fproperP; split.
  + by move=> z; rewrite !inE negb_or=> /and3P /= [-> _ ->]. 
  + exists y'; rewrite !inE /= (sub_y'l y' (mem_head _ _)) ?y'_lF //=.
    by rewrite negbK eq_refl.
Qed.

Lemma HBFS_iterP_ : if HBFS_iter G x succ is inr Sr then True else False.
Proof.
rewrite /HBFS_iter /param_BFS_iter.
move: (HIter_inv #|`vertices G|.+1) (HIter_nE #|`vertices G|.+1).
rewrite /HIter; case: (iter _ _ _)=> //=.
case=> -[s y] k /= [inv_s _ _ _ _].
case: (Queue.rq_witness s.(queue))=> rs rq_rs /(_ _ rq_rs) [_ _].
apply/negP; rewrite ltnNge negbK; apply/fsubset_leq_card/fsubsetP=> z.
by rewrite !inE /= => /andP []; case: inv_s=> _ _ /fsubsetP /[apply].
Qed.

Lemma HBFS_iterP : if HBFS_iter G x succ is inr Sr then
  inv_state Sr /\ forall p: epath G, src p = x -> dst p \in Sr.(visited) else False.
Proof.
move: HBFS_iterP_; rewrite /HBFS_iter /param_BFS_iter.
elim: (#|`vertices G|.+1)=> //= n.
move: (HIter_inv n); rewrite /HIter /HBFS_step.
case: (iter n _ _)=> //= -[[S y] k] inv_syk _.
move: (Hstep_inv_end inv_syk) (Hstep_inv inv_syk); rewrite /HBFS_step.
by case: (param_BFS_step _ _ _).
Qed.

End HIter.

End Proofs.
End BFS.

Section Diameter.

Lemma BFSP x: x \in vertices G -> 
  HBFS G x succ = 
  \max_(p : epath G | is_shortest_epath p && (src p == x)) size_path p.
Proof.
move=> xG; move: (HBFS_iterP xG).
rewrite /HBFS /param_BFS /param_BFS_ /HBFS_iter.
case: param_BFS_iter=> //= s [[coll_s x_vis_s vix_vtx_s] path_s].
rewrite coll_s.
apply/eq_bigl=> p; rewrite /supp_shortest andbA andbC andbA.
apply/andb_idr=> /andP [_ /eqP]; exact: path_s.
Qed.

Lemma HdiameterE : diameter G = Hdiameter_BFS G succ.
Proof.
rewrite /diameter /Hdiameter_BFS big_seq_fsetE /=.
apply/le_anti/andP; split.
- apply/bigmax_leqP=> p sht_p; apply/(bigmax_sup [`mem_src p])=> //.
  rewrite BFSP ?fsvalP //; apply/(bigmax_sup p)=> //=.
  by rewrite sht_p eq_refl.
- apply/bigmax_leqP=> x _; rewrite BFSP ?fsvalP //.
  apply/bigmax_leqP=> p /andP [sht_p] _.
  exact:leq_bigmax_cond.
Qed.

End Diameter.

End DiameterProof.

Section HighBFS.

Definition high_BFS {T : choiceType} (G : graph T) x:=
  HBFS G x (successors G).

Definition high_diameter_BFS {T : choiceType} (G : graph T):=
  Hdiameter_BFS G (successors G).

Lemma high_BFSE {T : choiceType} (G : graph T) x:
  x \in vertices G -> 
  high_BFS G x = eccentricity G x.  
Proof. by move=> xG; rewrite /high_BFS BFSP. Qed.

Lemma high_diameter_BFSE {T : choiceType} (G : graph T):
  high_diameter_BFS G = diameter G.
Proof. by rewrite /high_diameter_BFS -HdiameterE. Qed.

Lemma high_BFS_diameter_le {T : choiceType} (G : graph T) x:
  x \in vertices G ->
  high_BFS G x <= diameter G.
Proof.
move=> xG; rewrite -high_diameter_BFSE /high_BFS /high_diameter_BFS.
rewrite /Hdiameter_BFS big_seq_fsetE /=.
exact/(bigmax_sup [`xG]).
Qed.

End HighBFS.

Section Gisof.
Context {T1 T2 : choiceType} (G1 : graph T1) (G2 : graph T2) (f : T1 -> T2).
Hypothesis G1G2 : gisof G1 G2 f.

Lemma gisof_high_BFSE x : x \in vertices G1 ->
  high_BFS G1 x = high_BFS G2 (f x).
Proof.
case/gisofE: G1G2=> f_inj _ _.
move=> xG1; rewrite !high_BFSE // -?(gisof_vtx G1G2) ?in_imfset //.
apply/anti_leq/andP; split.
- apply/bigmax_leqP=> p /andP [shtt_p /eqP src_p].
  rewrite (size_epath_gisof G1G2).
  apply/leq_bigmax_cond=> /=; apply/andP; split; rewrite ?src_p //.
  rewrite /is_shortest; apply/forallP=> p2.
  case: (gisof_epath_bij p2 G1G2)=> p1 <-.
  apply/implyP=> /= /eqP /f_inj; move/(_ (mem_src _) (mem_src _))=> /eqP src_eq.
  apply/implyP=> /= /eqP /f_inj; move/(_ (mem_dst _) (mem_dst _))=> /eqP dst_eq.
  rewrite -!size_epath_gisof; move/forallP:shtt_p=> /(_ p1).
  by move/implyP=> /(_ src_eq) /implyP /(_ dst_eq).
- apply/bigmax_leqP=> fp; case: (gisof_epath_bij fp G1G2)=> p1 <-.
  case/andP=> shtt_fp /= /eqP /f_inj; move/(_ (mem_src _) xG1)=> src_eq.
  rewrite -size_epath_gisof; apply/leq_bigmax_cond/andP.
  rewrite src_eq eqxx; split=> //.
  apply/forallP=> p; apply/implyP=> /eqP src_p; apply/implyP=> /eqP dst_p.
  move/forallP: shtt_fp=> /(_ (gisof_epath G1G2 p)) /implyP.
  rewrite /= src_p dst_p=> /(_ (eqxx _)) /implyP /(_ (eqxx _)).
  by rewrite -!size_epath_gisof.
Qed.

Lemma gisof_high_diameter : 
  high_diameter_BFS G1 = high_diameter_BFS G2.
Proof.
rewrite /high_diameter_BFS /Hdiameter_BFS -(gisof_vtx G1G2) big_imfset /=.
  by case/gisofE: G1G2.
under eq_big_seq=> /= i iG1. 
  move:(gisof_high_BFSE iG1); rewrite /high_BFS => ->.
over. by [].
Qed.

Lemma gisof_diameter : diameter G1 = diameter G2.
Proof.
rewrite -!high_diameter_BFSE.
exact: gisof_high_diameter.
Qed.

End Gisof.

Section RelGraph.
Section RelStruct.

Lemma rel_struct_BFS g G: rel_structure g G -> forall x, mem_vertex g x->
  BFS g x = high_BFS G x :> nat.
Proof.
move=> gG x xg; rewrite (repr_graph_BFS gG) // /high_BFS !BFSP //; try
  by rewrite -(rel_struct_vtx gG).
move=> j jG; rewrite /succ (rel_struct_succ gG) ?(rel_struct_vtx gG) //.
by move=> ?; rewrite !inE.
Qed.

Lemma rel_struct_diameter: (rel_structure =~> (fun x y=> nat_of_bin x = y))
  diameter_BFS diameter.
Proof.
move=> g G gG.
rewrite (repr_graph_diameter gG) (@HdiameterE _ _ (succ g)) //.
move=> x xG; rewrite /succ (rel_struct_succ gG) ?(rel_struct_vtx gG) //.
by move=> ?; rewrite !inE.
Qed.

End RelStruct.
Section RelGraphR.

Context {t : Type} {T : choiceType} (r : t -> T -> Prop).

Lemma rel_graph_eccentricity gl G:
  rel_spec r eq->
  @rel_graph_r _ _ r gl G -> 
  forall i x, mem_vertex gl.1 i-> x \in vertices G->
  r gl.2.[i] x-> 
  nat_of_bin (BFS gl.1 i) = eccentricity G x.
Proof.
move=> r_eq; case=> G' /[dup] glG' [_ [gG' lL] G'G] i x ig xG ix.
rewrite (rel_struct_BFS gG') // (gisof_high_BFSE G'G) -?(rel_struct_vtx gG') //.
by rewrite -(rel_graph_r_spec r_eq glG' G'G ig xG ix) high_BFSE.
Qed.

Lemma rel_graph_diameter:
  (@rel_graph_r _ _ r =~> (fun x y=> nat_of_bin x = y))
  (fun gl=> diameter_BFS gl.1) diameter.
Proof.
apply/rel_equiv_func; [exact:rel_equiv_refl|exact:rel_comp_eqR|].
apply/(rel_comp_func (g:=(fun x=> diameter x.1))).
- move=> g G [_]; move: rel_struct_diameter=> /rel_couple_func_fst.
  exact.
- move=> ?? gisof_gG; apply/gisof_diameter/gisof_gG.
Qed. 

End RelGraphR.
End RelGraph.

