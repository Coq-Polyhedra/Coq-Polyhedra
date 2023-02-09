(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From Coq Require Import PArray Uint63.
From Polyhedra Require Import extra_misc.
Require Import PArith.BinPos PArith.BinPosDef.
Require Import NArith.BinNat NArith.BinNatDef.
Require Import extra_int.


Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope positive_scope.
Import Order.Theory.

(* -------------------------------------------------------------------- *)

Section MaxLength.

Lemma max_length_lt: (max_length < max_int_)%O.
Proof.
rewrite ltEint /max_int_ /nat_to_int /int_threshold.
rewrite Znat.Nat2Z.inj_pred_max; unlock.
suff ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size by [].
- elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
  by rewrite Zpower.two_power_nat_S => ->.
Qed.

Lemma length_lt_max {T : Type} (a : array T): (length a < max_int_)%O.
Proof.
apply/(le_lt_trans (y:=max_length)); rewrite ?max_length_lt //.
by rewrite leEint leb_length.
Qed.

Lemma lt_length_lt_max {T : Type} (a : array T) i: (i < length a)%O -> (i < max_int_)%O.
Proof. by move/lt_trans; apply; exact/length_lt_max. Qed. 

Lemma int_threshold_length {T : Type} (a : array T) (x : nat): (x < length a)%nat -> x \in gtn int_threshold.
Proof. move=> x_len; rewrite inE; exact/(ltn_trans x_len)/int_thresholdP. Qed.

Lemma length_succ {T : Type} (a : array T):
  (length a).+1 = Uint63.succ (length a).
Proof. by rewrite succ_intE ?length_lt_max. Qed.

Lemma max_length_lt2: ((max_length + max_length)%uint63 < max_int_)%O.
Proof.
rewrite ltEint /max_int_ /nat_to_int /int_threshold.
rewrite Znat.Nat2Z.inj_pred_max; unlock.
suff ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size by [].
- elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
  by rewrite Zpower.two_power_nat_S => ->.
Qed.

Lemma sum_length {T T' : Type} (a : array T) (b : array T'):
  (length a + length b)%nat = (length a + length b)%uint63.
Proof.
rewrite add_intE // inE; apply/(@ltn_trans max_int_)/int_thresholdP.
apply/(@leq_ltn_trans (max_length + max_length)%uint63); last rewrite -ltEint_nat max_length_lt2 //.
rewrite add_intE; last apply/leq_add; rewrite -?leEint_nat ?leEint ?leb_length //.
by apply/wB_natE; rewrite /wB_nat /int_to_nat /wB /max_length; vm_compute.
Qed.


End MaxLength.

Section Misc.

Lemma array_2set_same {T : Type} (a : array T) (i j : int) (x : T):
  a.[i <- x].[j <- x] = a.[j <- x].[i <- x].
Proof.
apply/array_ext; rewrite ?length_set // ?default_set //.
move=> k k_a; case/boolP: (i == k)=> [/eqP ->|/eqP ik].
- rewrite get_set_same ?length_set ?k_a //.
  case/boolP: (j == k)=> [/eqP ->|/eqP jk]; rewrite ?get_set_same ?length_set ?k_a //.
  by rewrite get_set_other // get_set_same ?k_a.
- rewrite [RHS]get_set_other //; case/boolP: (j == k)=> [/eqP ->|/eqP jk].
  + by rewrite !get_set_same ?length_set ?k_a.
  + by rewrite !get_set_other.
Qed.

End Misc.


Module PArrayUtils.

(* -------------------------------------------------------------------- *)
Definition fold {T S : Type} (f : T -> S -> S) (a : array T) (x : S) : S :=
   (IFold.ifold (fun i s => f a.[i] s) (length a) x).

Definition all {T : Type} (p : T -> bool) (a : array T) :=
  (IFold.iall (fun i => p a.[i]) (length a)).

Definition mask_all {T : Type} (p : T -> bool) (ind : array int) (a : array T) :=
  all (fun i => p a.[i]) ind. 

Definition fold_pair {T1 T2 A : Type} (f : T1 -> T2 -> A -> A) (a1 : array T1) (a2 : array T2) (x0 : A) :=
  IFold.ifold (fun i s=> f a1.[i] a2.[i] s) (if (length a1 <? length a2)%uint63 then length a1 else length a2) x0. 

Definition all_pair {T1 T2 : Type} (p : T1 -> T2 -> bool) a1 a2 :=
  IFold.iall (fun i=> p a1.[i] a2.[i]) (if (length a1 <? length a2)%uint63 then length a1 else length a2).

Definition map {T1 T2 : Type} (f : T1 -> T2) (a : array T1):=
  IFold.ifold (fun i acc=> acc.[i <- f a.[i]]) (length a) (make (length a) (f (default a))).

Definition map_mem {T1 T2 : Type} (f : int -> T1 -> T2) (a : array T1):=
  IFold.ifold (fun i acc=> acc.[i <- f i a.[i]]) (length a) (make (length a) (f 0%uint63 (default a))).

Definition is_sorted_rel_ {T : Type} (r : rel T) (a : array T):=
  fold (fun x '(b, t, fst)=> if fst then (true, x, false) else
          if b then (r t x, x, false) else (b, x, false)
        ) a (true, default a, true).

Definition is_sorted_rel {T : Type} (r : rel T) (a : array T):=
  (is_sorted_rel_ r a).1.1.

Definition is_lti_sorted (a : array int) :=
  (is_sorted_rel ltb a).

Definition eq_array_rel {T : Type} (r : rel T) (a b : array T):=
  (length a =? length b)%uint63 &&
  all_pair (fun x y=> r x y) a b.

Definition eq_array_int (a b : array Uint63.int):=
  eq_array_rel eqb a b.

Definition lex_array_rel_ {T : Type} (r : T -> T -> comparison) (a b : array T) :=
  fold_pair 
    (fun x y acc=> if acc is Eq then r x y else acc) a b Eq.

Definition lex_array_rel {T : Type} (r : T -> T -> comparison) (a b : array T):=
  (length a =? length b)%uint63 &&
  let res := lex_array_rel_ r a b
  in if res is Gt then false else true.

Definition ltx_array_rel {T : Type} (r : T -> T -> comparison)(a b : array T) :=
  (length a =? length b)%uint63 &&
  let res := lex_array_rel_ r a b
  in if res is Lt then true else false.

Definition lt_array_int (a b : array int):= ltx_array_rel Uint63.compare a b.

Definition seq_to_arr {T : Type} (d : T) (s : seq T) :=
  IFold.ifold ((fun i acc=> acc.[i <- nth d s i])) (nat_to_int (seq.size s)) (make (nat_to_int (seq.size s)) d).

Definition mk_fun {T : Type} (f : int -> T) (n : int) (x : T):=
  map_mem (fun i _=> f i) (make n x).

Definition array_dot {T : Type} (addf mulf: T -> T -> T) (x0 : T)
  (a b : array T):=
  fold_pair (fun x y res=> addf res (mulf x y)) a b x0.

Definition array_mul_row_mx {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):=
  map (fun c=> array_dot addf mulf x0 v c) M.

Definition array_mulmx {T : Type} addf mulf x0
  (M N : array (array T)):=
  map (fun v=> array_mul_row_mx addf mulf x0 v N) M.

End PArrayUtils.

Section FoldArray.

Definition arr_to_seq {T : Type} (a : array T) :=
  map (fun i => a.[i]) (irange0 (length a)).

Lemma size_arr_to_seq {T : Type} (a : array T) :
  seq.size (arr_to_seq a) = length a.
Proof. by rewrite size_map size_irange0. Qed.

Lemma nth_arr_to_seq {T : Type} (a : array T) n:
  (n < length a)%nat -> nth (default a) (arr_to_seq a) n = a.[nat_to_int n].
Proof. by move=> n_len; rewrite (nth_map 0%uint63) ?size_irange0 // nth_irange0. Qed.

Definition arr_fold {T S : Type} (f : T -> S -> S) (a : array T) (x : S):=
  foldl (fun s t=> f t s) x (arr_to_seq a).

Lemma arr_foldE {T S : Type} (f : T -> S -> S) (a : array T) (x : S):
  PArrayUtils.fold f a x = arr_fold f a x.
Proof.
rewrite /PArrayUtils.fold ifoldE /arr_fold /arr_to_seq /ifold.
elim/last_ind: (irange0 (length a))=> //= h t.
by rewrite map_rcons !foldl_rcons => ->.
Qed.

Definition arr_all {S : Type} (p : S -> bool) (a : array S) :=
  all p (arr_to_seq a). 

Lemma arr_allE {T : Type} a (p : T -> bool):
  PArrayUtils.all p a = arr_all p a.
Proof.
rewrite /arr_all /PArrayUtils.all /IFold.iall ifoldE.
rewrite /ifold /arr_to_seq.
elim/last_ind : (irange0 (length a))=> //= t h IH.
by rewrite foldl_rcons map_rcons all_rcons andbC IH.
Qed.

Definition arr_fold_pair {A T1 T2 : Type} (f : T1 -> T2 -> A -> A) a1 a2 (x0 : A):=
  foldl (fun acc v=> f v.1 v.2 acc) x0 (zip (arr_to_seq a1) (arr_to_seq a2)).

Lemma zip_map_irange {T1 T2 : Type} (a1 : array T1) (a2 : array T2):
  zip (arr_to_seq a1) (arr_to_seq a2) =
  [seq (a1.[i], a2.[i]) | i <- irange0 (if (length a1 <? length a2)%uint63 then length a1 else length a2)].
Proof.
set n := if _ then _ else _.
have size_a12: seq.size (zip (arr_to_seq a1) (arr_to_seq a2)) = n :> nat.
- rewrite /n; case: ifP.
  + rewrite -ltEint ltEint_nat=> len_a12. 
    rewrite size1_zip ?size_arr_to_seq ?size_irange0 //.
    exact/ltnW.
  + rewrite -ltEint ltEint_nat=> len_a21.
    rewrite size2_zip ?size_arr_to_seq ?size_irange0 //.
    by rewrite leqNgt len_a21.
apply/(eq_from_nth (x0:=(default a1, default a2))); rewrite ?size_map ?size_irange0 //.
move=> i; rewrite nth_zip_cond size_a12=> i_n; rewrite i_n /=.
rewrite (nth_map 0%uint63) ?size_irange0 //.
rewrite nth_irange0 // ?nth_arr_to_seq //.
- move: i_n; rewrite /n; case: ifP; rewrite -?ltEint ?ltEint_nat //.
  by move=> h i_a2; apply/(leq_trans i_a2); rewrite leqNgt h.
- move: i_n; rewrite /n; case: ifP; rewrite -?ltEint ?ltEint_nat //.
  move=> h i_a1; apply/(leq_trans i_a1); exact/ltnW.
Qed.


Lemma arr_fold_pairE {A T1 T2 : Type} a1 a2 (f : T1 -> T2 -> A -> A) (x0 : A):
  PArrayUtils.fold_pair f a1 a2 x0 = arr_fold_pair f a1 a2 x0.
Proof.
rewrite /PArrayUtils.fold_pair ifoldE /ifold /arr_fold_pair.
rewrite /arr_to_seq zip_map_irange.
set n := if _ then _ else _.
elim/last_ind: (irange0 n)=> //= t h IH.
by rewrite map_rcons !foldl_rcons /= IH.
Qed.
(* rewrite /PArrayUtils.fold_pair rAS_iter_pair /= N_minE !lengthNE ?leqnn //.
by rewrite take_oversize ?size_zip ?size_arr_to_seq ?leqnn.
Qed. *)

Definition arr_all_pair {T1 T2 : Type} (f : T1 -> T2 -> bool) a1 a2:=
  all (fun x=> f x.1 x.2) (zip (arr_to_seq a1) (arr_to_seq a2)).

Lemma arr_all_pairE {T1 T2 : Type} (f : T1 -> T2 -> bool) a1 a2:
  PArrayUtils.all_pair f a1 a2 = arr_all_pair f a1 a2.
Proof.
rewrite /PArrayUtils.all_pair iallE /arr_all_pair.
rewrite zip_map_irange /iall.
elim/last_ind: (irange0 _)=> //= t h IH.
by rewrite map_rcons !all_rcons /= IH.
Qed.
(* rewrite /PArrayUtils.all_pair rAS_fold_pair.
elim/last_ind: (zip _ _)=> //= t h.
by rewrite foldl_rcons all_rcons andbC => ->.
Qed. *)

Lemma all_arr {T : Type} (p : T -> bool) (a : array T):
  reflect
  (forall i, (i < length a)%O -> p a.[i])
  (arr_all p a).
Proof.
apply/(iffP idP).
- move=> /(all_nthP (default a)); rewrite size_arr_to_seq.
  move=> all_h /= i; rewrite ltEint_nat=> /[dup] ? /all_h.
  by rewrite (nth_map 0%uint63) ?size_irange0 // nth_irange0 // int_to_natK.
- move=> h; apply/(all_nthP (default a))=> i.
  rewrite size_arr_to_seq=> i_len; rewrite nth_arr_to_seq //.
  apply: h; rewrite ltEint_nat nat_to_intK // inE.
  apply/(ltn_trans i_len)/int_thresholdP.
Qed.

Lemma zip_arr_to_seq {T : Type} (a b : array T):
  length a = length b ->
  zip (arr_to_seq a) (arr_to_seq b) = [seq (a.[i], b.[i]) | i <- irange0 (length a)].
Proof.
move=> len_eq.
apply/(@eq_from_nth _ (default a, default b)); rewrite ?size_zip ?size_map ?size_irange0 ?len_eq ?minnn //.
move=> i i_len; rewrite nth_zip ?size_arr_to_seq ?len_eq // !nth_arr_to_seq ?len_eq //.
by rewrite (nth_map 0%uint63) ?size_irange0 // !nth_irange0.
Qed.

Definition arr_mask_all {T : Type} (f : T -> bool) (ind : array int) (a : array T):=
  arr_all (fun i=> f a.[i]) ind.

Lemma arr_mask_allE {T : Type} (f : T -> bool) (ind : array int) (a : array T):
  reflect 
  (forall i, (i < length ind)%O -> f a.[ind.[i]])
  (arr_mask_all f ind a).
Proof.
apply/(iffP idP); rewrite /arr_mask_all.
- by move/all_arr.
- by move=> ?; apply/all_arr.
Qed.

End FoldArray.

Section Seq2Arr.

Definition seq_to_arr {T : Type} (d : T) (s : seq T) :=
  foldl (fun acc i=> acc.[i <- nth d s i]) (make (nat_to_int (seq.size s)) d) (irange0 (nat_to_int (seq.size s))).

Lemma seq_to_arrP {T : Type} (d : T) (s : seq T):
  (seq.size s <= max_length)%nat ->
  (forall k : int, (k < seq.size s)%nat -> 
  (seq_to_arr d s).[k] = nth d s k) /\ seq.size s = length (seq_to_arr d s).
Proof.

move=> s_max.
move: (leqnn (seq.size s)); rewrite /seq_to_arr.
elim: {1 3 5 8}(seq.size s) => [|n IH]. 
- move=> _; split=> //; rewrite irange0_iota; move: (size_iota 0 0)=> /size0nil -> /=.
  rewrite length_make -leEint leEint_nat nat_to_intK ?inE; first exact/(leq_ltn_trans s_max)/int_thresholdP.
  rewrite s_max nat_to_intK // inE; exact/(leq_ltn_trans s_max)/int_thresholdP.
- move=> n_size_s; case: (IH (ltnW n_size_s))=> nth_IH len_IH.
  rewrite irange0_iota !nat_to_intK ?inE; 
    first apply/(leq_ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
  rewrite iotaS_rcons add0n map_rcons foldl_rcons.
  split; first (move=> k /ltnSE; rewrite leq_eqVlt => /orP []).
  + move/eqP => /(congr1 nat_to_int); rewrite int_to_natK => ->.
    rewrite get_set_same //; move: len_IH; rewrite irange0_iota.
    rewrite nat_to_intK ?inE; first exact/(ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
    rewrite -ltEint ltEint_nat => <-; rewrite nat_to_intK // inE.
    exact/(ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
  + move=> k_n; rewrite get_set_other.
      move/(congr1 int_to_nat)=> k_n_eq; move: k_n; rewrite -k_n_eq nat_to_intK ?ltnn // inE.
      exact/(ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
    move: (nth_IH k k_n); rewrite irange0_iota nat_to_intK // inE.
    exact/(ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
  + rewrite length_set; move: len_IH; rewrite irange0_iota nat_to_intK // inE.
    exact/(ltn_trans n_size_s)/(leq_ltn_trans s_max)/int_thresholdP.
Qed.

Lemma seq_to_arrE {T : Type} (d : T) (s : seq T):
  (seq.size s <= max_length)%nat ->
  PArrayUtils.seq_to_arr d s = seq_to_arr d s.
Proof.
move=> s_max; rewrite /PArrayUtils.seq_to_arr.
by rewrite ifoldE.
Qed.

Lemma seq_to_arr_length {T : Type} (d : T) (s : seq T):
  (seq.size s <= max_length)%nat ->
  (seq.size s = length (seq_to_arr d s))%nat.
Proof.
move=> s_max.
by case: (seq_to_arrP d s_max).
Qed.
(* by move=> s_max; case: (seq_to_arr_ d s_max). Qed.  *)

Lemma seq_to_arr_default {T : Type} (d : T) (s : seq T):
  (seq.size s <= max_length)%nat ->
  default (seq_to_arr d s) = d.
Proof.
move=> s_max; rewrite /seq_to_arr.
elim/last_ind: (irange0 _)=> /=; rewrite ?default_make //.
by move=> t h; rewrite foldl_rcons default_set. 
Qed.

Lemma seq_to_arr_nth {T : Type} (d : T) (s : seq T):
  (seq.size s <= max_length)%nat ->
  forall k, (seq_to_arr d s).[k] = nth d s (int_to_nat k).
Proof.
move=> s_max k; move: (leq_total k (seq.size s)).
have s_k_nth: (seq.size s <= k)%nat -> (seq_to_arr d s).[k] = nth d s k.
- move=> h; rewrite get_out_of_bounds ?nth_default //. 
  + by rewrite -ltEint ltEint_nat -seq_to_arr_length // ltnNge h.
  + by rewrite seq_to_arr_default.
case/orP=> //; rewrite leq_eqVlt; case/orP=> [/eqP/esym/eq_leq //|].
by case: (seq_to_arrP d s_max)=> + _; move=> /[apply].
Qed.

End Seq2Arr.


Section MapArray.

Definition arr_map {T T' : Type} (f : T -> T') (a : array T):=
  ifold (fun i acc=> acc.[i <- f a.[i]]) (length a) 
  (make (length a) (f (default a))).

Lemma arr_mapE {T T' : Type} (f : T -> T') (a : array T):
  (PArrayUtils.map f a) = arr_map f a.
Proof. by rewrite /PArrayUtils.map ifoldE. Qed.

Lemma length_arr_map {T T' : Type} (a : array T) (f : T -> T'):
  length (arr_map f a) = length a.
Proof.
rewrite /arr_map /ifold.
elim/last_ind: (irange0 (length a)); rewrite ?length_make ?leb_length //.
by move=> t h; rewrite foldl_rcons length_set.
Qed.

Lemma arr_map_nth {T T' : Type} (a : array T) (f : T -> T'):
  forall k, (arr_map f a).[k] = f (a.[k]).
Proof.
move=> k; rewrite /arr_map /ifold.
case: (leP (length a) k).
- move=> len_a_k; rewrite !get_out_of_bounds -?ltEint ?ltNge ?length_arr_map ?len_a_k //.
  elim/last_ind: (irange0 _)=> /=; rewrite ?default_make //.
  by move=> h t IH; rewrite foldl_rcons default_set IH.
- rewrite irange0_iota ltEint_nat.
  move: (leqnn (length a)).
  elim: {-2}(int_to_nat (length a))=> // n IH; rewrite iotaS_rcons add0n.
  rewrite map_rcons foldl_rcons=> n_len_a; rewrite ltnS leq_eqVlt.
  case/orP.
  + move/eqP=> /(congr1 nat_to_int); rewrite int_to_natK => ->.
    rewrite get_set_same // -ltEint ltEint_nat.
    rewrite nat_to_intK ?inE; first exact/(ltn_trans n_len_a)/int_thresholdP.
    set F := foldl _ _ _; suff ->: length F = length a by [].
    rewrite /F; elim: n {IH n_len_a F}; first by rewrite /= length_make leb_length.
    move=> n IH; rewrite iotaS_rcons add0n map_rcons foldl_rcons.
    by rewrite length_set IH.
  + move=> k_n; move: (IH (ltnW n_len_a) k_n)=> <-.
    apply/get_set_other=> n_k.
    move: (k_n); rewrite -n_k nat_to_intK ?ltnn // inE.
    exact/(ltn_trans n_len_a)/int_thresholdP.
Qed. 

Lemma rAS_map {T T': Type} (a : array T) (f : T -> T'): 
  arr_to_seq (arr_map f a) = map f (arr_to_seq a).
Proof.
rewrite /arr_to_seq -map_comp length_arr_map.
by apply/eq_map=> k /=; rewrite arr_map_nth.
Qed.

Definition arr_map_mem {T1 T2 : Type} (f : int -> T1 -> T2) (a : array T1):=
  ifold (fun i acc=> acc.[i <- f i a.[i]]) (length a) (make (length a) (f 0%uint63 (default a))).

Lemma arr_map_memE {T1 T2 : Type} (f : int -> T1 -> T2) (a : array T1):
  PArrayUtils.map_mem f a = arr_map_mem f a.
Proof. by rewrite /PArrayUtils.map_mem ifoldE. Qed.

Definition arr_mk_fun {T : Type} (f : int -> T) (n : int) (x : T):=
  arr_map_mem (fun i _=> f i) (make n x).
  
Lemma arr_mk_funE {T : Type} (f : int -> T) (n : int) (x : T):
  PArrayUtils.mk_fun f n x = arr_mk_fun f n x.
Proof. by rewrite /PArrayUtils.mk_fun arr_map_memE. Qed.

Lemma length_arr_mk_fun {T : Type} (f : int -> T) (n : int) (x : T):
  (n <= max_length)%O -> length (arr_mk_fun f n x)= n.
Proof.
move=> n_max.
rewrite /arr_mk_fun /arr_map_mem /ifold length_make -leEint n_max.
elim/last_ind: (irange0 n)=> /=; rewrite ?length_make -?leEint ?n_max //.
by move=> t h IH; rewrite foldl_rcons length_set IH.
Qed.

Lemma nth_arr_mk_fun {T : Type} (f : int -> T) (n : int) (x : T):
  (n <= max_length)%O -> forall i, (i < n)%O -> (arr_mk_fun f n x).[i] = f i.
Proof.
move=> n_max i i_n.
rewrite /arr_mk_fun /arr_map_mem /ifold length_make -leEint n_max.
move: i_n; rewrite irange0_iota ltEint_nat.
move: (leqnn (int_to_nat n))=> /[swap].
elim: {-3}(int_to_nat n)=> // k IHk; rewrite iotaS_rcons add0n map_rcons foldl_rcons.
rewrite ltnS leq_eqVlt; case/orP.
- move/eqP=> i_k k_n; rewrite -i_k int_to_natK get_set_same //.
  elim/last_ind: (map _ _)=> /= [|h' t']; rewrite ?foldl_rcons ?length_set //.
  by rewrite length_make -leEint n_max -ltEint ltEint_nat i_k k_n.
- move=> i_k k_n; move: (IHk i_k (ltnW k_n))=> <-.
  rewrite get_set_other // => /(congr1 int_to_nat); rewrite nat_to_intK.
  + rewrite inE; apply/(ltn_trans k_n); move: n_max; rewrite leEint_nat.
    move/leq_ltn_trans; apply; exact/int_thresholdP.
  + by move: i_k=> /[swap] ->; rewrite ltnn.
Qed.

(*case/rat_bigQ_rVP=> len_a a_eq /rat_bigQ_rVP [len_b b_eq].
apply/rat_bigQ_rVP.
have len_add: n = length (bigQ_add_rV a b).
- rewrite /bigQ_add_rV /ifold.
  elim/last_ind: (irange0 _)=> /=; first by rewrite length_make leb_length.
  by move=> t h IH; rewrite foldl_rcons length_set IH.
split=> // i; rewrite mxE /bigQ_add_rV /ifold irange0_iota.
move: (ltn_ord i) (leqnn (int_to_nat (length a))); rewrite {2}len_a.
elim: {-3}(int_to_nat (length _))=> // k IHk.
rewrite iotaS_rcons add0n map_rcons foldl_rcons ltnS leq_eqVlt.
case/orP.
- move/eqP=> i_k _; rewrite -i_k get_set_same ?mxE.
  + apply/eqP/rat_bigQ_add; apply/eqP; [exact:a_eq|exact: b_eq].
  + elim/last_ind: (map _ _)=> /=; last by move=> t h IH; rewrite foldl_rcons length_set IH.
    rewrite length_make leb_length ltin -len_a nat_to_intK ?ltn_ord // inE. 
    apply/(ltn_trans (ltn_ord _)); rewrite len_a; apply/int_thresholdP.
- move=> /[dup] i_k /IHk + k_len; rewrite (ltnW k_len)=> /(_ isT). 
  set F := foldl _ _ _.
  rewrite get_set_other // => /(congr1 int_to_nat).
  rewrite ?nat_to_intK ?inE; try apply/(ltn_trans i_k); 
    try apply/(ltn_trans k_len)/int_thresholdP.
  by move: i_k=> /[swap] ->; rewrite ltnn.
Qed.*)

End MapArray.

Section EqArray.

Definition eq_array_rel {T : Type} (r : rel T) (a b : array T):=
  (length a == length b) && arr_all_pair r a b.

Lemma eq_array_relE {T : Type} (a b : array T) (r : rel T):
  PArrayUtils.eq_array_rel r a b = eq_array_rel r a b.
Proof.
rewrite /PArrayUtils.eq_array_rel /eq_array_rel.
by rewrite eqEint arr_all_pairE.
Qed.

Lemma eq_array_relP {T : Type} (a b : array T) (r : rel T):
  reflect (length a = length b /\ forall i, (i < length a)%O -> r a.[i] b.[i])
  (eq_array_rel r a b).
Proof.
apply/(iffP idP).
- case/andP=> /eqP len_eq; rewrite /arr_all_pair zip_map_irange.
  rewrite len_eq ltin ltnn all_map => /allP h.
  split=> // i i_len; move: (h i); rewrite mem_irangeE le0x i_len /=.
  exact.
- case=> len_eq h; apply/andP; split; rewrite ?len_eq //.
  rewrite /arr_all_pair zip_map_irange len_eq ltin ltnn all_map.
  apply/allP=> i /=; rewrite mem_irangeE le0x /= -len_eq.
  exact: h.
Qed.

(* rewrite /eq_array_rel /arr_all_pair.
apply/(iffP idP).
- case/andP=> /eqb_spec eq_len /(all_nthP (default a, default b)).
  rewrite size_zip !size_arr_to_seq eq_len minnn => h.
  split=> // i; rewrite ltEint_nat => i_len; move: (h _ i_len).
  rewrite nth_zip ?size_arr_to_seq ?eq_len //=.
  by rewrite !nth_arr_to_seq ?eq_len // int_to_natK.
- case=> eq_len h; apply/andP; split; first exact/eqb_spec.
  apply/(all_nthP (default a, default b)) => i.
  rewrite size_zip ?size_arr_to_seq -eq_len minnn => i_len.
  rewrite nth_zip ?size_arr_to_seq ?eq_len //=.
  rewrite !nth_arr_to_seq -?eq_len //; apply/h.
  rewrite ltEint_nat nat_to_intK //.
  exact/(ltn_trans i_len)/int_thresholdP.
Qed. *)

Lemma eq_array_rel_sym {T : Type} (r : rel T):
  symmetric r -> symmetric (eq_array_rel r).
Proof.
move=> sym_r x y; apply/idP/idP.
- case/eq_array_relP=> len_xy h; apply/eq_array_relP.
  rewrite len_xy; split=> // i; rewrite -len_xy=> /h.
  by rewrite sym_r.
- case/eq_array_relP=> len_xy h; apply/eq_array_relP.
  rewrite len_xy; split=> // i; rewrite -len_xy=> /h.
  by rewrite sym_r.
Qed.

Definition eq_array_int (a b : array int) := 
  eq_array_rel (Uint63.eqb) a b.

Lemma eq_array_intP (a b : array Uint63.int):
  reflect 
  (length a = length b /\ forall i, (i < length a)%O -> a.[i] = b.[i])
  (eq_array_int a b).
Proof.
rewrite /eq_array_int.
apply/(iffP (eq_array_relP a b eqb))=> -[-> h]; 
  split=> // i ?; exact/eqb_spec/h.
Qed.

Lemma eq_array_intC: symmetric eq_array_int.
Proof. by apply/eq_array_rel_sym=> x y; rewrite !eqEint eq_sym. Qed.

End EqArray.

Section LexArray.

Definition lex_array_rel_ {T : Type} (r : T -> T -> comparison) (a b : array T) :=
  arr_fold_pair (fun x y acc=> if acc is Eq then r x y else acc) a b Eq.

Lemma lex_array_rel_E {T : Type} (a b : array T) (r : T -> T -> comparison):
  PArrayUtils.lex_array_rel_ r a b = lex_array_rel_ r a b.
Proof. by rewrite /PArrayUtils.lex_array_rel_ arr_fold_pairE. Qed.

Lemma lex_array_rel_Eq {T : Type} (a b : array T) (r : T -> T -> comparison):
  length a = length b -> lex_array_rel_ r a b = Eq ->
  forall i, (i < length a)%O -> r a.[i] b.[i] = Eq.
Proof.
move=> len_eq; rewrite /lex_array_rel_ /arr_fold_pair zip_arr_to_seq //.
rewrite irange0_iota; move=> foldl_h i; rewrite ltEint_nat.
move: (leqnn (int_to_nat (length a))) foldl_h i; move:{1 3 4}(int_to_nat (length a)).
elim=> [|n IHn]; first by move=> _ _ ?.
rewrite iotaS_rcons add0n !map_rcons foldl_rcons /=.
move=> n_len; case E: (foldl _ _ _)=> // r_n_Eq i.
move/ltnSE; rewrite leq_eqVlt; case/orP.
- by move/eqP/(congr1 nat_to_int); rewrite int_to_natK => ->.
- apply/IHn=> //; exact: ltnW.
Qed.
  
Lemma lex_array_rel_Lt {T : Type} (a b : array T) (r : T -> T -> comparison):
  length a = length b -> lex_array_rel_ r a b = Lt ->
  exists (j : int), [/\ (j < length a)%nat, r a.[j] b.[j] = Lt & (forall i, (i < j)%O -> r a.[i] b.[i] = Eq)].
Proof.
move=> len_eq; rewrite /lex_array_rel_ /arr_fold_pair zip_arr_to_seq //.
rewrite irange0_iota; move: (leqnn (int_to_nat (length a))).
move: {1 3 4}(int_to_nat (length a)).
elim=> // n IHn; rewrite iotaS_rcons add0n !map_rcons foldl_rcons.
move=> n_len; case E: (foldl _ _ _)=> //=.
- move=> r_n_Lt; exists (nat_to_int n); split=> //.
  + rewrite nat_to_intK // inE; exact/(ltn_trans n_len)/int_thresholdP.
  + elim: n E n_len {IHn r_n_Lt}; first by (move=> _ _ ?; rewrite ltEint_nat).
    move=> n IHn; rewrite iotaS_rcons add0n !map_rcons foldl_rcons.
    case E: (foldl _ _ _)=> // r_n_Eq n_len i.
    rewrite ltEint_nat nat_to_intK ?inE; first exact/(ltn_trans n_len)/int_thresholdP.
    move/ltnSE; rewrite leq_eqVlt; case/orP.
    * by move/eqP/(congr1 nat_to_int); rewrite int_to_natK => ->.
    * move=> ?; apply/IHn=> //; rewrite ?ltEint_nat ?nat_to_intK // ?inE.
      - exact/(ltn_trans _ n_len).
      - apply/(leq_trans (ltnW n_len))/ltnW/int_thresholdP.
- move=> _; case: (IHn (ltnW n_len) E)=> j [j_n r_j r_i].
  exists j; split=> //; rewrite ltnS; exact: ltnW.
Qed.

Definition ltx_array_rel {T : Type} (a b : array T) r:=
  (length a == length b) && 
  if lex_array_rel_ r a b is Lt then true else false.
  
Lemma ltx_array_relE {T : Type} (a b : array T) r:
  PArrayUtils.ltx_array_rel r a b = ltx_array_rel a b r.
Proof. by rewrite /PArrayUtils.ltx_array_rel eqEint lex_array_rel_E. Qed.

Definition ltx_array_rel_prop {T : Type} (a b : array T)
  (r : T -> T -> comparison):=
  length a = length b /\
    exists j, [/\   (j < length a)%O,
              (forall i, (i < j)%O -> r a.[i] b.[i] = Eq) &
              r a.[j] b.[j] = Lt].

Lemma ltx_array_relP {T : Type} (a b : array T)
  (r : T -> T -> comparison):
  reflect
  (ltx_array_rel_prop a b r)
  (ltx_array_rel a b r).
Proof.
apply/(iffP idP).
- case/andP=> /eqP len_eq.
  case E: (lex_array_rel_ _ _ _)=> //= _.
  case: (lex_array_rel_Lt len_eq E)=> j [j_len r_j r_i_eq].
  split=> //; exists j; rewrite ltEint_nat; split=> //.
- case=> len_eq [j] [j_len r_i_eq r_j].
  rewrite /ltx_array_rel /lex_array_rel_ /arr_fold_pair len_eq.
  apply/andP; split; first exact/eqP.
  set S := zip _ _; rewrite -[S](cat_take_drop j). 
  rewrite (drop_nth (default a, default b)) ?size_zip ?size_arr_to_seq -?len_eq ?minnn -?ltEint_nat //.
  rewrite nth_zip ?size_arr_to_seq ?len_eq // !nth_arr_to_seq -?len_eq -?ltEint_nat //.
  rewrite int_to_natK.
  have take_lt: all (fun x=> if r x.1 x.2 is Eq then true else false) (take j S).
  + apply/(all_nthP (default a, default b))=> i.
    rewrite size_takel ?size_zip ?size_arr_to_seq -?len_eq ?minnn -?leEint_nat; first exact/ltW.
    move=> ij; rewrite nth_take // nth_zip ?size_arr_to_seq ?len_eq //=.
    rewrite !nth_arr_to_seq -?len_eq; try by (apply/(ltn_trans ij); rewrite -?ltEint_nat).
    move: (r_i_eq (nat_to_int i)); rewrite ltEint_nat nat_to_intK ?inE ?ij; try by move=> ->.
    apply/(ltn_trans ij)/(@ltn_trans (length a)); try exact/int_thresholdP.
    by rewrite -ltEint_nat.
  elim: (take j S) take_lt.
  + move=> /= _; rewrite r_j.
    by elim: (drop _ _).
  + move=> h t IH /= /andP [] + /IH.
    by case: (r h.1 h.2).
Qed.

Definition lex_array_rel {T : Type} (r : T -> T -> comparison) (a b : array T):=
  (length a == length b) && if lex_array_rel_ r a b is Gt then false else true.

Lemma lex_array_relE {T : Type} (a b : array T) (r : T -> T -> comparison):
  PArrayUtils.lex_array_rel r a b = lex_array_rel r a b.
Proof. by rewrite /PArrayUtils.lex_array_rel eqEint lex_array_rel_E. Qed.

Lemma lex_arr_eqVlt {T : Type} (a b : array T) (r : T -> T -> comparison):
  lex_array_rel r a b = 
    (eq_array_rel (fun x y => if r x y is Eq then true else false) a b) || 
    ltx_array_rel a b r.
Proof.
apply/idP/idP.
- rewrite /lex_array_rel.
  case/andP=> /eqP len_eq.
  case E: (lex_array_rel_ r a b)=> // _.
  + move: (lex_array_rel_Eq len_eq E)=> all_eq.
    apply/orP; left; apply/eq_array_relP; split=> //.
    by move=> i /all_eq ->.
  + move: (lex_array_rel_Lt len_eq E)=> [j] [j_len r_j_lt r_i_eq].
    apply/orP; right; apply/ltx_array_relP; split=> //.
    by exists j; split=> //; rewrite ltEint_nat.
- case/orP; last first. 
  + rewrite /ltx_array_rel /lex_array_rel.
    by case: (lex_array_rel_ _ _ _)=> //=; rewrite andbF.
  + case/eq_array_relP=> len_eq r_eq; rewrite /lex_array_rel.
    apply/andP; split; first exact/eqP.
    rewrite /lex_array_rel_ /arr_fold_pair.
    set S:= zip _ _.
    have all_S: all (fun x=> if r x.1 x.2 is Eq then true else false) S.
    * apply/(all_nthP (default a, default b))=> i.
      rewrite size_zip !size_arr_to_seq -len_eq minnn => i_len_a.
      rewrite nth_zip ?size_arr_to_seq ?len_eq //=.
      rewrite !nth_arr_to_seq -?len_eq //.
      apply/r_eq; rewrite ltEint_nat nat_to_intK // inE.
      exact/(ltn_trans i_len_a)/int_thresholdP.
    elim/last_ind: S all_S=> //= t h IH.
    rewrite all_rcons foldl_rcons => /andP [+ /IH].
    case: (r h.1 h.2)=> // _.
    by case: (foldl _ _ _).
Qed.

Definition lt_array_int (a b : array int):=
  ltx_array_rel a b Uint63.compare.
  
Lemma lt_array_intE (a b : array int):
  PArrayUtils.lt_array_int a b = lt_array_int a b.
Proof. by rewrite /PArrayUtils.lt_array_int ltx_array_relE. Qed.

Lemma lt_array_int_irr : irreflexive lt_array_int.
Proof.
move=> x; apply/idP/idP; apply/negP=> /ltx_array_relP.
case=> _ [j] [_ _]; rewrite compare_def_spec /compare_def.
by rewrite -ltEint ltxx eqEint eqxx.
Qed.

Lemma lt_array_int_trans : transitive lt_array_int.
Proof.
move=> y x z /ltx_array_relP [len_xy] [j_xy] [j_xy_len r_xy_eq r_xy_lt].
case/ltx_array_relP=> len_yz [j_yz] [j_yz_len r_yz_eq r_yz_lt].
apply/ltx_array_relP; split; rewrite ?len_xy //.
exists (Order.meet j_xy j_yz); split.
- by rewrite ltIx; apply/orP; right.
- move=> i; rewrite ltxI=> /andP [/r_xy_eq + /r_yz_eq].
  rewrite !compare_def_spec /compare_def -ltEint !eqEint.
  by case: ltgtP=> // -> _.
- case: ltgtP.
  + move/r_yz_eq; rewrite compare_def_spec /compare_def -ltEint eqEint.
    by case: ltgtP=> // <- _.
  + move/r_xy_eq; rewrite compare_def_spec /compare_def -ltEint eqEint.
    by case: ltgtP=> // -> _.
  + move=> eq_j; move: r_xy_lt r_yz_lt.
    rewrite !compare_def_spec /compare_def -ltEint !eqEint.
    case: ltgtP=> // + _; rewrite eq_j=> xy_lt.
    by case: ltgtP=> // + _; move/(lt_trans xy_lt)=> ->.
Qed.

Lemma lt_array_int_neq a b: lt_array_int a b -> 
  ~~ eq_array_int a b.
Proof.
move/ltx_array_relP=> [len_eq] [j] [j_len r_eq r_lt].
apply/negP=> /eq_array_intP [_ /(_ j j_len) ab_j].
move: r_lt; rewrite ab_j compare_def_spec /compare_def -ltEint eqEint.
by case: ltgtP=> //; rewrite ltxx.
Qed.

End LexArray.

Section SortArray.

Definition rel_sorted {T : Type} (r : rel T) (a : array T):=
  sorted r (arr_to_seq a).

Definition is_sorted_rel_ {T : Type} (r : rel T) (a : array T):=
  arr_fold 
    (fun x '(b, t, fst)=> if fst then (true, x, false) else
    if b then (r t x, x, false) else (b, x, false)
  ) a (true, default a, true).

Lemma is_sorted_rel_E {T : Type} (a : array T) (r : rel T):
  PArrayUtils.is_sorted_rel_ r a = is_sorted_rel_ r a.
Proof. by rewrite /PArrayUtils.is_sorted_rel_ arr_foldE. Qed. 

Lemma rel_sorted_P {T : Type} (r : rel T) (a : array T): 
  (0 < length a)%O -> 
  is_sorted_rel_ r a = 
  (rel_sorted r a, last (default a) (arr_to_seq a), false).
Proof.
rewrite /is_sorted_rel_ /arr_fold ltEint_nat -size_arr_to_seq.
rewrite /rel_sorted.
elim/last_ind: (arr_to_seq a)=> //= t h IH _.
rewrite foldl_rcons sorted_rcons last_rcons.
elim/last_ind: t IH=> //= tt ht _.
rewrite foldl_rcons !last_rcons !sorted_rcons !size_rcons /=.
rewrite ltn0Sn=> /(_ isT).
case: (foldl _ _ _)=> -[x y z].
case: z; first by case=> <-.
case: x; first by case=> ->; case: ifP=> // ->.
by case=> <-.
Qed.

Definition is_sorted_rel {T : Type} (r : rel T) (a : array T):=
  (is_sorted_rel_ r a).1.1.

Lemma is_sorted_relE {T : Type} (r : rel T) (a : array T):
  PArrayUtils.is_sorted_rel r a = is_sorted_rel r a.
Proof. by rewrite /PArrayUtils.is_sorted_rel is_sorted_rel_E. Qed.

Lemma rel_sortedP {T : Type} (a : array T) (r : rel T):
  is_sorted_rel r a = rel_sorted r a.
Proof.
move: (le0x (length a)); rewrite le_eqVlt; case/orP.
- move/eqP/esym/(congr1 int_to_nat); rewrite -size_arr_to_seq.
  rewrite /is_sorted_rel /is_sorted_rel_ /arr_fold /rel_sorted.
  by move/size0nil=> ->.
- by move/(rel_sorted_P r); rewrite /is_sorted_rel=> ->.
Qed.

Lemma sorted_rel_inj {T : Type} (a : array T) (r : rel T):
  irreflexive r -> transitive r -> rel_sorted r a ->
  forall i j, (i < length a)%O -> (j < length a)%O ->
  a.[i] = a.[j] -> i = j.
Proof.
move=> irr_r trans_r; rewrite /rel_sorted.
move/(sorted_ltn_nth trans_r)=> /(_ (default a)) sort_nth_r.
move=> i j i_len j_len a_ij.
move: (sort_nth_r (int_to_nat i) (int_to_nat j)) (sort_nth_r (int_to_nat j) (int_to_nat i)).
rewrite !inE size_arr_to_seq !nth_arr_to_seq -!ltEint_nat // !int_to_natK i_len j_len.
rewrite a_ij irr_r.
by case: ltgtP=> // [_ /(_ isT isT isT)|_ _ /(_ isT isT isT)].
Qed.

Lemma sorted_rel_inj_rel {T : Type} (a : array T) (r r_eq: rel T):
  transitive r -> (forall x y, r_eq x y -> ~~ r x y /\ ~~ r y x) ->
  rel_sorted r a ->
  forall i j, (i < length a)%O -> (j < length a)%O ->
  r_eq a.[i] a.[j] -> i = j.
Proof.
move=> trans_r irr_rel; rewrite /rel_sorted.
move/(sorted_ltn_nth trans_r)=> /(_ (default a)) sort_nth_r.
move=> i j i_len j_len /irr_rel [r_ij_n r_ji_n].
apply/int_to_nat_inj/eqP/contraT; rewrite neq_ltn.
case/orP=> /sort_nth_r; 
  rewrite !inE !nth_arr_to_seq ?size_arr_to_seq -!ltEint_nat ?i_len ?j_len //.
- by move=> /(_ isT isT); rewrite !int_to_natK (negPf r_ij_n).
- by move=> /(_ isT isT); rewrite !int_to_natK (negPf r_ji_n).
Qed.

Lemma sorted_rel_eq {T : Type} (a : array T) (r : rel T):
  irreflexive r -> transitive r -> rel_sorted r a ->
  forall i j, (i < length a)%O -> (j < length a)%O ->
  r a.[i] a.[j] = (i < j)%O.
Proof.
move=> irr_r trans_r; rewrite /rel_sorted.
move/(sorted_ltn_nth trans_r)=> /(_ (default a)) sort_nth_r.
move=> i j i_len j_len.
move: (sort_nth_r (int_to_nat i) (int_to_nat j)) (sort_nth_r (int_to_nat j) (int_to_nat i)).
rewrite !inE !size_arr_to_seq !nth_arr_to_seq -!ltEint_nat // i_len j_len !int_to_natK.
move/(_ isT isT)=> + /(_ isT isT).
case: ltgtP.
- by move=> _ /(_ isT) ->.
- move=> _ _ /(_ isT) r_a_ji.
  case/boolP: (r a.[i] a.[j])=> // /trans_r /(_ r_a_ji).
  by rewrite irr_r.
- by move=> ->.
Qed.

Lemma sorted_rel_uniq {T : eqType} (a : array T) (r : rel T):
  irreflexive r -> transitive r -> rel_sorted r a -> uniq (arr_to_seq a).
Proof. by move=> ??; apply/sorted_uniq. Qed.

Lemma sorted_rel_equiv {T1 T2 : Type} (a1 : array T1) (a2 : array T2)
  (r1 : rel T1) (r2 : rel T2) (r : T1 -> T2 -> Prop):
  (length a1 = length a2)->
  (forall i, (i < length a1)%O -> r a1.[i] a2.[i])->
  (forall x1 y1 x2 y2, r x1 x2 -> r y1 y2 -> r1 x1 y1 = r2 x2 y2)->
  rel_sorted r1 a1 = rel_sorted r2 a2.
Proof.
(* TODO : Ugly*)
move=> len_eq a12_r r_r12; apply/(@sorted_rel_pair _ _ _ _ _ _ _ (default a1) (default a2)); 
  [exact:r_r12 |rewrite !size_arr_to_seq len_eq //|].
move=> i; rewrite size_arr_to_seq=> i_len; rewrite !nth_arr_to_seq // -?len_eq //.
apply/a12_r; rewrite ltEint_nat; exact/(leq_ltn_trans _ i_len)/(nat_to_int_le i).
Qed.

Section IntSort.

Definition lti_sorted (a : array int) :=
  rel_sorted Order.lt a.

Definition is_lti_sorted (a : array int):=
  is_sorted_rel Uint63.ltb a.

Lemma is_lti_sortedE (a : array int):
  PArrayUtils.is_lti_sorted a = is_lti_sorted a.
Proof. by rewrite /PArrayUtils.is_lti_sorted is_sorted_relE. Qed.

Lemma lti_sortedP (a : array int):
  is_lti_sorted a = lti_sorted a.
Proof. exact: rel_sortedP. Qed.

Lemma lti_sorted_inj (a : array int):
  lti_sorted a ->
  forall i j, (i < length a)%O -> (j < length a)%O ->
  a.[i] = a.[j] -> i = j.
Proof. apply/sorted_rel_inj; [exact: lt_irreflexive|exact: lt_trans]. Qed.

Lemma lti_sorted_eq (a : array int):
  lti_sorted a ->
  forall i j, (i < length a)%O -> (j < length a)%O ->
  (a.[i] < a.[j])%O = (i < j)%O.
Proof. apply/sorted_rel_eq; [exact: lt_irreflexive|exact: lt_trans]. Qed.

Lemma lti_sorted_uniq a:
  lti_sorted a -> uniq (arr_to_seq a).
Proof. apply/sorted_rel_uniq; [exact: lt_irreflexive|exact: lt_trans]. Qed.

End IntSort.
End SortArray.

Section Mulmx.

Definition array_dot {T : Type} (addf mulf: T -> T -> T) (x0 : T)
  (a b : array T):=
  arr_fold_pair (fun x y res=> addf res (mulf x y)) a b x0.

Definition array_mul_row_mx {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):=
  arr_map (fun c=> array_dot addf mulf x0 v c) M.

Definition array_mulmx {T : Type} addf mulf x0
  (M N : array (array T)):=
  arr_map (fun v=> array_mul_row_mx addf mulf x0 v N) M.

Lemma array_dotE {T : Type} addf mulf x0 (a b : array T):
  PArrayUtils.array_dot addf mulf x0 a b =
  array_dot addf mulf x0 a b.
Proof. exact/arr_fold_pairE. Qed.

Lemma array_mul_row_mxE {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):
  PArrayUtils.array_mul_row_mx addf mulf x0 v M =
  array_mul_row_mx addf mulf x0 v M.
Proof.
rewrite /PArrayUtils.array_mul_row_mx arr_mapE.
rewrite /array_mul_row_mx /arr_map /ifold array_dotE.
by apply/eq_foldl=> ??; rewrite array_dotE.
Qed.

Lemma array_mulmxE {T : Type} addf mulf x0
  (M N : array (array T)):
  PArrayUtils.array_mulmx addf mulf x0 M N =
  array_mulmx addf mulf x0 M N.
Proof.
rewrite /PArrayUtils.array_mulmx arr_mapE.
rewrite /array_mulmx /arr_map array_mul_row_mxE.
by apply/eq_foldl=> ??; rewrite array_mul_row_mxE.
Qed.

End Mulmx.
