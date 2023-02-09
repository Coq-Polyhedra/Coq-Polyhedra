(* ------------------------------------------------------------------------------------------------ *)
From Coq      Require Import PArray Uint63.
From mathcomp Require Import all_ssreflect all_algebra finmap.

From Polyhedra Require Import extra_misc vector_order inner_product.
From PolyhedraHirsch Require Import extra_int extra_array graph high_graph.

Require Import NArith.BinNat NArith.BinNatDef.

Import Order.Theory.

(* ------------------------------------------------------------------------------------------------ *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* ------------------------------------------------------------------------------------------------ *)
Section RelFunc.

Definition rel_func {T T' U U' : Type} (r1 : T -> U -> Prop) (r2 : T' -> U' -> Prop)
  (f : T -> T') (g : U -> U') := (forall x y, r1 x y -> r2 (f x) (g y)).

Lemma rel_func_if {t t' T T' : Type} (r : t -> T -> Prop) (r' : t' -> T' -> Prop)
  (b : t -> bool) (B : T -> bool) (f_t f_f : t -> t') (F_t F_f : T -> T'):
  (rel_func r eq) b B ->
  (forall x X, r x X -> b x -> r' (f_t x) (F_t X))->
  (forall x X, r x X -> ~~ b x -> r' (f_f x) (F_f X))->
  (rel_func r r') (fun x=> if b x then f_t x else f_f x) (fun X=> if B X then F_t X else F_f X).
Proof.
move=> bB fF_t fF_f x X xX; rewrite -(bB _ _ xX).
case/boolP: (b x); [exact:fF_t|exact:fF_f].
Qed.
  

End RelFunc.

Notation "R =~> R'" := (rel_func R R') (at level 70, right associativity, format "R  =~>  R'").

Section Composition.

Definition rel_comp {T U V : Type} (r1 : T -> U -> Prop) (r2 : U -> V -> Prop)
  (x : T) (X : V) := exists2 xX : U, r1 x xX & r2 xX X.

Local Notation "R |~ R'" := (rel_comp R R') (at level 65, right associativity, format "R  |~  R'").

Lemma rel_comp_func {T U V T' U' V': Type} 
  (r1 : T -> U -> Prop) (r2 : U -> V -> Prop)
  (r1' : T' -> U' -> Prop) (r2' : U' -> V' -> Prop)
  (f : T -> T') (g : U -> U') (h : V -> V'):
  (r1 =~> r1') f g -> (r2 =~> r2') g h ->
  (r1 |~ r2 =~> r1' |~ r2') f h.
Proof.
move=> r1r1' r2r2' x z [y r1_xy r2_yz].
exists (g y); [exact:r1r1'|exact:r2r2'].
Qed.

Lemma rel_comp_func2 {T U V T' U' V' T'' U'' V'': Type} 
  (r1 : T -> U -> Prop) (r2 : U -> V -> Prop)
  (r1' : T' -> U' -> Prop) (r2' : U' -> V' -> Prop)
  (r1'' : T'' -> U'' -> Prop) (r2'' : U'' -> V'' -> Prop)
  (f : T -> T' -> T'') (g : U -> U' -> U'')
  (h : V -> V' -> V''):
  (r1 =~> r1' =~> r1'') f g -> (r2 =~> r2' =~> r2'') g h ->
  (r1 |~ r2 =~> r1' |~ r2' =~> r1'' |~  r2'') f h. 
Proof. 
move=> fg gh x X [xX r1_x r2_x] y Y [yY r1'_y r2'_y].
exists (g xX yY); [exact/fg|exact/gh].
Qed.

Definition rel_equiv {t T : Type} (r r' : t -> T -> Prop):=
  forall x X, r x X <-> r' x X.

Lemma rel_equiv_refl {t T : Type} (r : t -> T -> Prop):
  rel_equiv r r.
Proof. by []. Qed.

Lemma rel_comp_eqL {t T : Type} (r : t -> T -> Prop):
  rel_equiv r (eq |~ r).
Proof. move=> x y; split; [by move=> ?; exists x|by case=> ? ->]. Qed.

Lemma rel_comp_eqR {t T : Type} (r : t -> T -> Prop):
  rel_equiv r (r |~ eq). 
Proof. move=> x y; split; [by move=> ?; exists y|by case=> ?? <-]. Qed.

Lemma rel_equiv_func {t t' T T' : Type}
  (r1 r2 : t -> T -> Prop) (r1' r2' : t' -> T' -> Prop):
  rel_equiv r1 r2 -> rel_equiv r1' r2' ->
  rel_equiv (r1 =~> r1') (r2 =~> r2').
Proof. by move=> r1r2 r1r2' f F; split; move=> fF x X /r1r2 /fF /r1r2'. Qed.

Lemma rel_equiv_func2 {t t' t'' T T' T'' : Type}
  (r1 r2 : t -> T -> Prop) (r1' r2' : t' -> T' -> Prop)
  (r1'' r2'' : t'' -> T'' -> Prop):
  rel_equiv r1 r2 -> rel_equiv r1' r2' -> rel_equiv r1'' r2'' ->
  rel_equiv (r1 =~> r1' =~> r1'') (r2 =~> r2' =~> r2'').
Proof. move=> ???; apply/rel_equiv_func=> //; exact/rel_equiv_func. Qed.

End Composition.

Notation "R |~ R'" := (rel_comp R R') (at level 70, right associativity, format "R  |~  R'").

Section RelCouple.

Definition rel_couple {t t' T T' : Type} (r : t -> T -> Prop) (r' : t' -> T' -> Prop):=
  fun x X=> r x.1 X.1 /\ r' x.2 X.2.

Lemma rel_couple_func {t1 t2 t1' t2' T1 T2 T1' T2' : Type} 
  (r1 : t1 -> T1 -> Prop) (r1' : t1' -> T1' -> Prop)
  (r2 : t2 -> T2 -> Prop) (r2' : t2' -> T2' -> Prop)
  (f1 : t1 -> t1') (f2 : t2 -> t2') (F1 : T1 -> T1') (F2 : T2 -> T2'):
  (r1 =~> r1') f1 F1 -> (r2 =~> r2') f2 F2 ->
  (rel_couple r1 r2 =~> rel_couple r1' r2') (fun x=> (f1 x.1, f2 x.2)) (fun X=> (F1 X.1, F2 X.2)).
Proof.
move=> fF1 fF2 [x1 x2] [X1 X2] /= [] /= /fF1 ? /fF2 ?.
by split.
Qed.

Lemma rel_couple_func_fst {t1 t2 t1' T1 T2 T1' : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop)
  (r1' : t1' -> T1' -> Prop)
  (f : t1 -> t1') (F : T1 -> T1'):
  (r1 =~> r1') f F ->
  (rel_couple r1 r2 =~> r1') (fun x=> f x.1) (fun X=> F X.1).
Proof. move=> fF x X [? _]; exact/fF. Qed.

Lemma rel_couple_func_snd {t1 t2 t2' T1 T2 T2' : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop)
  (r2' : t2' -> T2' -> Prop)
  (f : t2 -> t2') (F : T2 -> T2'):
  (r2 =~> r2') f F ->
  (rel_couple r1 r2 =~> r2') (fun x=> f x.2) (fun X=> F X.2).
Proof. move=> fF x X [_ ?]; exact/fF. Qed.

Lemma rel_couple_comp {t1 T1 T1' t2 T2 T2' : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop) 
  (r1' : T1 -> T1' -> Prop) (r2' : T2 -> T2' -> Prop):
  forall x Y,
  ((rel_couple r1 r2) |~ (rel_couple r1' r2')) x Y <->
  rel_couple (r1 |~ r1') (r2 |~ r2') x Y.
Proof.
case=> x1 x2 [Y1 Y2]; split.
- case=> -[X1 X2] [/= x1X1 x2X2] [/= X1Y1 X2Y2].
  by split=> /=; [exists X1|exists X2].
- case=> /= -[X1 x1X1 X1Y1] [X2 x2X2 X2Y2].
  by exists (X1,X2); split=> //.
Qed.
End RelCouple.

Section RelArray.

Definition rel_array {t T : Type} (r : t -> T -> Prop) a A := 
  (length a = length A) /\ (forall i, (i < length a)%O -> r a.[i] A.[i]).

Lemma rel_array_length {t T : Type} (r : t -> T -> Prop): (rel_array r =~> eq) length length.
Proof. by move=> ?? []. Qed.

Lemma rel_array_r {t T : Type} (r : t -> T -> Prop) a A:
  rel_array r a A -> (forall i, (i < length a)%O -> r a.[i] A.[i]).
Proof. by case. Qed.

Lemma rel_array_make {t T : Type} (r : t -> T -> Prop) k:
  (r =~> rel_array r) (fun x=> make k x) (fun X=> make k X).
Proof.
move=> x X xX; split; rewrite ?length_make //.
by move=> i _; rewrite !get_make.
Qed.

Lemma rel_array_write {t T : Type} (r : t -> T -> Prop) k x X:
  r x X ->
  (rel_array r =~> rel_array r) (fun a=> set a k x) (fun A=> set A k X).
Proof.
move=> xX a A aA [:len_eq]; split; rewrite ?length_set.
  abstract: len_eq; exact: (rel_array_length aA).
move=> i i_len; case/boolP: (k == i).
- by move/eqP=> ->; rewrite !get_set_same -?ltEint -?len_eq ?i_len.
- move=> k_n_i; rewrite !get_set_other; try exact/eqP.
  exact/(rel_array_r aA).
Qed.

Lemma rel_array_iall {t T : Type} (r : t -> T -> Prop) f :
  (rel_array r =~> eq) (fun a=> iall f (length a)) (fun A=> iall f (length A)).
Proof. by move=> a A aA; rewrite (rel_array_length aA). Qed.

Lemma rel_array_iall_dep {t T : Type} (r : t -> T -> Prop) f F:
  (eq =~> r =~> eq) f F ->
  (rel_array r =~> eq)
    (fun a=> iall (fun i=> f i a.[i]) (length a))
    (fun A=> iall (fun i=> F i A.[i]) (length A)).
Proof.
move=> fF a A aA; rewrite -(rel_array_length aA); apply/eq_in_all.
move=> i; rewrite mem_irangeE le0x /= => i_len.
by apply/fF=> //; apply/(rel_array_r aA).
Qed.

Lemma rel_array_map {t t' T T' : Type}
  (r : t -> T -> Prop) (r' : t' -> T' -> Prop)
  (f : t -> t') (F : T -> T'):
  (r =~> r') f F ->
  (rel_array r =~> rel_array r') (arr_map f) (arr_map F).
Proof.
move=> fF a A aA; split.
- rewrite !length_arr_map; exact/(rel_array_length aA).
- move=> i; rewrite !arr_map_nth length_arr_map => /(rel_array_r aA). 
  exact/fF.
Qed.

Fixpoint rel_seq_r {t T : Type} (r : t -> T -> Prop) (s : seq t) (S : seq T):=
  match s, S with
  |h::q, H::Q => r h H /\ rel_seq_r r q Q
  |[::], [::] => True
  |_, _ => False
  end.

Lemma rel_array_to_seq {t T : Type} (r : t -> T -> Prop):
  (rel_array r =~> (rel_seq_r r)) arr_to_seq arr_to_seq.
Proof.
move=> x X xX.
move: (rel_array_length xX)=> /(congr1 int_to_nat); rewrite -!size_arr_to_seq.
have: (forall k, k < size (arr_to_seq x) -> r (nth (default x) (arr_to_seq x) k) (nth (default X) (arr_to_seq X) k)).
  move=> k; rewrite size_arr_to_seq=> k_len; rewrite !nth_arr_to_seq -?(rel_array_length xX) //.
  apply:rel_array_r=> //; rewrite ltEint_nat; apply/leq_ltn_trans/k_len/nat_to_int_le.
elim: (arr_to_seq x) (arr_to_seq X)=> [|a l IH] [|a' l'] //= nth_al size_l; split.
- apply/(nth_al 0)/ltn0Sn.
- by apply/IH/succn_inj=> // k; rewrite -ltnS=> /nth_al /=.
Qed.

Lemma rel_array_fold_pair {t1 t2 t' T1 T2 T' : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop) (r' : t' -> T' -> Prop)
  (f : t1 -> t2 -> t' -> t') (F : T1 -> T2 -> T' -> T'):
  (r1 =~> r2 =~> r' =~> r') f F ->
  (rel_array r1 =~> rel_array r2 =~> r' =~> r') (arr_fold_pair f) (arr_fold_pair F).
Proof.
move=> fF x X xX y Y yY a A aA.
move: (rel_array_to_seq xX) (rel_array_to_seq yY); rewrite /arr_fold_pair.
elim: (arr_to_seq x) (arr_to_seq X) (arr_to_seq y) (arr_to_seq Y) a A aA=> /= [|xa xl IH].
- by case=> //; case=> [|??]; case.
- case=> // Xa Xl; case=> [|ya yl]; case=> //= Ya Yl a A aA [xXa xXl] [yYa yYl].
  apply/IH=> //; exact/fF.
Qed.

Lemma rel_array_fold_pair_in {t1 t2 t' T1 T2 T' : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop) (r' : t' -> T' -> Prop)
  (f : t1 -> t2 -> t' -> t') (F : T1 -> T2 -> T' -> T')
  a1 A1 a2 A2:
  (length A1 = length A2) ->
  (forall i, (i < length A1)%O -> (r' =~> r') (f a1.[i] a2.[i]) (F A1.[i] A2.[i])) ->
  rel_array r1 a1 A1 -> rel_array r2 a2 A2 -> 
  (r' =~> r') (arr_fold_pair f a1 a2) (arr_fold_pair F A1 A2).
Proof.
move=> len_eq h_in a1A1 a2A2 z Z zZ.
rewrite /arr_fold_pair /arr_to_seq (rel_array_length a1A1) (rel_array_length a2A2).
rewrite -len_eq.
have: forall i, i \in irange0 (length A1) -> 
  (r' =~> r') (f a1.[i] a2.[i]) (F A1.[i] A2.[i]) by 
  move=> i; rewrite mem_irangeE le0x /=; exact:h_in.
elim/last_ind: (irange0 _)=> //= t h IH h_in_IH.
rewrite !map_rcons !zip_rcons ?size_map // !foldl_rcons /=.
apply/h_in_IH; last apply/IH; rewrite ?mem_rcons ?inE ?eqxx //.
by move=> i it; apply/h_in_IH; rewrite mem_rcons inE it orbT.
Qed.


Lemma rel_array_eq {t T : Type} (r : t -> T -> Prop)
  (rel_t : rel t) (rel_T : rel T):
  (r =~> r =~> eq) rel_t rel_T ->
  (rel_array r =~> rel_array r =~> eq) 
    (eq_array_rel rel_t) (eq_array_rel rel_T).
Proof.
move=> tT x X xX y Y yY; rewrite /eq_array_rel /arr_all_pair.
congr andb; rewrite ?(rel_array_length xX) ?(rel_array_length yY) //. 
move: (rel_array_to_seq xX) (rel_array_to_seq yY).
elim: (arr_to_seq x) (arr_to_seq X) (arr_to_seq y) (arr_to_seq Y)=> [|xa xl IH].
- by case=> /= [|Xa Xl]; case=> [|??]; case.
- case=> // Xa Xl [|ya yl] [|Ya Yl] //=.
  case=> ?? [??]; congr andb; [exact:tT|exact:IH].
Qed.

Lemma rel_array_lex {t T : Type} (r : t -> T -> Prop)
  (cmp : t -> t -> comparison) (Cmp : T -> T -> comparison):
  (r =~> r =~> eq) cmp Cmp ->
  (rel_array r =~> rel_array r =~> eq) (lex_array_rel cmp) (lex_array_rel Cmp).
Proof.
move=> cC x X xX y Y yY [: len_eq]; congr andb. 
  abstract : len_eq; rewrite ?(rel_array_length xX) ?(rel_array_length yY) //.
rewrite /lex_array_rel_.
set a := arr_fold_pair _ _ _ _; set A := arr_fold_pair _ _ _ _.
suff ->: a = A by [].
apply:(rel_array_fold_pair)=> //; [|exact:xX|exact:yY].
move=> p P pP q Q qQ c C ->; case: C=> //; exact/cC.
Qed.

Lemma rel_array_arr_mk_fun {t T : Type} (r : t -> T -> Prop) f F n:
  (n <= max_length)%O ->
  (forall i, (i < n)%O -> r (f i) (F i)) ->
  (r =~> rel_array r) (arr_mk_fun f n) (arr_mk_fun F n).
Proof.
move=> n_max fF x X xX; split; rewrite ?length_arr_mk_fun //.
move=> i i_n; rewrite !nth_arr_mk_fun //.
exact/fF.
Qed.

Lemma rel_array_dot {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array r =~> rel_array r =~> r) 
  (array_dot addf mulf x0) (array_dot addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply: rel_array_fold_pair=> //; [|exact:aA|exact:bB].
move=> ?????????; apply/addh=> //; exact/mulh.
Qed.

Lemma rel_array_mul_row_mx {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array r =~> rel_array (rel_array r) =~> rel_array r)
  (array_mul_row_mx addf mulf x0) (array_mul_row_mx addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply: rel_array_map; [|exact:bB].
exact:rel_array_dot.
Qed.

Lemma rel_array_mulmx {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array (rel_array r) =~> rel_array (rel_array r) =~>
  rel_array (rel_array r))
  (array_mulmx addf mulf x0) (array_mulmx addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply:rel_array_map; [|exact:aA].
by move=> ???; apply:rel_array_mul_row_mx.
Qed.

End RelArray.

Section RelSpec.

Definition rel_spec {t T : Type} (r : t -> T -> Prop) (R : T -> T -> Prop) :=
  forall x X Y, r x X -> r x Y -> R Y X.

Lemma rel_spec_couple {t1 t2 T1 T2 : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop)
  (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop):
  rel_spec r1 R1 -> rel_spec r2 R2 ->
  rel_spec (rel_couple r1 r2) (rel_couple R1 R2).
Proof.
move=> rR1 rR2 [a b] [A B] [A' B'] [/= aA bB] [/= aA' bB'].
split; [exact:(rR1 _ _ _ aA aA')|exact:(rR2 _ _ _ bB bB')].
Qed.

Lemma rel_spec_comp {t T TT : Type} 
  (r : t -> T -> Prop) (R : T -> TT -> Prop)
  (eq_T : T -> T -> Prop) (eq_TT : TT -> TT -> Prop):
  rel_spec r eq_T -> rel_spec R eq_TT ->
  (forall X Y Z, eq_T Y X -> R X Z -> R Y Z)->
  rel_spec (r |~ R) eq_TT.
Proof.
move=> rT RTT eq_h x XX YY [X xX XXX] [Y xY YYY].
by move: (rT _ _ _ xX xY)=> /eq_h/(_ XXX)/RTT; apply.
Qed.

Lemma rel_spec_array {t T : Type}
  (r : t -> T -> Prop) (eq_T : T -> T -> Prop):
  rel_spec r eq_T ->
  rel_spec (rel_array r) 
    (fun a b=> (length a = length b) /\ 
      (forall i, (i < length a)%O -> eq_T a.[i] b.[i])).
Proof.
move=> r_spec a A B aA aB; split; 
  rewrite -?(rel_array_length aA) -?(rel_array_length aB) //.
move=> i i_len; move: (rel_array_r aA i_len) (rel_array_r aB i_len).
apply/r_spec.
Qed.

End RelSpec.
(* ------------------------------------------------------------------------------------------------ *)

Section RelInt.

Definition rel_int (i : Uint63.int) (n : nat):= n = i.
Definition rel_int_ord {m : nat} (i : Uint63.int) (n : 'I_m.+1) := rel_int i (val n).

Lemma rel_int_eq: (rel_int =~> rel_int =~> eq)
  (@eq_op _) (@eq_op _).
Proof.
move=> x X xX y Y yY; apply/idP/idP.
- by move/eqP/(congr1 int_to_nat); rewrite xX yY => ->; rewrite eqxx.
- by rewrite xX yY=> /eqP /int_to_nat_inj ->.
Qed.

Lemma rel_int_ord_lt (m : nat):
  (@rel_int_ord m =~> @rel_int_ord m =~> eq)
    (fun i j=> (i < j)%O) (fun I J=> (I < J)%nat).
Proof. by move=> x X xX y Y yY; rewrite xX yY ltEint_nat. Qed.

End RelInt.

Section ArraySet.

Context {T : finType}.

Definition rel_array_set (lt_T : rel T) (a : array T) (s : {set T}):= 
  rel_sorted lt_T a /\ s = [set a.[i] | i in irange0 (length a)].

Context (lt_T : rel T).

Lemma rel_array_set_iall f F a A:
  (forall i, (i < length a)%O -> f i = F a.[i])->
  rel_array_set lt_T a A -> 
  (iall f (length a)) = [forall i, (i \in A) ==> F i].
Proof.
move=> fF aA; apply/idP/idP.
- move/allP=> h; apply/forallP=> k; apply/implyP.
  case: aA=> _ ->; case/imsetP=> i; rewrite mem_irangeE le0x /=.
  move=> /[dup] /fF + + ->; move=> <- ?; apply/h.
  by rewrite mem_irangeE le0x.
- move/forallP=> h; apply/allP=> i; rewrite mem_irangeE le0x /=.
  move=> i_len; rewrite (fF _ i_len).
  move: h=> /(_ a.[i])/implyP; apply.
  by case: aA=> _ ->; apply/imset_f; rewrite mem_irangeE le0x /=.
Qed.

Hypothesis irr_lt_T : irreflexive lt_T.
Hypothesis tra_lt_T : transitive lt_T.

Lemma rel_array_set_length: 
  (rel_array_set lt_T =~> rel_int)
  length (fun A => #|A|).
Proof.
move=> a A [std_a ->]; rewrite card_in_imset.
- move=> i j; rewrite !mem_irangeE !le0x /=; exact/sorted_rel_inj/std_a.
- move/card_uniqP: (uniq_irange 0%uint63 (length a))=> ->.
  by rewrite size_irange subn0.
Qed.

Lemma rel_array_set_eq:
  (rel_array_set lt_T =~> rel_array_set lt_T =~> eq)
  (eq_array_rel (@eq_op _)) (@eq_op _).
Proof.
move=> a A aA b B bB; apply/idP/idP.
- case/eq_array_relP=> len_ab ab_eq; apply/eqP/setP=> i.
  case: aA=> _ ->; case: bB=> _ ->; rewrite -len_ab.
  apply/idP/idP; case/imsetP=> j; rewrite mem_irangeE le0x /= => j_len ->.
  + move/ab_eq: (j_len)=> /eqP ->; apply/imsetP; exists j=> //.
    by rewrite mem_irangeE le0x.
  + move/ab_eq: (j_len)=> /eqP <-; apply/imsetP; exists j=> //.
    by rewrite mem_irangeE le0x.
- move/eqP=> AB [:len_ab]; rewrite /eq_array_rel; apply/andP; split.
  + abstract:len_ab; apply/eqP/int_to_nat_inj.
    by rewrite -(rel_array_set_length aA) -(rel_array_set_length bB) AB.
  + rewrite /arr_all_pair.
    suff ->: (arr_to_seq a) = (arr_to_seq b) by
      elim: (arr_to_seq _)=> //= h t; rewrite eqxx.
    apply/irr_sorted_eq; [exact:tra_lt_T|exact:irr_lt_T|by case: aA|by case: bB| ].
    move=> x; case: aA bB=> _ /setP /(_ x) + [_ /setP/(_ x)].
    rewrite AB=> -> eq_h; apply/idP/idP.
    * case/mapP=> k k_mem x_eq; move: eq_h; rewrite x_eq imset_f //.
      by move/esym=> /imsetP [k'] ? ->; apply/map_f.
    * case/mapP=> k k_mem x_eq; move: eq_h; rewrite x_eq imset_f //.
      by move=> /imsetP [k'] ? ->; apply/map_f.
Qed.
    
End ArraySet.

Section ArrSetRel.

Context {t : Type} (T : finType) (r : t -> T -> Prop).
Context {lt_T : rel T}.

Definition rel_arr_set_r:= 
  (rel_array r) |~ (@rel_array_set _ lt_T).

Lemma rel_arr_set_r_spec:
  rel_spec r eq->
  rel_spec rel_arr_set_r eq.
Proof.
move=> r_spec; apply:rel_spec_comp; first apply:(rel_spec_array r_spec).
- by move=> x X Y [_ ->] [_ ->].
- move=> x y Z [len_xy nth_xy] [st_x ->]; split.
  + rewrite (sorted_rel_equiv len_xy nth_xy (r2:=lt_T)) //.
    by move=> ???? -> ->.
  + rewrite -len_xy; apply/setP=> z; apply/idP/idP.
    * case/imsetP=> i; rewrite ?mem_irangeE ?le0x /= => ? ->. 
      apply/imsetP; exists i; rewrite ?mem_irangeE ?le0x //.
      exact/esym/nth_xy.
    * case/imsetP=> i; rewrite ?mem_irangeE ?le0x /= => ? ->. 
      apply/imsetP; exists i; rewrite ?mem_irangeE ?le0x //.
      exact/nth_xy.
Qed.

Lemma rel_arr_set_r_iall f F a A:
  (forall i V, (i < length a)%O -> r a.[i] V -> f i = F V) ->
  rel_arr_set_r a A -> 
  iall f (length a) = [forall x, (x \in A) ==> F x].
Proof.
move=> fF aA.
case: aA=> a' aa' a'A; rewrite (rel_array_iall _ aa').
apply/(rel_array_set_iall _ a'A)=> i i_len; apply/fF.
- by rewrite (rel_array_length aa').
- by apply/(rel_array_r aa'); rewrite (rel_array_length aa').
Qed.

Hypothesis irr_lt_T : irreflexive lt_T.
Hypothesis tr_lt_T : transitive lt_T.

Lemma rel_arr_set_r_length:
  (rel_arr_set_r =~> rel_int) length (fun A=> #|A|).
Proof.
apply/rel_equiv_func; [exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func; [exact:rel_array_length|exact:rel_array_set_length].
Qed.

Lemma rel_arr_set_r_eq eqt:
  (r =~> r =~> eq) eqt (@eq_op _)->
  (rel_arr_set_r =~> rel_arr_set_r =~> eq) (eq_array_rel eqt) (@eq_op _).
Proof.
move=> r_eq; apply/rel_equiv_func2; 
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply:rel_comp_func2; [|exact:rel_array_set_eq].
exact/rel_array_eq.
Qed.

End ArrSetRel.

(* ------------------------------------------------------------------------------------------------ *)

Section Vector.

Context {R : realFieldType}.

Definition rel_cV (n : nat) (a : array R) (A : 'cV[R]_(n.+1)):=
  (n.+1 = length a) /\ (forall i : 'I_(n.+1), a.[nat_to_int i] = A i ord0).

Definition rel_rV (n : nat) (a : array R) (A : 'rV[R]_n.+1):=
  rel_cV a A^T.

Lemma rel_cV_length (n : nat) a A:
  @rel_cV n a A -> n.+1 = length a.
Proof. by case. Qed.

Lemma rel_cV_nth (n : nat) a A:
  @rel_cV n a A -> (forall i : 'I_n.+1, a.[nat_to_int i] = A i ord0).
Proof. by case. Qed.

Lemma rel_rV_nth (n : nat) a A:
  @rel_rV n a A -> (forall i : 'I_n.+1, a.[nat_to_int i] = A ord0 i).
Proof. by move/rel_cV_nth=> h i; rewrite h mxE. Qed.

Lemma rel_cV_tr (n : nat):
  (@rel_cV n =~> @rel_rV n) id trmx.
Proof. by move=> a A aA; rewrite /rel_rV trmxK. Qed.

Lemma rel_rV_tr (n : nat):
  (@rel_rV n =~> @rel_cV n) id trmx.
Proof. by []. Qed. 

Lemma rel_cV_inj (n : nat):
  (@rel_cV n =~> @rel_cV n =~> eq) 
    (eq_array_rel (@eq_op _)) (@eq_op _).
Proof.
move=> a A aA b B bB; apply/idP/idP.
- case/eq_array_relP=> len_ab ab_i; apply/eqP/matrixP=> i j.
  rewrite (ord1_eq0 j); move: (ab_i (nat_to_int i)).
  rewrite ltEint_nat -(rel_cV_length aA) nat_to_intK; 
    first by (apply/(@int_threshold_length _ a); rewrite -(rel_cV_length aA)).
  by move/(_ (ltn_ord _))/eqP; rewrite (rel_cV_nth aA) (rel_cV_nth bB).
- move/eqP/matrixP=> AB; apply/eq_array_relP; split.
    by apply/int_to_nat_inj; rewrite -(rel_cV_length aA) -(rel_cV_length bB).
  move=> i; rewrite ltEint_nat -(rel_cV_length aA)=> i_n.
  move: (rel_cV_nth aA (Ordinal i_n)) (rel_cV_nth bB (Ordinal i_n)).
  rewrite int_to_natK => -> ->; exact/eqP/AB.
Qed.

Lemma rel_rV_inj (n : nat):
  (@rel_rV n =~> @rel_rV n =~> eq)
    (eq_array_rel (@eq_op _)) (@eq_op _).
Proof.
move=> a A /= /rel_rV_tr + b B /rel_rV_tr.
move/rel_cV_inj=> /[apply] ->; apply/idP/idP; 
  [by move/eqP=> /trmx_inj ->|by move/eqP=> ->].
Qed.

Lemma rel_cV_scal (n : nat) (L : R):
  (@rel_cV n =~> @rel_cV n) (arr_map (fun x=> (L * x)%R)) (fun X=> (L *: X)%R).
Proof.
move=> a A aA; split; [by rewrite length_arr_map (rel_cV_length aA)| ].
by move=> i; rewrite arr_map_nth mxE (rel_cV_nth aA).
Qed.

Lemma rel_cV_big (n : nat) (f : R -> R -> R):
  (@rel_cV n =~> @rel_cV n =~> eq) 
    (fun x y=> arr_fold_pair (fun elx ely a=> (a + (f elx ely))%R) x y 0%R) 
    (fun X Y=> \big[+%R/0%R]_(i : 'I_n.+1) (f (X i ord0) (Y i ord0))).
Proof.
move=> x X xX y Y yY; rewrite /arr_fold_pair zip_arr_to_seq.
  by apply/int_to_nat_inj; rewrite -(rel_cV_length xX) -(rel_cV_length yY).
rewrite irange0_iota -(rel_cV_length xX).
under eq_bigr=> i _ do rewrite -(rel_cV_nth xX i) -(rel_cV_nth yY i) /=.
rewrite [RHS]/= -(big_mkord (fun _ => true) (fun i : nat => f x.[nat_to_int i] y.[nat_to_int i])). 
rewrite /index_iota subn0.
elim: {1 2}n=> [|k Hk]; first by rewrite /= big_seq1 GRing.add0r.
by rewrite iotaS_rcons add0n !map_rcons foldl_rcons Hk big_rcons.
Qed.

Lemma rel_cV_dot (n : nat):
  (@rel_cV n =~> @rel_cV n =~> eq)
  (fun x y=> array_dot +%R *%R 0%R x y)
  (fun X Y=> vdot X Y).
Proof. exact/rel_cV_big. Qed.

Lemma rel_rV_lex (n : nat) (cmp : R -> R -> comparison):
  (forall x y, CompSpec (@eq R) (@Order.lt _ R) x y (cmp x y))->
  (@rel_rV n =~> @rel_rV n =~> eq)
  (lex_array_rel cmp) (fun x y=> (x <=lex y)%R).
Proof.
move=> cmpP x X xX y Y yY; rewrite /lex_array_rel.
have len_eq: (length x = length y) by
  apply/int_to_nat_inj; rewrite -(rel_cV_length xX) -(rel_cV_length yY).
rewrite len_eq eqxx /= /lex_array_rel_ lex_foo.
under eq_map=> i do rewrite -(rel_rV_nth xX).
under [X in ind_lexleq _ X]eq_map=> i do rewrite -(rel_rV_nth yY).
rewrite /arr_fold_pair zip_arr_to_seq // irange0_iota -(rel_cV_length xX).
rewrite -map_comp map_enum_ord_iota /=.
elim: (enum 'I_n.+1)=> [|a l IH] //=.
case: cmpP=> [->|->|]; 
    [rewrite eqxx ltxx; exact/IH |by elim: l {IH}|].
rewrite ltNge le_eqVlt negb_or=> /andP [/negPf -> /negPf ->].
by elim: l {IH}.
Qed.

End Vector.

Section Matrix.

Context {R : realFieldType}.

Definition rel_mx_col (m n : nat) (a : array (array R)) (A : 'M[R]_(m.+1,n.+1)):=
  (n.+1 = length a) /\ (forall i : 'I_n.+1, rel_cV a.[nat_to_int i] (col i A)).

Definition rel_mx_row (m n : nat) (a : array (array R)) (A : 'M[R]_(m.+1,n.+1)):=
  (m.+1 = length a) /\ (forall i : 'I_m.+1, rel_rV a.[nat_to_int i] (row i A)).

Lemma rel_mx_col_length (m n : nat):
  (@rel_mx_col m n =~> rel_int) (length) (fun A=> n.+1).
Proof. by move=> a A; case. Qed.

Lemma rel_mx_col_nth (m n : nat) a A:
  @rel_mx_col m n a A -> forall i : 'I_n.+1, rel_cV a.[nat_to_int i] (col i A).
Proof. by case. Qed.

Lemma rel_mx_row_nth (m n : nat) a A:
  @rel_mx_row m n a A -> forall i : 'I_m.+1, rel_rV a.[nat_to_int i] (row i A).
Proof. by case. Qed.

Lemma rel_mx_row_length (m n : nat):
  (@rel_mx_row m n =~> rel_int) (length) (fun A=> m.+1).
Proof. by move=> a A; case. Qed.

Lemma rel_mx_row_length_row (m n : nat):
  (@rel_mx_row m n =~> rel_int) (fun x=> length x.[0%uint63]) (fun A=> n.+1).
Proof. by move=> a A [_ /(_ ord0)] /rel_cV_length ->. Qed.

Lemma rel_mx_row_length_row_i (m n : nat) a A:
  @rel_mx_row m n a A -> forall i, (i < length a)%O ->
  n.+1 = length a.[i].
Proof.
move=> aA i; rewrite ltEint_nat -(rel_mx_row_length aA)=> i_m.
move: (rel_mx_row_nth aA (Ordinal i_m))=> /rel_cV_length ->.
by rewrite int_to_natK.
Qed.

Lemma rel_mx_col_map (m n : nat) (f : array R -> R) (F : 'cV[R]_m.+1 -> R):
  (@rel_cV R m =~> eq) f F ->
  (@rel_mx_col m n =~> @rel_rV R n) 
  (fun x=> arr_map f x) (fun X=> ((\col_(i < n.+1) F (col i X))^T)%R).
Proof.
move=> fF x X xX; split; rewrite ?length_arr_map; first exact/(rel_mx_col_length xX).
move=> i; rewrite !mxE arr_map_nth; exact/fF/rel_mx_col_nth.
Qed.

Lemma rel_mx_row_bigsum (m n : nat) f F add_arr:
  (eq =~> @rel_rV R n =~> @rel_rV R n) f F ->
  (@rel_rV R n =~> @rel_rV R n =~> @rel_rV R n) add_arr (fun X Y=> (X + Y)%R) ->
  (@rel_rV R m =~> @rel_mx_row m n =~> @rel_rV R n) 
  (fun v a=> arr_fold_pair (fun vi ai acc=> add_arr acc (f vi ai)) v a (make (length a.[0%uint63]) 0%R))
  (fun V A=> \big[+%R/0%R]_i F (V ord0 i) (row i A)).
Proof.
move=> fF addAdd v V vV a A aA.
rewrite /arr_fold_pair /arr_to_seq !irange0_iota.
rewrite -(rel_cV_length vV) -(rel_mx_row_length aA).
under eq_bigl=> x.
- move: (ltn_ord x) => <-; move: (mem_iota 0 m.+1 x).
  rewrite leq0n add0n [RHS]/= => <-.
  over.
move/mem_subseq: (subseq_refl (iota 0 m.+1)).
move: (iota_uniq 0 m.+1).
elim/last_ind: {-3}(iota _ _). 
- move=> _ _ /=; under eq_bigl=> x do rewrite inE; rewrite big_pred0_eq.
  split; rewrite ?length_make ?leb_length ?(rel_mx_row_length_row aA) //.
  by move=> i; rewrite get_make !mxE.
- move=> t h IH; rewrite rcons_uniq.
  case/andP=> h_n_t uniq_t ht_iota; move: (ht_iota)=> /(_ h).
  rewrite mem_rcons inE eqxx=> /(_ isT); rewrite mem_iota leq0n add0n /= => h_m.
  rewrite (bigD1 (Ordinal h_m))=> /=; rewrite ?mem_rcons ?in_cons ?eqxx //=.
  rewrite !map_rcons !zip_rcons ?size_map // foldl_rcons /=.
  rewrite GRing.addrC.
  have rule: forall i : 'I_m.+1, (val i \in rcons t h) && (i != Ordinal h_m) = (val i \in t).
  + move=> i; rewrite mem_rcons inE.
    case/boolP: (i == Ordinal h_m)=> [/eqP -> /=|]; 
      rewrite ?eqxx /= ?(negPf h_n_t) //.
    rewrite andbT=> /eqP i_n_h; apply/orb_idl=> /eqP ih.
    by case: i_n_h; apply/val_inj.
  under eq_bigl => x do rewrite rule /=.
  apply/addAdd=> //; first apply/IH=> //;
    [by move=> x xt; apply/ht_iota; rewrite mem_rcons inE xt orbT|].
  apply/fF; first by move: (rel_rV_nth vV (Ordinal h_m)).
  by move: (rel_mx_row_nth aA (Ordinal h_m)).
Qed.

Lemma rel_mx_row_mul (m n : nat):
  (@rel_rV R m =~> @rel_mx_col m n =~> @rel_rV R n) 
    (fun v a=> array_mul_row_mx +%R *%R 0%R v a)
    (fun V A=> (V *m A)%R).
Proof.
move=> v V vV a A aA; split.
- by rewrite length_arr_map; case: aA.
- move=> i; rewrite mxE -matrix_vdot row_id arr_map_nth.
  by apply/rel_cV_dot=> //; case: aA=> _ /(_ i).
Qed.

Lemma rel_mulmx (m n k : nat):
  (@rel_mx_row m n =~> @rel_mx_col n k =~> @rel_mx_row m k) 
  (fun a b=> array_mulmx +%R *%R 0%R a b)
  (fun A B=> (A *m B)%R).
Proof.
move=> a A aA b B bB; split.
- by rewrite length_arr_map; case: aA.
- move=> i; rewrite arr_map_nth row_mul.
  by apply/rel_mx_row_mul=> //; case: aA=> _ /(_ i).
Qed.

End Matrix.

Section PointRel.

Context {t : Type} {R : realFieldType}.
Context (r : t -> R -> Prop).

Definition rel_point_cV (n : nat) := rel_array r |~ @rel_cV R n.
Definition rel_point_rV (n : nat) := rel_array r |~ @rel_rV R n.

Lemma rel_point_rV_tr (n : nat):
  (@rel_point_cV n =~> @rel_point_rV n) id (fun X => (X^T)%R).
Proof. apply/(rel_comp_func (g:=id))=> //; exact: rel_cV_tr. Qed.

Lemma rel_point_rV_eq (n : nat) (eq_t : rel t):
  (r =~> r =~> eq) eq_t (@eq_op _) ->
  (@rel_point_rV n =~> @rel_point_rV n =~> eq)
    (eq_array_rel eq_t) (@eq_op _).
Proof.
move=> r_eq; apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func2; [apply/rel_array_eq/r_eq|exact:rel_rV_inj].
Qed.

Lemma rel_point_cV_eq (n : nat) (eq_t : rel t):
  (r =~> r =~> eq) eq_t (@eq_op _) ->
  (@rel_point_cV n =~> @rel_point_cV n =~> eq)
    (eq_array_rel eq_t) (@eq_op _).
Proof.
move=> r_eq; apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func2; [apply/rel_array_eq/r_eq|exact:rel_cV_inj].
Qed.


Lemma rel_point_cV_scal (n : nat) (mul_t : t -> t -> t):
  (r =~> r =~> r) mul_t (fun x y=> (x * y)%R) ->
  (r =~> @rel_point_cV n =~> @rel_point_cV n) (fun l a=> arr_map (fun x=> mul_t l x) a) (fun L A=> (L *: A)%R).
Proof.
move=> mul_t_r.
apply/rel_equiv_func2; [exact:rel_comp_eqR|exact: rel_equiv_refl|exact: rel_equiv_refl|].
apply/rel_comp_func2; [|move=> l L ->; apply:rel_cV_scal].
by move=> /= l L lL; apply/rel_array_map/mul_t_r.
Qed.

Lemma rel_point_rV_iall (n : nat) f F:
  (@rel_int_ord n =~> r =~> eq) f F->
  (@rel_point_rV n =~> eq) (fun x=> iall (fun i=> f i x.[i]) (length x))
  (fun X=> [forall I, F I (X ord0 I)]).
Proof.
move=> fF x Y [X xX XY]; apply/idP/idP.
- move/allP=> h; apply/forallP=> I.
  move: (fF)=> /(_ (nat_to_int I) I) [:I_len].
  rewrite /rel_int_ord /rel_int nat_to_intK ?inE /=.
  + abstract: I_len.
    apply/(ltn_trans (ltn_ord _)); rewrite (rel_cV_length XY); 
      exact:int_thresholdP.
  move/(_ (erefl _) (x.[nat_to_int I]) (Y ord0 I)).
  rewrite -(rel_rV_nth XY I)=> [:I_x] <-.
  + apply/(rel_array_r xX); rewrite ltEint_nat nat_to_intK ?inE //.
    abstract: I_x.
    by rewrite (rel_array_length xX) -(rel_cV_length XY).
  + by apply/h; rewrite mem_irangeE le0x ltEint_nat nat_to_intK ?inE ?I_x.
- move/forallP=> h; apply/allP=> i; rewrite mem_irangeE le0x /= => i_len.
  move: (i_len); rewrite ltEint_nat (rel_array_length xX) -(rel_cV_length XY).
  move=> i_n; move: (fF)=> /(_ i (Ordinal i_n)); rewrite /rel_int_ord /rel_int /=.
  move=> /(_ (erefl _) x.[i] (Y ord0 (Ordinal i_n))) ->; last exact/h.
  by rewrite -(rel_rV_nth XY) int_to_natK; apply/(rel_array_r xX).
Qed.


Definition rel_point_mx_col (m n: nat) := rel_array (rel_array r) |~ @rel_mx_col R m n.
Definition rel_point_mx_row (m n: nat) := rel_array (rel_array r) |~ @rel_mx_row R m n.

Lemma rel_point_mx_col_length (m n : nat):
  (@rel_point_mx_col m n =~> rel_int) length (fun _=> n.+1).
Proof.
apply/rel_equiv_func; [exact: rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func; [exact:rel_array_length|exact:rel_mx_col_length].
Qed.

Lemma rel_point_mx_col_spec (m n : nat):
  rel_spec r eq->
  rel_spec (@rel_point_mx_col m n) eq.
Proof.
move=> r_spec.
apply: rel_spec_comp; first try do 2? apply:rel_spec_array; first exact:r_spec.
- move=> x X Y /rel_mx_col_nth xX /rel_mx_col_nth xY. 
  apply/matrixP=> p q; move: (xX q) (xY q).
  move=> /rel_cV_nth /(_ p) + /rel_cV_nth /(_ p).
  by rewrite !mxE=> <- <-.
- move=> /= x y M [len_xy] h [len_x x_nth]; split; rewrite ?len_xy //.
  move=> i; case: (x_nth i)=> len_xi xi_nth.
  move: (h (nat_to_int i)); rewrite ltEint_nat len_xy -len_x.
  rewrite nat_to_intK ?inE; 
    first (apply/(ltn_trans (ltn_ord _)); rewrite len_x; exact/int_thresholdP).
  case/(_ (ltn_ord _))=> len_xyi xyi_nth; split; rewrite ?len_xyi //.
  move=> j; rewrite -(xi_nth j); apply/xyi_nth.
  rewrite ltEint_nat len_xyi -len_xi nat_to_intK //.
  rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite len_xi; exact:int_thresholdP.
Qed.

Lemma rel_point_mx_col_col0 (m n : nat):
  (@rel_point_mx_col m n =~> @rel_point_cV m) (fun x=> x.[0%uint63]) (col ord0).
Proof.
move=> x Y [X xX XY]; exists X.[0%uint63].
- move: (xX)=> /rel_array_r /(_ 0%uint63); apply.
  by rewrite (rel_array_length xX) ltEint_nat -(rel_mx_col_length XY).
- by move: XY=> /rel_mx_col_nth=> /(_ ord0).
Qed.

Lemma rel_point_mx_row_iall (m n : nat) f F:
  (@rel_int_ord m =~> @rel_point_rV n =~> eq) f F->
  (@rel_point_mx_row m n =~> eq)
    (fun x=> iall (fun i=> f i x.[i]) (length x)) (fun X=> [forall i, F i (row i X)]).
Proof.
move=> fF x Y [X xX XY]; apply/idP/idP.
- move/allP=> h; apply/forallP=> i.
  move: (fF)=> /(_ (nat_to_int i) i); rewrite /rel_int_ord /rel_int /=.
  move: (ltn_ord i). rewrite [X in (_ < X)](rel_mx_row_length XY)=> i_len.
  rewrite nat_to_intK; first exact/int_threshold_length/i_len.
  move=> /(_ (erefl _) x.[nat_to_int i] (row i Y)) <-;
    last (apply/h; 
    rewrite mem_irangeE le0x ltEint_nat 
    nat_to_intK ?(int_threshold_length i_len) ?(rel_array_length xX)//).
  exists X.[nat_to_int i]; [apply/(rel_array_r xX)|exact/rel_mx_row_nth].
  by rewrite (rel_array_length xX) ltEint_nat nat_to_intK // (int_threshold_length i_len).
- move/forallP=> h; apply/allP=> i; rewrite mem_irangeE le0x /= => i_len.
  move: (rel_mx_row_length XY); rewrite -(rel_array_length xX)=> len_x.
  move: (i_len); rewrite ltEint_nat -len_x=> i_m.
  move: fF=> /(_ i (Ordinal i_m)); rewrite /rel_int_ord /rel_int /=.
  move=> /(_ (erefl _) x.[i] (row (Ordinal i_m) Y)) ->; last exact:h.
  exists X.[i]; [exact/(rel_array_r xX)|].
  by move:(rel_mx_row_nth XY (Ordinal i_m))=> /=; rewrite int_to_natK.
Qed.

Lemma rel_point_dot (n : nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_cV n =~> @rel_point_cV n =~> r)
  (array_dot addf mulf x0) (fun X Y=> '[X,Y]%R).
Proof.
move=> addh mulh x0h.
apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqR|].
by apply/rel_comp_func2; [apply:rel_array_dot|apply:rel_cV_dot].
Qed.

Lemma rel_point_mul_row_mx (m n : nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_rV m =~> @rel_point_mx_col m n =~> @rel_point_rV n)
  (array_mul_row_mx addf mulf x0) (fun v M=> (v *m M)%R).
Proof.
move=> addh mulh x0h.
by apply/rel_comp_func2; [apply:rel_array_mul_row_mx|apply:rel_mx_row_mul].
Qed.

Lemma rel_point_mulmx (m n p: nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_mx_row m p =~> @rel_point_mx_col p n =~> @rel_point_mx_row m n)
  (array_mulmx addf mulf x0) (fun A B=> (A *m B)%R).
Proof.
move=> addh mulh x0h.
by apply/rel_comp_func2;
  [apply/rel_array_mulmx|apply/rel_mulmx].
Qed.

End PointRel.

Section PolyRel.

Context {t : Type} {R : realFieldType}.
Context {r : t -> R -> Prop}.

Definition rel_Po_r (m n : nat):= 
  rel_couple (rel_array (rel_array r)) (rel_array r) |~ 
  rel_couple (@rel_mx_row R m n) (@rel_cV R m).

Lemma rel_Po_r_m (m n : nat):
  ((@rel_Po_r m n) =~> rel_int) (fun ab=> length ab.1) (fun _=> m.+1).
Proof. 
apply/rel_equiv_func; [exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func. 
- apply: rel_couple_func_fst; exact: rel_array_length.
- case=> a b [A B] [/= + _]; move: a A; exact: rel_mx_row_length.
Qed.

Lemma rel_Po_r_n_temp (m n : nat):
  ((@rel_Po_r m n) =~> rel_int) (fun ab=> if (length ab.1 > 0)%O then length ab.1.[0%uint63] else 0%uint63) (fun _=> n.+1).
Proof.
pose g := fun x=> if (length x > 0)%O then length x.[0] else 0%uint63.
apply/rel_equiv_func; [exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/(@rel_comp_func _ _ _ _ _ _ _ _ _ _ _ (fun AB=> if (length AB.1 > 0)%O then length AB.1.[0%uint63] else 0%uint63)).
- apply:(@rel_couple_func_fst _ _ _ _ _ _ _ _ _ (@g t) (@g R)).
  apply:rel_func_if=> // [x X /rel_array_length -> //|].
  by move=> x X + len_x; move/rel_array_r=> /(_ _ len_x) /rel_array_length.
- case=> a b [A B] [/= + _]; move=> /[dup] /rel_mx_row_length.
  rewrite ltEint_nat=> <-; rewrite ltn0Sn; exact:rel_mx_row_length_row.
Qed.

Lemma rel_Po_r_n (m n : nat):
  ((@rel_Po_r m n) =~> rel_int) (fun ab=> length ab.1.[0%uint63]) (fun _=> n.+1).
Proof.
move=> ab AB /[dup] /rel_Po_r_m + /rel_Po_r_n_temp.
by rewrite ltEint_nat => <-; rewrite ltn0Sn.
Qed.

Lemma rel_Po_r_row_A (m n : nat):
  (@rel_Po_r m n =~> @rel_int_ord m =~> rel_array r |~ @rel_rV R n)
  (fun Po k=> Po.1.[k]) (fun Ab K=> row K Ab.1).
Proof.
move=> po [A b] [PO] [poPO _] [/= POA _] k K kK.
exists PO.1.[k].
- apply/(rel_array_r poPO); rewrite (rel_array_length poPO).
  rewrite ltEint_nat -(rel_mx_row_length POA) -kK; exact/ltn_ord.
- by case: POA=> _ /(_ K); rewrite kK int_to_natK.
Qed.

Lemma rel_Po_r_row_b (m n : nat):
  (@rel_Po_r m n =~> @rel_int_ord m =~> r)
  (fun Po k=> Po.2.[k]) (fun Ab K=> Ab.2 K ord0).
Proof.
move=> po [A b] [PO] [_ poPO] [_ POb] k K kK /=.
case: POb=> len_eq /(_ K); rewrite /= kK int_to_natK => <-.
apply/(rel_array_r poPO); rewrite (rel_array_length poPO).
rewrite ltEint_nat -len_eq -kK; exact:ltn_ord.
Qed.

Lemma rel_Po_r_all_row (m n : nat) (f : Uint63.int -> (array t) -> t -> bool ) (F : 'I_m.+1 -> 'rV[R]_n.+1 -> R -> bool):
  ((@rel_int_ord m) =~> (rel_array r |~ @rel_rV R n) =~> r =~> eq) f F ->
  ((@rel_Po_r m n) =~> eq)
    (fun ab=> iall (fun i=> f i ab.1.[i] ab.2.[i]) (length ab.1))
    (fun AB=> [forall i, F i (row i AB.1) (AB.2 i ord0)]).
Proof.
move=> fF Po Ab Po_Ab; apply/idP/idP.
- move/allP=> h; apply/forallP=> I.
  move: (rel_Po_r_row_A Po_Ab) (rel_Po_r_row_b Po_Ab).
  have iI: (rel_int_ord (nat_to_int I) I).
  + rewrite /rel_int_ord /rel_int nat_to_intK //.
    rewrite inE; apply/(ltn_trans (ltn_ord _)).
    rewrite (rel_Po_r_m Po_Ab); exact:int_thresholdP.
  move/(_ _ _ iI)=> AI /(_ _ _ iI) bI.
  move:(fF _ _ iI _ _ AI _ _ bI)=> <-; apply/h.
  rewrite mem_irangeE le0x /= ltEint_nat -iI -(rel_Po_r_m Po_Ab).
  exact:ltn_ord.
- move/forallP=> h; apply/allP=> i; rewrite mem_irangeE le0x /=.
  rewrite ltEint_nat -(rel_Po_r_m Po_Ab)=> i_m.
  have iI: rel_int_ord i (Ordinal i_m) by [].
  move: (rel_Po_r_row_A Po_Ab iI)=> AI.
  move: (rel_Po_r_row_b Po_Ab iI)=> bI.
  move: fF=> /(_ _ _ iI _ _ AI _ _ bI)=> ->; exact/h.
Qed.

End PolyRel.
(* ------------------------------------------------------------------------------------------------ *)

Section RelGraphStructure.

Definition precond_struct (g : graph.graph) := forall i, mem_vertex g i -> 
  (lti_sorted (neighbours g i) /\ forall j, (j < nb_neighbours g i)%O -> mem_vertex g (neighbours g i).[j]).

Definition rel_structure g (G : graph [choiceType of Uint63.int]):=
  [/\   
    precond_struct g,
    (forall i, mem_vertex g i = (i \in vertices G))&
    (forall i j, mem_vertex g i -> mem_edge g i j = edges G i j)
  ].

Lemma rel_struct_valid_nei g G : rel_structure g G -> forall i, mem_vertex g i ->
  forall j, (j < nb_neighbours g i)%O -> mem_vertex g (neighbours g i).[j].
Proof. by case=> + _ _ i ig; move=> /(_ i ig) []. Qed.

Lemma rel_struct_uniq_nei g G: rel_structure g G -> forall i, mem_vertex g i ->
  uniq (arr_to_seq (neighbours g i)).
Proof. by move=> gG i ig; case: gG=> /(_ _ ig) [/lti_sorted_uniq]. Qed.

Lemma rel_struct_nei_mem g G: rel_structure g G -> forall i, mem_vertex g i ->
  [seq j <- arr_to_seq (neighbours g i) | mem_vertex g j] =
  arr_to_seq (neighbours g i).
Proof.
move=> + i ig; move/rel_struct_valid_nei=> /(_ i ig) /= h.
apply/all_filterP/allP=> x /(nthP (default (neighbours g i))); rewrite size_arr_to_seq. 
case=> [k k_nei <-]; rewrite nth_arr_to_seq //.
move: (h (nat_to_int k)); apply; rewrite ltEint_nat nat_to_intK //.
exact: (int_threshold_length k_nei).
Qed.

Lemma rel_struct_vtx g G:
  rel_structure g G -> (forall i, mem_vertex g i = (i \in vertices G)).
Proof. by case. Qed.

Lemma rel_struct_edge g G:
  rel_structure g G -> (forall i j, mem_vertex g i -> mem_edge g i j = edges G i j).
Proof. by case. Qed.

Lemma rel_struct_vtx_set g G: rel_structure g G -> vertices G = [fset i | i in irange0 (length g)].
Proof. by move=> gG; apply/fsetP=> z; rewrite !inE /= mem_irangeE le0x -(rel_struct_vtx gG). Qed.

Lemma rel_struct_card g G: rel_structure g G -> #|`vertices G| = length g.
Proof. by move=> gG; rewrite (rel_struct_vtx_set gG) card_imfset //= undup_id ?uniq_irange // size_irange subn0. Qed.

Lemma rel_struct_succ g G:
  rel_structure g G-> forall i, mem_vertex g i->
  successors G i = [fset j | j in arr_to_seq (neighbours g i)].
Proof.
move=> gG i ig; apply/fsetP=> j.
rewrite in_succE -(rel_struct_edge gG) // inE /=.
rewrite mem_edgeP // mem_filter.
apply/andb_idl=> /(nthP (default (neighbours g i))) [k].
rewrite size_arr_to_seq=> k_nei <-; rewrite nth_arr_to_seq //.
case: gG=> /(_ _ ig) [_ /(_ (nat_to_int k))] + _ _; apply.
rewrite ltEint_nat nat_to_intK //; exact/int_threshold_length/k_nei.
Qed.

Lemma rel_struct_nb_nei g G:
  rel_structure g G -> forall i, mem_vertex g i ->
  #|` successors G i| = nb_neighbours g i.
Proof.
move=> gG i ig; rewrite (rel_struct_succ gG) //.
rewrite card_imfset //= undup_id ?size_arr_to_seq //.
by apply/lti_sorted_uniq; case: gG=> /(_ i ig) [].
Qed.

Lemma rel_struct_all f:
  (rel_structure =~> eq) (fun g=> iall f (length g)) (fun G=> all f (vertices G)).
Proof.
move=> g G gG; apply/eq_all_r=> x.
by rewrite mem_irangeE le0x /= -(rel_struct_vtx gG).
Qed.

Lemma rel_struct_nei_all f g G: rel_structure g G -> forall i, mem_vertex g i -> 
  neighbour_all f g i = all f (successors G i).
Proof.
move=> gG i ig; rewrite /neighbour_all.
under [LHS]eq_in_all=> x /mapP [y]. 
  rewrite mem_irangeE le0x /= => /(rel_struct_valid_nei gG ig) h ->; rewrite h.
over.
by apply/eq_all_r=> z; rewrite (rel_struct_succ gG ig) inE.
Qed.

Lemma rel_struct_nei_fold {T : Type} (f : Uint63.int -> T -> T) g G a: rel_structure g G ->
  (forall i j a, f i (f j a) = f j (f i a)) -> 
  forall i, mem_vertex g i ->
  neighbour_fold f a g i = foldl (fun a i => f i a) a (successors G i).
Proof.
move=> gG fP i ig; rewrite neighbour_foldP //=.
apply/perm_foldl=> //; apply/uniq_perm; [exact/filter_uniq/(rel_struct_uniq_nei gG)|exact:fset_uniq|].
rewrite (rel_struct_succ gG) // => z; rewrite mem_filter !inE; apply/andb_idl.
move/nthP=> /(_ (default (neighbours g i))) [k]; rewrite size_arr_to_seq => k_nei <-.
rewrite nth_arr_to_seq //; move: (rel_struct_valid_nei gG ig)=> /(_ (nat_to_int k)).
apply; rewrite ltEint_nat nat_to_intK //; exact:(int_threshold_length k_nei).
Qed.
  

End RelGraphStructure.

Section RelGraph.

Context {t : Type} (T : choiceType).
Context {r : t -> T -> Prop}.

Definition precond_lbl_graph {t : Type} (gl : graph.graph * array t):=
  (length gl.1 = length gl.2).

Definition rel_lbl_graph gl GL := precond_lbl_graph gl /\ (rel_couple (rel_structure) (rel_array r)) gl GL.

Definition rel_final_graph (Gc : graph _ * array T) Gf :=
  gisof Gc.1 Gf (fun i=> Gc.2.[i]).

Definition rel_graph_r := rel_lbl_graph |~ rel_final_graph.

(* Lemma rel_lbl_graph_all gl GL f F:
  (forall i, mem_vertex gl.1 i -> f i = F i)->
  rel_lbl_graph gl GL -> iall (fun i=> f i) (length gl.1) = all (fun i=> F i) (vertices GL.1).
Proof.
move=> fF [gG lL]; apply/idP/idP.
- move/allP=> h; apply/allP=> i; rewrite -(rel_struct_vtx gG)=> i_g.
  by rewrite -(fF _ i_g); apply/h; rewrite mem_irangeE le0x.
- move/allP=> h; apply/allP=> i; rewrite mem_irangeE le0x /= => i_g.
  by rewrite fF //; apply/h; rewrite -(rel_struct_vtx gG).
Qed. *)

Lemma rel_final_graph_succ_card GL G:
  rel_final_graph GL G -> forall i, i \in vertices GL.1 -> #|` successors GL.1 i| = #|`successors G GL.2.[i]|.
Proof.
move=> GL_G i iG; rewrite (gisof_succ GL_G) // card_in_imfset //.
move=> x y /=; rewrite !in_succE=> /edge_vtxr + /edge_vtxr.
apply: (gisof_inj GL_G).
Qed.

(* Lemma rel_final_graph_all F GL G:
  rel_final_graph GL G-> all (fun i=> F GL.2.[i]) (vertices GL.1) = all F (vertices G).
Proof.
move=> GL_G.
rewrite -(gisof_vtx GL_G); apply/idP/idP.
- by move/allP=> h; apply/allP=> x /imfsetP [/= i /h ? ->].
- move/allP=> h; apply/allP=> i i_GL1; exact/h/in_imfset.
Qed. *)

Lemma rel_graph_r_spec gl GL G:
  rel_spec r eq ->
  rel_lbl_graph gl GL -> rel_final_graph GL G ->
  forall i V, mem_vertex gl.1 i -> V \in vertices G -> r gl.2.[i] V ->
  V = GL.2.[i].
Proof.
move=> r_injr [len_gl [/= gG lL] GL_G] i V ig VG iV.
move: VG; rewrite -(gisof_vtx GL_G)=> /imfsetP [/= j jG] V_eq.
move: iV; rewrite V_eq; apply/r_injr/(rel_array_r lL).
by rewrite -(len_gl).
Qed.


Lemma rel_graph_r_all f F gl G:
  (forall i V, mem_vertex gl.1 i -> V \in vertices G -> r gl.2.[i] V -> f i = F V) ->
  rel_graph_r gl G -> iall f (length gl.1) = all F (vertices G).
Proof.
move=> fF [GL [len_gG [gG lL]] GL_G]; rewrite -(gisof_vtx GL_G).
set S := [fset _ | _ in _].
have S_eq : S =i [seq GL.2.[i] | i <- irange0 (length gl.1)].
- move=> x; apply/idP/idP.
  + case/imfsetP=> /= i iG ->; apply/map_f; rewrite mem_irangeE le0x /=.
    by move: iG; rewrite -(rel_struct_vtx gG).
  + case/mapP=> i; rewrite mem_irangeE le0x /= => ig ->.
    by apply/in_imfset=> /=; rewrite -(rel_struct_vtx gG).
rewrite (eq_all_r S_eq) all_map /iall; apply/eq_in_all=> x /=.
rewrite mem_irangeE le0x /= => xg.
apply/fF/(rel_array_r lL)=> //; rewrite -?(gisof_vtx GL_G) -?(len_gG) //.
by apply/in_imfset=> /=; rewrite -(rel_struct_vtx gG).
Qed.

Lemma rel_graph_r_succ_card gl G:
  rel_spec r eq->
  rel_graph_r gl G -> forall i V, mem_vertex gl.1 i -> V \in vertices G -> r gl.2.[i] V ->
  #|` successors G V| = nb_neighbours gl.1 i.
Proof.
move=> r_injr [GL [len_gl [gG lL]] GL_G] i V ig VG iV.
rewrite -(rel_struct_nb_nei gG) // (rel_final_graph_succ_card GL_G) -?(rel_struct_vtx gG) //.
suff ->: V = GL.2.[i] by [].
by apply/(rel_graph_r_spec r_injr _ GL_G ig VG iV); split=> //.
Qed.

Lemma rel_graph_r_nei_all gl G f F:
  (rel_spec r eq)->
  (forall i V, mem_vertex gl.1 i -> V \in vertices G -> r gl.2.[i] V -> f i = F V)->
  rel_graph_r gl G -> forall i V, mem_vertex gl.1 i -> V \in vertices G -> r gl.2.[i] V ->
  neighbour_all f gl.1 i = all F (successors G V).
Proof.
move=> r_injr fF [GL [len_gl [gG lL]] GL_G] i V ig VG iV; rewrite /neighbour_all /arr_all.
have nei_eq: arr_to_seq gl.1.[i] =i [fset x | x in arr_to_seq gl.1.[i]] by move=> x; rewrite inE.
rewrite (eq_all_r nei_eq) -(rel_struct_succ gG) // (rel_graph_r_spec r_injr _ GL_G ig VG iV); first by split.
rewrite (gisof_succ GL_G) -?(rel_struct_vtx gG) //.
set S := [fset _ | _ in _]; have succ_eq: S =i [seq GL.2.[j] | j <- successors GL.1 i].
move=> x; apply/idP/idP; [case/imfsetP=> /= k ? ->; exact/map_f|case/mapP=> k ? ->; exact/in_imfset].
rewrite (eq_all_r succ_eq) all_map; apply/eq_in_all=> x /(fsubsetP (sub_succ _ _)) xG.
rewrite (rel_struct_vtx gG) xG; apply/fF=> //; rewrite ?(rel_struct_vtx gG) //.
- by rewrite -(gisof_vtx GL_G) in_imfset.
- by apply/(rel_array_r lL); rewrite -len_gl; move: xG; rewrite -(rel_struct_vtx gG).
Qed. 

End RelGraph.

(* ------------------------------------------------------------------------------------------------ *)

Section SpecFunc.

Definition spec_func {t T : Type} (r : t -> T -> Prop) 
  (f : t -> T) (P : t -> Prop) := forall x, P x -> r x (f x).

Lemma spec_func_int: spec_func rel_int int_to_nat (fun _ => True).
Proof. by []. Qed.

Definition int_to_ord (m : nat) (x : Uint63.int) :=
  if @idP (x < m.+1)%nat is ReflectT h then Ordinal h else ord0. 

Lemma spec_func_int_ord (m : nat):
  spec_func (@rel_int_ord m) (@int_to_ord m) (fun x=> (x < m.+1)%nat).
Proof. move=> x x_m; rewrite /int_to_ord; case: {-}_/idP=> //. Qed.

Lemma spec_func_comp {t T T' : Type} 
  (r : t -> T -> Prop) (r' : T -> T' -> Prop)
  f g (P : t -> Prop) (Q : T -> Prop):
  (forall x, P x -> Q (f x)) -> 
  spec_func r f P -> spec_func r' g Q ->
  spec_func (r |~ r') (g \o f) P.
Proof. move=> PQ spec_f spec_g x Px; exists (f x); [exact:spec_f|exact/spec_g/PQ]. Qed.

Lemma spec_func_comp_pre {t T T' : Type} 
  (r : t -> T -> Prop) (r' : T -> T' -> Prop)
  f g (P P' : t -> Prop) (Q : T -> Prop):
  (forall x, P x -> P' x -> Q (f x))->
  spec_func r f P -> spec_func r' g Q->
  spec_func (r |~ r') (g \o f) (fun x=> P' x /\ P x).
Proof. move=> PQ spec_f spec_g x [Px P'x]; exists (f x); [exact:spec_f|exact/spec_g/PQ]. Qed.

Lemma spec_func_couple {t1 t2 T1 T2 : Type}
  (r1 : t1 -> T1 -> Prop) (r2 : t2 -> T2 -> Prop)
  f g (P : t1 -> Prop) (Q : t2 -> Prop):
  spec_func r1 f P -> spec_func r2 g Q ->
  spec_func (rel_couple r1 r2) 
    (fun x=> (f x.1, g x.2)) (fun x=> P x.1 /\ Q x.2).
Proof. move=> spec_f spec_g x [Px1 Qx2]; split=> /=; [exact/spec_f|exact/spec_g]. Qed.

Definition precond_array {t : Type} (P : t -> Prop) (a : array t):=
  (forall i, (i < length a)%O -> P a.[i]).

Lemma spec_func_rel_array {t T : Type} (r : t -> T -> Prop)
  (f : t -> T) (P : t -> Prop):
  spec_func r f P-> 
  spec_func (rel_array r) 
    (fun a=> arr_map f a) (precond_array P). 
Proof.
move=> spec_f a Pa; split; rewrite ?length_arr_map //.
move=> i /Pa; rewrite arr_map_nth; exact:spec_f.
Qed.

Section Vector.

Definition precond_len (R : Type) (n : nat) (a : array R):=
  n.+1 = length a.

Definition arr_to_cV (R : realFieldType) (n : nat) (a : array R):= 
  (\col_(i < n.+1) get a (nat_to_int i))%R.
Definition arr_to_rV (R : realFieldType) (n : nat) (a : array R):= 
  (\row_(i < n.+1) get a (nat_to_int i))%R.

Lemma spec_func_to_cV (R : realFieldType) n: 
  spec_func (@rel_cV R n) (@arr_to_cV R n) (@precond_len R n).
Proof. by move=> a a_len; split=> // i; rewrite mxE. Qed.

Lemma spec_func_to_rV R n:
  spec_func (@rel_rV R n) (@arr_to_rV R n) (@precond_len R n).
Proof. by move=> a a_len; split=> // i; rewrite !mxE. Qed.

Definition arr_to_mx_row (R : realFieldType) 
  (m n : nat) (a : array (array R)):=
  (\matrix_(i < m.+1) (@arr_to_rV R n (get a (nat_to_int i))))%R.

Definition precond_mx (R : Type) (m n : nat)
  (a : array (array R)):=
  (m.+1 = length a) /\ (precond_array (@precond_len R n) a).

Definition arr_to_mx_col (R : realFieldType) 
  (m n : nat) (a : array (array R)):=
  ((\matrix_(i < n.+1) (@arr_to_cV R m (get a (nat_to_int i)))^T)^T)%R.

Lemma spec_func_to_mx_row (R : realFieldType) (m n : nat):
  spec_func (@rel_mx_row R m n) (@arr_to_mx_row R m n)
    (@precond_mx R m n).
Proof.
move=> a [len_a len_row_a]; split=> // i.
rewrite rowK; apply/spec_func_to_rV/len_row_a.
rewrite ltEint_nat=> [:i_len].
rewrite nat_to_intK; last by (abstract:i_len; rewrite -len_a).
rewrite !inE; exact/(ltn_trans i_len)/int_thresholdP.
Qed.

Lemma spec_func_to_mx_col (R : realFieldType) (m n : nat):
  spec_func (@rel_mx_col R m n) (@arr_to_mx_col R m n)
    (@precond_mx R n m).
Proof.
move=> a [len_a len_row_a]; split=> // i.
rewrite -tr_row rowK trmxK; apply/spec_func_to_cV/len_row_a.
rewrite ltEint_nat=> [:i_len].
rewrite nat_to_intK; last by (abstract:i_len; rewrite -len_a).
rewrite !inE; exact/(ltn_trans i_len)/int_thresholdP.
Qed.

Definition arr_to_point_cV (t : Type) (R : realFieldType) (n : nat)
  (f : t -> R):= (@arr_to_cV R n) \o (arr_map f).

Definition arr_to_point_rV (t : Type) (R : realFieldType) (n : nat)
  (f : t -> R):= (@arr_to_rV R n) \o (arr_map f).
  
Lemma spec_func_to_point_cV (t : Type) (R : realFieldType) (n : nat)
  (r : t -> R -> Prop) (f : t -> R) (P : t -> Prop):
  spec_func r f P->
  spec_func (@rel_point_cV _ _ r n) (@arr_to_point_cV t R n f)
  (fun a=> @precond_len t n a /\ precond_array P a).
Proof.
move=> spec_f a /[dup] pre [len_a P_a].
apply/spec_func_comp_pre; 
  [ |apply/spec_func_rel_array/spec_f|exact/spec_func_to_cV|exact/pre].
by move=> x _ len_x; rewrite /precond_len len_x length_arr_map.
Qed.

Lemma spec_func_to_point_rV (t : Type) (R : realFieldType) (n : nat)
  (r : t -> R -> Prop) (f : t -> R) (P : t -> Prop):
  spec_func r f P->
  spec_func (@rel_point_rV _ _ r n) (@arr_to_point_rV t R n f)
  (fun a=> @precond_len t n a /\ precond_array P a).
Proof.
move=> spec_f a /[dup] pre [len_a P_a].
apply/spec_func_comp_pre; 
  [ |apply/spec_func_rel_array/spec_f|exact/spec_func_to_rV|exact/pre].
by move=> x _ len_x; rewrite /precond_len len_x length_arr_map.
Qed.

Definition arr_to_point_mx_row (t : Type) (R : realFieldType) (m n : nat)
  (f : t -> R):=
  (@arr_to_mx_row R m n) \o (arr_map (fun x => arr_map f x)).

Definition arr_to_point_mx_col (t : Type) (R : realFieldType) (m n : nat)
  (f : t -> R):=
  (@arr_to_mx_col R m n) \o (arr_map (fun x => arr_map f x)).

Lemma spec_func_to_point_mx_row (t : Type) (R : realFieldType) (m n : nat)
  (r : t -> R -> Prop) (f : t -> R) (P : t -> Prop):
  spec_func r f P->
  spec_func (@rel_point_mx_row _ _ r m n) (@arr_to_point_mx_row t R m n f)
  (fun a=> @precond_mx t m n a /\ precond_array (fun x=> precond_array P x) a).
Proof.
move=> spec_f; apply/spec_func_comp_pre;
  [|exact/spec_func_rel_array/spec_func_rel_array|exact/spec_func_to_mx_row].
move=> a _ [len_a pre_a]; split; rewrite ?length_arr_map //.
move=> i; rewrite length_arr_map=> /pre_a; rewrite /precond_len.
by rewrite arr_map_nth length_arr_map.
Qed.

Lemma spec_func_to_point_mx_col (t : Type) (R : realFieldType) (m n : nat)
  (r : t -> R -> Prop) (f : t -> R) (P : t -> Prop):
  spec_func r f P->
  spec_func (@rel_point_mx_col _ _ r m n) 
    (@arr_to_point_mx_col t R m n f)
  (fun a=> @precond_mx t n m a /\ precond_array (fun x=> precond_array P x) a).
Proof.
move=> spec_f; apply/spec_func_comp_pre;
  [|exact/spec_func_rel_array/spec_func_rel_array|exact/spec_func_to_mx_col].
move=> a _ [len_a pre_a]; split; rewrite ?length_arr_map //.
move=> i; rewrite length_arr_map=> /pre_a; rewrite /precond_len.
by rewrite arr_map_nth length_arr_map.
Qed.

End Vector.

Section ArraySet.

Definition arr_to_set {T : finType} (a : array T):=
  [set a.[i] | i in irange0 (length a)].

Lemma spec_func_arr_to_set {T : finType} (op : rel T):
  spec_func (rel_array_set op) (@arr_to_set T)
  (fun a=> rel_sorted op a).
Proof. by move=> a sta; split. Qed.

Definition precond_array_set {t : Type} (op_t : rel t) (P : t -> Prop) 
  (a : array t):=
  rel_sorted op_t a /\ precond_array P a.

Lemma spec_func_arr_to_set_r {t : Type} {T : finType} 
  (op_t : rel t) (op_T : rel T) 
  (r : t -> T -> Prop) (f : t -> T) (P : t -> Prop):
  (r =~> r =~> eq) op_t op_T ->
  spec_func r f P ->
  spec_func (@rel_arr_set_r _ _ r op_T) (arr_to_set \o (arr_map f))
  (precond_array_set op_t P).
Proof.
move=> op_tT spec_f; apply/spec_func_comp_pre;
  [|exact/spec_func_rel_array|exact/spec_func_arr_to_set].
move=> a Pa /=; apply/eq_imply/sorted_rel_equiv; 
  [| |move=> ???? h1 h2; apply:op_tT; [exact:h1|exact:h2]].
- by rewrite length_arr_map.
- move=> i i_len; rewrite arr_map_nth; exact/spec_f/Pa.
Qed.

End ArraySet.

Section Graph.

Definition graph_to_high (g : graph.graph):=
  mk_graph ([fset i | i in irange0 (length g)]) 
  (fun i j=> mem_edge g i j).

Lemma spec_func_structure:
  spec_func rel_structure graph_to_high precond_struct.
Proof.
move=> g Pg; split=> // i; rewrite ?vtx_mk_graph ?inE ?mem_irangeE ?le0x //.
move=> j ig; apply/idP/idP.
- move: Pg=> /(_ i ig) [_ h].
  rewrite mem_edgeP // mem_filter => /andP [jg nei_j].
  rewrite edge_mk_graph ?mem_edgeP ?mem_filter 
    ?jg ?nei_j ?inE ?mem_irangeE ?le0x //.
- move=> /[dup] /edge_vtxr; rewrite !vtx_mk_graph !inE !mem_irangeE !le0x /=.
  by move=> jg; rewrite edge_mk_graph // ?inE ?mem_irangeE ?le0x.
Qed.

Definition lbl_graph_to_high_lbl {t T: Type} (f : t -> T) gl:=
  (graph_to_high gl.1, arr_map f gl.2).


Lemma spec_func_lbl_graph {t : Type} {T : choiceType}
  (r : t -> T -> Prop) (f : t -> T) (P : t -> Prop):
  spec_func r f P ->
  spec_func (@rel_lbl_graph _ _ r) (lbl_graph_to_high_lbl f)
    (fun gl=> precond_lbl_graph gl /\ (precond_struct gl.1 /\ precond_array P gl.2)).
Proof.
move=> spec_f gl [pre_lbl pre_gr]; split=> //.
by apply:spec_func_couple; 
  [apply:spec_func_structure|apply/spec_func_rel_array/spec_f|].
Qed.

Definition high_lbl_to_final {T : choiceType} 
  (GL : high_graph.graph [choiceType of Uint63.int] * array T):=
  (fun x=> GL.2.[x]) @° GL.1.

Definition precond_high_to_final {T : choiceType} 
  (GL : high_graph.graph [choiceType of Uint63.int] *
        array T):=
  (forall x, x \in vertices GL.1 = (x < length GL.2)%O) /\
  {in irange0 (length GL.2) &, injective (get GL.2)}.

Lemma spec_func_final_graph (T : choiceType):
  spec_func (@rel_final_graph T) 
  (high_lbl_to_final) (precond_high_to_final).
Proof.
move=> GL [GL_len L_st] [:L_inj]; apply/gisofE; split.
- abstract: L_inj.
  by move=> x y; rewrite !GL_len=> ??; apply/L_st; rewrite ?mem_irangeE ?le0x.
- by rewrite vtx_img_graph.
- move=> x y xG yG; apply/idP/idP.
  + by move=> Gxy; apply/edge_img_graph; exists x,y; split.
  + case/edge_img_graph=> x' [y'] [++] /[dup] /edge_vtxlr [x'G y'G].
    by move/L_inj=> -> // /L_inj ->.
Qed.

Definition precond_graph {T : Type} 
  (ltt : rel T) (P : T -> Prop)
  (gl : graph.graph * array T):=
  rel_sorted ltt gl.2 /\
  precond_lbl_graph gl /\ 
  (precond_struct gl.1 /\ precond_array P gl.2).

Lemma spec_func_rel_graph_r {t : Type} {T : choiceType}
  (r : t -> T -> Prop) f (P : t -> Prop)
  (ltt eqt: rel t):
  transitive ltt ->
  (forall x y, P x -> P y -> f x == f y -> eqt x y)->
  (forall x y : t, eqt x y -> ~~ ltt x y /\ ~~ ltt y x)->
  spec_func r f P->
  spec_func (@rel_graph_r _ _ r)
  (high_lbl_to_final \o (fun gl=> (graph_to_high gl.1, arr_map f gl.2)))
  (precond_graph ltt P).
Proof.
move=> tr_ltt f_inj eqt_spec spec_f.
apply: (spec_func_comp_pre);
  [|exact/spec_func_lbl_graph/spec_f|exact:spec_func_final_graph].
case=> g l [pre_lbl] [/= pre_struct pre_arr] pre_st.
split.
- move=> x /=; rewrite length_arr_map vtx_mk_graph inE /=.
  by rewrite pre_lbl /= mem_irangeE le0x.
- move=> i j /=; rewrite length_arr_map !arr_map_nth.
  rewrite !mem_irangeE ?le0x /= => i_l j_l /eqP.
  move/f_inj=> /(_ (pre_arr _ i_l) (pre_arr _ j_l)).
  move/(sorted_rel_inj_rel tr_ltt); exact.
Qed.

End Graph.
End SpecFunc.

Module PrecondComputation.

Definition pre_struct_computation (g : graph.graph) :=
  IFold.iall (fun i=> 
    PArrayUtils.is_lti_sorted (GraphUtils.neighbours g i) &&
    PArrayUtils.all (fun j=> GraphUtils.mem_vertex g j) (GraphUtils.neighbours g i)) 
  (length g).

Definition pre_lbl_graph_computation {T : Type} 
  (g : graph.graph) (l : array T):=
  (length g =? length l)%uint63.

Definition pre_array_computation {T : Type} (f : T -> bool) (a : array T):=
  PArrayUtils.all f a.

Definition pre_length_computation {T : Type} (a : array T) (n : Uint63.int):=
  (length a =? n)%uint63.

Definition pre_mx_computation {T : Type} (a : array (array T)) (m n : Uint63.int):=
  (length a =? m)%uint63 && PArrayUtils.all (fun x=> pre_length_computation x n) a.

Definition pre_ord_computation (x m : Uint63.int):=
  (x <? m)%uint63.

Definition pre_graph_computation {T : Type}
  (ltT : rel T) (f : T -> bool)
  (g : graph.graph) (l : array T) :=
  [&& PArrayUtils.is_sorted_rel ltT l,
      pre_lbl_graph_computation g l,
      pre_struct_computation g &
      pre_array_computation f l
  ].

Definition pre_arr_set_computation {T : Type} (op_t : rel T)
  (f : T -> bool) (a : array T):=
  PArrayUtils.is_sorted_rel op_t a && pre_array_computation f a. 

End PrecondComputation.

Module PC := PrecondComputation.

Section PrecondEquiv.

Definition pre_struct_computation (g : graph.graph) :=
  iall (fun i=> 
    is_lti_sorted (neighbours g i) &&
    arr_all (fun j=> mem_vertex g j) (neighbours g i)) 
  (length g).

Definition pre_lbl_graph_computation {T : Type} 
  (g : graph.graph) (l : array T):=
  (length g == length l)%O.

Definition pre_array_computation {T : Type} (f : T -> bool) (a : array T):=
  arr_all f a.

Definition pre_length_computation {T : Type} (a : array T) (n : Uint63.int):=
  (length a == n)%O.

Definition pre_mx_computation {T : Type} 
  (a : array (array T)) (m n : Uint63.int):=
  (length a == m)%O && 
  arr_all (fun x=> pre_length_computation x n) a.

Definition pre_ord_computation (x m : Uint63.int):=
  (x < m)%O.

Definition pre_graph_computation 
  {T : Type} (ltT : rel T) (f : T -> bool) 
  (g : graph.graph) (l : array T):=
  [&& is_sorted_rel ltT l,
      pre_lbl_graph_computation g l,
      pre_struct_computation g &
      pre_array_computation f l
  ].

Definition pre_arr_set_computation {T : Type} (op_t : rel T)
(f : T -> bool) (a : array T):=
  is_sorted_rel op_t a && pre_array_computation f a. 

Lemma pre_struct_computationE g:
  PC.pre_struct_computation g = pre_struct_computation g.
Proof.
rewrite /PC.pre_struct_computation iallE; apply/eq_all=> i.
rewrite is_lti_sortedE arr_allE; congr andb.
Qed.

Lemma pre_lbl_graph_computationE {T : Type} g (l : array T):
  PC.pre_lbl_graph_computation g l = pre_lbl_graph_computation g l.
Proof. by rewrite /PC.pre_lbl_graph_computation eqEint. Qed.

Lemma pre_array_computationE {T : Type} (f : T -> bool) (a : array T):
  PC.pre_array_computation f a = pre_array_computation f a.
Proof. by rewrite /PC.pre_array_computation arr_allE. Qed.

Lemma pre_length_computationE {T : Type} (a : array T) n:
  PC.pre_length_computation a n = pre_length_computation a n.
Proof. by rewrite /PC.pre_length_computation eqEint. Qed.

Lemma pre_mx_computationE {T : Type} (a : array (array T)) m n:
  PC.pre_mx_computation a m n = pre_mx_computation a m n.
Proof.
rewrite /PC.pre_mx_computation eqEint; congr andb.
by rewrite arr_allE; apply/eq_all=> i; rewrite pre_length_computationE.
Qed.

Lemma pre_ord_computationE (x m : Uint63.int):
  PC.pre_ord_computation x m = pre_ord_computation x m.
Proof. by rewrite /PC.pre_ord_computation -ltEint. Qed.

Lemma pre_graph_computationE {T : Type}
  (ltT : rel T) (f : T -> bool) 
  (g : graph.graph) (l : array T):
  PC.pre_graph_computation ltT f g l =
  pre_graph_computation ltT f g l.
Proof.
rewrite /PC.pre_graph_computation; repeat congr andb.
- by rewrite is_sorted_relE.
- by rewrite pre_lbl_graph_computationE.
- by rewrite pre_struct_computationE.
- by rewrite pre_array_computationE.
Qed.

Lemma pre_arr_set_computationE {T : Type}
  (ltt : rel T) (f : T -> bool) a:
  PC.pre_arr_set_computation ltt f a =
  pre_arr_set_computation ltt f a.
Proof. by rewrite /PC.pre_arr_set_computation is_sorted_relE pre_array_computationE. Qed.

End PrecondEquiv.

Section PrecondProofs.

Lemma precond_structP g: pre_struct_computation g ->
  precond_struct g.
Proof.
move/allP=> h i ig.
move/(_ i): h; rewrite mem_irangeE le0x=> /(_ ig).
case/andP=> nei_st nei_vtx; split.
- by rewrite -lti_sortedP.
- move=> j j_nei; move: nei_vtx.
  move/allP=> /(_ (neighbours g i).[j]).
  rewrite /arr_to_seq map_f ?mem_irangeE ?le0x ?j_nei //.
  exact.
Qed.

Lemma precond_lbl_graphP {T : Type} g (l : array T): 
  pre_lbl_graph_computation g l ->
  precond_lbl_graph (g,l).
Proof. by move/eqP. Qed.

Lemma precond_arrayP {T : Type} 
  (f : T -> bool) (P : T -> Prop) (a : array T):
  (forall x, f x -> P x)->
  pre_array_computation f a -> precond_array P a.
Proof. by move=> fP /all_arr hf i i_a; apply/fP/hf. Qed.

Lemma precond_lengthP {T : Type} (a : array T) (i : Uint63.int) (n : nat):
  n.+1 = i->  
  pre_length_computation a i -> precond_len n a.
Proof. by rewrite /precond_len=> -> /eqP ->. Qed.

Lemma precond_mxP {T : Type} (a : array (array T)) 
  (i j : Uint63.int) (m n : nat):
  m.+1 = i -> n.+1 = j ->
  pre_mx_computation a i j -> precond_mx m n a.
Proof.
rewrite /precond_mx /precond_len => -> -> /andP [/eqP -> /all_arr] h.
by split=> // k k_a; move:h=> /(_ k k_a) /eqP ->.
Qed.

Lemma precond_graphP {T : Type} (ltt : rel T) (f : T -> bool)
  (P : T -> Prop) g l: 
  (forall x, f x -> P x)->
  pre_graph_computation ltt f g l->
  precond_graph ltt P (g,l).
Proof.
move=> fP /and4P [l_st pre_lbl pre_stru pre_arr]; split=> /=.
- by rewrite -rel_sortedP.
- split=> /=. exact/precond_lbl_graphP.
- split=> /=. exact/precond_structP.
- exact/(precond_arrayP fP).
Qed.

Lemma precond_array_setP {T : Type} (ltt : rel T)
  (f : T -> bool) (P : T -> Prop) a:
  (forall x, f x -> P x)->
  pre_arr_set_computation ltt f a ->
  precond_array_set ltt P a.
Proof.
move=> fP /andP [st_a f_a]; split; rewrite -?rel_sortedP //.
exact/(precond_arrayP fP).
Qed.

End PrecondProofs.
