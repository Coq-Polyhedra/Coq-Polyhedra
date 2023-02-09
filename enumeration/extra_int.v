(* -------------------------------------------------------------------- *)
From Coq      Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect.
From Polyhedra Require Import extra_misc.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

(* -------------------------------------------------------------------- *)
Coercion int_to_nat (x : int) : nat :=
  BinInt.Z.to_nat (to_Z x).

Definition wB_nat (x : nat) := (BinInt.Z.lt (BinInt.Z.of_nat x) wB).
Definition int_threshold := locked (2 ^ Uint63.size).

Lemma int_threshold0 : (int_threshold > 0).
Proof.
by rewrite /int_threshold; unlock.
Qed.

Lemma int_threshold1 : (int_threshold > 1).
Proof.
by rewrite /int_threshold; unlock.
Qed.

Definition nat_to_int (x : nat) : int := of_Z (BinInt.Z.of_nat x).
Definition max_int_ := nat_to_int (predn (int_threshold)).

Lemma wB_natE (x : nat): wB_nat x <-> (x < int_threshold).
Proof.
suff: wB = BinInt.Z.of_nat (int_threshold).
- by rewrite /wB_nat=> ->; split;
    [move/Znat.Nat2Z.inj_lt/ssrnat.ltP|move/ssrnat.ltP/Znat.Nat2Z.inj_lt].
rewrite /wB /int_threshold -Zpower.two_power_nat_equiv; unlock.
elim: Uint63.size=> //= n IHn.
rewrite expnS Zpower.two_power_nat_S IHn.
have ->: (Zpos (xO 1%AC)) = BinInt.Z.of_nat 2 by [].
by rewrite -Znat.Nat2Z.inj_mul.
Qed.

Lemma ltin i j: (i <? j)%uint63 = (i < j)%nat.
Proof.
apply/idP/idP.
- move/ltbP/Znat.Z2Nat.inj_lt.
  case: (to_Z_bounded i) (to_Z_bounded j)=> + _ [+ _] h.
  by move: h => /[apply] /[apply] /ssrnat.ltP.
- move/ssrnat.ltP=> h; apply/ltbP/Znat.Z2Nat.inj_lt=> //.
  + by case: (to_Z_bounded i).
  + by case: (to_Z_bounded j).
Qed.
  
Lemma lein i j: (i <=? j)%uint63 = (i <= j)%nat.
Proof.
apply/idP/idP.
- move/lebP/Znat.Z2Nat.inj_le.
  case: (to_Z_bounded i) (to_Z_bounded j)=> + _ [+ _] h.
    by move: h => /[apply] /[apply] /ssrnat.leP.
- move/ssrnat.leP=> h; apply/lebP/Znat.Z2Nat.inj_le=> //.
  + by case: (to_Z_bounded i).
  + by case: (to_Z_bounded j).
Qed.

Lemma wB_nat_int (x : int) : wB_nat x.
Proof.
rewrite /wB_nat /int_to_nat. 
by case: (to_Z_bounded x)=> ??; rewrite Znat.Z2Nat.id.
Qed.

Lemma int_thresholdP (x : int) : x < int_threshold.
Proof. exact/wB_natE/wB_nat_int. Qed.

Lemma int_to_natK : cancel int_to_nat nat_to_int.
Proof. 
move=> x; rewrite /nat_to_int /int_to_nat.
rewrite Znat.Z2Nat.id ?of_to_Z //.
by case: (to_Z_bounded x).
Qed.

Lemma nat_to_intK : {in gtn int_threshold, cancel nat_to_int int_to_nat}.
Proof.
move=> y; rewrite inE=> /wB_natE y_lt.
rewrite /int_to_nat /nat_to_int of_Z_spec.
rewrite Zdiv.Zmod_small ?Znat.Nat2Z.id //; split=> //.
exact: Zorder.Zle_0_nat.
Qed.

Lemma int_to_nat_inj: injective int_to_nat.
Proof. by move=> i j /(congr1 nat_to_int); rewrite !int_to_natK. Qed.

Lemma nat_to_int_inj: {in gtn int_threshold &, injective nat_to_int}.
Proof. by move=> ???? /(congr1 int_to_nat); rewrite !nat_to_intK. Qed.

(* -------------------------------------------------------------------- *)

Definition int_eqMixin := CanEqMixin int_to_natK.
Canonical  int_eqType  := EqType int int_eqMixin.

Definition int_choiceMixin := CanChoiceMixin int_to_natK.
Canonical  int_choiceType  := ChoiceType int int_choiceMixin.

Definition int_countMixin := CanCountMixin int_to_natK.
Canonical  int_countType  := CountType int int_countMixin.

(* -------------------------------------------------------------------- *)
Definition enum_int63 := map nat_to_int (iota 0 int_threshold).

Lemma enum_int63P : Finite.axiom enum_int63.
Proof.
move=> x; rewrite count_uniq_mem; last apply/eqP; rewrite ?eqb1.
- rewrite map_inj_in_uniq ?iota_uniq //.
  move=> i j; rewrite ?mem_iota add0n !leq0n /= => ??.
  by apply/nat_to_int_inj; rewrite inE.
- apply/(nthP 0%uint63); exists x; rewrite ?size_map ?size_iota;
    first exact/int_thresholdP.
  rewrite (nth_map 0) ?size_iota; first exact/int_thresholdP.
  rewrite nth_iota ?add0n; first exact/int_thresholdP.
  by rewrite int_to_natK.
Qed.

Definition int63_finMixin := FinMixin enum_int63P.
Canonical  int63_finType  := FinType int int63_finMixin.

(* ---------------------------------------------------------------------- *)

Definition imin (i j : int) := if (i <? j)%uint63 then i else j.
Definition imax (i j : int) := if (i <? j)%uint63 then j else i.

Program Definition int63_orderMixin :=
  @LeOrderMixin _ leb ltb imin imax _ _ _ _ _ _.

Next Obligation. by rewrite ltin lein ltn_neqAle eq_sym. Qed.
Next Obligation. move=> ??; rewrite !lein => ?; exact/int_to_nat_inj/anti_leq. Qed.
Next Obligation. move=> ???; rewrite !lein; exact/leq_trans. Qed.
Next Obligation. by move=> ??; rewrite !lein leq_total. Qed.

Canonical int_porderType :=
  POrderType Order.NatOrder.nat_display int int63_orderMixin.

(* ------------------------------------------------------------------------ *)

Lemma eqEint (x y : int): (x =? y)%uint63 = (x == y).
Proof. by apply/idP/idP; [move/eqb_spec=> -> | move/eqP=> ->; apply/eqb_spec]. Qed. 

Lemma leEint : <=%O = leb.
Proof. by []. Qed.

Lemma ltEint : <%O = ltb.
Proof. by []. Qed.

Lemma le0int (x : int) : (0%uint63 <= x)%O.
Proof. by rewrite leEint lein leq0n. Qed.

Lemma leintT (x : int) : (x <= max_int_)%O.
Proof.
rewrite leEint lein /max_int_ nat_to_intK ?inE ?ltn_predL ?int_threshold0 //.
move: (int_thresholdP x); rewrite -[X in x < X](prednK int_threshold0).
exact/ltnSE.
Qed.

Canonical int_bPOrderType := BPOrderType int (BottomMixin le0int).
Canonical int_tPOrderType := TPOrderType int (TopMixin leintT).
Canonical int_tbPOrderType := [tbPOrderType of int].
Canonical int_meetSemilatticeType := MeetSemilatticeType int int63_orderMixin.
Canonical int_bMeetSemilatticeType := [bMeetSemilatticeType of int].
Canonical int_tMeetSemilatticeType := [tMeetSemilatticeType of int].
Canonical int_tbMeetSemilatticeType := [tbMeetSemilatticeType of int].
Canonical int_joinSemilatticeType := JoinSemilatticeType int int63_orderMixin.
Canonical int_bJoinSemilatticeType := [bJoinSemilatticeType of int].
Canonical int_tJoinSemilatticeType := [tJoinSemilatticeType of int].
Canonical int_tbJoinSemilatticeType := [tbJoinSemilatticeType of int].
Canonical int_latticeType := [latticeType of int].
Canonical int_bLatticeType := [bLatticeType of int].
Canonical int_tLatticeType := [tLatticeType of int].
Canonical int_tbLatticeType := [tbLatticeType of int].
Canonical int_distrLatticeType := DistrLatticeType int int63_orderMixin.
Canonical int_bDistrLatticeType := [bDistrLatticeType of int].
Canonical int_tDistrLatticeType := [tDistrLatticeType of int].
Canonical int_tbDistrLatticeType := [tbDistrLatticeType of int].
Canonical int_orderType := OrderType int int63_orderMixin.
Canonical int_bOrderType := [bOrderType of int].
Canonical int_tOrderType := [tOrderType of int].
Canonical int_tbOrderType := [tbOrderType of int].
Canonical int_finPOrderType := [finPOrderType of int].
Canonical int_finBPOrderType := [finBPOrderType of int].
Canonical int_finTPOrderType := [finTPOrderType of int].
Canonical int_finTBPOrderType := [finTBPOrderType of int].
Canonical int_finMeetSemilatticeType := [finMeetSemilatticeType of int].
Canonical int_finBMeetSemilatticeType := [finBMeetSemilatticeType of int].
Canonical int_finJoinSemilatticeType := [finJoinSemilatticeType of int].
Canonical int_finTJoinSemilatticeType := [finTJoinSemilatticeType of int].
Canonical int_finLatticeType :=  [finLatticeType of int].
Canonical int_finTBLatticeType :=  [finTBLatticeType of int].
Canonical int_finDistrLatticeType :=  [finDistrLatticeType of int].
Canonical int_finTBDistrLatticeType :=  [finTBDistrLatticeType of int].
Canonical int_finOrderType := [finOrderType of int].
Canonical int_finTBOrderType := [finTBOrderType of int].

(* -------------------------------------------------------------------- *)

Section IntTheory.

Definition lteEint := (ltEint, leEint).

Lemma leEint_nat (x y : int) : (x <= y)%O = (x <= y)%nat.
Proof. by rewrite leEint lein. Qed.

Lemma ltEint_nat (x y : int) : (x < y)%O = (x < y)%nat.
Proof. by rewrite ltEint ltin. Qed.

End IntTheory.

(* -------------------------------------------------------------------- *)
Section SuccTheory.


Lemma succ_intE (c : int) :
  (c < max_int_)%O -> Uint63.succ c = c.+1 :> nat.
Proof. 
rewrite ltEint_nat nat_to_intK ?inE ?ltn_predL ?int_threshold0 //.
move=> c_int; rewrite /int_to_nat succ_spec Zdiv.Zmod_small; last first; try split.
- rewrite Znat.Z2Nat.inj_add; [by case: (to_Z_bounded c)|exact:BinInt.Z.le_0_1|].
  by rewrite /= Pnat.Pos2Nat.inj_1 PeanoNat.Nat.add_1_r.
- apply/Ztac.add_le; [by case: (to_Z_bounded c)|exact:BinInt.Z.le_0_1].
- move: c_int; rewrite /int_threshold; unlock.
  rewrite /int_to_nat -ltnS prednK ?expn_gt0 //.
  move/ssrnat.ltP/Znat.inj_lt; rewrite /wB Znat.Nat2Z.inj_succ.
  rewrite Znat.Z2Nat.id; first by case: (to_Z_bounded c).
  rewrite BinInt.Z.add_1_r -Zpower.two_power_nat_equiv.
  suff ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size by [].
  elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
  by rewrite Zpower.two_power_nat_S => ->.
Qed.

Lemma succ_int_max:
  Uint63.succ max_int_ = 0%uint63.
Proof.
rewrite /max_int_ /int_threshold; apply/to_Z_inj=> /=.
rewrite to_Z_0 succ_spec /nat_to_int of_Z_spec.
rewrite Zdiv.Zplus_mod_idemp_l.
unlock; rewrite Znat.Nat2Z.inj_pred_max -BinInt.Z.add_max_distr_r.
rewrite [X in BinInt.Z.max X _]BinInt.Z.add_0_l.
rewrite BinInt.Z.add_pred_l BinInt.Z.add_1_r BinInt.Z.pred_succ.
rewrite /wB.
have ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size.
  - elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
    by rewrite Zpower.two_power_nat_S => ->.
by rewrite Zpower.two_power_nat_equiv BinInt.Z.max_r ?Zdiv.Z_mod_same_full.
Qed.

Lemma succ_intP (c : int) :
  (c < max_int_)%O <-> Uint63.succ c = c.+1 :> nat.
Proof.
split; first exact: succ_intE.
apply/contra_eqT=> /negPf c_max.
move: (lex1 c); rewrite le_eqVlt c_max orbF=> /eqP -> /=.
by rewrite succ_int_max.
Qed.

Lemma succ_int_ltE (a b : int) :
  (a < b)%O -> Uint63.succ a = a.+1 :> nat.
Proof.
move=> ab.
move: (lt_le_trans ab (lex1 _)).
exact: succ_intE.
Qed.

Lemma succ_int_mono (a b : int):
  (a < max_int_)%O -> (b < max_int_)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
by move=> a_max b_max; rewrite !leEint_nat !succ_intE.
Qed.

Lemma succ_int_lt_mono (a b x y: int):
  (a < x)%O -> (b < y)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int_mono.
Qed.

Lemma succ_int_morph_lt (a b : int):
  (b < max_int_)%O -> (a < b)%O -> (succ a < succ b)%O.
Proof. by move=> b_max /[dup] a_b; rewrite !ltEint_nat !succ_intE //; apply/(lt_trans a_b). Qed.

Lemma succ_int_max_lt (a b : int):
  (a < max_int_)%O -> (b < max_int_)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_max b_max; case: leP.
- by rewrite -succ_int_mono //; case: leP.
- by move/ltW; rewrite -succ_int_mono //; case: leP.
Qed.

Lemma succ_int_lt_max (a b x y: int):
  (a < x)%O -> (b < y)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int_max_lt.
Qed.

Lemma nat_to_intS n : succ (nat_to_int n) = nat_to_int n.+1.
Proof.
apply/to_Z_inj; rewrite succ_spec /nat_to_int.
rewrite Znat.Nat2Z.inj_succ -BinInt.Z.add_1_r !of_Z_spec.
exact/Zdiv.Zplus_mod_idemp_l.
Qed.

Lemma ltiS_ltVeqS (x y : int) : (y < max_int_)%O -> (x < succ y)%O -> (x < y)%O \/ x = y.
Proof.
move=> y_max; rewrite !ltEint_nat succ_intE // ltnS leq_eqVlt.
by case/orP=> [/eqP/int_to_nat_inj ->|->]; [right|left].
Qed.

Lemma ltiSi (i : int): (i < max_int_)%O -> (i < succ i)%O.
Proof. by move=> ?; rewrite ltEint_nat succ_intE. Qed.

End SuccTheory.

(* -------------------------------------------------------------------- *)

Section PredTheory.

Lemma pred_intE (x : int) : (0 < x)%O -> Uint63.pred x = x.-1 :> nat.
Proof.
move=> x0; rewrite /int_to_nat pred_spec Zdiv.Zmod_small; last first; try split.
- rewrite Znat.Z2Nat.inj_sub; first exact:BinInt.Z.le_0_1.
  by rewrite /= Pnat.Pos2Nat.inj_1 PeanoNat.Nat.sub_1_r.
- move: x0; rewrite ltEint_nat /int_to_nat=> /ssrnat.ltP/Znat.Z2Nat.inj_lt.
  rewrite !to_Z_0 => /(_ (BinInt.Z.le_refl _)).
  case: (to_Z_bounded x)=> Z0_x _ /(_ Z0_x) Z0_ltx.
  exact/ZMicromega.lt_le_iff.
- apply/BinInt.Z.lt_sub_lt_add_r.
  case: (to_Z_bounded x)=> _; move/BinInt.Z.lt_trans; apply.
  exact/BinInt.Z.lt_add_pos_r/BinInt.Z.lt_0_1.
Qed.

Lemma pred_succ (x : int) : Uint63.pred (Uint63.succ x) = x.
Proof.
apply/to_Z_inj; rewrite pred_spec succ_spec Zdiv.Zminus_mod_idemp_l.
rewrite BinInt.Z.add_simpl_r.
by move/Zdiv.Zmod_small: (to_Z_bounded x).
Qed.

End PredTheory.

Section SubTheory.

Lemma sub_intE x y: (x < y)%O -> 
  int_to_nat (y - x) = int_to_nat y - int_to_nat x.
Proof.
rewrite ltEint /int_to_nat sub_spec /=.
move/ltbP=> xy; rewrite Zdiv.Zmod_small; first split.
- exact/Zorder.Zle_minus_le_0/BinInt.Z.lt_le_incl.
- case: (to_Z_bounded y)=> _ /(@BinInt.Z.sub_lt_mono_r _ _ (to_Z x)).
  move/BinInt.Z.lt_le_trans; apply; apply/BinInt.Z.le_sub_nonneg.
  by case: (to_Z_bounded x).
- by rewrite Znat.Z2Nat.inj_sub //; case: (to_Z_bounded x).
Qed.

End SubTheory.

Section AddTheory.

Lemma add_intE x y: int_to_nat x + int_to_nat y \in gtn int_threshold ->
  int_to_nat (x + y)%uint63 = x + y.
Proof.
move=> xy_max; rewrite /int_to_nat; rewrite add_spec.
move/wB_natE: xy_max; rewrite /wB_nat Znat.Nat2Z.inj_add.
rewrite /int_to_nat !Znat.Z2Nat.id; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)|].
move=> xy_max.
rewrite Zdiv.Zmod_small; first (split=> //; apply/BinInt.Z.add_nonneg_nonneg; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)]).
rewrite Znat.Z2Nat.inj_add //; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)].
Qed.

End AddTheory.

Section ExtraIntTheory.

Lemma nat_to_int_le (n : nat): ((nat_to_int n) <= n)%nat.
Proof.
rewrite /nat_to_int /int_to_nat of_Z_spec -[X in (_ <= X)%nat](Znat.Nat2Z.id n).
apply/ssrnat.leP/Znat.Z2Nat.inj_le; try exact: Zorder.Zle_0_nat.
- move/BinInt.Z.mod_pos_bound: wB_pos=> /(_ (BinInt.Z.of_nat n)).
  by case.
- apply/Zdiv.Zmod_le; [exact: wB_pos|exact:Zorder.Zle_0_nat].
Qed.

End ExtraIntTheory.

(* -------------------------------------------------------------------- *)


Section IRange.

Definition irange (i j : int) : seq int :=
  sort Order.le (enum [set x | (i <= x)%O && (x < j)%O ]).

Lemma irangee (i : int): irange i i = [::].
Proof.
rewrite /irange.
suff ->: ([set x | (i <= x)%O && (x < i)%O] = set0) by rewrite enum_set0.
by apply/setP=> z; rewrite !inE le_lt_asym.
Qed.

Lemma uniq_irange i j : uniq (irange i j).
Proof. by rewrite sort_uniq enum_uniq. Qed.

Lemma sorted_irange i j : sorted Order.lt (irange i j).
Proof. by rewrite sort_lt_sorted enum_uniq. Qed.

Lemma mem_irangeE i j x :
  (x \in irange i j) = (i <= x)%O && (x < j)%O.
Proof. by rewrite mem_sort mem_enum inE. Qed.

Lemma irange_cons i j: (i < j)%O -> irange i j = i :: irange (succ i) j.
Proof.
move=> ij; apply/le_sorted_eq.
- exact/sort_sorted/le_total.
- rewrite /= path_sortedE; first exact/le_trans.
  apply/andP; split; last exact/sort_sorted/le_total.
  apply/allP=> z; rewrite mem_irangeE=> /andP [+ _].
  rewrite !leEint_nat (succ_int_ltE ij); exact: ltnW.
- apply/uniq_perm; rewrite /= ?uniq_irange // ?andbT.
  + by rewrite mem_irangeE ij andbT leEint_nat (succ_int_ltE ij) ltnn.
  + move=> z; rewrite in_cons !mem_irangeE.
    case/boolP: (z == i)=> [/eqP ->|]; rewrite ?lexx ?ij //=.
    move=> z_n_i; congr andb; rewrite !leEint_nat (succ_int_ltE ij).
    rewrite leq_eqVlt eq_sym.
    case/boolP: (int_to_nat z == int_to_nat i)=> //=.
    by move/eqP=> /int_to_nat_inj /eqP; rewrite (negPf z_n_i).
Qed.



Lemma irange_cat i j k: (i <= j)%O -> (j <= k)%O ->
  irange i k = irange i j ++ irange j k.
Proof.
rewrite !le_eqVlt; case/orP=> [/eqP ->|]; rewrite ?irangee //.
move=> ij; case/orP=> [/eqP ->|]; rewrite ?irangee ?cats0 //.
move=> jk; apply/le_sorted_eq.
- exact/sort_sorted/le_total.
- apply/sorted_cat; first exact/le_trans; split; try exact/sort_sorted/le_total.
  apply/allrelP=> x y; rewrite !mem_irangeE.
  case/andP=> _ /ltW /le_trans + /andP [+ _].
  exact.
- apply/uniq_perm; first exact/uniq_irange.
  + rewrite cat_uniq !uniq_irange /= andbT -all_predC.
    apply/allP=> x /=; rewrite !mem_irangeE negb_and leNgt.
    by case/andP=> ->; rewrite orbT.
  + move=> x; rewrite mem_cat !mem_irangeE.
    case: (leP j x)=> /=; rewrite ?andbF ?orbF ?andbT /=.
    * by move/ltW: ij => /le_trans /[apply] -> /=.
    * by move: jk=> /[swap] /lt_trans /[apply] ->; rewrite andbT.
Qed.
  

  
Definition irange0 (j : int) : seq int := irange 0 j.

Lemma irange0_iota j: irange0 j = map nat_to_int (iota 0 j). 
Proof.
apply/lt_sorted_eq; first exact: sorted_irange.
- rewrite sorted_map.
  case E: (int_to_nat j)=> [|j'] //=.
  apply/(pathP 0%nat)=> i.
  rewrite size_iota=> /[dup] i_j'; rewrite -ltnS -E => /ltnW i_j.
  case: i i_j' i_j; first by (move=> /= ??; rewrite nth_iota).
  move=> n ?? /=; rewrite !nth_iota //; first exact/ltnW.
  rewrite !add1n ltEint_nat !nat_to_intK // inE.
  + apply/(@ltn_trans j)=> //; exact: int_thresholdP.
  + apply/(@leq_ltn_trans j)=> //; exact: int_thresholdP.
- move=> x; rewrite mem_irangeE le0x /=.
  apply/idP/idP.
  + move=> x_j; apply/mapP; exists (int_to_nat x); rewrite ?int_to_natK //.
    by rewrite mem_iota add0n leq0n /=; rewrite -ltEint_nat.
  + case/mapP=> y; rewrite mem_iota leq0n add0n /=; move=> y_j ->.
    rewrite ltEint_nat nat_to_intK // inE.
    apply/(@ltn_trans j)=> //; exact: int_thresholdP.
Qed.

Lemma size_irange0 j: seq.size (irange0 j) = j.
Proof. by rewrite irange0_iota size_map size_iota. Qed.

Lemma size_irange i j: seq.size (irange i j) = (j - i)%nat.
Proof.
case: (leP i j).
- move=> ij.
  move/(congr1 size): (irange_cat (le0x i) ij); rewrite size_cat !size_irange0.
  by move=> ->; rewrite addKn.
- move=> /[dup] ij; rewrite ltEint_nat=> /ltnW; rewrite -subn_eq0=> /eqP ->; apply/eqP/nilP.
  move: (mem_irangeE i j); case: (irange i j)=> //= a l.
  move=> /(_ a); rewrite in_cons eqxx /= => /esym/andP [] /le_lt_trans /[apply].
  by move/ltW; rewrite leNgt ij.
Qed.

Lemma nth_irange0 (j : int) k:
  (k < j)%nat -> nth 0%uint63 (irange0 j) k = nat_to_int k.
Proof.
move=> kj; rewrite irange0_iota (nth_map 0) ?size_iota //.
by rewrite nth_iota.
Qed.

Lemma nth_irange (i j : int) k:
  (k < j - i)%nat -> nth 0%uint63 (irange i j) k = nat_to_int (k + i).
Proof.
move=> kji; move: (leq_ltn_trans (leq0n k) kji); rewrite subn_gt0.
rewrite -ltEint_nat=> /ltW ij.
move: (irange_cat (le0x i) ij)=> /(congr1 (fun s=> nth 0%uint63 s (k + i))).
rewrite nth_irange0 addnC -?ltn_subRL // nth_cat size_irange0.
by rewrite ltnNge leq_addr /= addKn => ->.
Qed.

Lemma irange0_succ (i : int):
  (i < max_int_)%O -> irange0 (succ i) = rcons (irange0 i) i.
Proof.
move=> i_max; rewrite !irange0_iota succ_intE // iotaS_rcons add0n map_rcons.
by rewrite int_to_natK.
Qed. 

End IRange.

Module IFold.

Fixpoint ifold_ {T : Type} (n : nat) (f : int -> T -> T) (i M : int) (x : T) :=
  if (i =? M)%uint63 then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M x in
      let: (i, x) := ifold_ n f i M x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int -> T -> T) (i : int) (x : T) :=
  (ifold_ Uint63.size f 0 i x).2.

Definition iall (f : int -> bool) (i : int):=
  (ifold (fun i acc=> acc && f i) i true).

(* -------------------------------------------------------------------- *)
Definition iofold_ {T U: Type} (n : nat) (f : int -> T -> T + U) (i M : int) (x : T + U) :=
  ifold_ n (fun i r=> if r is inl a then f i a else r) i M x.
(*TODO : Replace by an actual interruption function*)
  
Definition iofold {T U: Type} (f : int -> T -> T + U) (i : int) (x : T + U):=
  (iofold_ Uint63.size f 0 i x).2.

End IFold.
Section Ifold.

Lemma ifold_E {S : Type} (n : nat) (f : int -> S -> S) (i M : int) (x : S):
  (i <= M)%nat ->
  let: j := ((int_to_nat i) + (2 ^ n) - 1)%nat in
  let: j' := if (j <= int_to_nat M)%nat then nat_to_int j else M in
  IFold.ifold_ n f i M x = (j', foldl (fun s t=> f t s) x (irange i j')).
Proof.
elim: n i x=> /= [i x | n IHn i x].
- rewrite expn0 addnK; case: ifP=> [/eqb_spec ->|]; rewrite ?leqnn ?int_to_natK ?irangee //=.
  by move=> _ ->; rewrite irangee.
- have leq_pow: forall y k, (y + 2 ^ k.+1 - 1 <= y)%nat = false.
  + move=> y k; rewrite leqNgt ltn_subRL addnC ltn_add2l.
    by apply/negbF; rewrite -{1}(expn0 2) ltn_exp2l.
  move=> iM; case: ifP=> [/eqb_spec ->|]; rewrite ?leq_pow ?irangee //.
  move/eqb_false_spec/eqP=> inM.
  have inM_nat: (int_to_nat i != int_to_nat M) by move: inM; apply/contra_neq=> /int_to_nat_inj.
  move: iM; rewrite leq_eqVlt (negPf inM_nat) /= -ltEint_nat => SiM.
  move: (IHn (Uint63.succ i) (f i x)); rewrite (succ_int_ltE SiM) -ltEint_nat=> /(_ SiM) ->.
  rewrite -addnBAC // subSS subn0.
  set N1 := (_ + 2 ^ n)%nat.
  case: ifP; last first. 
  + rewrite IHn /N1 //; case: n {IHn N1}; rewrite ?expn0 ?addn1 -?ltEint_nat ?SiM //.
    move=> n N1_leq; rewrite leq_pow.
    suff ->: (i + 2 ^ n.+2 - 1 <= M)%nat = false by rewrite (irange_cons SiM) irangee.
    move: N1_leq; apply/contraFF=> /(leq_trans _); apply.
    rewrite -addnBA ?expn_gt0 // leq_add2l [in X in (_ <= X)%nat]expnS.
    elim: n; rewrite ?expn1 // => n; rewrite -(@leq_pmul2l 2) // -expnS.
    move/leq_trans; apply; rewrite mulnBr !mul2n ?doubleS ?double0.
    exact/leq_sub2l.
  + move=> N1_M; have N1_thre: N1 \in gtn int_threshold by rewrite !inE; exact/(leq_ltn_trans N1_M)/int_thresholdP.
    rewrite IHn ?nat_to_intK //; set N2 := (i + 2 ^ n.+1 - _)%nat.
    have N1_N2_eq: (N1 + 2 ^ n - 1)%nat = N2.
    * rewrite -addnBA ?expn_gt0 // -addnA addnBA ?expn_gt0 // addnn -mul2n -expnS.
      by rewrite addnBA ?expn_gt0.
    have N1_N2_leq: (N1 <= N2)%nat by rewrite -N1_N2_eq -addnBA ?expn_gt0 // leq_addr.
    rewrite N1_N2_eq; congr pair; rewrite (@irange_cons i) /=.
      case: ifP=> // N2_M; rewrite ltEint_nat ?nat_to_intK ?inE; first apply/(leq_ltn_trans N2_M)/int_thresholdP.
      rewrite /N2 -addnBA ?expn_gt0 // -ltn_psubLR ?subnn subn_gt0 -[X in (X < _)%nat](expn0 2); exact: ltn_exp2l.
    rewrite -foldl_cat -irange_cat //.
    * by rewrite leEint_nat (succ_int_ltE SiM) ?nat_to_intK // -ltn_psubLR ?subnn expn_gt0.
    * rewrite leEint_nat nat_to_intK //; case: ifP=> // N2_M.
      rewrite ?nat_to_intK ?inE //; exact/(leq_ltn_trans N2_M)/int_thresholdP.
Qed.

Definition ifold {S : Type} (f : int -> S -> S) (M : int) (x : S):=
  foldl (fun s t=> f t s) x (irange0 M).

Lemma ifoldE {S : Type} (f : int -> S -> S) (M : int) (x : S):
  IFold.ifold f M x = ifold f M x.
Proof.
rewrite /IFold.ifold ifold_E ?leq0n //=.
move: (int_thresholdP M); rewrite /int_threshold; unlock.
rewrite add0n -add1n -leq_subRL ?expn_gt0 //.
rewrite leq_eqVlt ltnNge; case/orP=> [/eqP <-|]; rewrite ?leqnn ?int_to_natK //.
by move/negPf => ->.
Qed.

Definition iall (f : int -> bool) (M : int) := 
  all f (irange0 M).

Lemma iallE (f : int -> bool) (M : int):
  IFold.iall f M = iall f M.
Proof. 
rewrite /IFold.iall ifoldE /ifold /iall.
elim/last_ind: (irange0 M)=> // t h IH.
by rewrite foldl_rcons all_rcons andbC IH.
Qed.

Definition iofold {T U : Type} (f : int -> T -> T + U) (M : int) (x : T + U):=
  foldl (fun r i=> if r is inl t then f i t else r) x (irange0 M).

Lemma iofoldE {T U : Type} (f : int -> T -> T + U) (M : int) (x : T + U):
  IFold.iofold f M x = iofold f M x.
Proof.
rewrite /IFold.iofold /IFold.iofold_.
rewrite ifold_E ?leq0n //.
move: (int_thresholdP M); rewrite /int_threshold; unlock.
rewrite add0n -add1n -leq_subRL ?expn_gt0 //.
rewrite leq_eqVlt ltnNge; case/orP=> [/eqP <-|]; rewrite ?leqnn ?int_to_natK //.
by move/negPf=> -> /=.
Qed.

Lemma ifold_iter {T : Type} (f : T -> T) (n : int) (x : T):
  ifold (fun _=> f) n x = iter n f x.
Proof.
rewrite /ifold irange0_iota.
elim: (int_to_nat n)=> // k IH.
by rewrite iotaS_rcons add0n map_rcons foldl_rcons IH /=.
Qed.

End Ifold.
