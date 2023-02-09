(* -------------------------------------------------------------------- *)
(* This file content originates from the CoqEAL library.                *)
(*                                                                      *)
(*   https://github.com/coq-community/coqeal                            *)
(*                                                                      *)
(* The MIT License (MIT)                                                *)
(*                                                                      *)
(* Copyright (c) 2014  Guillaume Cano                                   *)
(* Copyright (c) 2014  Cyril Cohen                                      *)
(* Copyright (c) 2014  Maxime Dénès                                     *)
(* Copyright (c) 2014  Anders Mörtberg                                  *)
(* Copyright (c) 2014  Vincent Siles                                    *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From Bignums Require Import BigQ.
From Coq Require Import Uint63 PArray PArith PeanoNat.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import extra_array extra_int refinement.

Import Order.Theory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Code CoqEAL *)

Section Z2Int.

Definition Z2int (z : BinNums.Z) : ssrint.int :=
  match z with
  | Z0 => 0
  | Zpos p => ((Pos.to_nat p)%:Z)%R
  | Zneg n => (- (Pos.to_nat n)%:Z)%R
  end.

Definition int2Z (n : ssrint.int) : BinNums.Z :=
match n with
| Posz O => Z0
| Posz n => Zpos (Pos.of_nat n)
| Negz n => Zneg (Pos.of_nat n.+1)
end.

Lemma Z2int_inj x y : Z2int x = Z2int y -> x = y.
Proof.
rewrite /Z2int.
case x, y=>//.
{ move=>[] H.
  by rewrite -[Z0]/(BinInt.Z.of_nat 0%N) H Znat.positive_nat_Z. }
{ rewrite /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=; move: (Pos2Nat.is_pos p).
  by rewrite E => /ssrnat.ltP. }
{ by case; move/(congr1 BinInt.Z.of_nat); rewrite Znat.positive_nat_Z. }
{ by case; move/(congr1 BinInt.Z.of_nat); rewrite !Znat.positive_nat_Z. }
{ case E: (Pos.to_nat _)=>//=; case E': (Pos.to_nat _)=> //=.
  by move: (Pos2Nat.is_pos p); rewrite E; move/ssrnat.ltP. }
{ move/eqP; rewrite GRing.oppr_eq0=> /eqP; case=> E.
  by move/ssrnat.ltP: (Pos2Nat.is_pos p); rewrite E. }
{ case E: (Pos.to_nat _)=> //=.
  by move/ssrnat.ltP: (Pos2Nat.is_pos p); rewrite E.  }
{ move/GRing.oppr_inj; case=> /(congr1 BinInt.Z.of_nat).
  by rewrite !Znat.positive_nat_Z; case=> ->. }
Qed.

Lemma Z2int_opp n : Z2int (BinInt.Z.opp n) = (- (Z2int n))%R.
Proof. by case n=>// p /=; rewrite GRing.opprK. Qed.

Lemma Z2int_abs x : Z2int (BinInt.Z.abs x) = `|Z2int x|%nat.
Proof. by case: x => // p /=; rewrite abszN. Qed.


Lemma Z2int_add x y : Z2int (BinInt.Z.add x y) = (Z2int x + Z2int y)%R.
Proof.
case: x; case: y=> //=.
- by move=> ?; rewrite GRing.add0r.
- by move=> ?; rewrite GRing.addr0.
- by move=> ??; rewrite Pnat.Pos2Nat.inj_add.
- move=> q p; rewrite BinInt.Z.pos_sub_spec.
  case: BinPos.Pos.compare_spec=> /=.
  + move=> ->; by rewrite GRing.addrN.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    rewrite -subzn; last exact: ltnW.
    by rewrite GRing.opprB.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    by rewrite -subzn; last exact: ltnW.
- by move=> ?; rewrite GRing.addr0.
- move=> q p; rewrite BinInt.Z.pos_sub_spec.
  case: BinPos.Pos.compare_spec=> /=.
  + by move=> ->; rewrite GRing.addNr //.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    rewrite -subzn ?GRing.opprB; last exact: ltnW.
    by rewrite GRing.addrC.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt /ssrnat.ltP pq /Pnat.Pos2Nat.inj_sub ->. 
    rewrite -subzn; last exact: ltnW.
    by rewrite GRing.addrC.
- move=> p q; rewrite Pnat.Pos2Nat.inj_add plusE PoszD.
  by rewrite -GRing.opprB GRing.opprK GRing.addrC.
Qed.

Lemma Z2int_mul_nat_of_pos (x : BinNums.Z) (y : positive) :
  (Z2int x * Pos.to_nat y)%R = Z2int (BinInt.Z.mul x (BinNums.Zpos y)).
Proof.
rewrite /Z2int; case Ex: x.
{ by rewrite GRing.mul0r BinInt.Z.mul_0_l. }
{ by rewrite /= Pos2Nat.inj_mul multE . }
by rewrite /= GRing.mulNr Pos2Nat.inj_mul multE.
Qed.

Lemma Z2int_mul x y : Z2int (BinInt.Z.mul x y) = (Z2int x * Z2int y)%R.
Proof.
case y=>/=.
{ by rewrite GRing.mulr0 BinInt.Z.mul_0_r. }
{ by move=> p; rewrite Z2int_mul_nat_of_pos. }
move=> p.
rewrite GRing.mulrN Z2int_mul_nat_of_pos -Z2int_opp.
by rewrite BinInt.Z.opp_eq_mul_m1 -BinInt.Z.mul_assoc -BinInt.Z.opp_eq_mul_m1 /=.
Qed.

Lemma divE x y : Nat.div x y = divn x y.
Proof.
case: y => [//|y].
rewrite /Nat.div.
move: (Nat.divmod_spec x y 0 y).
case: Nat.divmod => q r /(_ (le_n _)) [].
rewrite Nat.mul_0_r Nat.sub_diag !Nat.add_0_r Nat.mul_comm => + Hr /=.
rewrite multE minusE plusE => /(f_equal (fun x => divn x y.+1)) ->.
rewrite divnMDl // divn_small ?addn0 //.
rewrite ltn_subLR; [|exact/ssrnat.leP].
  by rewrite -addSnnS addnC addnS ltnS leq_addr.
Qed.

Lemma Z2int_div x y : BinInt.Z.le Z0 x -> BinInt.Z.le Z0 y ->
  Z2int (BinInt.Z.div x y) = divz (Z2int x) (Z2int y).
Proof.
Admitted.
(* case: x => [|x|//] _; [by rewrite intdiv.div0z|].
case: y => [|y|//] _; [by rewrite intdiv.divz0|].
rewrite -!Znat.positive_nat_Z -Znat.Nat2Z.inj_div.
rewrite !Znat.positive_nat_Z /= /divz gtr0_sgz ?mul1r; last first.
{ by move/ssrnat.ltP: (Pos2Nat.is_pos y). }
rewrite divE absz_nat /Z2int.
move: (Zorder.Zle_0_nat (Pos.to_nat x %/ Pos.to_nat y)).
rewrite -[X in _ = Posz X]Znat.Nat2Z.id mul1n.
by case: BinInt.Z.of_nat => //=.
Qed. *)

Lemma Z2int_le x y : (Z2int x <= Z2int y)%R <-> BinInt.Z.le x y.
Proof.
rewrite /Z2int; case Ex: x; case Ey: y=> //.
{ rewrite Num.Theory.oppr_ge0; split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply/negP; rewrite -ltNge; exact/ssrnat.ltP/Pos2Nat.is_pos. }
{ split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply/negP; rewrite -ltNge; exact/ssrnat.ltP/Pos2Nat.is_pos. }
{ rewrite /Num.Def.ler /=.
  by rewrite -!Znat.positive_nat_Z -Znat.Nat2Z.inj_le; split => /ssrnat.leP. }
{ split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply /negP; rewrite -ltNge.
  apply: (@lt_trans _ _ 0%R); rewrite ?Num.Theory.oppr_lt0; 
    apply/ssrnat.ltP/Pos2Nat.is_pos. }
{ rewrite Num.Theory.oppr_le0; split; by rewrite /BinInt.Z.le. }
{ split=>_; [by rewrite /BinInt.Z.le|].
  apply: (@le_trans _ _ 0%R); [apply Num.Theory.oppr_le0|apply ltW].
  exact/ssrnat.ltP/Pos2Nat.is_pos. }
rewrite Num.Theory.ler_opp2; split.
{ rewrite /BinInt.Z.le /BinInt.Z.compare /Num.Def.ler /= => /ssrnat.leP.
  by rewrite -Pos.compare_antisym -Pos2Nat.inj_le -Pos.compare_le_iff. }
rewrite /BinInt.Z.le /BinInt.Z.compare /Num.Def.ler /=.
rewrite -Pos.compare_antisym => H; apply/ssrnat.leP.
by rewrite -Pos2Nat.inj_le -Pos.compare_le_iff.
Qed.

Lemma Z2int_lt x y : (Z2int x < Z2int y)%R <-> BinInt.Z.lt x y.
Proof.
rewrite -lez_addr1 -[GRing.one _]/(Z2int BinInt.Z.one) -Z2int_add Z2int_le.
rewrite /BinInt.Z.one BinInt.Z.add_1_r; exact: BinInt.Z.le_succ_l.
Qed.

Lemma nat_of_pos_Z_to_pos x : Pos.to_nat x = `|Z2int (Zpos x)|%N.
Proof. by rewrite /absz /Z2int. Qed.

Lemma Zabs_natE n : BinInt.Z.abs_nat n = `|Z2int n|%N.
Proof.
case: n => //= p.
by rewrite abszN absz_nat.
Qed.

Lemma Z2int_Z_of_nat n : Z2int (BinInt.Z.of_nat n) = n.
Proof.
by case: n => //= n; rewrite Pos.of_nat_succ Nat2Pos.id.
Qed.

Lemma dvdnP m n : reflect 
  (BinInt.Z.divide (BinInt.Z.of_nat m) (BinInt.Z.of_nat n)) (m %| n).
Proof.
apply: (iffP idP) => H.
{ rewrite dvdn_eq in H; rewrite -(eqP H) /BinInt.Z.divide; exists (BinInt.Z.of_nat (n %/ m)).
  by rewrite Znat.Nat2Z.inj_mul. }
{ have [q Hq] := H; apply/dvdnP; exists `|Z2int q|%N; apply/Znat.Nat2Z.inj.
  have [Zq|NZq] := ZArith_dec.Z_zerop q.
  { by rewrite Zq /= in Hq *. }
  case: m Hq H => [|m] Hq H.
  { by rewrite BinInt.Zmult_comm /= in Hq; rewrite mulnC /=. }
  rewrite Znat.Nat2Z.inj_mul -Zabs_natE Znat.Zabs2Nat.id_abs BinInt.Z.abs_eq //.
  (* have H0 : (0 <= BinInt.Z.mul q (BinInt.Z.of_nat m.+1)). by rewrite -Hq; apply Zorder.Zle_0_nat. *)
  apply: (Zorder.Zmult_le_0_reg_r (BinInt.Z.of_nat m.+1)).
  - apply/BinInt.Z.lt_gt; rewrite -/(BinInt.Z.of_nat 0).
    exact/Znat.inj_lt/ssrnat.ltP.
  - rewrite -Hq; exact: Zorder.Zle_0_nat. }
Qed.

Lemma ZgcdE n d : BinInt.Z.gcd n (Zpos d) = 
  BinInt.Z.of_nat (div.gcdn `|Z2int n| (Pos.to_nat d)).
Proof.
apply: BinInt.Z.gcd_unique.
{ exact: Zorder.Zle_0_nat. }
{ apply/BinInt.Z.divide_abs_r; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE dvdn_gcdl. }
{ apply/BinInt.Z.divide_abs_r; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE /= dvdn_gcdr. }
move=> q Hn Hd; apply/BinInt.Z.divide_abs_l; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
rewrite Zabs_natE dvdn_gcd.
apply/andP; split; apply/dvdnP; rewrite -!Zabs_natE !Znat.Zabs2Nat.id_abs.
{ by apply/BinInt.Z.divide_abs_l/BinInt.Z.divide_abs_r. }
{ by apply/BinInt.Z.divide_abs_l; rewrite Znat.positive_nat_Z. }
Qed.

Lemma ZgcdE' n m : BinInt.Z.gcd n m = BinInt.Z.of_nat (gcdn `|Z2int n| `|Z2int m|).
Proof.
case m.
{ rewrite BinInt.Z.gcd_0_r {2}/absz {2}/Z2int /= gcdn0 -Znat.Zabs2Nat.id_abs; f_equal.
  rewrite /BinInt.Z.abs_nat /absz /Z2int.
  case n=>// p; rewrite //.
  case (Pos.to_nat _); [by rewrite GRing.oppr0|move=> n'].
  by rewrite /GRing.opp /=. }
{ by move=> p; rewrite ZgcdE nat_of_pos_Z_to_pos. }
by move=> p; rewrite -BinInt.Z.gcd_opp_r /= ZgcdE abszN /absz.
Qed.


Lemma Z_ggcd_1_r n : BinInt.Z.ggcd n (Zpos 1) = (Zpos 1, (n, Zpos 1)).
Proof.
move: (BinInt.Z.ggcd_gcd n (Zpos 1)) (BinInt.Z.ggcd_correct_divisors n (Zpos 1)). 
rewrite BinInt.Z.gcd_1_r.
case (BinInt.Z.ggcd _ _)=> g ab /= ->; case ab=> a b [].
by rewrite !BinInt.Z.mul_1_l => <- <-.
Qed.

Lemma Z_ggcd_coprime a b :
  let '(g, (a', b')) := BinInt.Z.ggcd a b in
  g <> Z0 -> coprime `|Z2int a'| `|Z2int b'|.
Proof.
move: (BinInt.Z.ggcd_gcd a b) (BinInt.Z.ggcd_correct_divisors a b).
case (BinInt.Z.ggcd _ _)=> g ab; case ab=> a' b' /= Hg [] Ha Hb Pg.
rewrite /coprime; apply/eqP /Znat.Nat2Z.inj; rewrite -ZgcdE' /=.
suff ->: a' = (BinInt.Z.div a g).
{ suff ->: b' = (BinInt.Z.div b g); [by apply BinInt.Z.gcd_div_gcd|].
  by rewrite Hb BinInt.Z.mul_comm Zdiv.Z_div_mult_full. }
by rewrite Ha BinInt.Z.mul_comm Zdiv.Z_div_mult_full.
Qed.

Lemma Z2int_lcm x y : BinInt.Z.le Z0 x -> BinInt.Z.le Z0 y ->
  Z2int (BinInt.Z.lcm x y) = lcmn `|Z2int x| `|Z2int y|.
Proof.
case: x => [|x|//] _; [by rewrite /= lcm0n|].
case: y => [|y|//] _; [by rewrite /= lcmn0|].
rewrite /BinInt.Z.lcm Z2int_abs Z2int_mul Z2int_div //.
rewrite ZgcdE' abszM; apply: f_equal; apply/eqP.
rewrite -(@eqn_pmul2r (gcdn `|Z2int (Zpos x)| `|Z2int (Zpos y)|)); last first.
{ rewrite gcdn_gt0; apply/orP; left; rewrite absz_gt0 /= eqz_nat.
  exact/lt0n_neq0/ssrnat.ltP/Pos2Nat.is_pos. }
rewrite muln_lcm_gcd.
rewrite -(absz_nat (gcdn _ _)) -mulnA -abszM.
rewrite Z2int_Z_of_nat /=.
  by rewrite intdiv.divzK // /mem /in_mem /intdiv.dvdz /= dvdn_gcdr.
Qed.

Lemma Z2int_Zpos_neq0 x: Z2int (Zpos x) != 0%R.
Proof. 
rewrite /=; apply/negP=> /eqP; case=> E.
by move/ssrnat.ltP: (Pos2Nat.is_pos x); rewrite E.
Qed.

End Z2Int.

Section BigQRat.


Definition bigQ2rat_def (bq : bigQ) :=
  let q := Qreduction.Qred [bq]%bigQ in
  ((Z2int (QArith_base.Qnum q))%:Q / (Z2int (Zpos (QArith_base.Qden q)))%:Q)%R.

Definition rat_bigQ (b : bigQ) (r : rat) := bigQ2rat_def b = r.

Lemma rat_bigQ0: rat_bigQ 0%bigQ 0%R.
Proof. exact: val_inj. Qed.

Lemma rat_bigQ1: rat_bigQ 1%bigQ 1%R.
Proof. exact: val_inj. Qed.

Lemma rat_bigQ_opp : (rat_bigQ =~> rat_bigQ) BigQ.opp (@GRing.opp _).
Proof.
rewrite /rat_bigQ /bigQ2rat_def => b r. 
rewrite BigQ.strong_spec_opp Qreduction.Qred_opp [in LHS]/QArith_base.Qnum /=.
rewrite Z2int_opp mulrNz GRing.mulNr.
by move=> <-.
Qed.

Lemma Z2int_Qred n d :
  ((Z2int (QArith_base.Qnum (Qreduction.Qred (QArith_base.Qmake n d))))%:Q /
    (Pos.to_nat (QArith_base.Qden (Qreduction.Qred (QArith_base.Qmake n d))))%:Q
   = (Z2int n)%:Q / (Z2int (Zpos d))%:Q)%R.
Proof.
rewrite -(fracqE (Z2int n, Z2int (Zpos d))) -[RHS]divq_num_den.
rewrite /Qreduction.Qred.
move: (BinInt.Z.ggcd_gcd n (Zpos d)) (BinInt.Z.ggcd_correct_divisors n (Zpos d)).
move: (Z_ggcd_coprime n (Zpos d)).
case: BinInt.Z.ggcd => g [n' d'] /=.
case: g => [|g|g].
{ by move=> _ _ [_]; rewrite BinInt.Z.mul_0_l. }
{ move=> coprime_n'_d' => _ [->].
  rewrite (nat_of_pos_Z_to_pos d) => /[dup] posd' ->.
  have d'n0 : (`|Z2int d'| != 0)%R.
  { rewrite Num.Theory.normr_eq0.
    case: d' posd' {coprime_n'_d'} => // d' _.
    exact: Z2int_Zpos_neq0. }
  rewrite !Z2int_mul abszM PoszM gez0_abs; [|by rewrite -[0%R]/(Z2int Z0) Z2int_le].
  rewrite fracqMM ?Posz_nat_of_pos_neq0 ?abszE; last exact: Z2int_Zpos_neq0.
  move: (@valq_frac (Z2int n', `|Z2int d'|%R) d'n0).
  rewrite scalqE // GRing.mul1r => [[neq deq]].
  have -> : Pos.to_nat (BinInt.Z.to_pos d') = `|Z2int d'|%R :> ssrint.int.
  { rewrite nat_of_pos_Z_to_pos BinInt.Z2Pos.id ?abszE //.
    by case: d' posd' {coprime_n'_d' d'n0 neq deq}. }
  rewrite [X in (X%:~R / _)%R]neq [X in (_ / X%:~R)%R]deq.
  rewrite (_ : gcdn _ _ = 1%nat) ?GRing.mul1r //; exact/eqP/coprime_n'_d'. }
by move: (BinInt.Z.gcd_nonneg n (Zpos d)) => + _ => /[swap] <-.
Qed.

Lemma BigQ_red_den_nonzero q :
  match BigQ.red q with BigQ.Qz _ => True | BigQ.Qq _ d => [d]%bigN <> Z0 end.
Proof.
case: q => [//|n d] /=.
rewrite /BigQ.norm.
rewrite BigN.spec_compare.
case: BinInt.Z.compare_spec => [| |//] Hgcd.
{ rewrite /BigQ.check_int BigN.spec_compare.
  case BinInt.Z.compare_spec => [//| |//] Hd.
  apply: BigNumPrelude.Zlt0_not_eq.
  move: Hd; exact: BinInt.Z.lt_trans. }
rewrite /BigQ.check_int BigN.spec_compare.
case BinInt.Z.compare_spec => [//| |//] Hd.
apply: BigNumPrelude.Zlt0_not_eq.
move: Hd; exact: BinInt.Z.lt_trans.
Qed.

Lemma ratBigQ_red x y : rat_bigQ y x ->
  match BigQ.red y with
  | BigQ.Qz n => numq x = Z2int [n]%bigZ /\ denq x = 1%R
  | BigQ.Qq n d => numq x = Z2int [n]%bigZ /\ denq x = Z2int [d]%bigN
  end.
Proof.
case: (ratP x) => nx dx nx_dx_coprime {x}.
rewrite /rat_bigQ /bigQ2rat_def -BigQ.strong_spec_red.
have ry_red : Qreduction.Qred [BigQ.red y]%bigQ = [BigQ.red y]%bigQ.
{ by rewrite BigQ.strong_spec_red Qcanon.Qred_involutive. }
have ry_dneq0 := BigQ_red_den_nonzero y.
case: (BigQ.red y) ry_dneq0 ry_red => [ny _ _|ny dy dy_neq0].
{ rewrite /BigQ.to_Q /QArith_base.Qnum /QArith_base.Qden GRing.mulr1.
  move=> /(f_equal ( *%R^~ dx.+1%:~R)%R).
  rewrite GRing.mulfVK ?mulrz_neq0 // -intrM => /intr_inj nx_eq.
  have dx_1 : (dx.+1 = 1)%nat.
  { by move: nx_dx_coprime => /eqP <-; rewrite -nx_eq abszM /= gcdnC gcdnMl. }
    by rewrite -nx_eq dx_1 GRing.mulr1. }
rewrite /BigQ.to_Q ifF ?BigN.spec_eqb ?BinInt.Z.eqb_neq //.
rewrite Qcanon.Qred_iff ZgcdE -[Zpos 1]/(BinInt.Z.of_nat 1%nat) => /Znat.Nat2Z.inj.
rewrite /QArith_base.Qnum /QArith_base.Qden nat_of_pos_Z_to_pos => /eqP ny_dy_coprime.
move=> /eqP; rewrite rat_eqE !coprimeq_num // !coprimeq_den //=.
rewrite !Num.Theory.gtr0_sg //; last exact/ssrnat.ltP/Pos2Nat.is_pos.
rewrite !GRing.mul1r => /andP[/eqP <-].
rewrite ifF; [|exact/eqP/eqP/Num.Theory.lt0r_neq0/ssrnat.ltP/Pos2Nat.is_pos].
rewrite -!abszE !absz_nat => /eqP[<-]; split=> [//|].
rewrite -[LHS]/(Z2int (Zpos (BinInt.Z.to_pos [dy]%bigN))) BinInt.Z2Pos.id //.
exact: BigQ.N_to_Z_pos.
Qed.

Lemma rat_bigQ_add: (rat_bigQ =~> rat_bigQ =~> rat_bigQ) BigQ.add (@GRing.add _).
Proof.
move=> p x + q y.
rewrite /rat_bigQ /bigQ2rat_def; move=> <- <-.
rewrite (Qreduction.Qred_complete _ _ (BigQ.spec_add _ _)).
case: (BigQ.to_Q p) => np dp {p}.
case: (BigQ.to_Q q) => nq dq {q}.
rewrite /QArith_base.Qplus !Z2int_Qred.
rewrite Z2int_add !Z2int_mul /= Pos2Nat.inj_mul multE.
rewrite intrD PoszM !intrM.
rewrite [RHS]GRing.addf_div // intq_eq0;
  exact/lt0n_neq0/ssrnat.ltP/Pos2Nat.is_pos.
Qed.

Lemma rat_bigQ_mul: (rat_bigQ =~> rat_bigQ =~> rat_bigQ) BigQ.mul (@GRing.mul _).
Proof.
move=> p x + q y.
rewrite /rat_bigQ /bigQ2rat_def; move=> <- <-.
rewrite (Qreduction.Qred_complete _ _ (BigQ.spec_mul _ _)).
case: (BigQ.to_Q p) => np dp {p}.
case: (BigQ.to_Q q) => nq dq {q}.
rewrite /QArith_base.Qmult !Z2int_Qred /=.
rewrite Z2int_mul Pos2Nat.inj_mul multE.
rewrite PoszM !intrM.
by rewrite [RHS]GRing.mulf_div.
Qed.

Lemma rat_bigQ_lt: (rat_bigQ =~> rat_bigQ =~> iff) BigQ.lt (@Order.lt _ _).
Proof.
move=> p x + q y.
rewrite /rat_bigQ /bigQ2rat_def; move=> <- <-.
rewrite /BigQ.lt.
case: (BigQ.to_Q p) => np dp {p}.
case: (BigQ.to_Q q) => nq dq {q}.
rewrite !Z2int_Qred.
rewrite Num.Theory.ltr_pdivr_mulr ?ltr0z /=;
  last exact/ssrnat.ltP/Pos2Nat.is_pos.
rewrite GRing.mulrAC Num.Theory.ltr_pdivl_mulr ?ltr0z; 
  last exact/ssrnat.ltP/Pos2Nat.is_pos.
rewrite !nat_of_pos_Z_to_pos.
rewrite !gez0_abs /=; try apply/ltnW/ssrnat.ltP/Pos2Nat.is_pos.
rewrite -!intrM ltr_int.
rewrite /QArith_base.Qlt /= -/(Z2int (Zpos dp)) -/(Z2int (Zpos dq)).
rewrite -!Z2int_mul.
case: ltP.
{ move=> /(proj1 (Z2int_lt _ _)); rewrite /BinInt.Z.lt=> ->; split=> //. }
move=> /(proj1 (Z2int_le _ _)) /BinInt.Z.le_ngt h.
by split=> //.
Qed.

Lemma rat_bigQ_eq:
  (rat_bigQ =~> rat_bigQ =~> eq) BigQ.eqb eq_op.
Proof.
move=> x X <- y Y <-; rewrite /bigQ2rat_def.
rewrite /BigQ.eqb BigQ.spec_eq_bool.
apply/idP/idP.
- by move/QArith_base.Qeq_bool_iff/Qreduction.Qred_complete=> ->.
- move/eqP; case: [x]%bigQ=> xn xd.
  case: [y]%bigQ=> yn yd /=; rewrite !Z2int_Qred /=.
  move/eqP; rewrite GRing.eqr_div.
  + move/eqP=> h; apply/QArith_base.Qeq_bool_iff.
    rewrite /QArith_base.Qeq /=.
    apply/Z2int_inj; rewrite !Z2int_mul /=.
    by move:h; rewrite -!intrM; move/intr_inj.
  + apply/negP=> /eqP; rewrite -rat0.
    move/intr_inj; move: (Pos2Nat.is_pos xd).
    by elim: (Pos.to_nat xd)=> // /Nat.lt_irrefl.
  + apply/negP=> /eqP; rewrite -rat0.
    move/intr_inj; move: (Pos2Nat.is_pos yd).
    by elim: (Pos.to_nat yd)=> // /Nat.lt_irrefl.
Qed.

Lemma rat_bigQ_injr: rel_spec rat_bigQ eq.
Proof. by move=> ??? <- <-. Qed.

(* Lemma rat_bigQEl b b' r:
  rat_bigQ b r -> (b == b')%bigQ -> rat_bigQ b' r.
Proof.
rewrite /rat_bigQ /bigQ2rat_def /BigQ.eq.
case: [b]%bigQ=> n d.
case: [b']%bigQ=> n' d'.
by move=> h /Qreduction.Qred_complete <-.
Qed. *)

(* Lemma rat_bigQEr b r r':
  rat_bigQ b r -> r = r' -> rat_bigQ b r'.
Proof. by move=> ? <-. Qed. *)

End BigQRat.

Module BigQUtils.

Definition delta_line (n k : Uint63.int) (x : bigQ):= (make n 0%bigQ).[k <- x].

Definition perturbed_line (n k : Uint63.int) (b x : bigQ):=
  (make (Uint63.succ n) 0%bigQ).[0%uint63 <- b].[Uint63.succ k <- x].

Definition bigQ_dot (x y : array bigQ) : bigQ :=
  PArrayUtils.array_dot BigQ.add BigQ.mul 0%bigQ x y.

Definition bigQ_mul_row_mx (a : array bigQ) (x : array (array bigQ)) :=
  PArrayUtils.array_mul_row_mx BigQ.add BigQ.mul 0%bigQ a x.

Definition bigQ_mulmx (m n : array (array bigQ)):=
  PArrayUtils.array_mulmx BigQ.add BigQ.mul 0%bigQ m n.

Definition BQlex_order (x y : array bigQ) :=
  PArrayUtils.lex_array_rel BigQ.compare x y.

Definition BQltx_order (x y : array bigQ) :=
  PArrayUtils.ltx_array_rel BigQ.compare x y.

Definition eq_array_bigQ (a b : array bigQ) :=
  PArrayUtils.eq_array_rel (BigQ.eqb) a b.

Definition bigQ_scal_rV (lambda : bigQ) (x : array bigQ):=
  PArrayUtils.map (fun v=> BigQ.mul lambda v) x.

Definition bigQ_add_rV (x y : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (x.[i] + y.[i])%bigQ) (length x) (0%bigQ).

Definition bigQ_ge0 (x : bigQ):= match (0 ?= x)%bigQ with
  |Gt => false
  |_ => true
end.

Definition weighted_lines (v : array bigQ) (A : array (array bigQ)):=
  PArrayUtils.fold_pair
    (fun v_i A_i acc => bigQ_add_rV acc (bigQ_scal_rV v_i A_i))
  v A (make (length A.[0%uint63]) 0%bigQ).

End BigQUtils.

Section BigQComputations.

Definition bigQ_dot (x y : array bigQ) : bigQ :=
  array_dot BigQ.add BigQ.mul 0%bigQ x y.

Definition bigQ_mul_row_mx (a : array bigQ) (x : array (array bigQ)) :=
  array_mul_row_mx BigQ.add BigQ.mul 0%bigQ a x.

Definition bigQ_mulmx (m n : array (array bigQ)):=
  array_mulmx BigQ.add BigQ.mul 0%bigQ m n.

Definition BQlex_order (x y : array bigQ) :=
  lex_array_rel BigQ.compare x y.

Definition BQltx_order (x y : array bigQ) :=
  ltx_array_rel x y BigQ.compare.

Definition eq_array_bigQ (a b : array bigQ) :=
  eq_array_rel (BigQ.eqb) a b.

Definition bigQ_scal_rV (lambda : bigQ) (x : array bigQ):=
  arr_map (fun v=> BigQ.mul lambda v) x.

Definition bigQ_add_rV (x y : array bigQ):=
  arr_mk_fun (fun i=> (x.[i] + y.[i])%bigQ) (length x) (0%bigQ).

Definition weighted_lines (v : array bigQ) (A : array (array bigQ)):=
  arr_fold_pair
    (fun v_i A_i acc => bigQ_add_rV acc (bigQ_scal_rV v_i A_i))
    v A (make (length A.[0%uint63]) 0%bigQ).

Section Equiv.

Lemma bigQ_dotE (x y : array bigQ):
  BigQUtils.bigQ_dot x y = bigQ_dot x y.
Proof. exact: array_dotE. Qed.

Lemma bigQ_mul_row_mxE (a : array bigQ) (x : array (array bigQ)):
  BigQUtils.bigQ_mul_row_mx a x = bigQ_mul_row_mx a x.
Proof. exact: array_mul_row_mxE. Qed.

Lemma bigQ_mulmxE (m n : array (array bigQ)):
  BigQUtils.bigQ_mulmx m n = bigQ_mulmx m n.
Proof. exact: array_mulmxE. Qed.

Lemma BQlex_orderE (x y : array bigQ):
  BigQUtils.BQlex_order x y = BQlex_order x y.
Proof. exact: lex_array_relE. Qed.

Lemma BQltx_orderE (x y : array bigQ):
  BigQUtils.BQltx_order x y = BQltx_order x y.
Proof. exact: ltx_array_relE. Qed.

Lemma eq_array_bigQE (a b : array bigQ):
  BigQUtils.eq_array_bigQ a b = eq_array_bigQ a b.
Proof. exact: eq_array_relE. Qed.

Lemma bigQ_scal_rVE (lambda : bigQ) (x : array bigQ):
  BigQUtils.bigQ_scal_rV lambda x = bigQ_scal_rV lambda x.
Proof. by rewrite /BigQUtils.bigQ_scal_rV arr_mapE. Qed.

Lemma bigQ_add_rVE (x y : array bigQ):
  BigQUtils.bigQ_add_rV x y = bigQ_add_rV x y.
Proof. by rewrite /BigQUtils.bigQ_add_rV arr_mk_funE. Qed.

Lemma weighted_linesE (v : array bigQ) (A : array (array bigQ)):
  BigQUtils.weighted_lines v A = weighted_lines v A.
Proof.
rewrite /BigQUtils.weighted_lines arr_fold_pairE; apply/eq_foldl=> ??.
by rewrite bigQ_add_rVE bigQ_scal_rVE.
Qed.

End Equiv.
Section Proofs.

Lemma BQltx_order_trans: transitive BQltx_order.
Proof.
move=> y x z /ltx_array_relP [len_xy +] /ltx_array_relP [len_yz +].
case=> j [j_lenx xy_i_eq xy_j_lt] [j'] [j'_leny yz_i_eq yz_j_lt].
apply/ltx_array_relP; split; rewrite ?len_xy //.
exists (Order.min j j'); split; rewrite ?lt_minl ?j'_leny ?orbT //.
- move=> i; rewrite lt_minr=> /andP [/xy_i_eq + /yz_i_eq].
  by case: BigQ.compare_spec=> // ->.
- case: ltgtP.
  + by move/yz_i_eq; case: BigQ.compare_spec=> // <-.
  + by move/xy_i_eq; case: BigQ.compare_spec=> // ->.
  + move=> j_eq; move: xy_j_lt yz_j_lt; rewrite j_eq.
    do 2! case: BigQ.compare_spec=> //.
    move/[swap]/QArith_base.Qlt_trans=> /[apply] + _ _.
    by rewrite BigQ.spec_compare=> /QArith_base.Qlt_alt.
Qed.

Lemma BQltx_order_neq x y: BQltx_order x y -> ~~ eq_array_bigQ x y.
Proof.
case/ltx_array_relP=> len_xy [k [k_len k_eq k_lt]].
apply/negP=> /eq_array_relP [_] /(_ k k_len).
move: k_lt=> /[swap] /BigQ.eqb_eq xy_k.
case: BigQ.compare_spec=> //; rewrite xy_k.
by case: BigQ.lt_strorder=> + _; move=> /[apply].
Qed.

Lemma eq_array_bigQC x y: eq_array_bigQ x y = eq_array_bigQ y x.
Proof.
apply/eq_array_rel_sym=> a b. rewrite /BigQ.eqb !BigQ.spec_eq_bool.
by apply/idP/idP; apply/QArith_base.Qeq_bool_sym.
Qed.

End Proofs.
End BigQComputations.

Section BQR.

Lemma rat_bigQ_ge0 x X: rat_bigQ x X -> 
  BigQUtils.bigQ_ge0 x = (0 <= X)%R.
Proof.
move=> xX; rewrite /BigQUtils.bigQ_ge0.
case: BigQ.compare_spec.
- move/BigQ.eqb_eq. move: (rat_bigQ_eq rat_bigQ0 xX).
  by rewrite /BigQ.eqb=> -> /eqP ->; rewrite lexx.
- by move/rat_bigQ_lt=> /(_ _ _ rat_bigQ0 xX)/ltW ->.
- move/rat_bigQ_lt=> /(_ _ _ xX rat_bigQ0).
  by rewrite ltNge=> /negPf ->.
Qed.

End BQR.

Section RelArrayBQR.

Definition rat_dot := @array_dot [realFieldType of rat] +%R *%R 0%R.
Definition rat_mul_row_mx :=
  @array_mul_row_mx [realFieldType of rat] +%R *%R 0%R.
Definition rat_mulmx :=
  @array_mulmx [realFieldType of rat] +%R *%R 0%R.

Lemma BQR_array_dot: 
  (rel_array rat_bigQ =~> rel_array rat_bigQ =~> rat_bigQ)
    bigQ_dot rat_dot.
Proof.
rewrite /array_dot /bigQ_dot.
move=> a A aA b B bB.
apply: (rel_array_fold_pair)=> //; [ |exact:aA|exact:bB].
move=> ?????????; apply/rat_bigQ_add=> //; exact/rat_bigQ_mul.
Qed.

Definition rat_compare (x y : rat):=
  if (x < y)%R then Lt else if (x == y) then Eq else Gt.

Lemma BQR_array_lex: (rel_array rat_bigQ =~> rel_array rat_bigQ =~> eq)
  BQlex_order (lex_array_rel rat_compare).
Proof.
apply/rel_array_lex=> x X xX y Y yY.
case: BigQ.compare_spec.
- move/BigQ.eqb_eq; rewrite -/BigQ.eqb (rat_bigQ_eq xX yY).
  by move/eqP=> ->; rewrite /rat_compare ltxx eqxx.
- move/rat_bigQ_lt=> /(_ _ _ xX yY); rewrite /rat_compare.
  by move=> ->.
- move/rat_bigQ_lt=> /(_ _ _ yY xX); rewrite /rat_compare.
  by rewrite ltNge le_eqVlt negb_or=> /andP [/negPf -> /negPf ->].
Qed.

Lemma BQR_array_eq: (rel_array rat_bigQ =~> rel_array rat_bigQ =~> eq)
  eq_array_bigQ (eq_array_rel eq_op).
Proof. exact/rel_array_eq/rat_bigQ_eq. Qed.

Lemma BQR_array_mul_rV_mx:
  (rel_array rat_bigQ =~> rel_array (rel_array rat_bigQ) 
    =~> rel_array rat_bigQ)
    bigQ_mul_row_mx rat_mul_row_mx.
Proof. by apply:rel_array_mul_row_mx; [exact:rat_bigQ_add|exact:rat_bigQ_mul|]. Qed.

Definition rat_add_rV (X Y : array rat):=
  (arr_mk_fun (fun i=> (get X i + get Y i)%R) (length X) (0%R)).

Lemma BQR_array_add x X y Y:
  (length X = length Y) ->
  rel_array rat_bigQ x X -> rel_array rat_bigQ y Y -> 
  rel_array rat_bigQ (bigQ_add_rV x y) (rat_add_rV X Y).
Proof.
move=> len_eq xX yY; rewrite /bigQ_add_rV.
rewrite (rel_array_length xX); apply/rel_array_arr_mk_fun=> //.
  by rewrite leEint leb_length.
move=> i i_len; apply/rat_bigQ_add.
- move: (rel_array_r xX)=> /(_ i); rewrite (rel_array_length xX) i_len. 
  exact.
- move: (rel_array_r yY)=> /(_ i); rewrite (rel_array_length yY).
  rewrite -len_eq i_len; exact.
Qed.

Definition rat_scal_rV (lambda : rat) (X : array rat):=
  arr_map (fun v=> (lambda * v)%R) X.

Lemma BQR_array_scal:
  (rat_bigQ =~> rel_array rat_bigQ =~> rel_array rat_bigQ)
  bigQ_scal_rV rat_scal_rV.
Proof.
move=> l L lL x X xX; apply/rel_array_map; [|exact:xX].
exact:rat_bigQ_mul.
Qed.

Definition rat_weighted_lines v A:=
  arr_fold_pair
  (fun v_i A_i acc => rat_add_rV acc (rat_scal_rV v_i A_i))
  v A (make (length A.[0%uint63]) 0%R).

Lemma BQR_array_weighted_lines v V a A:
  (0%uint63 < length A)%O ->
  length V = length A ->
  (forall i, (i < length A)%O -> length A.[i] = length A.[0])->
  rel_array rat_bigQ v V ->
  rel_array (rel_array rat_bigQ) a A ->
  rel_array rat_bigQ
  (weighted_lines v a) (rat_weighted_lines V A).
Proof.
move=> len_A_gt0 len_eq len_ai vV aA.
set r' := fun (x : array bigQ) (X : array rat) =>
  (forall i, (i < length A)%O -> length X = length A.[i]) /\ 
  rel_array rat_bigQ x X.
suff: r' (weighted_lines v a) (rat_weighted_lines V A) by case.
apply: (rel_array_fold_pair_in (r':=r')); [exact:len_eq| |exact:vV|exact:aA| ].
- move=> i i_len z Z [len_z zZ].
  move: (rel_array_r vV)=> /(_ i); rewrite (rel_array_length vV).
  move=> /(_ i_len) viVI.
  move: (rel_array_r aA)=> /(_ i); rewrite (rel_array_length aA) -len_eq.
  move=> /(_ i_len) aiAI; move: (BQR_array_scal viVI aiAI)=> avAV.
  have:= (BQR_array_add _ zZ avAV); rewrite length_arr_map (len_z i); last
    by rewrite -len_eq.
  move=> /(_ (erefl _))=> rel_res; split=> //.
  by move=> k k_len; rewrite length_arr_mk_fun; [exact/len_z|rewrite leEint leb_length].
- split; first by (move=> i i_len; rewrite length_make leb_length len_ai).
  move: (rel_array_r aA); rewrite (rel_array_length aA).
  move=> /(_ _ len_A_gt0)=> /rel_array_length -> /=.
  apply/(rel_array_make (length A.[0%uint63]) rat_bigQ0).
Qed.

Lemma BQR_array_mulmx:
  (rel_array (rel_array rat_bigQ) =~> rel_array (rel_array rat_bigQ) =~>
  rel_array (rel_array rat_bigQ))
  bigQ_mulmx rat_mulmx.
Proof. by apply:rel_array_mulmx; [exact:rat_bigQ_add|exact:rat_bigQ_mul|]. Qed.

End RelArrayBQR.

Section RatVector.

Context {n : nat}.

Local Notation rel_cV_rat := (@rel_cV [realFieldType of rat] n).
Local Notation rel_rV_rat := (@rel_rV [realFieldType of rat] n).

Lemma rel_cV_rat_eq:
  (rel_cV_rat =~> rel_cV_rat =~> eq) (eq_array_rel (@eq_op _)) (@eq_op _).
Proof.
move=> x X xX y Y yY; apply/idP/idP.
- case/eq_array_relP=> len_xy xy_i; apply/eqP/matrixP=> p q.
  rewrite ord1 -(rel_cV_nth xX p) -(rel_cV_nth yY p).
  apply/eqP/xy_i=> [:len_x]; rewrite ltEint_nat nat_to_intK;
    first by (abstract:len_x; rewrite -(rel_cV_length xX)).
  rewrite inE; exact/(ltn_trans len_x)/int_thresholdP.
- move/eqP/matrixP=> XY; apply/eq_array_relP=> [:len_xy]; split.
  + abstract:len_xy; apply/int_to_nat_inj.
    by rewrite -(rel_cV_length xX) -(rel_cV_length yY).
  + move=> i; rewrite ltEint_nat -(rel_cV_length xX)=> i_n.
    move:(rel_cV_nth xX (Ordinal i_n)) (rel_cV_nth yY (Ordinal i_n)).
    rewrite /= int_to_natK => -> ->; exact/eqP/XY.
Qed.

Lemma rel_cV_rat_dot: 
  (rel_cV_rat =~> rel_cV_rat =~> eq) rat_dot (fun x y=> vdot x y).
Proof. move=> /= x X xX y Y yY; exact/rel_cV_big. Qed.

Lemma rel_rV_rat_lex:
  (rel_rV_rat =~> rel_rV_rat =~> eq)
    (lex_array_rel rat_compare) (fun x y=> (x <=lex y)%R).
Proof.
apply/rel_rV_lex=> x y; rewrite /rat_compare /CompSpec.
case: ltgtP=> [_|_|->]; [exact:CompLt|exact:CompGt|exact:CompEq].
Qed.

Lemma rel_rV_rat_add:
  (rel_rV_rat =~> rel_rV_rat =~> rel_rV_rat)
  (fun x y=> rat_add_rV x y)
  (fun X Y=> (X + Y)%R).
Proof.
move=> x X xX y Y yY; split; rewrite ?length_arr_mk_fun ?leEint ?leb_length ?(rel_cV_length xX) //.
move=> i; rewrite !mxE nth_arr_mk_fun ?leEint ?leb_length // ?ltEint_nat.
- by move:(rel_rV_nth xX) (rel_rV_nth yY)=> /(_ i) -> /(_ i) ->.
- rewrite -(rel_cV_length xX); rewrite nat_to_intK //.
  rewrite !inE; apply/(ltn_trans (ltn_ord _)). 
  rewrite {1}(rel_cV_length xX); exact/int_thresholdP.
Qed.

Lemma rel_rV_rat_scal lambda:
  (rel_rV_rat =~> rel_rV_rat)
  (rat_scal_rV lambda) (fun X=> (lambda *: X)%R).
Proof.
move=> x X xX; split; rewrite ?length_arr_map ?(rel_cV_length xX) //.
by move=> i; rewrite !mxE arr_map_nth (rel_rV_nth xX).
Qed.

End RatVector.

Section RatMatrix.
Context {m n : nat}.

Local Notation rel_mx_rat_col := (@rel_mx_col [realFieldType of rat] m n).
Local Notation rel_mx_rat_row := (@rel_mx_row [realFieldType of rat] m n).

Lemma rel_rV_rat_mul_col:
  (@rel_rV [realFieldType of rat] m =~> rel_mx_rat_col =~> 
    @rel_rV [realFieldType of rat] n)
    (fun x y=> arr_map (fun col=> rat_dot x col) y)
    (fun X Y=> (X *m Y)%R).
Proof.
move=> x X xX y Y yY.
have ->: (X *m Y)%R = ((\col_(i < n.+1) '[X^T, col i Y])^T)%R.
- apply/matrixP=> i j; rewrite (ord1_eq0 i) !mxE /vdot.
  by under [RHS]eq_bigr=> k _ do rewrite !mxE.
by apply/rel_mx_col_map=> //; apply/rel_cV_rat_dot.
Qed.

Lemma rel_rV_rat_weighted_lines:
  (@rel_rV [realFieldType of rat] m =~> rel_mx_rat_row =~> @rel_rV [realFieldType of rat] n)
  rat_weighted_lines (fun V A=> (V *m A)%R).
Proof.
move=> v V vV a A aA; rewrite /rat_weighted_lines mulmx_sum_row.
apply: rel_mx_row_bigsum=> //.
- move=> ?? ->; exact/rel_rV_rat_scal.
- exact/rel_rV_rat_add.
Qed.

End RatMatrix.
Section BQRVector.

Definition rel_cV_bqr {n : nat} := 
  @rel_point_cV _ _ rat_bigQ n.
Definition rel_rV_bqr {n : nat} := 
  @rel_point_rV _ _ rat_bigQ n.

Lemma rel_cV_bqr_eq {n : nat}:
  (@rel_cV_bqr n =~> @rel_cV_bqr n =~> eq)
    (eq_array_bigQ) (@eq_op _).
Proof.
apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func2; [exact:BQR_array_eq|exact:rel_cV_rat_eq].
Qed.


Lemma rel_rV_bqr_lex {n : nat}:
  (@rel_rV_bqr n =~> @rel_rV_bqr n =~> eq)
  BQlex_order (fun x y=> (x <=lex y)%R).
Proof.
apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqL|].
apply/rel_comp_func2; [exact:BQR_array_lex|exact:rel_rV_rat_lex].
Qed.

Lemma rel_rV_bqr_pertline {n : Uint63.int} {N : nat}:
  (n < max_length)%O ->
  rel_int n N.+1 ->
  (@rel_int_ord N =~> rat_bigQ =~> rat_bigQ =~> @rel_rV_bqr N.+1)
  (BigQUtils.perturbed_line n)
  (fun K B M1=> row_mx B%:M (row K (M1%:M))).
Proof.
move=> n_max nN k K kK b B bB x X xX.
exists (make (Uint63.succ n) 0%R).[0%uint63 <- B].[succ k <- X].
- move: (rel_array_make (succ n) rat_bigQ0).
  by move/(rel_array_write 0%uint63 bB)/(rel_array_write (succ k) xX).
- move=> [: n_len]; split.
  + rewrite !length_set; abstract: n_len; rewrite length_make.
    rewrite -leEint leEint_nat !succ_intE; last exact/lt_trans/max_length_lt.
    rewrite -ltEint_nat n_max succ_intE; last exact/lt_trans/max_length_lt.
    by rewrite nN.
  + move=> i; case/boolP: (nat_to_int i == (succ k)).
    * move/eqP=> i_k [: k_len]; rewrite i_k get_set_same.
      { 
        rewrite !mxE; case: splitP.
        - move=> j /(congr1 nat_to_int); rewrite i_k (ord1_eq0 j).
          move/(congr1 int_to_nat); rewrite succ_intE //.
          abstract: k_len.
          rewrite ltEint_nat -kK; apply/(ltn_trans (ltn_ord K)).
          rewrite nN; apply/(@ltn_trans max_length); rewrite -ltEint_nat //.
          exact:max_length_lt.
        -  move=> k' /(congr1 nat_to_int); rewrite i_k.
          rewrite add1n -nat_to_intS=> /(congr1 pred); rewrite !pred_succ.
          move/(congr1 int_to_nat); rewrite nat_to_intK.
          + by rewrite -kK=> /val_inj <-; rewrite !mxE eqxx. 
          + rewrite inE; apply/(ltn_trans (ltn_ord k')).
            rewrite nN; exact:int_thresholdP.
      }
      { 
        rewrite length_set -ltEint ltEint_nat -n_len succ_intE //.
        by rewrite -kK ltnS ltn_ord.
      }
    * rewrite eq_sym; move/eqP=> ?; rewrite get_set_other //.
      case/boolP: (i == ord0).
      {
        move/eqP=> i_0; rewrite i_0 get_set_same -?ltEint ?ltEint_nat -?n_len //.
        rewrite !mxE; case: splitP=> // j _; rewrite (ord1_eq0 j).
        by rewrite !mxE eqxx.
      }
      {
        move=> in0; rewrite get_set_other ?get_make ?mxE.
        - case: splitP.
          + move=> j; rewrite (ord1_eq0 j) /= => ?.
            by move/eqP: in0; case; apply/val_inj.
          + move=> j i_j; rewrite !mxE.
            suff ->: (K == j) = false by [].
            apply/negbTE/eqP=> /(congr1 val)/(congr1 succn).
            rewrite kK -[in RHS]add1n -i_j=> /(congr1 nat_to_int).
            by rewrite -(nat_to_intS) int_to_natK.
        - move/(congr1 int_to_nat)=> /esym.
          rewrite nat_to_intK; first (move=> i0; move/eqP: in0; case; exact/val_inj).
          apply/(ltn_trans (ltn_ord _)); rewrite nN.
          apply/(@leq_ltn_trans max_length); rewrite -?ltEint_nat //.
          apply/(@ltn_trans max_int_); rewrite -?ltEint_nat ?max_length_lt //.
          exact/int_thresholdP.
          }
Qed.

Lemma rel_rV_bqr_delta n N:
  (n <= max_length)%O ->
  rel_int n N.+1->
  (@rel_int_ord N =~> rat_bigQ =~> rel_rV_bqr)
  (fun i x=> BigQUtils.delta_line n i x) (fun I X=> row I X%:M).
Proof.
move=> n_max nN i I iI x X xX.
exists (make n 0%R).[i <- X].
- split; rewrite ?length_set ?length_make //.
  move=> k; rewrite -leEint n_max=> k_n.
  case/boolP: (i == k)=> /eqP; [move=> ->|].
  + by rewrite !get_set_same ?length_make -?leEint ?n_max -?ltEint ?k_n.
  + by move=> i_k; rewrite !get_set_other // !get_make.
- split; rewrite ?length_set ?length_make -?leEint ?n_max ?nN //.
  move=> K; rewrite !mxE.
  case/boolP: (I == K).
  + move/eqP=> <-; rewrite iI int_to_natK get_set_same //=.
    rewrite length_make -leEint n_max -ltEint ltEint_nat.
    rewrite -nN -iI; exact/ltn_ord.
  + move=> IK; rewrite /= GRing.mulr0n get_set_other ?get_make //.
    move/(congr1 int_to_nat); rewrite -iI nat_to_intK ?inE.
    * by move/val_inj/eqP; rewrite /= (negPf IK).
    * apply/(ltn_trans (ltn_ord _)); rewrite nN.
      apply/(@leq_ltn_trans max_length); first rewrite -?leEint_nat ?n_max //.
      exact/int_thresholdP.
Qed.

Lemma rel_rV_bqr_delta_bis n N i:
  (n <= max_length)%O ->
  rel_int n N.+1 ->
  (rat_bigQ =~> @rel_rV_bqr N) (fun x=> BigQUtils.delta_line n i x)
  (fun X=> (\row_j (X*+(int_to_nat i == j)))%R).
Proof.
move=> n_max nN x X xX.
exists (make n 0%R).[i <- X].
- split; rewrite ?length_set ?length_make //.
  move=> k; rewrite -leEint n_max=> k_n.
  case/boolP: (i == k)=> /eqP; [move=> ->|].
  + by rewrite !get_set_same ?length_make -?leEint ?n_max -?ltEint ?k_n.
  + by move=> i_k; rewrite !get_set_other // !get_make.
- split; rewrite ?length_set ?length_make -?leEint ?n_max ?nN //.
  move=> k; rewrite !mxE; case/boolP: (int_to_nat i == val k).
  + move=> /eqP /[dup] i_k <-; rewrite int_to_natK get_set_same //.
    rewrite -ltEint length_make -leEint n_max ltEint_nat.
    by rewrite i_k ltn_ord.
  + move=> i_n_k; rewrite /= GRing.mulr0n get_set_other ?get_make //.
    move: i_n_k=> /[swap] ->; rewrite nat_to_intK /= ?eqxx //.
    rewrite !inE; apply/(ltn_trans (ltn_ord _))/int_thresholdP.
Qed.

Lemma rel_rV_bqr_add (n : nat):
  (@rel_rV_bqr n =~> @rel_rV_bqr n =~> @rel_rV_bqr n)
  bigQ_add_rV (fun v w=> (v + w)%R).
Proof.
move=> x X' [X xX XX'] y Y' [Y yY YY'].
move: (rel_rV_rat_add XX' YY').
exists (rat_add_rV X Y)=> //; apply/BQR_array_add=> //.
by apply/int_to_nat_inj; rewrite -(rel_cV_length XX') -(rel_cV_length YY').
Qed.

Lemma rel_rV_bqr_scal (n : nat):
  (rat_bigQ =~> @rel_rV_bqr n =~> @rel_rV_bqr n)
  bigQ_scal_rV (fun L X=> (L *: X)%R).
Proof.
move=> l L lL; apply/rel_comp_func; [exact/BQR_array_scal/lL|].
exact/rel_rV_rat_scal.
Qed.
  
End BQRVector.

Section BQRMatrix.

Context {m n : nat}.

Definition rel_mx_bqr_col := @rel_point_mx_col _ _ rat_bigQ m n.
Definition rel_mx_bqr_row := @rel_point_mx_row _ _ rat_bigQ m n.

Lemma rel_mx_bqr_mul_col:
  (@rel_rV_bqr m =~> rel_mx_bqr_col =~> @rel_rV_bqr n)
    bigQ_mul_row_mx (fun X Y=> (X *m Y)%R).
Proof.
apply/rel_comp_func2;
  [exact:BQR_array_mul_rV_mx|exact:rel_rV_rat_mul_col].
Qed.

Lemma rel_mx_bqr_row_weighted_lines:
  (@rel_rV_bqr m =~> rel_mx_bqr_row =~> @rel_rV_bqr n)
  weighted_lines (fun v A=> (v *m A)%R).
Proof.
move=> v V' [V vV VV'] a A' [A aA AA']; exists (rat_weighted_lines V A).
- apply/BQR_array_weighted_lines=> //.
+ by rewrite ltEint_nat -(rel_mx_row_length AA').
+ by apply/int_to_nat_inj; rewrite -(rel_cV_length VV') -(rel_mx_row_length AA').
+ move=> i iA; apply/int_to_nat_inj.
  by rewrite -(rel_mx_row_length_row AA') -(rel_mx_row_length_row_i AA' iA).
- exact/rel_rV_rat_weighted_lines.
Qed.

End BQRMatrix.

(* Section BigQ2Rat_Vector.
Section Def.

Context {n : nat}.

Definition rat_bigQ_rV (a : array bigQ) (v : 'rV[rat]_n):=
  (n == length a) && [forall i : 'I_n, a.[nat_to_int i] -bQr- (v ord0 i)].
  
Definition rat_bigQ_cV (a : array bigQ) (v : 'cV[rat]_n):=
  (n == length a) && [forall i : 'I_n, a.[nat_to_int i] -bQr- (v i ord0)].

Definition bigQ_arr_to_rat_cV {n : nat} (a : array bigQ) := 
  (\col_(j < n) (bigQ2rat_def (get a (nat_to_int j))))%R.  

End Def.

Section Proofs.

Lemma rat_bigQ_rVP {n : nat} (a : array bigQ) (v : 'rV[rat]_n):
  reflect 
    ((n = length a) /\ (forall i : 'I_n, a.[nat_to_int i] -bQr- (v ord0 i)))
    (rat_bigQ_rV a v).
Proof.
apply/(iffP idP).
- case/andP=> /eqP eq_len /forallP h; split=> //.
- case=> len_eq h; apply/andP; split; rewrite ?len_eq //.
  exact/forallP.
Qed.

Lemma rat_bigQ_cVP {n : nat} (a : array bigQ) (v : 'cV[rat]_n):
  reflect 
    ((n = length a) /\ (forall i : 'I_n, a.[nat_to_int i] -bQr- (v i ord0)))
    (rat_bigQ_cV a v).
Proof.
apply/(iffP idP).
- case/andP=> /eqP eq_len /forallP h; split=> //.
- case=> len_eq h; apply/andP; split; rewrite ?len_eq //.
  exact/forallP.
Qed.


Lemma BQ2R_cVP (a : array bigQ):
  rat_bigQ_cV a (@bigQ_arr_to_rat_cV (length a) a).
Proof. by apply/rat_bigQ_cVP; split=> // i; rewrite mxE. Qed.

Lemma BQ2R_cVP_cast (a : array bigQ) (n : nat):
  n = length a -> 
  rat_bigQ_cV a (@bigQ_arr_to_rat_cV n a).
Proof.
move=> n_eq; apply/rat_bigQ_cVP; split=> //.
by move=> i; rewrite !mxE.
Qed.

Lemma BQR_rV_injl {n : nat} (a b : array bigQ) (v w : 'rV[rat]_n):
  rat_bigQ_rV a v -> rat_bigQ_rV b w -> reflect (v = w) (eq_array_bigQ a b).
Proof.
move/rat_bigQ_rVP => + /rat_bigQ_rVP.
move=> bqr_av bqr_bw; apply/(iffP idP).
- case/eq_array_relP=> len_eq eqb_i.
  apply/rowP=> i.
  case: bqr_bw=> len_b /(_ i).
  case: bqr_av=> len_a /(_ i).
  move: (eqb_i (nat_to_int i)).
  rewrite ltEint_nat nat_to_intK ?inE; last (apply/(@ltn_trans n)=> //; rewrite len_a; exact/int_thresholdP).
  rewrite -len_a ltn_ord=> /(_ isT) /BigQ.eqb_eq /[swap] /eqP/rat_bigQEl /[apply] + /eqP.
  exact/rat_bigQ_injr.
- move=> vw; move: bqr_av bqr_bw; rewrite vw.
  case=> len_a bqr_ai [len_b bqr_bi]; apply/eq_array_relP.
  split; first by (apply: int_to_nat_inj; rewrite -len_a -len_b).
  move=> i; rewrite ltEint_nat -len_a => i_n; apply/BigQ.eqb_eq.
  move: (bqr_ai (Ordinal i_n)) (bqr_bi (Ordinal i_n)). 
  by move/eqP/rat_bigQ_injl=> + /eqP;move=> /[apply]; rewrite /= int_to_natK.
Qed. 

Lemma BQR_rV_tr {n : nat} (a : array bigQ) (v : 'rV[rat]_n):
  rat_bigQ_cV a (v^T) <-> rat_bigQ_rV a v.
Proof.
split.
- move/rat_bigQ_cVP; case=> ? h.
  apply/rat_bigQ_rVP; split=> // i; rewrite -[v]trmxK mxE; exact: h.
- move/rat_bigQ_rVP; case=> ? h.
  apply/rat_bigQ_cVP; split=> // i; rewrite mxE; exact: h.
Qed.

Lemma BQR_cV_tr {n : nat} (a : array bigQ) (v : 'cV[rat]_n):
  rat_bigQ_rV a (v^T) <-> rat_bigQ_cV a v.
Proof.
split.
- move/rat_bigQ_rVP; case=> ? h.
  apply/rat_bigQ_cVP; split=> // i; rewrite -[v]trmxK mxE; exact: h.
- move/rat_bigQ_cVP; case=> ? h.
  apply/rat_bigQ_rVP; split=> // i; rewrite mxE; exact: h.
Qed.

Lemma BQR_scal_rV {n : nat} (lambda : bigQ) (lambda' : rat)
  (a : array bigQ) (v : 'rV[rat]_n): 
  rat_bigQ lambda' lambda -> rat_bigQ_rV a v ->
  rat_bigQ_rV (bigQ_scal_rV lambda a) (lambda' *: v).
Proof.
move=> bqr_lambda bqr_av.
apply/rat_bigQ_rVP; split.
- by rewrite length_arr_map; case/rat_bigQ_rVP: bqr_av.
- move=> i; rewrite !mxE arr_map_nth.
  apply/eqP/rat_bigQ_mul=> //; apply/eqP; case/rat_bigQ_rVP: bqr_av.
  by move=> _ /(_ i).
Qed.

Lemma BQR_arr_rV {n : nat} (a b : array bigQ) (v w : 'rV[rat]_n):
  rat_bigQ_rV a v -> rat_bigQ_rV b w ->
  rat_bigQ_rV (bigQ_add_rV a b) (v + w).
Proof.
case/rat_bigQ_rVP=> len_a a_eq /rat_bigQ_rVP [len_b b_eq].
apply/rat_bigQ_rVP; rewrite length_arr_mk_fun ?leEint ?leb_length //; split=> //.
move=> i; rewrite /bigQ_add_rV nth_arr_mk_fun ?mxE ?leEint ?leb_length //.
- apply/eqP/rat_bigQ_add; apply/eqP; [exact: a_eq|exact: b_eq].
- rewrite ltEint_nat -len_a nat_to_intK ?ltn_ord //.
  rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite len_a; exact/int_thresholdP.
Qed.

Lemma BQR_dot {n : nat} (a b : array bigQ) (v w : 'cV[rat]_n):
  rat_bigQ_cV a v -> rat_bigQ_cV b w -> rat_bigQ '[v,w] (bigQ_dot a b).
Proof.
case/rat_bigQ_cVP=> + bqr_a_v /rat_bigQ_cVP [+ bqr_b_w].
move=> /[dup] n_int /(congr1 nat_to_int) + /(congr1 nat_to_int).
rewrite !int_to_natK=> len_a len_b.
rewrite /bigQ_dot /arr_fold_pair  zip_arr_to_seq -?len_a //.
rewrite irange0_iota nat_to_intK; rewrite ?n_int ?inE; last exact/int_thresholdP.
rewrite /vdot (eq_bigl (fun k => (val k < n)%nat)); last by (move=> k; rewrite ltn_ord).
move: {1 16 19}n (leqnn n); elim=> [|k IH]; first by rewrite big_pred0_eq.
move=> k_n; rewrite iotaS_rcons add0n !map_rcons foldl_rcons /=.
rewrite big_ord_narrow big_ord_recr /=.
apply/rat_bigQ_add; last (apply/rat_bigQ_mul; apply/eqP).
- move: (IH (ltnW k_n)); rewrite (big_ord_narrow (ltnW k_n)).
  set S := BigOp.bigop _ _ _; set S' := BigOp.bigop _ _ _.
  suff ->: S = S' by [].
  apply/eq_bigr=> i _; set wid := widen_ord _ _; set wid' := widen_ord _ _.
  suff ->: wid = wid' by []; exact/val_inj.
- exact: (bqr_a_v (widen_ord k_n ord_max)).
- exact: (bqr_b_w (widen_ord k_n ord_max)).
Qed.


Lemma BQR_ltx_order {n : nat} (a b : array bigQ) (v w : 'rV[rat]_n):
  rat_bigQ_rV a v -> rat_bigQ_rV b w -> BQltx_order a b = (v <lex w)%R.
Proof.
move=> /rat_bigQ_rVP + /rat_bigQ_rVP.
case=> len_a bqr_av [len_b bqr_bw]; apply/idP/idP.
- case/ltx_array_relP=> len_eq /= [j] [j_len j_lt_eq j_eq].
  apply/lex_lev_strictP; move: (j_len).
  rewrite ltEint_nat -len_a=> j_n; exists (Ordinal j_n).
  split.
  + move=> i /= i_j; move/(_ (nat_to_int i)): j_lt_eq bqr_av bqr_bw.
    rewrite ltEint_nat nat_to_intK ?i_j ?inE; 
      last (apply/(ltn_trans i_j)/(@ltn_trans (length a)); [by rewrite -?ltEint_nat //|exact/int_thresholdP]).
    move/(_ isT); case: BigQ.compare_spec=> // + _ /(_ i) /eqP + /(_ i) /eqP.
    move=> /[swap] /rat_bigQEl /[apply]; exact: rat_bigQ_injr.
  + move: (bqr_av (Ordinal j_n)) (bqr_bw (Ordinal j_n))=> /= /eqP + /eqP.
    move/rat_bigQ_lt=> /[apply] <-; rewrite int_to_natK.
    by case: BigQ.compare_spec j_eq.
- case/lex_lev_strictP=> j [j_lt_eq j_eq].
  apply/ltx_array_relP; split; first apply/int_to_nat_inj; rewrite -?len_a -?len_b //.
  have j_int: j < int_threshold by apply/(ltn_trans (ltn_ord _)); rewrite len_a; exact/int_thresholdP.
  exists (nat_to_int j); split.
  + rewrite ltEint_nat -len_a nat_to_intK ?inE //.
  + move=> i; rewrite ltEint_nat nat_to_intK ?inE // => i_j.
    move: (i_j) (ltn_ord j)=> /ltn_trans /[apply] => i_n.
    move: (j_lt_eq (Ordinal i_n))=> /= /(_ i_j) vw_i_eq.
    move: (bqr_av (Ordinal i_n)) (bqr_bw (Ordinal i_n)); rewrite vw_i_eq.
    move=> /eqP + /eqP.
    move/rat_bigQ_injl=> /[apply] /=; rewrite int_to_natK => ->.
    case: BigQ.compare_spec=> //; by move/QOrderedType.QOrder.lt_irrefl.
  + move: (bqr_av j) (bqr_bw j)=> /eqP + /eqP. 
    move/rat_bigQ_lt /[apply]; rewrite j_eq.
    case: BigQ.compare_spec=> //.
    * move=> /[swap] /=; rewrite /BigQ.lt /BigQ.eq => h.
      by move: QArith_base.Qlt_not_eq=> /[apply]; rewrite h=> /(_ isT).
    * move=> /[swap] /=; rewrite /BigQ.lt => h.
      move/QArith_base.Qlt_trans => /(_ [b.[nat_to_int j]]%bigQ).
      by rewrite h=> /(_ isT)/QArith_base.Qlt_irrefl.
Qed.

Lemma BQR_lex_order {n : nat} (a b : array bigQ) (v w : 'rV[rat]_n):
  rat_bigQ_rV a v -> rat_bigQ_rV b w -> BQlex_order a b = (v <=lex w)%R.
Proof.
move=> bqr_av bqr_bw; rewrite /BQlex_order lex_arr_eqVlt lex_eqOlt.
rewrite -(BQR_ltx_order bqr_av bqr_bw); congr orb.
apply/idP/idP.
- case/eq_array_relP=> len_eq nth_h; apply/eqP/(BQR_rV_injl bqr_av bqr_bw).
  by apply/eq_array_relP; split.
- case/eqP/(BQR_rV_injl bqr_av bqr_bw)/eq_array_relP=> len_eq nth_h.
  by apply/eq_array_relP; split.
Qed.

Lemma BQltx_order_irr: irreflexive BQltx_order.
Proof.
move=> x; apply/idP/idP.
apply/negP=> /ltx_array_relP.
rewrite /ltx_array_rel; case=> _ [j] [_ _].
by case: BigQ.compare_spec=> // /QArith_base.Qlt_irrefl.
Qed.



Lemma BQltx_inj (a : array (array bigQ)):
  rel_sorted BQltx_order a -> 
  (forall i j, (i < length a)%O -> (j < length a)%O -> 
  eq_array_bigQ a.[i] a.[j] -> i = j).
Proof.
move/(sorted_rel_inj_rel BQltx_order_trans); apply.
move=> x y; rewrite /eq_array_bigQ /BQltx_order.
case/eq_array_relP=> len_eq xy_i_eq; split.
- rewrite /ltx_array_rel len_eq eqxx /=.
  case E: (lex_array_rel_ _ _)=> //=.
  case: (lex_array_rel_Lt len_eq E)=> j []; rewrite -ltEint_nat=> /xy_i_eq.
  move/BigQ.eqb_correct ->; rewrite BigQ.spec_compare.
  by case: QArith_base.Qcompare_spec=> // /QOrderedType.QOrder.lt_irrefl.
- rewrite /ltx_array_rel len_eq eqxx /=.
  case E: (lex_array_rel_ _ _)=> //=.
  case: (lex_array_rel_Lt (esym len_eq) E)=> [j] []; rewrite -ltEint_nat -len_eq.
  move=> /xy_i_eq /BigQ.eqb_correct ->; rewrite BigQ.spec_compare.
  by case: QArith_base.Qcompare_spec=> // /QOrderedType.QOrder.lt_irrefl.
Qed.

End Proofs.

End BigQ2Rat_Vector.

Section BigQ2Rat_Matrix.
Section Def.

Definition rat_bigQ_mx_col {m n : nat} (a : array (array bigQ)) (M : 'M_(m,n)):=
  n = length a /\
  (forall j : 'I_n, rat_bigQ_cV a.[nat_to_int j] (col j M)).

Definition bigQ_mat_to_rat_mat {m n : nat} (a : array (array bigQ)):=
  ((\matrix_(j < n) (@bigQ_arr_to_rat_cV m (get a (nat_to_int j)))^T )^T)%R.

End Def.

Section Proofs.

Lemma BQ2R_matP (a : array (array bigQ)):
  (forall j, (j < length a)%O -> length a.[j] = length a.[0]) ->
  @rat_bigQ_mx_col (length a.[0]) (length a) a (bigQ_mat_to_rat_mat a).
Proof.
move=> len_0; split; first by [].
move=> j; rewrite /bigQ_mat_to_rat_mat.
apply/rat_bigQ_cVP; split.
- rewrite -(len_0 (nat_to_int j)) //.
  rewrite ltEint_nat nat_to_intK // inE.
  apply/(ltn_trans (ltn_ord _))/int_thresholdP.
- by move=> i; rewrite !mxE.
Qed.

Lemma BQ2R_matP_cast (a : array (array bigQ)) (m n : nat):
  m = length a -> (forall i, (i < length a)%O -> n = length a.[i]) ->
  @rat_bigQ_mx_col n m a (bigQ_mat_to_rat_mat a).
Proof.
move=> m_eq n_eq; split=> // j.
apply/rat_bigQ_cVP; split.
- apply/n_eq; rewrite ltEint_nat -m_eq nat_to_intK //.
  rewrite inE; apply/(ltn_trans (ltn_ord _)); rewrite m_eq.
  exact/int_thresholdP.
- by move=> i; rewrite !mxE.
Qed.

Lemma BQR_rV_M_mul {m n : nat} (a : array bigQ) (x : array (array bigQ))
  (v : 'rV[rat]_m) (M : 'M_(m,n)):
  rat_bigQ_rV a v -> rat_bigQ_mx_col x M -> 
  rat_bigQ_rV (bigQ_mul_row_mx a x) (v *m M).
Proof.
move=> bqr_a_v bqr_x_M; apply/rat_bigQ_rVP; split.
- rewrite /bigQ_mul_row_mx /= /PArrayUtils.map length_arr_map.
  by case: bqr_x_M.
- move=> i; rewrite /bigQ_mul_row_mx arr_map_nth -matrix_vdot.
  apply/eqP/BQR_dot.
  + by apply/BQR_rV_tr; rewrite row_id.
  + by case: bqr_x_M=> _ /(_ i).
Qed.

End Proofs.
End BigQ2Rat_Matrix.
 *)
