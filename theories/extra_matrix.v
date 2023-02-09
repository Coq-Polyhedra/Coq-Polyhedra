(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2021 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2021 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2021 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector fingroup perm.
Require Import extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section ExtraMx.

Lemma col_mx0l (R : comRingType) (n : nat) (x : 'cV[R]_n) (y : 'cV[R]_0) : col_mx y x = x.
Proof.
apply/ colP => i; rewrite !mxE; case: splitP => [j | j i_eq_0j]; first by move: (valP j).
suff <-: (i = j) by done.
  exact: ord_inj.
Qed.

Lemma col0P (R: comRingType) (m: nat) (u: 'cV[R]_m) : u^~ 0 =1 (fun _ => 0) <-> u = 0.
Proof.
split => H.
- apply/colP => i; rewrite mxE.
  exact: H.
- move => i; move/colP/(_ i): H.
  by rewrite mxE.
Qed.

Lemma col_neq_0 (R: comRingType) (m: nat) (u: 'cV[R]_m) : (u != 0) = [exists i, u i 0 != 0].
Proof.
apply/idP/idP.
- apply/contraR.
  rewrite negb_exists.
  move/forallP => null_entries.
  apply/eqP/col0P => i.
  move: (null_entries i).
  rewrite negbK.
  by apply/eqP.
- apply/contraTneq => u_eq_0.
  rewrite negb_exists.
  apply/forallP => i.
  by rewrite negbK u_eq_0 mxE.
Qed.

Lemma scalar_mx_eq0 (R : realFieldType) (C : 'M[R]_1) : (C == 0) = (C 0 0 == 0).
Proof.
rewrite [C in LHS]mx11_scalar -scalemx1 scalemx_eq0.
by move/negbTE: (matrix_nonzero1 R 0) ->; rewrite orbF.
Qed.

Lemma row_cV (R : realFieldType) (n: nat) (u: 'cV[R]_n) (i: 'I_n) : row i u = (u i 0)%:M.
Proof.
apply/colP => j; rewrite !mxE.
by rewrite [j]ord1_eq0 /= mulr1n.
Qed.

Lemma const_mx11 (R : realFieldType) (a: R) : const_mx a = a%:M :> 'M_1.
Proof.
by apply/matrixP => i j; rewrite !mxE [i]ord1_eq0 [j]ord1_eq0 mulr1n.
Qed.

Lemma scalar_mx_inj (R : realFieldType) (n: nat) : (n > 0)%N -> injective (@scalar_mx R n).
Proof.
move => n_gt0 x y.
pose i' := Ordinal n_gt0.
by move/matrixP/(_ i' i'); rewrite !mxE /= 2!mulr1n.
Qed.

Lemma mulmx_row_cV_rV (R : realFieldType) (n p: nat) (x: 'cV[R]_n) (y: 'rV[R]_p) (j : 'I_n) : (row j x) *m y = (x j 0) *: y.
Proof.
rewrite -mul_scalar_mx; apply: (congr1 (mulmx^~ _)).
rewrite [row _ _]mx11_scalar; apply: congr1.
by rewrite mxE.
Qed.

Lemma non_trivial_ker (R : realFieldType) (n p : nat) (A' : 'M[R]_(p,n)) (x : 'cV_n) :
  x != 0 -> A' *m x = 0 -> (\rank A' <= n.-1)%N.
Proof.
move => Hx HAx.
move: Hx; rewrite -ltnS; apply: contraLR.
rewrite -ltnNge negbK.
move/(leq_ltn_trans (leqSpred n)); rewrite ltnS => HrkA.
have: (n == (\rank A'))%N
  by move:(rank_leq_col A') => HrkA'; rewrite eqn_leq; apply/andP; split.
move/eqP/eq_leq; rewrite {HrkA} col_leq_rank => /row_fullP.
move => [B]; move/(congr1 (mulmx^~ x)).
rewrite mul1mx -mulmxA HAx mulmx0; move => H; symmetry in H.
by move/eqP: H.
Qed.

Lemma corank1_kermx (R : realFieldType) (n p : nat) (A' : 'M[R]_(p,n)) :
  (n > 0)%N -> \rank A' = n.-1 -> \rank (kermx A'^T) = 1%N.
Proof.
move => ?.
rewrite mxrank_ker mxrank_tr; move ->.
by rewrite -subn1 subKn.
Qed.

Lemma addsmx_kermx (R : realFieldType) (n p q : nat) (A : 'M[R]_(p,n)) (B : 'M[R]_(q,n)) :
  (kermx (col_mx A B)^T == kermx A^T :&: kermx B^T)%MS.
Proof.
rewrite tr_col_mx.
apply/andP; split.
- rewrite sub_capmx; apply/andP; split;
    apply/rV_subP => v /sub_kermxP Hv; apply/sub_kermxP;
    rewrite mul_mx_row -row_mx0 in Hv;
    by move/eq_row_mx: Hv => [? ?].
- apply/rV_subP => v .
  rewrite sub_capmx.
  move/andP => [/sub_kermxP HA /sub_kermxP HB]; apply/sub_kermxP.
  by rewrite mul_mx_row HA HB row_mx0.
Qed.

Lemma kermxK (R : realFieldType) (p q : nat) (A : 'M[R]_(p,q)) :
  (A == kermx (kermx A^T)^T)%MS.
Proof.
suff: (A <= (kermx (kermx A^T)^T))%MS.
  move/mxrank_leqif_eq/snd.
  by rewrite mxrank_ker mxrank_tr mxrank_ker mxrank_tr (subKn (rank_leq_col _)) eq_refl.
apply/rV_subP => ? /submxP [? ->].
apply/sub_kermxP; rewrite -[X in X *m _]trmxK -trmx_mul -trmx0.
by apply/(congr1 trmx); rewrite trmx_mul mulmxA mulmx_ker mul0mx.
Qed.

Lemma submx_kermx (R : realFieldType) (p q r : nat) (A : 'M[R]_(p,r)) (B : 'M[R]_(q,r)) :
  (A <= B)%MS = (kermx B^T <= kermx A^T)%MS.
Proof.
have H (p' q' r': nat) (M : 'M[R]_(p',r')) (N : 'M[R]_(q',r')): (M <= N)%MS -> (kermx N^T <= kermx M^T)%MS.
- move/submxP => [? ->]; rewrite trmx_mul.
  by apply/rV_subP => v /sub_kermxP Hv; apply/sub_kermxP; rewrite mulmxA Hv mul0mx.
apply/idP/idP; first by apply: H.
move/(H _) => H'; move/andP: (kermxK A) =>  [HA _]; move/andP: (kermxK B) =>  [_ HB].
by apply: (submx_trans HA (submx_trans H' HB)).
Qed.

Lemma col_mul (R : comRingType) (p q r : nat) (j : 'I_r) (M : 'M[R]_(p,q)) (N : 'M_(q, r)) :
  col j (M *m N) = M *m (col j N).
Proof.
have H: row j (N^T *m M^T) = row j N^T *m M^T.
by apply: row_mul.
rewrite -trmx_mul -!tr_col -trmx_mul in H.
by apply: trmx_inj.
Qed.

Lemma col_mul_scalar (R : comRingType) (q r : nat) (j : 'I_r) (N : 'M_(q, r)) (a : R):
  col j (a *: N) = a *: (col j N).
Proof.
by apply/colP => i; rewrite !mxE.
Qed.

Lemma trmx_mul_scalar (R : comRingType) (q r : nat) (N : 'M_(q, r)) (a : R):
  (a *: N)^T = a *: (N^T).
Proof.
by apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma castmx_mul (R : ringType)
  (m m' n p p': nat) (em : m = m') (ep : p = p')
  (M : 'M[R]_(m, n)) (N : 'M[R]_(n, p)) :
  castmx (em, ep) (M *m N) = castmx (em, erefl _) M *m castmx (erefl _, ep) N.
Proof.
by case: m' / em; case: p' / ep.
Qed.

Lemma mulmx_cast (R : ringType)
  (m n n' p p' : nat) (en : n' = n) (ep : p' = p)
  (M : 'M[R]_(m, n)) (N : 'M[R]_(n', p')) :
  M *m (castmx (en, ep) N) =
  (castmx (erefl _, (esym en)) M) *m (castmx (erefl _, ep) N).
Proof.
by case: n / en in M *; case: p / ep in N *.
Qed.

Lemma cast_mulmx (R: realFieldType) (m m' n p: nat) (em: m = m') (M: 'M[R]_(m,n)) (N: 'M[R]_(n,p)) :
  castmx (em, erefl n) M *m N = castmx (em, erefl p) (M *m N).
Proof.
by rewrite castmx_mul castmx_id.
Qed.

Lemma castmx_inj (R: realFieldType) (m m' n n': nat) (em: m = m') (en: n = n') :
  injective (@castmx R _ _ _ _ (em, en)).
Proof.
move => M N.
move/(congr1 (castmx (esym em, esym en))).
by rewrite 2!castmxK.
Qed.

Lemma mulmx_tr_row_perm (R: ringType) (m n p: nat) (s: 'S_n) (A: 'M[R]_(n,m)) (B: 'M[R]_(n,p)):
  (row_perm s A)^T *m (row_perm s B) = A^T *m B.
Proof.
rewrite tr_row_perm col_permE row_permE.
rewrite mulmxA -[X in X *m _]mulmxA -perm_mxM.
by rewrite gsimp perm_mx1 mulmx1.
Qed.

Lemma castmx_row (R : Type) (m m' n1 n2 n1' n2' : nat)
  (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (eq_m : m = m') (A1 : 'M[R]_(m, n1)) (A2 : 'M_(m, n2)) :
  castmx (eq_m, eq_n12) (row_mx A1 A2) =
  row_mx (castmx (eq_m, eq_n1) A1) (castmx (eq_m, eq_n2) A2).
Proof.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by case: _ / eq_m; rewrite castmx_id.
Qed.

Lemma castmx_col (R : Type) (m m' n1 n2 n1' n2' : nat)
  (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (eq_m : m = m') (A1 : 'M[R]_(n1, m)) (A2 : 'M_(n2, m)) :
  castmx (eq_n12, eq_m) (col_mx A1 A2) =
  col_mx (castmx (eq_n1, eq_m) A1) (castmx (eq_n2, eq_m) A2).
Proof.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by case: _ / eq_m; rewrite castmx_id.
Qed.

Lemma castmx_block (R : Type) (m1 m1' m2 m2' n1 n2 n1' n2' : nat)
  (eq_m1 : m1 = m1') (eq_n1 : n1 = n1') (eq_m2 : m2 = m2') (eq_n2 : n2 = n2')
  (eq_m12 : (m1 + m2 = m1' + m2')%N) (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (ul : 'M[R]_(m1, n1)) (ur : 'M[R]_(m1, n2))
  (dl : 'M[R]_(m2, n1)) (dr : 'M[R]_(m2, n2)) :
  castmx (eq_m12, eq_n12) (block_mx ul ur dl dr) =
  block_mx (castmx (eq_m1, eq_n1) ul) (castmx (eq_m1, eq_n2) ur)
  (castmx (eq_m2, eq_n1) dl) (castmx (eq_m2, eq_n2) dr).
Proof.
case: _ / eq_m1 in eq_m12 *; case: _ / eq_m2 in eq_m12 *.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by rewrite !castmx_id.
Qed.

Lemma row_castmx (R : Type) (m m' n n' : nat) (eq_m : m = m') (eq_n : n = n') (i : 'I_m') (A : 'M[R]_(m,n)):
  row i (castmx (eq_m, eq_n) A) = row (cast_ord (esym eq_m) i) (castmx (erefl m, eq_n) A).
Proof.
by apply/rowP => ?; rewrite !mxE !castmxE /= cast_ord_id.
Qed.

Lemma col_castmx (R : Type) (m m' n n' : nat) (eq_m : m = m') (eq_n : n = n') (j : 'I_n') (A : 'M[R]_(m,n)):
 col j (castmx (eq_m, eq_n) A) = col (cast_ord (esym eq_n) j) (castmx (eq_m, erefl n) A).
Proof.
by apply/colP => ?; rewrite !mxE !castmxE /= cast_ord_id.
Qed.

Lemma rank_castmx (F : fieldType) (m m' n : nat) (eq_m : m = m') (A : 'M[F]_(m,n)) :
  \rank (castmx (eq_m, erefl n) A) = \rank A.
Proof.
by apply: eqmx_rank; move/eqmxP : (eqmx_cast A (eq_m, erefl n)).
Qed.

Lemma row_free_castmx (F : fieldType) (m m' n : nat) (eq_m : m = m') (A : 'M[F]_(m,n)) :
  row_free (castmx (eq_m, erefl n) A) = row_free A.
Proof.
by rewrite -2!row_leq_rank rank_castmx {2}eq_m.
Qed.

Lemma submx_castmx (F : fieldType) (m1 m1' m2 n : nat) (eq_m1 : m1 = m1') (A : 'M[F]_(m1,n)) (B : 'M[F]_(m2,n)) :
  (castmx (eq_m1, erefl n) A <= B)%MS = (A <= B)%MS.
Proof.
by apply/idP/idP; move/eqmxP/andP: (eqmx_cast A (eq_m1, erefl n)) => [? ?]; apply: submx_trans.
Qed.

Lemma col_mx_eq (R : realFieldType) (m1 m2 p : nat) (B1 C1 : 'M[R]_(m1 ,p) ) (B2 C2 : 'M[R]_(m2 ,p)) :
(col_mx B1 B2 == col_mx C1 C2) = (( B1 == C1 ) && ( B2 == C2 )).
Proof.
apply/idP/idP.
  - move/eqP => H.
    apply/andP.
    split.
      + by move/proj1/eqP: (eq_col_mx H).
      + by move/proj2/eqP: (eq_col_mx H).
  - move/andP => [/eqP H1 /eqP H2].
    apply/eqP/matrixP => i j.
    rewrite !mxE.
    case: (splitP i).
      + move => k Hk.
        by move/matrixP: H1.
      + move => k Hk.
        by move/matrixP: H2.
Qed.


Lemma col_mx_eq0 (R : realFieldType) (m1 m2 p : nat) (B1 : 'M[R]_(m1 ,p) ) (B2 : 'M[R]_(m2 ,p)) :
(col_mx B1 B2 == 0) = (( B1 == 0 ) && ( B2 == 0 )).
Proof.
by rewrite -{1}[0]vsubmxK 2!linear0; apply: col_mx_eq.
Qed.

Lemma sum_col_mx (R : realFieldType) (I : finType) (m1 m2 n: nat) (M: I -> 'M[R]_(m1,n)) (N: I -> 'M[R]_(m2,n)) :
  \sum_i (col_mx (M i) (N i)) = col_mx (\sum_i M i) (\sum_i N i).
Proof.
apply/row_matrixP => i; rewrite -[i]splitK; set i' := unsplit _.
have ->: row i' (\sum_i0 col_mx (M i0) (N i0)) = \sum_i0 row i' (col_mx (M i0) (N i0))
  by apply: big_morph; by [apply: raddfD | apply: row0].
rewrite /i' /unsplit; case: splitP => [j _ | j _].
- rewrite rowKu.
  have ->: \sum_i0 row (lshift m2 j) (col_mx (M i0) (N i0)) = \sum_i0 (row j (M i0)).
    by apply: eq_bigr => k _; rewrite rowKu.
  by symmetry; apply: big_morph; by [apply: raddfD | apply: row0].
- rewrite rowKd.
  have ->: \sum_i0 row (rshift m1 j) (col_mx (M i0) (N i0)) = \sum_i0 (row j (N i0)).
    by apply: eq_bigr => k _; rewrite rowKd.
  by symmetry; apply: big_morph; by [apply: raddfD | apply: row0].
Qed.

Lemma mulmx_const_mx1 (R : realFieldType) (m n: nat) (M : 'M[R]_(m, n)) :
  M *m (const_mx 1) = \sum_i col i M.
Proof.
by apply/colP=> j; rewrite mxE summxE; apply: eq_bigr => i _; rewrite !mxE mulr1.
Qed.


Lemma mulmx_sum_col (R : realFieldType) (m n : nat) (A : 'M[R]_(m, n)) (u : 'cV_n):  A *m u = \sum_i u i 0 *: col i A.
Proof.
apply/colP => j.
rewrite mxE summxE.
by apply/eq_bigr => i; rewrite !mxE mulrC.
Qed.

Lemma mulmx_col'_row' (R : realFieldType) (m n p : nat) (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) (i : 'I_n) (j : 'I_m) (h : 'I_p) :
  (A *m B) j h = A j i * B i h + ((col' i A) *m (row' i B)) j h.
Proof.
rewrite !mxE.
suff ->: \sum_(j0 < n.-1) (col' i A) j j0 * (row' i B) j0 h = \sum_(j0 < n | j0 != i) A j j0 * B j0 h
  by rewrite (bigID (xpred1 i)) big_pred1_eq.
have ->: \sum_(j0 < n.-1) (col' i A) j j0 * (row' i B) j0 h = \sum_(j0 < n.-1) (A j (lift i j0)) * (B (lift i j0) h).
  by apply: eq_bigr => k _; rewrite !mxE.
rewrite -[RHS]big_filter.
suff ->: [seq i0 <- index_enum (ordinal_finType n) | i0 != i] = map (lift i) [seq _ <- index_enum (ordinal_finType n.-1) | true]
  by rewrite big_map big_filter.
rewrite filter_predT /index_enum -!enumT.
exact: predC1_enum.
Qed.

Lemma row'_eq (R : realFieldType) (n : nat) (x : 'cV[R]_n.-1) (i : 'I_n) (K : R) :
  let: y := \col_(k < n) match (unlift i k) with | Some j => x j 0 | None => K end in
    row' i y = x.
Proof.
by apply/colP => k; rewrite !mxE (liftK i).
Qed.

End ExtraMx.

Section QuasiInverse.

Section Core.

Variable R : realFieldType.
Variable m n: nat.

Hypothesis emn : m = n.
Variable M: 'M[R]_(m,n).


Definition qinvmx := (castmx (erefl n, esym emn) (invmx (castmx (emn, erefl n) M))).

Hypothesis Hrow_free : row_free M.

Lemma qinvmx_unitmx : castmx (emn, erefl n) M \in unitmx.
Proof.
rewrite -row_free_unit -row_leq_rank rank_castmx.
by rewrite -[X in (X <= _)%N]emn row_leq_rank.
Qed.

Lemma qmulmxV : M *m qinvmx = 1%:M.
Proof.
apply: (castmx_inj (em := emn) (en := (erefl m))).
rewrite castmx_mul castmx_id.
rewrite -[X in X *m _](castmx_id (erefl _, erefl _)) -castmx_mul.
rewrite mulmxV; last exact: qinvmx_unitmx.
apply/matrixP => i j.
- rewrite 2!castmxE /= 2!cast_ord_id esymK 2!mxE.
  do 2![apply: congr1]; apply/eqP/eqP => [-> | <-];
  by rewrite ?cast_ordK ?cast_ordKV.
Qed.

Lemma qmulVmx : qinvmx *m M = 1%:M.
Proof.
rewrite -[X in _ *m X](castmx_id (erefl _, erefl _)) -mulmx_cast.
by rewrite mulVmx; last exact: qinvmx_unitmx.
Qed.

Lemma qmulKmx (p: nat) (x: 'M_(n,p)) : qinvmx *m (M *m x) = x.
Proof.
by rewrite mulmxA qmulVmx mul1mx.
Qed.

Lemma qmulKVmx (p: nat) (x: 'M_(m,p)) : M *m (qinvmx *m x) = x.
Proof.
by rewrite mulmxA qmulmxV mul1mx.
Qed.

Lemma qmulmxK (p: nat) (x: 'M_(p,m)): (x *m M) *m qinvmx = x.
Proof.
by rewrite -mulmxA qmulmxV mulmx1.
Qed.

Lemma qmulmxKV (p: nat) (x: 'M_(p,n)): (x *m qinvmx) *m M = x.
Proof.
by rewrite -mulmxA qmulVmx mulmx1.
Qed.

End Core.

Section Extra.

Variable R : realFieldType.
Variable m n: nat.

Hypothesis emn : m = n.
Variable M: 'M[R]_(m,n).

Hypothesis Hrow_free : row_free M.

Lemma trmx_qinv : (qinvmx emn M)^T = (qinvmx (esym emn) M^T).
Proof.
set M' := (qinvmx (esym emn) M^T)^T.
suff: M' *m M = 1%:M.
- rewrite -{1}(qmulVmx emn Hrow_free).
  move/(row_free_inj Hrow_free) <-.
  by rewrite trmxK.
- apply: trmx_inj.
  rewrite trmx1 trmx_mul trmxK.
  apply: qmulmxV.
  by rewrite -row_leq_rank mxrank_tr  -[X in (X <= _)%N]emn row_leq_rank.
Qed.

End Extra.
End QuasiInverse.

Section TrmxAux.

Variable R: realFieldType.

(* Auxiliary Lemmas about trmx *)
Lemma trmx_add (d1 d2 : nat) (M1: 'M[R]_(d1, d2)) (M2: 'M[R]_(d1, d2)) :
  (M1 + M2)^T = M1^T + M2^T.
Proof.
  by apply/matrixP => ? ?; rewrite !mxE.
Qed.

Lemma trmx_sub (d1 d2: nat) (M1: 'M[R]_(d1, d2)) (M2: 'M[R]_(d1, d2)) :
  (M1 - M2)^T = M1^T - M2^T.
Proof.
  by apply/matrixP => ? ?; rewrite !mxE.
Qed.

Lemma trmx_rmul (m n : nat) (M: 'M[R]_(m, n)) (v: 'rV[R]_n) :
  M *m v^T = (v *m M^T)^T.
Proof.
  have H : (M^T)^T = M by rewrite trmxK.
  by rewrite -[M in M *m _]H trmx_mul.
Qed.

Lemma trmx_lmul (m n : nat) (M: 'M[R]_(_, m)) (v: 'cV[R]_n) :
  M^T *m v = (v^T *m M)^T.
Proof.
  by rewrite trmx_mul trmxK.
Qed.

End TrmxAux.


Section PickInKer.

Variable m n: nat.
Variable R: realFieldType.
Variable A: 'M[R]_(m,n).

Definition pick_in_ker :=
  let M := kermx A^T in
  match [pick j | row j M != 0] with
  | Some j => (row j M)^T
  | None => 0
  end.

Lemma pick_in_kerP : A *m pick_in_ker = 0.
Proof.
rewrite /pick_in_ker.
case: pickP => [i|].
- set v := row i _.
  move => v_neq0.
  suff /(congr1 trmx): v *m A^T = 0.
  + by rewrite trmx_mul trmxK trmx0.
  + by move/sub_kermxP: (row_sub i (kermx A^T)).
- by rewrite mulmx0.
Qed.

Lemma pick_in_ker_neq0 : (\rank A < n)%N -> pick_in_ker != 0.
Proof.
move => rk_lt_n.
rewrite /pick_in_ker; case: pickP => [i |].
- by apply: contraNneq; move/(congr1 trmx); rewrite trmxK trmx0 => ->.
- move => no_non_null_row.
  have ker_eq0: (kermx A^T = 0).
  + apply/row_matrixP => i; rewrite row0.
    move/(_ i): no_non_null_row.
    by move/negbT; rewrite negbK => /eqP.
  move: (mxrank_ker A^T); rewrite ker_eq0 mxrank0 mxrank_tr.
  move/eqP; rewrite eq_sym subn_eq0.
  move/leq_ltn_trans/(_ rk_lt_n).
  by rewrite ltnn.
Qed.

End PickInKer.

Section RowFree.
Variable R : realFieldType.

Lemma row_free_free {m n : nat} (A : 'M[R]_(m,n)) :
  row_free A = free [seq row i A | i <- enum 'I_m].
Proof.
have/perm_free ->: perm_eq [seq row i A | i <- enum 'I_m] [tuple row i A | i < m] by [].
apply/idP/freeP => [/mulmx_free_eq0 mulAeq0 k|mulA0].
  under eq_bigr do rewrite -tnth_nth tnth_map tnth_ord_tuple.
  move=> kA0 i; have /eqP : \row_i k i *m A = 0.
    by rewrite mulmx_sum_row; under eq_bigr do rewrite mxE.
  by rewrite mulAeq0 => /eqP/rowP/(_ i); rewrite !mxE.
apply/inj_row_free => v; rewrite mulmx_sum_row => vA0.
apply/rowP => i; rewrite mxE mulA0//.
by under eq_bigr do rewrite -tnth_nth tnth_map tnth_ord_tuple.
Qed.

End RowFree.

Section ExtraKer.

Context {R : realFieldType} (m n: nat) (A : 'M[R]_(m,n)).

Lemma rank1_ker {p : nat} (x y : 'M[R]_(p, m)): \rank (kermx A) = 1%nat ->
  x *m A = 0 -> y *m A = 0 -> y = 0 \/ exists lambda, x = lambda *m y.
Proof.
move=> rank1 /sub_kermxP x_ker /sub_kermxP y_ker.
case/boolP: (y == 0)=> [/eqP ->| y_n0]; first by left. right.
apply/submxP; suff ->: (y :=: kermx A)%MS by [].
apply/eqmxP; move/eq_leqif: (mxrank_leqif_eq y_ker)=> <-.
move: y_n0 (mxrankS y_ker); rewrite rank1 -mxrank_eq0.
by case: (\rank y)=> // n' _; rewrite eqSS; case: n'.
Qed.

End ExtraKer.

Section SpanMatrix.

Lemma vbasis_mat {k n : nat} {R : realFieldType} (S : k.-tuple 'rV[R]_n):
  (\matrix_i tnth S i == 
  \matrix_i tnth (vbasis <<S>>) i)%MS.
Proof.
apply/rV_eqP=> u; apply/idP/idP.
- case/submxP=> c ->; rewrite mulmx_sum_row.
  under eq_bigr=> i _ do rewrite rowK.
  apply/summx_sub=> i _; apply/scalemx_sub.
  apply/submxP; exists (\row_j coord (vbasis <<S>>%VS) j (tnth S i)).
  rewrite mulmx_sum_row; under eq_bigr=> j _ do rewrite rowK mxE [X in _ *: X](tnth_nth 0).
  exact/coord_vbasis/memv_span/mem_tnth.
- case/submxP=> c ->; rewrite mulmx_sum_row.
  under eq_bigr=> i _ do rewrite rowK.
  apply/summx_sub=> i _; apply/scalemx_sub.
  apply/submxP; exists (\row_j coord S j (tnth (vbasis <<S>>%VS) i)).
  rewrite mulmx_sum_row; under eq_bigr=> j _ do rewrite rowK mxE [X in _ *: X](tnth_nth 0).
  exact/coord_span/vbasis_mem/mem_tnth.
Qed.

Lemma span_matrix_rV {n k : nat} {R : realFieldType} (S : k.-tuple 'rV[R]_n):
  \dim (span S) = \rank (\matrix_(i < k) (tnth S i)).
Proof.
rewrite (eqmx_rank (vbasis_mat _)).
apply/anti_leq/andP; split; last by rewrite rank_leq_row.
rewrite row_leq_rank row_free_free; apply/(basis_free (U:=(span S))).
under eq_map=> i do rewrite rowK; rewrite map_tnth_enum.
exact/vbasisP.
Qed.

Lemma span_matrix_cV {n k : nat} {R : realFieldType} (S : k.-tuple 'cV[R]_n):
  \dim (span S) = \rank (\matrix_(i < n, j < k) tnth S j i 0).
Proof.
set A := matrix_of_fun _ _.
have ->: A = (\matrix_i tnth (map_tuple trmx S) i)^T by 
  apply/matrixP=> i j; rewrite !mxE tnth_map !mxE.
rewrite mxrank_tr -span_matrix_rV /=.
set St := map _ _.
have ->: St = [seq (linfun trmx) i | i <- S] by 
  under eq_map=> x do rewrite lfunE /=.
rewrite -limg_span limg_dim_eq //=.
suff ->: lker (linfun trmx) = 0%VS by rewrite capv0.
move=> F p q; apply/eqP/lker0P=> x y; rewrite !lfunE /=.
exact/trmx_inj.
Qed.

End SpanMatrix.
