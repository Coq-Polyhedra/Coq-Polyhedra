(**************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect           *)
(*                                                                        *)
(* (c) Copyright 2016, Xavier Allamigeon (xavier.allamigeon at inria.fr)  *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)   *)
(* All rights reserved.                                                   *)
(* You may distribute this file under the terms of the CeCILL-B license   *)
(**************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector.
Require Import extra_misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section ExtraMx.

Lemma scalar_mx_eq0 (R : realFieldType) (C : 'M[R]_1) : (C == 0) = (C 0 0 == 0).
Proof.
rewrite [C in LHS]mx11_scalar -scalemx1 scalemx_eq0.
by move/negbTE: (matrix_nonzero1 R 0) ->; rewrite orbF.
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

Lemma sum_col_mx (R : realFieldType) (m1 m2 n p: nat) (M: 'I_p -> 'M[R]_(m1,n)) (N: 'I_p -> 'M[R]_(m2,n)) :
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


End ExtraMx.

