(*************************************************************************)
(* Coq-Polyhedra: formalizing convex polyhedra in Coq/SSReflect          *)
(*                                                                       *)
(* (c) Copyright 2019, Xavier Allamigeon (xavier.allamigeon at inria.fr) *)
(*                     Ricardo D. Katz (katz at cifasis-conicet.gov.ar)  *)
(*                     Vasileios Charisopoulos (vharisop at gmail.com)   *)
(* All rights reserved.                                                  *)
(* You may distribute this file under the terms of the CeCILL-B license  *)
(*************************************************************************)

From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product vector_order extra_matrix row_submx.
Require Import simplex barycenter polypred.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

Module HPolyhedron.

Section Def.

Variable (R : realFieldType) (n : nat).

Record hpoly := HPoly {
  nb_ineq : nat ;
  _ : 'M[R]_(nb_ineq,n) ;
  _ : 'cV[R]_nb_ineq
}.

End Def.

Notation "''hpoly[' R ]_ n" := (hpoly R n) (at level 8).
Notation "''hpoly_' n" := (hpoly _ n) (at level 8).
Notation "'#ineq' P" := (nb_ineq P) (at level 0).
Notation "''P' ( m , A , b )" := (@HPoly _ _ m A b) (at level 0).
Notation "''P' ( A , b )" := 'P(_, A, b) (at level 0).

Section ChoicePred.

Variable R : realFieldType.
Variable n : nat.

Definition mem_hpoly (P : 'hpoly[R]_n) :=
  let: 'P(A,b) := P in
    [pred x : 'cV_n | (A *m x) >=m b] : pred_class.

Canonical hpoly_predType := mkPredType mem_hpoly.

Definition matrix_from_hpoly (P : 'hpoly[R]_n) :=
  let: 'P(A,b) := P in
    Tagged (fun m => 'M[R]_(m,n) * 'cV[R]_m)%type (A, b).

Definition hpoly_from_matrix (M : {m : nat & 'M[R]_(m,n) * 'cV[R]_m}%type) :=
  let: (A, b) := tagged M in
    HPoly A b.

Lemma matrix_from_hpolyK :
  cancel matrix_from_hpoly hpoly_from_matrix.
Proof.
by move => [m A b]; rewrite /matrix_from_hpoly /hpoly_from_matrix.
Qed.

Definition hpoly_eqMixin := CanEqMixin matrix_from_hpolyK.
Canonical hpoly_eqType := Eval hnf in EqType 'hpoly[R]_n hpoly_eqMixin.
Definition hpoly_choiceMixin := CanChoiceMixin matrix_from_hpolyK.
Canonical hpoly_choiceType := Eval hnf in ChoiceType 'hpoly[R]_n hpoly_choiceMixin.
Canonical hpoly_choicePredType := ChoicePredType _ 'hpoly[R]_n.

End ChoicePred.

Section PolyPred.

Variable R : realFieldType.
Variable n : nat.

Implicit Type (P : 'hpoly[R]_n).

Definition mk_hs c d : 'hpoly[R]_n := 'P(c^T, d%:M).

Lemma in_hs c d x : x \in (mk_hs c d) = ('[c,x] >= d).
Proof.
rewrite inE vdotC -vdot_def.
by apply/forallP/idP => [ /(_ 0) | H i]; rewrite ?[i]ord1_eq0 !mxE /= !mulr1n.
Qed.

Definition poly0 := mk_hs 0 1.

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => x; rewrite in_hs vdot0l inE ler10.
Qed.

Definition polyT : 'hpoly[R]_n := 'P(0, const_mx 0, 0).

Lemma in_polyT : polyT =i predT.
Proof.
by move => x; rewrite !inE mul0mx lev_refl.
Qed.

Definition polyI P Q :=
  let: 'P(A, b) := P in
  let: 'P(A', b') := Q in
    'P(col_mx A A', col_mx b b').

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
move => x.
case: P => mP AP bP; case: Q => mQ AQ bQ.
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Definition bounded P c :=
  let: 'P(A, b) := P in
    Simplex.bounded A b c.

Definition opt_value P c :=
  let: 'P(A, b) := P in
    Simplex.opt_value A b c.

Definition poly_subset P Q :=
  let: 'P(A, b) := P in
  let: 'P(A', b') := Q in
    (~~ Simplex.feasible A b) ||
      [forall i, (Simplex.bounded A b (row i A')^T) && (Simplex.opt_value A b (row i A')^T >= b' i 0)].

Lemma poly_subsetP P Q :
  reflect {subset P <= Q} (poly_subset P Q).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [/orP poly_subset_P_Q | subset_P_Q].
- case: poly_subset_P_Q => [empty_P | /forallP hs_incl x x_in_P].
  + move => x x_in_P.
    move: empty_P; apply/contraR => _.
    by apply/Simplex.feasibleP; exists x.
  + apply/forallP => i.
    move/andP: (hs_incl i) => [/Simplex.boundedP [_ opt_is_opt] ?].
    apply: (@ler_trans _ (Simplex.opt_value A b (row i A')^T) _ _); first by done.
    by rewrite -row_vdot; apply: opt_is_opt.
- apply/orP.
  case: (boolP (Simplex.feasible A b)) => [feasible_P | _]; last by left.
  right.
  apply/forallP => i.
  suff bounded_P_row_i_A': Simplex.bounded A b (row i A')^T.
    apply/andP; split; first exact: bounded_P_row_i_A'.
    move/Simplex.boundedP: bounded_P_row_i_A' => [[x [/subset_P_Q  x_in_Q <-]] _].
    rewrite row_vdot.
    exact: ((forallP x_in_Q) i).
  apply/(Simplex.boundedP_lower_bound _ feasible_P).
  exists (b' i 0).
  move => x /subset_P_Q x_in_Q.
  rewrite row_vdot.
  exact: ((forallP x_in_Q) i).
Qed.

Lemma poly_subsetPn P Q :
  reflect (exists2 x, x \in P & x \notin Q) (~~ (poly_subset P Q)).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [| [?] ? not_in_Q];
  last by move: not_in_Q; apply/contra; move/poly_subsetP ->.
rewrite negb_or negbK negb_forall.
move/andP => [feasible_P /existsP [i /nandP unbounded_or]].
have unbounded_suff:
  ~~ Simplex.bounded A b (row i A')^T -> exists2 x : 'cV_n, (x \in 'P (A, b)) & (x \notin 'P (A', b')).
  rewrite -(Simplex.unbounded_is_not_bounded _ feasible_P) => /Simplex.unboundedP unbounded_P_row_i_A'.
  move: (unbounded_P_row_i_A' (b' i 0)) => [x [x_in_P ineq]].
  exists x; try by done.
  move: ineq; apply: contraL => x_in_Q.
  rewrite -lerNgt row_vdot.
  exact: ((forallP x_in_Q) i).
case: unbounded_or; first exact: unbounded_suff.
case: (boolP (Simplex.bounded A b (row i A')^T)) => [? | ? _]; last by apply: unbounded_suff.
rewrite -ltrNge => ineq.
exists (Simplex.opt_point A b (row i A')^T); first exact: Simplex.opt_point_is_feasible.
move: ineq; apply: contraL => opt_point_in_Q.
rewrite -lerNgt /Simplex.opt_value row_vdot.
exact: ((forallP opt_point_in_Q) i).
Qed.

Lemma boundedP P c :
  reflect (exists2 x, (x \in P) & poly_subset P (mk_hs c '[c,x])) (bounded P c).
Proof. (* RK *)
case: P => m A b.
apply/(equivP (Simplex.boundedP A b c) _);
  split => [[[x [? opt_value_eq]] opt_value_is_opt] | [x ? /poly_subsetP incl_hs]].
- exists x; first by done.
  apply/poly_subsetP => y y_in_P.
  rewrite in_hs opt_value_eq.
  by apply: opt_value_is_opt.
- have opt_value_eq: '[ c, x] = Simplex.opt_value A b c.
    apply: Simplex.opt_value_is_optimal; first by done.
    move => y y_in_P.
    rewrite -in_hs.
    exact: (incl_hs _ y_in_P).
  split.
  + by exists x.
  + move => y y_in_P.
    rewrite -in_hs -opt_value_eq.
    exact: (incl_hs _ y_in_P).
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs c K))) (~~ bounded P c).
Proof. (* RK *)
case: P => m A b non_empty_P.
have feasible_P: Simplex.feasible A b
  by move/poly_subsetPn: non_empty_P => [x ? _];
  apply/Simplex.feasibleP; exists x.
rewrite /bounded (Simplex.bounded_is_not_unbounded c feasible_P) negbK.
apply/(equivP (Simplex.unboundedP A b c) _);
  split => [unbounded_cond_point K | unbounded_cond_hs K].
- apply/poly_subsetPn.
  move: (unbounded_cond_point K) => [x [? val_x_sineq]].
  exists x; first by done.
  by rewrite in_hs -ltrNge.
- move/poly_subsetPn: (unbounded_cond_hs K) => [x ? x_not_in_hs].
  exists x; split; first by done.
  by rewrite in_hs -ltrNge in x_not_in_hs.
Qed.

Definition pointed P :=
  let: 'P(A, _) := P in
    Simplex.pointed A.

Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
case: P => m A b non_empty_P.
have feasible_P: exists x, x \in 'P (A, b)
  by move/poly_subsetPn: non_empty_P => [x ? _]; exists x.
apply/(equivP (Simplex.pointedPn A) _); split =>
  [[d [? /Simplex.feasible_dirP d_feas_dir /Simplex.feasible_dirP md_feas_dir]] | [d [? d_recession_dir]]];
    exists d; split; try by done.
- move => x x_in_P λ.
  case: (boolP (0 <= λ)) => [? | ?].
  + by apply: d_feas_dir.
  + rewrite -[d]opprK scalerN -scaleNr.
    apply: md_feas_dir; try by done.
    by rewrite oppr_ge0; apply: ltrW; rewrite ltrNge.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  by move => x x_in_P λ _; apply: d_recession_dir.
- apply/(@Simplex.feasible_dirP _ _ _ _ b); try by done.
  move => x x_in_P λ _; rewrite scalerN -scaleNr.
  by apply: d_recession_dir.
Qed.

(* TO BE FIXED. The lock is here to prevent unfolding the definition. *)
Fact conv_key : unit. by []. Qed.
Definition conv (V : {fset 'cV[R]_n}) := locked_with conv_key poly0.

Lemma convP V x :
  reflect (exists2 w, [w \weight over V] & x = \bary[w] V) (x \in conv V).
Admitted. (* cannot be proved yet *)

(* In contrast, convexP can be proved immediately,
   this follows from the convexity of halfspaces *)
Lemma convexP P (V : {fset 'cV[R]_n}) :
  {subset V <= P} -> poly_subset (conv V) P.
Admitted.

Definition hpoly_polyPredMixin :=
  PolyPred.Mixin in_poly0 in_polyT in_polyI poly_subsetP poly_subsetPn
                 in_hs boundedP boundedPn pointedPn convP convexP.
Canonical hpoly_polyPredType := PolyPredType R n hpoly_polyPredMixin.

Definition poly_sort :=
  PolyPred.sort (Quotient.quot_polyPredType hpoly_polyPredType).
End PolyPred.

Module Import Exports.
Canonical hpoly_eqType.
Canonical hpoly_predType.
Canonical hpoly_choiceType.
Canonical hpoly_choicePredType.
Canonical hpoly_polyPredType.
Identity Coercion poly_sort_to_polypred: poly_sort >-> PolyPred.sort.
Notation "''hpoly[' R ]_ n" := (@hpoly R n) (at level 8).
Notation "''hpoly_' n" := (hpoly _ n) (at level 8).
Notation "''poly[' R ]_ n" := (@poly_sort R n) (at level 8).
Notation "''poly_' n" := 'poly[_]_n (at level 8).
Notation "'#ineq' P" := (nb_ineq P) (at level 0).
Notation "''P' ( m , A , b )" := (@HPoly _ _ m A b) (at level 0).
Notation "''P' ( A , b )" := 'P(_, A, b) (at level 0).
End Exports.
End HPolyhedron.

Export HPolyhedron.Exports.

Section HPolyhedronSpec.
(* YOUR ATTENTION PLEASE: hpolyP (provisional name) is intended to replace
 * every occurence of the ugly -reprK rewriting rule.
 * This is because hpolyP avoids specifying precisely which occurence
 * of (P : 'poly[R]_n) should be replaced by \repr P.
 * In this way, we just have a simple
 * case/hpoly: P => m A b
 * instead of a complicated
 * rewrite -{X,Y,-Z}[P]reprK; case: (\repr P) => m A b
 *)

Variable (R : realFieldType) (n : nat).

Variant hpoly_spec : 'poly[R]_n -> 'hpoly[R]_n -> {m & 'M[R]_(m,n) * 'cV[R]_m}%type -> Type :=
  HpolySpec (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
    hpoly_spec '['P(A,b)] 'P(A,b) (Tagged _ (A, b)).

Lemma hpolyP (P : 'poly[R]_n) :
  hpoly_spec P (\repr P) (HPolyhedron.matrix_from_hpoly (\repr P)).
Proof.
by rewrite -{1}[P]reprK; case: (\repr P).
Qed.

End HPolyhedronSpec.

(*Section Test.

Local Open Scope poly_scope.

Variable (R : realFieldType) (n : nat) (P : {quot 'hpoly[R]_n}) (c x : 'cV[R]_n) (Q : 'hpoly[R]_n).

Hypothesis H : bounded P c.
Check (x \in \repr P).
Check (x \in Q).
Check (opt_point H).
Check (`[line c & x] : 'hpoly[R]_n).
Check (\repr P) : 'hpoly[R]_n.

Goal P = '[\repr P].
Proof.
by rewrite reprK.
Qed.
End Test.*)

Section HPolyEq.

Variable (R : realFieldType) (n : nat).

Definition hpolyEq_of_set (base : 'hpoly[R]_n) :=
  let: 'P(A,b) as P := base in
    fun (J : {set 'I_(#ineq P)}) =>
      let AJ := col_mx A (-(row_submx A J)) in
      let bJ := col_mx b (-(row_submx b J)) in
        'P(AJ, bJ).

Notation "''P^=' ( P ; J )" := (@hpolyEq_of_set P J) : poly_scope.
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J) : poly_scope.

Fact in_hpolyEq (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) :
  (x \in 'P^=(A, b; J)) = (x \in 'P(A, b)) && [forall j in J, ((A *m x) j 0 == b j 0)].
Proof.
rewrite !inE mul_col_mx col_mx_lev mulNmx -row_submx_mul lev_opp2 /=.
apply/andP/andP.
- move => [x_in_P ineqJ]; split; try by done.
  suff /row_submx_colP H: row_submx (A *m x) J = row_submx b J.
  + apply/forall_inP => j j_in_J.
    move/(_ _ j_in_J): H ->; exact: eq_refl.
  + apply: lev_antisym; apply/andP; split; try by done.
    exact: row_submx_lev.
- move => [x_in_P /forall_inP eqJ]; split; try by done.
  apply/row_submx_levP => j j_in_J.
  by move/(_ _ j_in_J)/eqP: eqJ ->.
Qed.

Lemma in_hpolyEq_setT (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) :
  (x \in 'P^=(A, b; setT)) = (A *m x == b).
Proof. (* RK *)
rewrite in_hpolyEq.
apply/idP/idP => [/andP [_ /forallP forall_cond] | /eqP A_x_eq_b].
- apply/eqP/colP => j.
  by apply/eqP/(implyP (forall_cond j)).
- apply/andP; split.
  + rewrite inE A_x_eq_b.
    exact: lev_refl.
  + apply/forallP => j.
    apply/implyP => _.
    by rewrite A_x_eq_b.
Qed.

Lemma in_hpolyEqP (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) :
  reflect (x \in 'P(A, b) /\ forall j, j \in J -> (A *m x) j 0 = b j 0) (x \in 'P^=(A, b; J)).
Proof.
by rewrite in_hpolyEq; apply: (equivP andP);
  split; move => [x_in_PAb /eqfun_inP x_sat].
Qed.

Lemma hpolyEq_eq (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) j :
  x \in 'P^=(A, b; J) -> j \in J -> (A *m x) j 0 = b j 0.
Proof.
move => /in_hpolyEqP [_ x_act] j_in_J; exact: x_act.
Qed.

Lemma hpolyEq_ineqE (x : 'cV[R]_n) (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (J : {set 'I_m}) j :
  x \in 'P^=(A, b; J) -> j \in J ->
    (x \in `[hp (row j A)^T & b j 0] : 'hpoly[R]_n) = (x \in `[hs -(row j A)^T & -(b j 0)] : 'hpoly[R]_n).
Admitted.

Lemma hpolyEq_antimono (base : 'hpoly[R]_n) (I J : {set 'I_(#ineq base)}) :
  I \subset J -> 'P^=(base; J) `<=` 'P^=(base; I).
Proof.
Admitted.
(*case: base I J => [m A b] I J.
move => /subsetP I_subset_J x.
rewrite 2!in_hpolyEq.
move/andP => [x_in_P /forallP sat_in_J].
apply/andP; split.
- exact: x_in_P.
- apply/forallP => j.
  apply/implyP => j_in_I.
  apply: (implyP (sat_in_J j)).
  exact: (I_subset_J _ j_in_I).
Qed.*)

Lemma hpolyEq_antimono0 {base : 'hpoly[R]_n} {I} :
  'P^=(base; I) `<=` base.
Proof.
Admitted.
(*case : base I => [m A b] I.
by move => x /in_hpolyEqP [].
Qed.*)

Lemma hpolyEq_polyI (base: 'hpoly[R]_n) (I J : {set 'I_(#ineq base)}) :
  'P^=(base; I) `&` 'P^=(base; J) `=~` 'P^=(base; I :|: J).
Admitted.

Lemma polyEq_polyI (base: 'hpoly[R]_n) (I J : {set 'I_(#ineq base)}) :
  '['P^=(base; I)] `&` '['P^=(base; J)] = '['P^=(base; I :|: J)].
Proof.
rewrite quotE; apply/quotP; exact: hpolyEq_polyI.
Qed.

Lemma hpolyEq_big_polyI (base: 'hpoly[R]_n) (I : finType) (P : pred I) F :
  ~~ pred0b P -> \polyI_(i | P i) 'P^=(base; F i) `=~` 'P^=(base; \bigcup_(i | P i) (F i)).
Proof.
move: base F => [m A b] F /pred0Pn [i0 Pi0].
apply/andP; split; last first.
- apply/big_polyIsP => [i Pi]; apply/hpolyEq_antimono; exact: bigcup_sup.
- apply/poly_subsetP => x /in_big_polyI x_in.
  apply/in_hpolyEqP; split;
    first by move/(_ _ Pi0): x_in; exact: (poly_subsetP hpolyEq_antimono0).
  move => j /bigcupP => [[i]] Pi; apply: hpolyEq_eq; exact: x_in.
Qed.

Lemma polyEq_big_polyI (base: 'hpoly[R]_n) (I : finType) (P : pred I) F :
  ~~ pred0b P -> \polyI_(i | P i) '['P^=(base; F i)] = '['P^=(base; \bigcup_(i | P i) (F i))].
Proof.
rewrite quotE => ?; apply/quotP; exact: hpolyEq_big_polyI.
Qed.

Lemma hpolyEq_of_hpolyEq (base: 'hpoly[R]_n) I J : (* quite short proof after all! *)
  exists K, 'P^=('P^=(base; I); J) `=~` 'P^=(base; K).
Proof.
move: I J; case: base => [m A b] I J.
pose f (j : 'I_#ineq ('P^= (A, b; I))) :=
  match splitP' j with
  | SplitLo' j' _ => j'
  | SplitHi' k _ => (enum_val k)
  end.
pose K := I :|: (f @: J); exists K.
apply/andP; split; apply/poly_subsetP => x x_in.
- apply/in_hpolyEqP; split.
  + by move/(poly_subsetP hpolyEq_antimono0)/(poly_subsetP hpolyEq_antimono0): x_in.
  + move => k /setUP; case.
    * apply: hpolyEq_eq; move: x x_in; apply: (poly_subsetP hpolyEq_antimono0).
    * move/imsetP => [j'] j'_in_J ->; rewrite /f.
      case: (splitP' j') => [j j'_eq| j j'_eq].
      - by move/hpolyEq_eq/(_ j'_in_J) : x_in; rewrite j'_eq mul_col_mx !col_mxEu.
      - move/hpolyEq_eq/(_ j'_in_J) : x_in; rewrite j'_eq mul_col_mx !col_mxEd.
        rewrite mulNmx -row_submx_mul mxE [RHS]mxE 2!row_submx_mxE.
        exact: oppr_inj.
      - apply/in_hpolyEqP; split.
        move: x x_in; apply/poly_subsetP/hpolyEq_antimono; exact: subsetUl.
        move => j /(mem_imset f)/(subsetP (@subsetUr _ I _)) fj_in_K.
        move/hpolyEq_eq/(_ fj_in_K): x_in.
        rewrite /f; case: splitP' => [j' ->| j' -> eq].
        + by rewrite mul_col_mx !col_mxEu.
        + rewrite mul_col_mx !col_mxEd mulNmx -row_submx_mul mxE [RHS]mxE 2!row_submx_mxE.
          by rewrite eq.
Qed.

Lemma hpolyEq0 (base: 'hpoly[R]_n) :
  'P^=(base; set0) `=~` base.
Proof.
apply/poly_equivP; case: base => [m A b] x.
rewrite in_hpolyEq.
set t := (X in _ && X); suff ->: t by rewrite andbT.
by apply/forall_inP => i; rewrite in_set0.
Qed.

Lemma hpolyEq1 (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (i : 'I_m) :
  'P^=(A, b; [set i]) `=~` 'P(A,b) `&` `[hp (row i A)^T & b i 0].
Proof.
apply/poly_equivP => x; rewrite in_hpolyEq !inE; apply: congr1; rewrite row_vdot.
by apply/forall_inP/idP => [/(_ _ (set11 i)) | ? j /set1P ->].
Qed.


Lemma polyEq1 (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (i : 'I_m) :
  '['P^=(A, b; [set i])] = '['P(A,b)] `&` `[hp (row i A)^T & b i 0].
Proof.
rewrite !quotE; apply/quotP; exact: hpolyEq1.
Qed.

End HPolyEq.

Notation "''P^=' ( P ; J )" := (@hpolyEq_of_set _ _ P J) : poly_scope.
Notation "''P^=' ( A , b ; J )" := 'P^=('P(A,b); J) : poly_scope.

Section Duality.

Variable (R : realFieldType) (n : nat).

Lemma dual_opt_sol (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (c : 'cV[R]_n) (H : bounded 'P(A,b) c) :
    exists u, [/\ u >=m 0, c = A^T *m u & '[b, u] = opt_value H].
Admitted.
(*Proof.
move: (H) => H0. (* duplicate assumption *)
move: H; rewrite /bounded -Simplex.boundedP_cert.
set u := Simplex.dual_opt_point _ _ _ .
by move/and3P => [opt_point_in_P /andP [/eqP Au_eq_c u_le0] /eqP eq_value]; exists u.
Qed.*)

Lemma normal_cone_lower_bound (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) :
  u >=m 0 -> 'P(A, b) `<=` `[hs (A^T *m u) & '[b,u]].
Proof.
move => u_ge0; apply/poly_subsetP => x ?.
by rewrite inE -vdot_mulmx vdotC; apply: vdot_lev.
Qed.

Lemma normal_cone_bounded (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) :
  ('P(A, b) `>` `[poly0]) -> u >=m 0 -> bounded 'P(A,b) (A^T *m u).
Proof.
move => P_non_empty u_ge0; apply/bounded_lower_bound => //.
exists '[b,u]; exact: normal_cone_lower_bound.
Qed.

(*
Lemma opt_value_csc (m : nat) (A: 'M[R]_(m,n)) (b : 'cV[R]_m) (u : 'cV[R]_m) (x : 'cV[R]_n) :
  u >=m 0 -> x \in 'P(A,b) ->
    let c := A^T *m u in
      reflect (forall i, u i 0 > 0 -> (A *m x) i 0 = b i 0)
              ('[c,x] == '[b, u]).
Proof.
move => u_ge0 x_in_P /=.
have u_in_dual : u \in Simplex.dual_polyhedron A (A^T *m u)
 by rewrite inE eq_refl.
rewrite -subr_eq0 (Simplex.compl_slack_cond_duality_gap_equiv x_in_P u_in_dual).
apply/(iffP idP).
(* stupid proof, because of the fact that compl_slack_cond has not the right formulation (and compl_slack_condP doesn't help) *)
- move => Hcsc i u_i_gt0.
  move/forallP/(_ i): Hcsc; rewrite inE.
  by move/lt0r_neq0/negbTE: u_i_gt0 => -> /= /eqP.
- move => Hcsc; apply/forallP => i; rewrite -[X in X || _]negbK.
  have ->: (u i 0 != 0) = (u i 0 > 0)
      by rewrite lt0r; move/gev0P/(_ i): u_ge0 ->; rewrite andbT.
  by rewrite -implybE; apply/implyP; rewrite inE; move/Hcsc ->.
Qed.*)

End Duality.

(*
Section FeasibleBasicPoints. (* RK *)

Variable R : realFieldType.
Variable n : nat.

Definition feasible_basic_point (hP : 'hpoly[R]_n) (x : 'cV_n) :=
  let: 'P(A,b) := hP in
    (x \in 'P(A,b)) && (\rank (row_submx A (Simplex.active_ineq A b x)) >= n)%N.

Lemma feasible_basic_pointP (m : nat) (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (x : 'cV_n) :
  reflect (exists bas : Simplex.basis A, ((Simplex.is_feasible b) bas) /\ x = Simplex.point_of_basis b bas)
          (feasible_basic_point 'P(A,b) x).
Proof.
apply: (iffP idP) => [/andP [x_in rank_ineq] | [bas [bas_is_feasible ->]]].
- move: (row_base_correctness rank_ineq) => [H1 /eqP H2 H3].
  have is_basis: Simplex.is_basis A (Simplex.Prebasis H2) by apply/Simplex.is_basisP_rank.
  exists (Simplex.Basis is_basis).
  suff x_eq: x = Simplex.point_of_basis b (Simplex.Basis is_basis)
    by split; [rewrite /Simplex.is_feasible -Simplex.polyhedron_equiv_lex_polyhedron -x_eq | done].
  apply: Simplex.basis_subset_active_ineq_eq.
  by rewrite -Simplex.active_ineq_equal_active_lex_ineq.
- apply/andP; split.
  + rewrite Simplex.polyhedron_equiv_lex_polyhedron.
    exact: (Simplex.feasible_basis_is_feasible (Simplex.FeasibleBasis bas_is_feasible)).
  + apply: (@leq_trans (\rank (row_submx A (Simplex.set_of_prebasis (Simplex.prebasis_of_basis bas)))) _ _).
    * by rewrite (Simplex.is_basisP_rank A (Simplex.prebasis_of_basis bas) (Simplex.basis_is_basis bas)).
    * apply: mxrank_leqif_sup.
      apply: row_submx_subset_submx.
      rewrite Simplex.active_ineq_equal_active_lex_ineq.
      exact: (Simplex.basis_subset_of_active_ineq b bas).
Qed.

Lemma feasible_basic_point_pointedP (hP : 'hpoly[R]_n) :
  reflect (exists x, feasible_basic_point hP x) ((non_empty hP) && (pointed hP)).
Proof.
case: hP => m A b.
apply: (iffP idP) => [feasible_and_pointed | [x /andP [x_in_hP rank_ineq]]].
- rewrite -Simplex.exists_feasible_basis in feasible_and_pointed.
  move/set0Pn: feasible_and_pointed => [bas bas_is_feasible].
  exists (Simplex.point_of_basis b bas).
  apply/feasible_basic_pointP.
  exists bas.
  by split; [rewrite in_set in bas_is_feasible | done].
- apply/andP; split.
  + by apply/non_emptyP; exists x.
  + apply: (@leq_trans (\rank (row_submx A (Simplex.active_ineq A b x))) _ _); first exact: rank_ineq.
    apply: mxrank_leqif_sup.
    exact: (row_submx_submx A (Simplex.active_ineq A b x)).
Qed.

End FeasibleBasicPoints.
 *)
