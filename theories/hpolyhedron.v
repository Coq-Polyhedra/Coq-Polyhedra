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
Require Import simplex barycenter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Delimit Scope poly_scope with PH.

Module Base.
Section Base.

Variable (R : realFieldType) (n : nat).

Definition opp_base_elt (b : ('cV[R]_n * R)%type) : ('cV[R]_n * R)%type := (- (fst b), - (snd b)).

End Base.
End Base.

Notation "'base_elt' [ R , n ]" := ('cV[R]_n * R)%type (at level 2).
Notation "'base_elt'" := (base_elt[_,_]) (at level 2).
Notation "'base_t' [ R , n ]" := {fset base_elt[R,n]} (at level 2).
Notation "'base_t'" := (base_t[_,_]) (at level 2).
Notation "- e" := (Base.opp_base_elt e) : poly_scope.

Section PWeight.

Variable (R : realFieldType) (n : nat) (base : base_t[R,n]).

Definition pweight (w : {fsfun base_elt[R,n] -> R for fun => 0%R}) :=
  (finsupp w `<=` base)%fset && [forall v : base, w (val v) >= 0].

Definition combine w : base_elt :=
  (\sum_(v : base) (w (val v)) *: (fst (val v)), \sum_(v : base) (w (val v)) * (snd (val v))).

Lemma pweight_ge0 w : pweight w -> forall e, w e >= 0.
Proof.
move/andP => [w_supp /forallP w_ge0] e.
case: finsuppP => [| e_in_supp]; first done.
suff e_in_base: e \in base.
- pose v := [`e_in_base]%fset.
  by move/(_ v): w_ge0.
- by move: e e_in_supp; apply/fsubsetP.
Qed.

End PWeight.

Module HPolyhedron.

Section Def.

Variable (R : realFieldType) (n : nat).

Record hpoly := HPoly {
  nb_ineq : nat ;
  _ : 'M[R]_(nb_ineq,n) ;
  _ : 'cV[R]_nb_ineq
}.

Definition mem_hpoly P : {pred 'cV[R]_n} :=
  let: HPoly _ A b := P in
  [pred x : 'cV_n | (A *m x) >=m b].
Coercion mem_hpoly : hpoly >-> pred_sort.

End Def.

Notation "''hpoly[' R ]_ n" := (hpoly R n) (at level 8).
Notation "''hpoly_' n" := (hpoly _ n) (at level 8).

Section Choice.

Variable R : realFieldType.
Variable n : nat.

Definition matrix_from_hpoly (P : 'hpoly[R]_n) :=
  let: HPoly _ A b := P in
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

End Choice.

Section PolyPred.

Context {R : realFieldType} {n : nat}.

Implicit Type (P : 'hpoly[R]_n).

Definition mk_hs (b : base_elt[R,n]) : 'hpoly[R]_n := HPoly (b.1)^T (b.2)%:M.

Lemma in_hs b x : x \in (mk_hs b ) = ('[b.1,x] >= b.2).
Proof.
rewrite inE vdotC -vdot_def.
by apply/forallP/idP => [ /(_ 0) | H i]; rewrite ?[i]ord1_eq0 !mxE /= !mulr1n.
Qed.

Definition poly0 := mk_hs (0,1).

Lemma in_poly0 : poly0 =i pred0.
Proof.
by move => x; rewrite in_hs vdot0l inE ler10.
Qed.

Definition polyT : 'hpoly[R]_n := @HPoly _ _ 0 (const_mx 0) 0.

Lemma in_polyT : polyT =i predT.
Proof.
by move => x; rewrite !inE mul0mx lev_refl.
Qed.

Definition polyI P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    HPoly (col_mx A A') (col_mx b b').

Lemma in_polyI P Q : (polyI P Q) =i [predI P & Q].
Proof.
move => x.
case: P => mP AP bP; case: Q => mQ AQ bQ.
by rewrite !inE mul_col_mx col_mx_lev.
Qed.

Definition bounded P c :=
  let: HPoly _ A b := P in
    Simplex.bounded A b c.

Definition opt_value P c :=
  let: HPoly _ A b := P in
    Simplex.opt_value A b c.

Definition poly_subset P Q :=
  let: HPoly _ A b := P in
  let: HPoly _ A' b' := Q in
    (~~ Simplex.feasible A b) ||
      [forall i, (Simplex.bounded A b (row i A')^T) && (Simplex.opt_value A b (row i A')^T >= b' i 0)].

Lemma poly_subsetP {P Q : 'hpoly[R]_n} :
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

Lemma poly_subsetPn {P Q : 'hpoly[R]_n} :
  reflect (exists2 x, x \in P & x \notin Q) (~~ (poly_subset P Q)).
Proof. (* RK *)
case: P => m A b; case: Q => m' A' b'.
apply: (iffP idP) => [| [?] ? not_in_Q];
  last by move: not_in_Q; apply/contra; move/poly_subsetP ->.
rewrite negb_or negbK negb_forall.
move/andP => [feasible_P /existsP [i /nandP unbounded_or]].
have unbounded_suff:
  ~~ Simplex.bounded A b (row i A')^T -> exists2 x : 'cV_n, (x \in HPoly A b) & (x \notin HPoly A' b').
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

Lemma boundedP (P : 'hpoly[R]_n) c :
  reflect (exists2 x, (x \in P) & poly_subset P (mk_hs (c, '[c,x]))) (bounded P c).
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
    by move => y /incl_hs; rewrite in_hs.
  split.
  + by exists x.
  + move => y /incl_hs.
    by rewrite in_hs -opt_value_eq.
Qed.

Lemma boundedPn P c :
  ~~ (poly_subset P poly0) ->
    reflect (forall K, ~~ (poly_subset P (mk_hs (c, K)))) (~~ bounded P c).
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
  ~~ (poly_subset P poly0) ==>
  let: HPoly _ A _ := P in
    Simplex.pointed A.

Lemma pointedPn P :
  ~~ (poly_subset P poly0) ->
    reflect (exists (d : 'cV[R]_n), ((d != 0) /\ (forall x, x \in P -> (forall λ, x + λ *: d \in P)))) (~~ pointed P).
Proof. (* RK *)
case: P => m A b non_empty_P.
rewrite /pointed non_empty_P /=.
have feasible_P: exists x, x \in HPoly A b
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

Definition poly_equiv P Q := (poly_subset P Q) && (poly_subset Q P).

Lemma poly_equivP {P Q : 'hpoly[R]_n} : reflect (P =i Q) (poly_equiv P Q).
Proof.
apply/(iffP andP) => [[/poly_subsetP P_le_Q /poly_subsetP Q_le_P] x | P_eq_Q ].
- apply/idP/idP; [exact: P_le_Q | exact: Q_le_P].
- by split; apply/poly_subsetP => x; rewrite P_eq_Q.
Qed.

Lemma poly_equiv_refl : reflexive poly_equiv.
Proof.
by move => P; apply/poly_equivP.
Qed.

Lemma poly_equiv_sym : symmetric poly_equiv.
Proof.
by move => P Q; apply: (sameP poly_equivP);
   apply: (iffP poly_equivP) => [H x | H x]; rewrite H.
Qed.

Lemma poly_equiv_trans : transitive poly_equiv.
Proof.
move => P' P P'' /poly_equivP P_eq_P' /poly_equivP P'_eq_P''.
by apply/poly_equivP => x; rewrite P_eq_P'.
Qed.

Section Farkas.

Variable (base : base_t[R,n]).

Let P := \big[polyI/polyT]_(b : base) (mk_hs (val b)).

Definition nth_fset (K : choiceType) (V : {fset K}) (i : 'I_#|predT : pred V|) :=
  val (enum_val i).

Lemma nth_fsetP (K : choiceType) (V : {fset K}) (i : 'I_#|predT : pred V|) :
  nth_fset i \in V.
Proof.
rewrite /nth_fset; exact: fsvalP.
Qed.

Notation m := #| xpredT : pred base |.

Let A := \matrix_(i < m) ((nth_fset i).1)^T.
Let b := \col_(i < m) ((nth_fset i).2).

Fact valP' (v : base) : v \in (xpredT : pred base).
by [].
Qed.

Definition vect_to_pweight (w : 'cV[R]_m) :=
  [fsfun v : base => w (enum_rank_in (valP' v) v) 0] : {fsfun base_elt[R,n] -> R for fun => 0%R}.

Lemma vect_to_pweightP (w : 'cV[R]_m) :
  w >=m 0 -> pweight base (vect_to_pweight w).
Proof.
move/gev0P => w_pos.
apply/andP; split; first exact: finsupp_sub.
apply/forallP => e; rewrite fsfun_ffun /= insubT; first exact: fsvalP.
move => ? /=; exact: w_pos.
Qed.

Lemma combineE w :
  (A^T *m w = (combine base (vect_to_pweight w)).1)
  * ('[b, w] = (combine base (vect_to_pweight w)).2).
Proof.
split.
- rewrite /=; apply/colP => i; rewrite mxE summxE.
  rewrite (reindex (@enum_val _ base)) /=.
  + apply/eq_bigr => j _; rewrite /= !mxE mulrC; apply: congr2; last done.
    rewrite /vect_to_pweight fsfun_ffun /= insubT; first exact: fsvalP.
    move => H /=; apply: congr2; last done.
      by rewrite fsetsubE enum_valK_in.
  + apply: onW_bij; exact: enum_val_bij.
- rewrite /= /vdot.
  rewrite (reindex (@enum_val _ base)) /=.
  + apply/eq_bigr => j _; rewrite /= !mxE mulrC; apply: congr2; last done.
    rewrite /vect_to_pweight fsfun_ffun /= insubT; first exact: fsvalP.
    move => H /=; apply: congr2; last done.
      by rewrite fsetsubE enum_valK_in.
  + apply: onW_bij; exact: enum_val_bij.
Qed.

Lemma memP : P =i HPoly A b.
Proof.
move => x.
have -> : (x \in P) = (\big[andb/true]_(b : base) ('[(val b).1, x] >= (val b).2)).
by rewrite /P; elim/big_rec2: _ => [|i y b' Pi <-];
  rewrite ?in_polyT ?in_polyI ?inE; last by rewrite lev_scalar_mx vdotC vdot_def.
rewrite inE big_andE.
apply/forall_inP/forallP => [H i | H e _].
- move/(_ (enum_val i) isT): H => /=.
  by rewrite -row_vdot rowK trmxK mxE.
- move/(_ (enum_rank_in (valP' e) e)): H.
  rewrite -row_vdot rowK trmxK mxE.
  by rewrite /nth_fset enum_rankK_in.
Qed.

Lemma farkas (e : base_elt) :
  ~~ (poly_subset P poly0) -> (poly_subset P (mk_hs e)) ->
  exists2 w, (pweight base w) & ((combine base w).1 = e.1 /\ (combine base w).2 >= e.2).
Proof.
move => P_neq0 /poly_subsetP incl.
have incl' : poly_subset (HPoly A b) (mk_hs e).
- by apply/poly_subsetP => x; rewrite -memP; apply/incl.
case: (Simplex.simplexP A b e.1).
- move => ? /(intro_existsT (Simplex.infeasibleP _ _)).
  suff -> : Simplex.feasible A b by done.
  apply/Simplex.feasibleP.
  move/poly_subsetPn: P_neq0 => [x] [x_in_P _].
  by exists x; rewrite inE; rewrite memP in x_in_P.
- move => ? /(intro_existsT (Simplex.unboundedP_cert _ _ _))/Simplex.unboundedP/(_ e.2)
    [x [x_in_PAb ineq]].
  have /incl: x \in P by rewrite memP inE.
  by rewrite in_hs; move/(ltr_le_trans ineq); rewrite ltrr.
- move => [x w] [x_feas w_feas csc].
  rewrite inE /= in w_feas; move/andP: w_feas => [/eqP w_feas1 w_pos].
    exists (vect_to_pweight w).
  + exact: vect_to_pweightP.
  + rewrite -2!combineE; split; first done.
    by rewrite -csc /=; rewrite -in_hs; apply/incl; rewrite memP inE.
Qed.

End Farkas.

End PolyPred.

Module Import Exports.
Canonical hpoly_eqType.
Canonical hpoly_choiceType.
Notation "''hpoly[' R ]_ n" := (@hpoly R n) (at level 8).
Notation "''hpoly_' n" := ('hpoly[_]_n) (at level 8).
End Exports.
End HPolyhedron.

Export HPolyhedron.Exports.
Coercion mem_hpoly := HPolyhedron.mem_hpoly.