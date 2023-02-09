(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra_misc inner_product lrel.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Declare Scope polyh_scope.
Delimit Scope polyh_scope with PH.

Local Open Scope polyh_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "''affine[' R ]_ n"
  (at level 8, n at level 2, format "''affine[' R ]_ n").
Reserved Notation "''affine[' R ]"
  (at level 8, format "''affine[' R ]").
Reserved Notation "''affine_' n"
  (at level 8, format "''affine_' n").
Reserved Notation "[ 'affine' I ]" (at level 0, format "[ 'affine'  I ]").
Reserved Notation "[ 'affine' U & Ω ]"
         (at level 0, format "[ 'affine'  U  &  Ω ]").
Reserved Notation "[ 'hp' e ]" (at level 0, format "[ 'hp'  e ]").
Reserved Notation "[ 'pt' Ω ]" (at level 0, format "[ 'pt'  Ω ]").
Reserved Notation "[ 'line' c & Ω ]"  (at level 0, format "[ 'line'  c  &  Ω ]").

Reserved Notation "'[' 'affine0' ']'" (at level 0).
Reserved Notation "'[' 'affineT' ']'" (at level 0).

(* -------------------------------------------------------------------- *)
Reserved Notation "\polyI_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \polyI_ i '/  '  F ']'").
Reserved Notation "\polyI_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \polyI_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \polyI_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\polyI_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \polyI_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \polyI_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \polyI_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\polyI_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\polyI_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \polyI_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \polyI_ ( i  <  n )  F ']'").
Reserved Notation "\polyI_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \polyI_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\polyI_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \polyI_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "x `<=` y `<=` z" (at level 70, y, z at next level).
Reserved Notation "x `<=` y `<` z" (at level 70, y, z at next level).
Reserved Notation "x `<` y `<=` z" (at level 70, y, z at next level).
Reserved Notation "x `<` y `<` z" (at level 70, y, z at next level).

Reserved Notation "x `>=` y" (at level 70, y at next level).
Reserved Notation "x `>` y" (at level 70, y at next level).

Reserved Notation "x `<=` y :> T" (at level 70, y at next level).
Reserved Notation "x `<` y :> T" (at level 70, y at next level).
Reserved Notation "x `>=` y :> T" (at level 70, y at next level).
Reserved Notation "x `>` y :> T" (at level 70, y at next level).

Reserved Notation "x `>=<` y" (at level 70, y at next level).
Reserved Notation "x `><` y" (at level 70, y at next level).

Reserved Notation "`<=` y" (at level 35).
Reserved Notation "`>=` y" (at level 35).
Reserved Notation "`<` y" (at level 35).
Reserved Notation "`>` y" (at level 35).
Reserved Notation "`>=<` y" (at level 35).
Reserved Notation "`><` y" (at level 35).
Reserved Notation "`<=` y :> T" (at level 35, y at next level).
Reserved Notation "`>=` y :> T" (at level 35, y at next level).
Reserved Notation "`<` y :> T" (at level 35, y at next level).
Reserved Notation "`>` y :> T" (at level 35, y at next level).
Reserved Notation "`>=<` y :> T" (at level 35, y at next level).
Reserved Notation "`><` y :> T" (at level 35, y at next level).

Reserved Notation "x `<=` y ?= 'iff' c"
  (at level 70, y, c at next level,
       format "x '[hv'  `<=`  y '/'  ?=  'iff'  c ']'").

Reserved Notation "x `<=` y ?= 'iff' c :> T"
  (at level 70, y, c at next level,
       format "x '[hv'  `<=`  y '/'  ?=  'iff'  c  :> T ']'").

(* -------------------------------------------------------------------- *)
Fact polyh_display : unit. Proof. exact: tt. Qed.

Notation poly_0    := (@Order.bottom polyh_display) (only parsing).
Notation poly_1    := (@Order.top polyh_display) (only parsing).
Notation poly_le   := (@Order.le polyh_display _) (only parsing).
Notation poly_lt   := (@Order.lt polyh_display _) (only parsing).
Notation poly_ge   := (@Order.ge polyh_display _) (only parsing).
Notation poly_gt   := (@Order.gt polyh_display _) (only parsing).
Notation poly_leif := (@Order.leif polyh_display _) (only parsing).
Notation poly_cmp  := (@Order.comparable polyh_display _) (only parsing).
Notation poly_meet := (@Order.meet polyh_display _).

Notation "<=%PH"  := poly_le   : fun_scope.
Notation ">=%PH"  := poly_ge   : fun_scope.
Notation "<%PH"   := poly_lt   : fun_scope.
Notation ">%PH"   := poly_gt   : fun_scope.
Notation "<?=%PH" := poly_leif : fun_scope.
Notation ">=<%PH" := poly_cmp  : fun_scope.
Notation "><%PH"  := (fun x y => ~~ (poly_cmp x y)) : fun_scope.

Notation "`<=` y" := (poly_ge y) : polyh_scope.
Notation "`<=` y :> T" := (`<=` (y : T)) (only parsing) : polyh_scope.
Notation "`>=` y"  := (poly_le y) : polyh_scope.
Notation "`>=` y :> T" := (`>=` (y : T)) (only parsing) : polyh_scope.

Notation "`<` y" := (poly_gt y) : polyh_scope.
Notation "`<` y :> T" := (`<` (y : T)) (only parsing) : polyh_scope.
Notation "`>` y" := (poly_lt y) : polyh_scope.
Notation "`>` y :> T" := (`>` (y : T)) (only parsing) : polyh_scope.

Notation "`>=<` y" := (poly_cmp y) : polyh_scope.
Notation "`>=<` y :> T" := (`>=<` (y : T)) (only parsing) : polyh_scope.

Notation "`><` y" := (fun x => ~~ (poly_cmp y x)) : polyh_scope.
Notation "`><` y :> T" := (`><` (y : T)) (only parsing) : polyh_scope.

Notation "x `<=` y" := (poly_le x y) : polyh_scope.
Notation "x `<=` y :> T" := ((x : T) `<=` (y : T)) (only parsing) : polyh_scope.
Notation "x `>=` y" := (y `<=` x) (only parsing) : polyh_scope.
Notation "x `>=` y :> T" := ((x : T) `>=` (y : T)) (only parsing) : polyh_scope.

Notation "x `<` y"  := (poly_lt x y) : polyh_scope.
Notation "x `<` y :> T" := ((x : T) `<` (y : T)) (only parsing) : polyh_scope.
Notation "x `>` y"  := (y `<` x) (only parsing) : polyh_scope.
Notation "x `>` y :> T" := ((x : T) `>` (y : T)) (only parsing) : polyh_scope.

Notation "x `<=` y `<=` z" := ((x `<=` y) && (y `<=` z)) : polyh_scope.
Notation "x `<` y `<=` z" := ((x `<` y) && (y `<=` z)) : polyh_scope.
Notation "x `<=` y `<` z" := ((x `<=` y) && (y `<` z)) : polyh_scope.
Notation "x `<` y `<` z" := ((x `<` y) && (y `<` z)) : polyh_scope.

Notation "x `<=` y ?= 'iff' C" := (poly_leif x y C) : polyh_scope.
Notation "x `<=` y ?= 'iff' C :> R" := ((x : R) `<=` (y : R) ?= iff C)
  (only parsing) : polyh_scope.

Notation "x `>=<` y" := (poly_cmp x y) : polyh_scope.
Notation "x >< y" := (~~ (poly_cmp x y)) : polyh_scope.

Notation "P `&` Q" := (poly_meet P Q) (at level 48, left associativity) : polyh_scope.

Notation "\meet_ ( i <- r | P ) F" :=
  (\big[poly_meet/poly_1]_(i <- r | P%B) F).
Notation "\meet_ ( i <- r ) F" :=
  (\big[poly_meet/poly_1]_(i <- r) F).
Notation "\meet_ ( i | P ) F" :=
  (\big[poly_meet/poly_1]_(i | P%B) F).
Notation "\meet_ i F" :=
  (\big[poly_meet/poly_1]_i F).
Notation "\meet_ ( i : I | P ) F" :=
  (\big[poly_meet/poly_1]_(i : I | P%B) F) (only parsing).
Notation "\meet_ ( i : I ) F" :=
  (\big[poly_meet/poly_1]_(i : I) F) (only parsing).
Notation "\meet_ ( m <= i < n | P ) F" :=
 (\big[poly_meet/poly_1]_(m <= i < n | P%B) F).
Notation "\meet_ ( m <= i < n ) F" :=
 (\big[poly_meet/poly_1]_(m <= i < n) F).
Notation "\meet_ ( i < n | P ) F" :=
 (\big[poly_meet/poly_1]_(i < n | P%B) F).
Notation "\meet_ ( i < n ) F" :=
 (\big[poly_meet/poly_1]_(i < n) F).
Notation "\meet_ ( i 'in' A | P ) F" :=
 (\big[poly_meet/poly_1]_(i in A | P%B) F).
Notation "\meet_ ( i 'in' A ) F" :=
 (\big[poly_meet/poly_1]_(i in A) F).

Section Solve.

Variable (R : realFieldType) (n : nat) (V : {vspace lrel[R]_n}).

Let base := vbasis V.

Definition sat x :=
   all (fun e : lrel => '[e.1, x] == e.2) base.

Lemma sum_lrel_fst m (v : 'I_m -> lrel[R]_n) : (* RK : I have added this auxiliary lemma. Should it be somewhere else? *)
  (\sum_(i < m) v i).1 = (\sum_(i < m) (v i).1).
Proof.
by apply: (@big_morph _ lrel[R]_n (fun y => y.1)).
Qed.

(*TODO : change the name, and maybe put this lemma somewhere else *)
Lemma sum_lrel_fst_gen (F : finType) (P : pred F) (v : F -> lrel[R]_n) :
  (\sum_(i : F | P i) v i).1 = (\sum_(i : F | P i) (v i).1).
Proof. by apply: (@big_morph _ lrel[R]_n (fun y => y.1)). Qed.

Lemma sum_lrel_snd m (v : 'I_m -> lrel[R]_n) : (* RK : I have added this auxiliary lemma. Should it be somewhere else? *)
  (\sum_(i < m) v i).2 = (\sum_(i < m) (v i).2).
Proof.
by apply: (@big_morph _ lrel[R]_n (fun y => y.2)).
Qed.

Lemma sum_lrel_snd_gen (F : finType) (P : pred F) (v : F -> lrel[R]_n) :
  (\sum_(i : F | P i) v i).2 = (\sum_(i : F | P i) (v i).2).
Proof. by apply: (@big_morph _ lrel[R]_n (fun y => y.2)). Qed.

Lemma size_vbasis_dim : (* RK : I have added this auxiliary lemma, since I could not find it even if it is quite natural. Should it be somewhere else? *)
  size (vbasis V) = \dim V.
Proof.
apply/eqP; rewrite eqn_leq.
move: (vbasisP V) => basis_of_vbasis.
apply/andP; split.
- rewrite basisEdim in basis_of_vbasis.
  exact: (proj2 (andP basis_of_vbasis)).
- rewrite basisEfree in basis_of_vbasis.
  exact: (proj2 (andP (proj2 (andP basis_of_vbasis)))).
Qed.

Lemma satP x :
  reflect (forall e, e \in V -> '[e.1, x] = e.2) (sat x).
Proof. (* RK *)
apply/(iffP idP) => [/allP sat_x e e_in_V | sat_in_V ].
- rewrite (coord_vbasis e_in_V) sum_lrel_fst sum_lrel_snd vdot_sumDl.
  apply: eq_bigr => i _; rewrite vdotZl.
  apply/(congr1 (fun y => coord (vbasis V) i e * y))/eqP/sat_x/mem_nth.
  by rewrite size_vbasis_dim.
- apply/allP => e ?.
  by apply/eqP/(sat_in_V e)/vbasis_mem.
Qed.

Let A := (\matrix_i (tnth base i).1^T)^T.
Let b := (\row_i (tnth base i).2).

Lemma satE x : sat x = (b == x^T *m A).
Proof. (* RK *)
apply/idP/idP => [/allP sat_x |/eqP/rowP b_eq].
- apply/eqP/trmx_inj/colP => j.
  rewrite trmx_mul -row_vdot trmxK rowK 2!trmxK !mxE.
  symmetry; apply/eqP/sat_x/mem_nth.
  by rewrite size_vbasis_dim.
- apply/satP => e e_in_V.
  rewrite (coord_vbasis e_in_V) sum_lrel_fst sum_lrel_snd vdot_sumDl.
  apply: eq_bigr => i _; rewrite vdotZl.
  apply/(congr1 (fun y => coord (vbasis V) i e * y)).
  move: (b_eq i) => b_eq_i; rewrite mxE (tnth_nth 0%R) in b_eq_i.
  by rewrite b_eq_i -trmx_mul mxE -row_vdot rowK (tnth_nth 0%R) trmxK.
Qed.

Definition is_sat := (b <= A)%MS.

Lemma is_satP :
  reflect (exists x, sat x) is_sat.
Proof.
apply/(iffP idP).
- move => h_sat.
  exists (b *m pinvmx A)^T; by rewrite satE trmxK mulmxKpV.
- case => x; rewrite satE => /eqP sat_x.
  by apply/submxP; exists x^T.
Qed.

Lemma is_satPn :
  reflect (sat =1 pred0) (~~ is_sat).
Proof.
apply/(iffP idP).
- move => satN x /=; apply/negbTE.
  move: satN; apply/contra => sat_x.
  by apply/is_satP; exists x.
- move => sat0.
  by apply/negP; case/is_satP => x; rewrite sat0.
Qed.

End Solve.

Arguments satP {R n V x}.
Arguments is_satP {R n V}.
Arguments is_satPn {R n V}.

Section Lift.

Variable (R : realFieldType) (n : nat).

Definition be_lift0 (x: 'cV[R]_n) := fun v => [<v, '[v,x]>].

Lemma be_lift0_linear x : lmorphism (be_lift0 x).
Proof.
by split; move => v w; rewrite /be_lift0 ?beaddE ?bescaleE ?vdotBl ?vdotZl.
Qed.

Definition be_lift x := linfun (Linear (be_lift0_linear x)).

Lemma befstE x : (befst \o (be_lift x) = \1)%VF.
Proof.
apply/lfunP => v.
by rewrite comp_lfunE !lfunE.
Qed.

Lemma be_liftE W x :
  sat W x -> ((be_lift x) @: (befst @: W))%VS = W.
Proof. (* RK *)
move/satP => sat_x.
have be_liftE_on_W u: u \in W -> be_lift x (befst u) = u.
  move => u_in_W.
  rewrite !lfunE; apply/eqP/be_eqP; split; first by done.
  exact: (sat_x _ u_in_W).
apply/vspaceP => w.
apply/idP/idP => [/memv_imgP [? /memv_imgP [v v_in_W] ->] ->| w_in_W].
- by rewrite (be_liftE_on_W _ v_in_W).
- apply/memv_imgP; exists (fst (be_lift0 x (fst w))).
  + by apply/memv_imgP; exists w; [done | rewrite lfunE].
  + by rewrite -(be_liftE_on_W _ w_in_W) !lfunE.
Qed.

(*Lemma dim_be_lift W Ω : (\dim ((be_lift Ω) @: W) = \dim W)%N.
Proof.
apply/limg_dim_eq/subv_anti/andP; split; rewrite ?sub0v //.
apply/subvP => v; rewrite memv_cap memv_ker => /andP [h /eqP].
move/(congr1 befst); rewrite -comp_lfunE befstE id_lfunE linear0 => ->.
by rewrite memv0.
Qed.*)

End Lift.

Module Core.
Section Core.
Context {R : realFieldType} (n : nat).

Variant type :=
| Affine0
| Affine (I : {vspace lrel[R]_n}) of is_sat I.

Definition type_of of phant R := type.
Notation  "''affine[' R ]" := (type_of (Phant R)).

Definition eq_vect V :=
  match V with
  | Affine0 => let e := [<0, 1>] in <[ e ]>%VS
  | Affine eqV _ => eqV
  end.

Definition affine V :=
  if (@idP (is_sat V)) is ReflectT H then
    Affine H
  else Affine0.

Definition affine_of (phR : phant R) := affine : _ -> type_of phR.

Lemma eq_vectK : cancel eq_vect affine.
Proof.
move => V; rewrite /eq_vect.
case: V.
- set e := [<0, 1>].
  suff /negP h: ~~ (is_sat <[e]>).
  rewrite /affine; case: {-}_/idP => //.
  apply/is_satPn; move => x /=.
  apply/negbTE/negP; move/satP/(_ _ (memv_line _)) => /= /eqP.
  by rewrite vdot0l eq_sym oner_eq0.
- move => V h; rewrite /affine.
  case: {-}_/idP => // h'.
  by apply/congr1/bool_irrelevance.
Qed.

Definition affine_eqMixin := (CanEqMixin eq_vectK).
Canonical affine_eqType := EqType type affine_eqMixin.
Definition affine_choiceMixin := (CanChoiceMixin eq_vectK).
Canonical affine_choiceType := ChoiceType type affine_choiceMixin.

Identity Coercion type_of_type : type_of >-> type.
Canonical affine_of_eqType := [eqType of 'affine[R]].
Canonical affine_of_choiceType := [choiceType of 'affine[R]].

Definition affine_pred_sort (S : type) : {pred 'cV[R]_n} :=
  match S with
  | Affine0 => pred0
  | Affine eqV _ => sat eqV
  end.

End Core.

Module Import Exports.
Coercion affine_pred_sort : type >-> pred_sort.
Canonical affine_eqType.
Canonical affine_choiceType.
Canonical affine_of_eqType.
Canonical affine_of_choiceType.
End Exports.
End Core.

Export Core.Exports.
Notation "''affine[' R ]_ n" := (Core.type_of n (Phant R)).
Notation "''affine[' R ]"    := 'affine[R]_(_).
Notation "''affine_' n"      := 'affine[_]_n.
Notation "[ 'affine' I ]"    := (@Core.affine_of _ _ (Phant _) I%VS).
Notation "'eq_vect'"         := Core.eq_vect (at level 8).

Section Specs.

Context {R : realFieldType} {n : nat}.

Implicit Type (x : 'cV[R]_n) (e : lrel[R]_n)
         (U : {vspace lrel[R]_n}) (V : 'affine[R]_n)
         (W : {vspace 'cV[R]_n}).

Definition affine0 : 'affine[R]_n := (Core.Affine0 _).

Lemma in_affine0 x : x \in affine0 = false.
Proof.
by [].
Qed.

Lemma affineN0 V :
  reflect (exists x, x \in V) (V != affine0).
Proof.
apply/(iffP idP).
- by case: V => [/eqP //| U U_sat _]; apply/is_satP.
- by case => x; apply/contraTneq => ->; rewrite in_affine0.
Qed.

Lemma in_affineE U x :
  (x \in [affine U]) = sat U x.
Proof.
rewrite /Core.affine_of /Core.affine.
case: {-}_/idP => [// | /negP/is_satPn ->].
by rewrite in_affine0.
Qed.

Lemma in_affineP {U x} :
  reflect (forall e, e \in U -> '[e.1, x] = e.2) (x \in [affine U]).
Proof.
rewrite in_affineE; exact: satP.
Qed.

Variant affine_spec : 'affine[R]_n -> bool -> Type :=
| Affine0 : affine_spec affine0 true
| Affine U of (exists x, x \in [affine U]) : affine_spec [affine U] false.

Lemma affineP V : affine_spec V (V == affine0).
Proof.
case: V => [| U U_sat].
- rewrite eq_refl; constructor.
- have ->: (Core.Affine U_sat) = [affine U].
    rewrite /Core.affine_of /Core.affine; case: {-}_/idP => // ?.
    apply/congr1; exact: bool_irrelevance.
  suff h: exists x, x \in [affine U].
    have /negbTE ->: [affine U] != affine0 by apply/affineN0.
    by constructor.
  case/is_satP : U_sat => x x_in; exists x.
  by rewrite in_affineE.
Qed.

Lemma affine_is_sat U :
  [affine U] != affine0 = is_sat U.
Proof.
rewrite /Core.affine_of /Core.affine; case: {-}_/idP.
- move => is_sat; rewrite is_sat.
  by apply/eqP.
- move/negP/negbTE ->.
  by rewrite eq_refl.
Qed.

Definition mk_affine W Ω : 'affine[R]_n :=
  [affine ((be_lift Ω) @: W^OC)%VS].

Notation "[ 'affine' W & Ω ]" := (mk_affine W Ω) : polyh_scope.

Lemma in_mk_affine W Ω x :
  (x \in [affine W & Ω]) = (x - Ω \in W).
Proof.
apply/in_affineP/idP => [h|].
- rewrite -[W]orthK; apply/orthvP => y.
  move/(memv_img (be_lift Ω))/h; rewrite lfunE /= => /eqP.
  by rewrite -subr_eq0 -vdotBr => /eqP.
- rewrite -{1}[W]orthK => /orthvP h.
  move => v /memv_imgP [{}v /h eq0 ->].
  rewrite vdotBr in eq0.
  by move/subr0_eq: eq0; rewrite lfunE /=.
Qed.

Lemma in_mk_affineP {W Ω x} :
  reflect (exists2 d, d \in W & x = Ω + d) (x \in [affine W & Ω]).
Proof.
rewrite in_mk_affine; apply/(iffP idP) => [?|[?? ->]].
- by exists (x - Ω); last rewrite addrC subrK.
- by rewrite addrC addKr.
Qed.

Lemma orig_affine W Ω : Ω \in [affine W & Ω].
Proof.
by rewrite in_mk_affine addrN mem0v.
Qed.

Lemma mk_affineN0 W Ω :
  [affine W & Ω] != affine0.
Proof.
by apply/affineN0; exists Ω; apply/orig_affine.
Qed.

Definition dir V :=
  match affineP V with
  | Affine0 => 0%VS
  | Affine U _ => (befst @: U)^OC%VS
  end.

Lemma dir0 : dir affine0 = 0%VS.
Proof.
rewrite /dir.
by case/affineP: affine0 (eq_refl (affine0 : 'affine[R]_n)).
Qed.

Lemma in_dirP V x :
  x \in V -> forall d, (d \in dir V) = (x + d \in V).
Proof.
rewrite /dir; case/affineP: V; rewrite ?in_affine0 ?in_affine //.
move => U _ /in_affineP x_in d.
apply/idP/in_affineP.
- move/orthvP => h v v_in_U.
  move/(_ (befst v) (memv_img _ v_in_U)): h.
  rewrite vdotDr lfunE => ->; rewrite addr0.
  by apply/x_in.
- move => h; apply/orthvP => c c_in.
  pose e := (be_lift x) c.
  have e_in_U: e \in U.
  + move/satP: x_in => /be_liftE <-.
    by apply/memv_img.
  move/(_ _ e_in_U): h.
  rewrite vdotDr; move/(_ _ e_in_U): x_in ->.
  move/(canRL (addKr _)); rewrite addNr.
  by rewrite /e lfunE.
Qed.

Lemma dir_mk_affine W Ω :
  dir [affine W & Ω] = W.
Proof.
apply/vspaceP => d.
rewrite (in_dirP (orig_affine W Ω)) in_mk_affine.
by rewrite addrAC addrN add0r.
Qed.

Lemma mk_affine_dir V x :
  x \in V -> V = [affine (dir V) & x].
Proof.
rewrite /dir; case/affineP: V; rewrite ?in_affine0 //.
move => U _ x_in.
apply/congr1; rewrite orthK.
by rewrite be_liftE //; rewrite in_affineE in x_in.
Qed.

Lemma dir_eq V V' x :
  x \in V -> x \in V' -> dir V = dir V' -> V = V'.
Proof.
by move => /mk_affine_dir {2}-> /mk_affine_dir {2}-> ->.
Qed.

Inductive mk_affine_spec : 'affine[R]_n -> {vspace 'cV[R]_n} -> Prop :=
| MkAffine0 : mk_affine_spec affine0 0%VS
| MKAffineN0 W Ω : mk_affine_spec [affine W & Ω] W.

Lemma mk_affineP V : mk_affine_spec V (dir V).
Proof.
case/affineP: V => [| U [x]].
- rewrite dir0; constructor.
- by move/mk_affine_dir => {1}->; constructor.
Qed.

Lemma affine_eqP V V' :
  (V =i V') <-> (V = V').
Proof.
split; last by move ->.
case/mk_affineP: V.
- move => ext_eq.
  apply/contraTeq: isT => /=.
  rewrite eq_sym; case/affineN0 => x.
  by rewrite -ext_eq; rewrite in_affine0.
- move => W Ω ext_eq.
  have Ω_in_V' : Ω \in V'.
  + by rewrite -ext_eq orig_affine.
  apply/(dir_eq (orig_affine _ _)) => //.
  apply/vspaceP => d.
  rewrite (in_dirP Ω_in_V') dir_mk_affine -ext_eq in_mk_affine.
  by rewrite addrAC addrN add0r.
Qed.

Definition affineI V V' :=
  match affineP V, affineP V' with
  | Affine0, _ => affine0
  | _, Affine0 => affine0
  | Affine U _, Affine U' _ => [affine (U + U')]
  end.

Lemma in_affineI x V V' :
  x \in affineI V V' = (x \in V) && (x \in V').
Proof.
rewrite /affineI.
case: (affineP V) => [| U _]; case: (affineP V') => [| U' _];
  rewrite ?in_affine0 ?andbF //.
apply/in_affineP/andP => [x_in| [x_in x_in']].
- by split; apply/in_affineP => e e_in; apply/x_in;
    move: e_in; apply/subvP; rewrite ?addvSl ?addvSr.
  (* TODO: add mem_addvl and mem_addvr statements  to vector.v *)
- move => ? /memv_addP [e1 e1_in] [e2 e2_in] -> /=.
  by rewrite vdotDl; apply: congr2; [apply/(in_affineP x_in) | apply/(in_affineP x_in')].
Qed.

Definition affine_le V V' := (V == affineI V V').

Lemma affine_leP {V V'} : reflect {subset V <= V'} (affine_le V V').
Proof.
apply/(iffP eqP).
- move/affine_eqP => eq x.
  by rewrite eq in_affineI => /andP[].
- move => sub; apply/affine_eqP => x.
  rewrite in_affineI.
  by apply/idP/andP => [?|[] //]; split => //; apply/sub.
Qed.

End Specs.

Notation "[ 'affine' W & Ω ]" := (mk_affine W Ω) : polyh_scope.

Module Order.
Section Order.

Context {R : realFieldType} {n : nat}.

Implicit Type (V : 'affine[R]_n).

Lemma affine_le_refl : reflexive (@affine_le R n).
Proof.
by move => ?; apply/affine_leP.
Qed.

Lemma affine_le_anti : antisymmetric (@affine_le R n).
Proof.
move => V V' /andP [/affine_leP sub /affine_leP sub'].
by apply/affine_eqP => x; apply/idP/idP; [apply/sub | apply/sub'].
Qed.

Lemma affine_le_trans : transitive (@affine_le R n).
Proof. (* RK *)
move => ? ? ? /affine_leP subset1 /affine_leP subset2.
by apply/affine_leP => ? ?; apply/subset2/subset1.
Qed.

Definition affine_LtPOrderMixin :=
  LePOrderMixin (fun _ _ => erefl _) affine_le_refl affine_le_anti affine_le_trans.

Canonical affine_POrderType :=
  Eval hnf in POrderType polyh_display 'affine[R]_n affine_LtPOrderMixin.

Program Definition affine_bottomMixin :=
  @BottomMixin polyh_display [porderType of 'affine[R]_n] affine0 _.

Next Obligation.
by apply/affine_leP => v; rewrite in_affine0.
Qed.

Program Canonical affine_PBOrderType :=
  Eval hnf in BPOrderType 'affine[R]_n affine_bottomMixin.

Program Definition affine_meetMixin :=
  @MeetMixin _ _ affineI _ _ _.

Next Obligation.
by move => V V'; apply/affine_eqP => x; rewrite !in_affineI andbC.
Qed.

Next Obligation.
by move => V1 V2 V3; apply/affine_eqP => x; rewrite !in_affineI andbA.
Qed.

Next Obligation.
apply/affine_leP/eqP => [|<-].
+ move=> le_xy; apply/affine_eqP=> c; rewrite in_affineI.
  by apply: andb_idr; apply: le_xy.
+ by move => c; rewrite in_affineI => /andP[].
Qed.

Canonical affine_MeetSemilatticeType :=
  Eval hnf in MeetSemilatticeType 'affine[R]_n affine_meetMixin.

Canonical affine_bMeetSemilatticeType := [bMeetSemilatticeType of 'affine[R]_n].
End Order.

Module Import Exports.
Canonical affine_POrderType.
Canonical affine_PBOrderType.
Canonical affine_MeetSemilatticeType.
Canonical affine_bMeetSemilatticeType.
End Exports.
End Order.

Export Order.Exports.

Notation "'[' 'affine0' ']'" := affine0.

Section BasicObjects.

Context {R : realFieldType} {n : nat}.

Implicit Type (Ω d : 'cV[R]_n) (e : lrel[R]_n)
         (U : {vspace lrel[R]_n}) (V : 'affine[R]_n).

Lemma affineS :
  {homo (@Core.affine _ _: {vspace lrel[R]_n} -> 'affine[R]_n) : U V / (U <= V)%VS >-> (U `>=` V)}.
Proof. (* RK *)
move => ? ? /subvP Hsubset; apply/affine_leP => ?.
move/in_affineP => Hin_affime.
apply/in_affineP =>  ? ?.
by apply/Hin_affime/Hsubset.
Qed.

Lemma dir_affine U :
  [affine U] `>` [affine0] -> dir [affine U] = (befst @: U)^OC%VS.
Proof. (* RK *)
move/andP => [? _].
have aff_U_neq0: exists x : 'cV_n, x \in [affine U] by apply/affineN0.
move: aff_U_neq0 => [? in_aff_U].
apply/vspaceP => d; rewrite (in_dirP in_aff_U).
apply/idP/orthvP => [/in_affineP in_aff ? /memv_imgP [u u_in_U] ->| H].
- rewrite lfunE /=; move/eqP: (in_aff _ u_in_U).
  by rewrite vdotDr ((in_affineP in_aff_U) _ u_in_U) -subr_eq0 [X in X-_]addrC -addrA subrr addr0 => /eqP <-.
- apply/in_affineP => u u_in_U.
  rewrite vdotDr ((in_affineP in_aff_U) _ u_in_U).
  suff ->: '[ u.1, d] = 0 by rewrite addr0.
  by apply/H/memv_imgP; exists u; [exact: u_in_U | rewrite lfunE].
Qed.


Lemma affine_proper0P V :
  reflect (exists x, x \in V) (V `>` [affine0]).
Proof.
rewrite lt0x; exact: affineN0.
Qed.

Lemma mk_affine_proper0 Ω W :
  [affine W & Ω] `>` [affine0].
Proof.
apply/affine_proper0P; exists Ω; exact: orig_affine.
Qed.

Lemma mk_affineS Ω : { mono (mk_affine^~ Ω) : W W' / (W <= W')%VS >-> (W `<=` W') }.
Proof. (* RK *)
move => ? ?; apply/affine_leP/subvP => [Hsubset w ? | Hsubset ?].
- rewrite -[w]addr0 -(subrr Ω) addrA -in_mk_affine addrC.
  by apply/Hsubset/in_mk_affineP; exists w.
- by rewrite !in_mk_affine; apply: Hsubset.
Qed.

Lemma dirS V V' : (V `<=` V') -> (dir V <= dir V')%VS.
Proof. (* RK *)
case/affineP: V => [_  |U [? Hin_affine] /affine_leP Hsubset];
  rewrite ?dir0 ?sub0v //.
by apply/subvP => ?; rewrite (in_dirP Hin_affine) (in_dirP (Hsubset _ Hin_affine)); apply/Hsubset.
Qed.

Lemma affine_mono U U' :
  [affine U] `>` [affine0] -> [affine U] `<=` [affine U'] = (U' <= U)%VS.
Proof.
move => U_neq0.
apply/idP/idP; last by apply/affineS.
move => U_sub_U'.
have U'_neq0: [affine U'] `>` [affine0] by apply/lt_le_trans: U_sub_U'.
move/dirS: (U_sub_U'); rewrite ?dir_affine // orthS.
case/affine_proper0P : U_neq0 => x x_in_U.
have x_in_U' : x \in [affine U'] by apply/(affine_leP U_sub_U').
by move/(limgS (be_lift x)); rewrite ?be_liftE -?in_affineE.
Qed.

Notation "'[' 'hp' e  ']'" := [affine <[e]> ].

Lemma in_hp :
  (forall e x, (x \in [hp e]) = ('[e.1,x] == e.2))
  * (forall c α (x : 'cV[R]_n), (x \in [hp [<c, α>]]) = ('[c,x] == α)).
Proof. (* RK *)
split => [ e x | c α x]; apply/in_affineP/idP => [in_hp | /eqP in_hp ? /vlineP [?] ->];
  rewrite ?vdotZl ?in_hp ?memv_line //.
by apply/eqP/(in_hp [<c, α>])/memv_line.
Qed.

Lemma hpN (e : lrel[R]_n) : [hp -e] = [hp e].
Proof.
by apply/affine_eqP => x; rewrite !in_hp /= vdotNl eqr_opp.
Qed.

Lemma be_lift_hp (x : 'cV[R]_n) (e : lrel[R]_n) :
  x \in [hp e] -> (be_lift x (befst e)) = e.
Proof.
rewrite lfunE /= /be_lift0 lfunE /=.
by rewrite in_hp => /eqP ->; rewrite beE.
Qed.

Lemma affineS1 (U : {vspace lrel[R]_n}) e :
  e \in U -> ([affine U] `<=` [hp e]).
Proof. (* RK *)
by apply/affineS.
Qed.

Definition affineT : 'affine[R]_n := [hp 0].

Notation "'[' 'affineT' ']'" := affineT : polyh_scope.

Lemma in_affineT x : x \in affineT = true.
Proof.
by rewrite in_hp vdot0l eq_refl.
Qed.

Lemma dir_affineT : dir affineT = fullv.
Proof.
have nullv_in_affineT : 0 \in affineT by rewrite in_affineT.
by apply/vspaceP => ?; rewrite memvf (in_dirP nullv_in_affineT) in_affineT.
Qed.

Program Definition affine_topMixin :=
  @TopMixin polyh_display [porderType of 'affine[R]_n] affineT _.

Next Obligation. by apply/affine_leP=> ? _; rewrite in_affineT. Qed.

Canonical affine_tPOrderType := TPOrderType 'affine[R]_n affine_topMixin.
Canonical affine_tbPOrderType := [tbPOrderType of 'affine[R]_n].

Canonical affine_tMeetSemilatticeType := [tMeetSemilatticeType of 'affine[R]_n].
Canonical affine_tbMeetSemilatticeType := [tbMeetSemilatticeType of 'affine[R]_n].

Lemma in_big_affineIP (I : finType) (P : pred I) (F : I -> 'affine[R]_n) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \meet_(i | P i) (F i)).
Proof.
apply: (iffP idP) => [? i Pi | x_in_F].
- by apply: (affine_leP (meets_inf F Pi)).
- elim/big_rec: _ => [|i V Pi ?]; first by rewrite in_affineT.
  by rewrite in_affineI; apply/andP; split; [apply: (x_in_F i) | done].
Qed.

Lemma in_big_affineI (I : finType) (P : pred I) (F : I -> 'affine[R]_n) x :
  (x \in \meet_(i | P i) (F i)) = [forall i, P i ==> (x \in F i)].
Proof. (* RK *)
apply/in_big_affineIP/idP.
- by move => Hforall; apply/forallP => i; apply/implyP/Hforall.
- by move/forallP => Hforall i; apply/implyP/Hforall.
Qed.

Lemma affine_span (I : base_t[R,n]) :
  [affine <<I>>] = \meet_(e : I) [hp (val e)].
Proof. (* RK *)
apply/affine_eqP => x.
rewrite in_affineE.
apply/idP/idP => [/satP sat_I | /in_big_affineIP in_all_hps].
- apply/in_big_affineIP => i _; rewrite (fst (in_hp)).
  by apply/eqP/(sat_I (val i))/memv_span/valP.
- apply/satP => e e_in.
  rewrite (coord_span e_in) sum_lrel_fst sum_lrel_snd vdot_sumDl /=.
  apply: eq_bigr => i _.
  have in_enum_fset_I: (I`_i) \in (enum_fset I) by apply/memt_nth.
  rewrite vdotZl; apply/congr1/eqP; rewrite -(fst (in_hp)).
  by apply: (in_all_hps (FSetSub in_enum_fset_I)).
Qed.

Lemma affine_vbasis (U : {vspace lrel[R]_n}) :
  let base := [fset e in ((vbasis U) : seq _)]%fset : {fset lrel[R]_n} in
  [affine U] = [affine << base >>].
Proof.
set base := [fset e in ((vbasis U) : seq _)]%fset : {fset lrel[R]_n}.
suff ->: U = << base >>%VS by [].
move: (vbasisP U) => /andP [/eqP <- _].
apply/subv_anti/andP; split; apply/sub_span; by move => ?; rewrite inE.
Qed.

Notation "'[' 'line' d & Ω ']'" := [affine <[d]> & Ω].

Lemma in_lineP {d Ω x : 'cV[R]_n} :
  reflect (exists μ, x = Ω + μ *: d) (x \in [line d & Ω]).
Proof.
apply/(iffP in_mk_affineP) => [[y /vlineP [μ ->]]| [μ ->] ].
+ by exists μ.
+ by exists (μ *: d); rewrite ?memvZ ?memv_line.
Qed.

Lemma line_subset_hp e v v' :
  (v \in [hp e]) -> (v' \in [hp e]) -> ([line (v' - v) & v] `<=` [hp e]).
Proof.
rewrite !in_hp => /eqP v_in /eqP v'_in.
apply/affine_leP => ? /in_lineP [μ -> ]; rewrite in_hp.
by rewrite vdotDr vdotZr vdotBr v_in v'_in addrN mulr0 addr0.
Qed.

Notation "'[' 'pt' Ω ']'" := [affine 0%VS & Ω].

Lemma in_pt Ω x : (x \in [pt Ω]) = (x == Ω).
Proof.
by rewrite in_mk_affine memv0 subr_eq0.
Qed.

End BasicObjects.

Notation "'[' 'hp' e  ']'" := [affine <[e]> ] : polyh_scope.
Notation "'[' 'line' d & Ω ']'" := [affine <[d]> & Ω] : polyh_scope.
Notation "'[' 'pt' Ω ']'" := [affine 0%VS & Ω] : polyh_scope.
Notation "'[' 'affineT' ']'" := (@affineT _ _) : polyh_scope.

Section Dimension.

Context {R : realFieldType} {n : nat}.

Implicit Type (V : 'affine[R]_n) (U : {vspace lrel[R]_n}).

Definition adim V :=
  if V == [affine0] then 0%N
  else (\dim (dir V)).+1%N.

Lemma adim0 : adim [affine0] = 0%N.
Proof.
by rewrite /adim ifT //.
Qed.

Lemma adimN0 V : (adim V > 0)%N = (V `>` affine0).
Proof.
by rewrite /adim; case: ifP => [/eqP -> // |]; rewrite lt0x => ->.
Qed.

Lemma adim_eq0 V : adim V = 0%N -> V = [affine0].
Proof.
by rewrite /adim; case: ifP => [/eqP ->|].
Qed.

Lemma adimN0_eq V : V `>` [affine0] -> adim V = (\dim (dir V)).+1%N.
Proof.
by rewrite lt0x /adim => /negbTE ->.
Qed.

Lemma adimS : {homo adim : V V' / (V `<=` V') >-> (V <= V')%N}.
Proof.
move => V V' sub.
rewrite /adim; case: ifPn => // V_neq0.
have V'_neq0: V' != [affine0].
- move: V_neq0; apply/contra_neq => V'_eq0.
  by rewrite V'_eq0 lex0 in sub; move/eqP: sub.
rewrite ifF ?ltnS; last by apply/negbTE.
by apply/dimvS/dirS.
Qed.

Lemma adim_leqif_eq V V' :
  (V `<=` V') -> (adim V <= adim V' ?= iff (V == V'))%N.
Proof.
move => V_sub_V'; split; rewrite ?adimS //.
apply/eqP/eqP; last by move => ->.
rewrite {1}/adim; case: ifP.
- by move/eqP ->; symmetry; apply/adim_eq0.
- move/negbT => V_neq0.
  have V'_neq0: V' != [affine0].
    rewrite -!lt0x in V_neq0 *.
    by apply/lt_le_trans: V_sub_V'.
  rewrite /adim ifF; last by apply/negbTE.
  move/succn_inj => adim_dir_eq.
  suff: dir V = dir V'.
  - case/affineN0: V_neq0 => x x_in.
    by apply/(dir_eq x_in)/(affine_leP V_sub_V').
  - by apply/eqP; rewrite -(eq_leqif (dimv_leqif_eq (dirS _))) ?adim_dir_eq.
Qed.

Lemma sub_geq_adim V V' :
  (V `<=` V') -> (adim V >= adim V')%N -> V = V'.
Proof. (* RK *)
move => V_sub_V' adimV_gte_adimV'; apply/eqP/contraT => V_neq_V'.
by move/leqifP: (adim_leqif_eq V_sub_V'); rewrite ifF;
  [rewrite ltnNge adimV_gte_adimV' | apply/negbTE].
Qed.

Lemma sub_eq_adim V V' :
  (V `<=` V') -> adim V = adim V' -> V = V'.
Proof. (* RK *)
move => ? adimV_eq_adimV'.
by apply/sub_geq_adim; [done | rewrite adimV_eq_adimV'].
Qed.

Lemma adim_affine_lt V V' :
  (V `<` V') -> (adim V < adim V')%N.
Proof. (* RK *)
move/andP => [V'_neq_V ?].
rewrite ltn_neqAle; apply/andP; split; last by apply/adimS.
move: V'_neq_V; apply/contra_neqN => /eqP ?; symmetry.
by apply/sub_eq_adim.
Qed.

Lemma adim_line Ω d : adim [line d & Ω] = (d != 0).+1.
Proof.
rewrite /adim ifF; last by apply/negbTE/mk_affineN0.
by rewrite dir_mk_affine dim_vline.
Qed.

Lemma affine_addv U U' :
  [affine (U + U')] = [affine U] `&` [affine U'].
Proof.
apply/affine_eqP=> x; rewrite in_affineI.
apply/in_affineP/andP.
- by move=> x_in_UU'; split; apply/in_affineP => e e_in;
     apply: x_in_UU'; apply/subvP: e_in; rewrite ?addvSl ?addvSr.
- case=> /in_affineP x_in_U /in_affineP x_in_U' e /memv_addP.
  case=> [e0 e0_in_U] [e1 e1_in_U'] -> /=.
  by rewrite vdotDl; apply: congr2; by [exact: x_in_U | exact: x_in_U'].
Qed.

Lemma dim_affineI V e :
  let V' := V `&` [hp e] in
  ~~ (V `<=` [hp e]) -> V' `>` [affine0] ->
  adim V = (adim V').+1%N.
Proof.
case/affineP: V; rewrite ?le0x // => [U] _ /= U_subN_e V'_prop0.
have [U_prop0 e_prop0]:
  ([affine0] `<` [affine U]) /\ ([affine0] `<` [hp e]).
- by split; apply: (lt_le_trans V'_prop0); rewrite ?leIl ?leIr.
have e_notin: (befst e \notin befst @: U)%VS.
- move: U_subN_e; apply: contraNN.
  case/affine_proper0P: V'_prop0 => x.
  rewrite in_affineI => /andP [x_in_U x_in_e].
  move/(memv_img (be_lift x)).
  rewrite be_liftE -?in_affineE ?be_lift_hp //.
  exact: affineS.
rewrite -affine_addv in V'_prop0 *.
rewrite ?adimN0_eq ?dir_affine //; apply congr1; rewrite !dim_orthv.
move/dir_affine: V'_prop0.
rewrite limgD limg_line.
move/(canLR orthK)/(congr1 (@dimv _ _)).
rewrite dim_add_line // => dim_eq.
by rewrite subnSK -?dim_eq ?dim_leqn.
Qed.

Lemma adim_pt Ω : adim [pt Ω] = 1%N.
Proof.
by rewrite adim_line eq_refl.
Qed.

Lemma dimv_eq1P (K : fieldType) (vT : vectType K) (V : {vspace vT}) :
  reflect (exists2 v, v != 0 & V = <[v]>%VS) (\dim V == 1%N).
(* TODO: move to extra_vector.v *)
Proof.
apply/(iffP idP) => [/eqP dim_V_eq1 |[? neq0 ->]];
  last by rewrite dim_vline neq0.
have : ~~ (V <= 0)%VS.
  move: dim_V_eq1; apply/contra_eqN.
  by rewrite subv0; move/eqP => ->; rewrite dimv0.
move/subvPn => [v ? v_not_in_V].
exists v; first by move: v_not_in_V; apply/contra; rewrite memv0.
apply/eqP; rewrite eqEsubv; apply/andP; split;
  last by rewrite -memvE.
suff ->: (V = <[v]>)%VS by done.
apply/eqP; rewrite eq_sym eqEdim; apply/andP; split;
  first by rewrite -memvE.
suff ->: \dim <[v]> = 1%N by rewrite dim_V_eq1.
rewrite memv0 in v_not_in_V.
by rewrite dim_vline v_not_in_V.
Qed.

Lemma adim2P V :
  adim V = 2%N -> exists Ω, exists2 d, d != 0 & V = [line d & Ω].
Proof. (* RK *)
move => adim_V_eq2.
have V_neq0 : V != affine0.
  apply/contraT => V_eq0; rewrite negbK in V_eq0.
  by rewrite (eqP V_eq0) adim0 in adim_V_eq2.
have dim_dir_V_eq1: (\dim (dir V)) = 1%N
  by apply/eq_add_S; rewrite /adim ifF // in adim_V_eq2; apply/negbTE.
move/eqP/dimv_eq1P: (dim_dir_V_eq1) => [d ? dir_V_eq].
move/affineN0: V_neq0 => [Ω Ω_in_V].
exists Ω; exists d; first by done.
by rewrite -dir_V_eq; apply/mk_affine_dir.
Qed.

Lemma adim1P V :
  adim V = 1%N -> exists Ω, V = [pt Ω].
Proof. (* RK *)
move => adim_V_eq1.
have V_neq0 : V != affine0.
  apply/contraT => V_eq0; rewrite negbK in V_eq0.
  by rewrite (eqP V_eq0) adim0 in adim_V_eq1.
move: (affineN0 _ V_neq0) => [Ω Ω_in_V].
exists Ω.
suff <-: (dir V) = 0%VS by apply/mk_affine_dir.
apply/eqP; rewrite -dimv_eq0.
by apply/eqP/eq_add_S; rewrite /adim ifF // in adim_V_eq1; apply/negbTE.
Qed.

Lemma adim_leSn V :
  (adim V <= n.+1)%N.
Proof. (* RK *)
rewrite /adim; case: (boolP (V == affine0)) => [_|_]; first by done.
rewrite ltnS.
by apply/(@leq_trans (n * 1)); [apply/rank_leq_col | rewrite muln1].
Qed.

Lemma dim_affine_le (U : {vspace lrel[R]_n}) :
  [affine U] `>` [affine0] -> (\dim U <= n)%N.
Proof. (* RK *)
apply/contraTT; rewrite -ltnNge lt0x negbK => dimU.
have {dimU} -> : U = fullv
  by apply/eqP; rewrite eqEdim; apply/andP; split;
    [exact: subvf | rewrite dimvf /Vector.dim /= addn1].
apply/eqP/affine_eqP => x; rewrite in_affine0; apply/negbTE/negP.
pose e := [<0, 1>]: lrel[R]_n.
have e_in_U: e \in fullv by rewrite memvf.
move/in_affineP/(_ _ e_in_U); rewrite vdot0l /= => /esym/eqP.
by rewrite oner_eq0.
Qed.

Lemma adimT : (adim affineT = n.+1)%N.
Proof. (* RK *)
rewrite /adim ifF.
- by rewrite dir_affineT dimvf /Vector.dim /= muln1.
- apply/(contraFF _ (erefl false)).
  move/eqP/affine_eqP => aff_eq.
  by move: (aff_eq 0); rewrite in_affine0 in_affineT.
Qed.

Lemma adimTP V : adim V = n.+1%N -> V = affineT.
Proof. (* RK *)
rewrite -adimT => ?.
apply/sub_eq_adim; last by done.
by apply/affine_leP => ?; rewrite in_affineT.
Qed.

Lemma adim_hp e :
  [hp e] `>` [affine0] -> adim [hp e] = ((e.1 == 0%R) + n)%N.
Proof. (* RK *)
move => hp_neq0.
rewrite /adim ifF; last by apply/negbTE; move/andP: hp_neq0 => [? _].
case: (boolP (e.1 == 0)) => [/eqP e1_eq0 | e1_neq0].
- suff ->: [hp e] = affineT
    by rewrite dir_affineT dimvf /Vector.dim /= muln1 add1n.
  apply/affine_eqP => ?; rewrite in_affineT in_hp e1_eq0 vdot0l.
  move/affineN0: (proj1 (andP hp_neq0)) => [?].
  by rewrite in_hp e1_eq0 vdot0l => ?.
- case: (boolP (0 < n)%N) => [? | n_eq0].
  + rewrite /adim (dir_affine hp_neq0) dim_orthv.
    have ->: ((befst @: <[e]>) = <[e.1]>)%VS
      by rewrite limg_line lfunE.
    rewrite dim_vline e1_neq0 add0n subn1.
    by apply/prednK.
  + rewrite -eqn0Ngt in n_eq0.
    rewrite extra_matrix.col_neq_0 in e1_neq0.
    move/existsP: e1_neq0 => [i _].
    by rewrite (eqP n_eq0) in i; move: (ord0_false i).
Qed.

Lemma subset_hp (V : {fset 'cV[R]_n}) :
  (0 < #|` V | <= n)%N ->
  exists2 e : lrel[R]_n, (e.1 != 0) & {subset V <= [hp e]}.
Proof.
rewrite cardfs_gt0 => /andP [/fset0Pn [v v_in] cardV_le].
pose U := <<[seq w - v | w <- (V `\ v)%fset]>>%VS.
have: ((\dim U).+1 <= n)%N.
- apply/leq_trans: cardV_le.
  have ->: #|` V| = #|` (V `\  v)|%fset.+1%N by rewrite (@cardfsD1 _ v) v_in.
  rewrite ltnS; apply/(leq_trans (dim_span _)).
  by rewrite size_map.
rewrite -subn_gt0 -dim_orthv lt0n dimv_eq0 => h.
pose c := vpick (U^OC)%VS.
pose e := [< c, '[c,v] >]; exists e; first by rewrite vpick0.
move => w; case/altP : (w =P v) => [-> _| w_neq_v w_in_V].
- by rewrite in_hp.
- rewrite in_hp /=.
  have ->: w = v + (w - v) by rewrite addrCA addrN addr0.
  rewrite vdotDr; suff ->: '[c, w-v] = 0 by rewrite addr0.
  rewrite vdotC; apply/(orthvP (V := U)); first exact: memv_pick.
  by rewrite memv_span //; apply/map_f; rewrite !inE w_neq_v.
Qed.

End Dimension.
