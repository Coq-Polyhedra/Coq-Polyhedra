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
Import GRing.Theory Num.Theory.

Local Open Scope poly_scope.

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

Reserved Notation "\affineI_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \affineI_ i '/  '  F ']'").
Reserved Notation "\affineI_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \affineI_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\affineI_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \affineI_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\affineI_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \affineI_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\affineI_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \affineI_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\affineI_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \affineI_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\affineI_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\affineI_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\affineI_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \affineI_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\affineI_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \affineI_ ( i  <  n )  F ']'").
Reserved Notation "\affineI_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \affineI_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\affineI_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \affineI_ ( i  'in'  A ) '/  '  F ']'").

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

Lemma sum_lrel_snd m (v : 'I_m -> lrel[R]_n) : (* RK : I have added this auxiliary lemma. Should it be somewhere else? *)
  (\sum_(i < m) v i).2 = (\sum_(i < m) (v i).2).
Proof.
by apply: (@big_morph _ lrel[R]_n (fun y => y.2)).
Qed.

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

Lemma sat_be_lift W x :
  sat ((be_lift x) @: W)%VS x.
Proof. (* RK *)
apply/satP => e /memv_imgP [? ?] ->.
by rewrite !lfunE.
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
rewrite /Core.affine_of /Core.affine; case: {-}_/idP => [// | /negP/is_satPn ->].
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

Notation "[ 'affine' W & Ω ]" := (mk_affine W Ω) : poly_scope.

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
  let U := eq_vect V in
  let U' := eq_vect V' in
  [affine (U + U')].

Lemma cond_affine0 U :  (* RK: I have added this auxiliary lemma *)
  let: e := [<0, 1>]: lrel[R]_n in
    e \in U -> [affine U] = affine0.
Proof.
move => e_in_U; rewrite /Core.affine_of /Core.affine.
case: {-}_/idP => [is_sat_U |_ //].
suff : ~~ (is_sat U) by rewrite is_sat_U.
apply/contraT.
move/negbNE/is_satP => [x] /satP sat_U_x.
move/eqP: (sat_U_x _ e_in_U).
by rewrite vdot0l eq_sym oner_eq0.
Qed.

Lemma in_affineI x V V' :
  x \in affineI V V' = (x \in V) && (x \in V').
Proof. (* RK *)
pose e := ([< 0, 1 >]: lrel[R]_n).
case: V => [ | I is_sat_I].
- suff ->: affineI (Core.Affine0 n) V' = affine0 by rewrite in_affine0.
  apply/cond_affine0/memv_addP.
  exists e; first exact: memv_line.
  exists 0; first exact: mem0v.
  by rewrite addr0.
- case: V' => [ | I' is_sat_I'].
  + suff ->: affineI (Core.Affine is_sat_I) (Core.Affine0 n) = affine0
      by rewrite andbC in_affine0.
    apply/cond_affine0/memv_addP.
    exists 0; first exact: mem0v.
    exists e; first exact: memv_line.
    by rewrite add0r.
  + rewrite -{2}(Core.eq_vectK (Core.Affine is_sat_I)) -{2}(Core.eq_vectK (Core.Affine is_sat_I')).
    apply/idP/idP => [/in_affineP x_in_affine | /andP [/in_affineP x_in_affine /in_affineP x_in_affine']].
    * apply/andP; split; apply/in_affineP => e' ?; apply/x_in_affine/memv_addP.
      - exists e'; first by done.
        exists 0; first exact: mem0v.
        by rewrite addr0.
      - exists 0; first exact: mem0v.
        exists e'; first by done.
        by rewrite add0r.
    * apply/in_affineP => e' /memv_addP [e1] e1_in [e2] e2_in ->.
      by rewrite vdotDl (x_in_affine _ e1_in) (x_in_affine' _ e2_in).
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

Notation "[ 'affine' W & Ω ]" := (mk_affine W Ω) : poly_scope.

Fact poly_display : unit. Proof. exact: tt. Qed.

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
  LePOrderMixin  (fun _ _ => erefl _) affine_le_refl affine_le_anti affine_le_trans.

Canonical affine_LtPOrderType :=
  Eval hnf in POrderType poly_display 'affine[R]_n affine_LtPOrderMixin.

Program Canonical affine_MeetSemilattice :=
  Eval hnf in MeetSemilatticeType 'affine[R]_n
    (@MeetSemilatticeMixin _ _ affineI _ _ _ _).

Next Obligation.
by move => V V'; apply/affine_eqP => x; rewrite !in_affineI andbC.
Qed.

Next Obligation.
by move => V1 V2 V3; apply/affine_eqP => x; rewrite !in_affineI andbA.
Qed.

Next Obligation.
by move => V; apply/affine_eqP => x; rewrite !in_affineI andbb.
Qed.

Next Obligation.
apply/affine_leP/eqP => [|<-].
+ move=> le_xy; apply/affine_eqP=> c; rewrite in_affineI.
  by apply: andb_idr; apply: le_xy.
+ by move => c; rewrite in_affineI => /andP[].
Qed.

Program Definition affine_bottomMixin :=
  @BottomMixin poly_display [porderType of 'affine[R]_n] affine0 _.

Next Obligation.
by apply/affine_leP => v; rewrite in_affine0.
Qed.

Canonical affine_BSemilatticeType :=
  Eval hnf in BSemilatticeType 'affine[R]_n affine_bottomMixin.

End Order.

Module Import Exports.
Canonical affine_LtPOrderType.
Canonical affine_MeetSemilattice.
Canonical affine_BSemilatticeType.
End Exports.
End Order.

Export Order.Exports.

Notation poly_le   := (@Order.le poly_display _) (only parsing).
Notation poly_lt   := (@Order.lt poly_display _) (only parsing).
Notation poly_ge   := (@Order.ge poly_display _) (only parsing).
Notation poly_gt   := (@Order.gt poly_display _) (only parsing).
Notation poly_leif := (@Order.leif poly_display _) (only parsing).
Notation poly_cmp  := (@Order.comparable poly_display _) (only parsing).
Notation poly_meet := (@Order.meet poly_display _).

Notation "<=%PH"  := poly_le   : fun_scope.
Notation ">=%PH"  := poly_ge   : fun_scope.
Notation "<%PH"   := poly_lt   : fun_scope.
Notation ">%PH"   := poly_gt   : fun_scope.
Notation "<?=%PH" := poly_leif : fun_scope.
Notation ">=<%PH" := poly_cmp  : fun_scope.
Notation "><%PH"  := (fun x y => ~~ (poly_cmp x y)) : fun_scope.

Notation "`<=` y" := (poly_ge y) : poly_scope.
Notation "`<=` y :> T" := (`<=` (y : T)) (only parsing) : poly_scope.
Notation "`>=` y"  := (poly_le y) : poly_scope.
Notation "`>=` y :> T" := (`>=` (y : T)) (only parsing) : poly_scope.

Notation "`<` y" := (poly_gt y) : poly_scope.
Notation "`<` y :> T" := (`<` (y : T)) (only parsing) : poly_scope.
Notation "`>` y" := (poly_lt y) : poly_scope.
Notation "`>` y :> T" := (`>` (y : T)) (only parsing) : poly_scope.

Notation "`>=<` y" := (poly_cmp y) : poly_scope.
Notation "`>=<` y :> T" := (`>=<` (y : T)) (only parsing) : poly_scope.

Notation "`><` y" := (fun x => ~~ (poly_cmp y x)) : poly_scope.
Notation "`><` y :> T" := (`><` (y : T)) (only parsing) : poly_scope.

Notation "x `<=` y" := (poly_le x y) : poly_scope.
Notation "x `<=` y :> T" := ((x : T) `<=` (y : T)) (only parsing) : poly_scope.
Notation "x `>=` y" := (y `<=` x) (only parsing) : poly_scope.
Notation "x `>=` y :> T" := ((x : T) `>=` (y : T)) (only parsing) : poly_scope.

Notation "x `<` y"  := (poly_lt x y) : poly_scope.
Notation "x `<` y :> T" := ((x : T) `<` (y : T)) (only parsing) : poly_scope.
Notation "x `>` y"  := (y `<` x) (only parsing) : poly_scope.
Notation "x `>` y :> T" := ((x : T) `>` (y : T)) (only parsing) : poly_scope.

Notation "x `<=` y `<=` z" := ((x `<=` y) && (y `<=` z)) : poly_scope.
Notation "x `<` y `<=` z" := ((x `<` y) && (y `<=` z)) : poly_scope.
Notation "x `<=` y `<` z" := ((x `<=` y) && (y `<` z)) : poly_scope.
Notation "x `<` y `<` z" := ((x `<` y) && (y `<` z)) : poly_scope.

Notation "x `<=` y ?= 'iff' C" := (poly_leif x y C) : poly_scope.
Notation "x `<=` y ?= 'iff' C :> R" := ((x : R) `<=` (y : R) ?= iff C)
  (only parsing) : poly_scope.

Notation "x `>=<` y" := (poly_cmp x y) : poly_scope.
Notation "x >< y" := (~~ (poly_cmp x y)) : poly_scope.

Notation "'[' 'affine0' ']'" :=
  (@Order.bottom poly_display Order.affine_BSemilatticeType ) : poly_scope.

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
Proof.
Admitted.

Lemma affine_proper0P V :
  reflect (exists x, x \in V) (V `>` [affine0]).
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

Lemma befst_inj (x : 'cV[R]_n) (e e' : lrel[R]_n) : (* TODO: to be removed *)
  (x \in [hp e]) -> (x \in [hp e']) -> e.1 = e'.1 -> e = e'.
Proof.
move => x_in_e x_in_e' fst_eq.
apply/val_inj/injective_projections => //=.
by move: x_in_e x_in_e'; do 2![rewrite in_hp => /eqP <-]; rewrite fst_eq.
Qed.

Lemma affineS1 (U : {vspace lrel[R]_n}) e :
  e \in U -> ([affine U] `<=` [hp e]).
Proof. (* RK *)
by apply/affineS.
Qed.

Definition affineT : 'affine[R]_n := [hp 0].

Notation "'[' 'affineT' ']'" := affineT : poly_scope.

Lemma in_affineT x : x \in affineT = true.
Proof.
by rewrite in_hp vdot0l eq_refl.
Qed.

Lemma dir_affineT : dir affineT = fullv.
(* RK: I have added this result *)
Proof.
have nullv_in_affineT : 0 \in affineT by rewrite in_affineT.
by apply/vspaceP => ?; rewrite memvf (in_dirP nullv_in_affineT) in_affineT.
Qed.

Lemma affineIC : commutative (@affineI R n).
Proof. by apply: meetC. Qed.

Lemma affineIA : associative (@affineI R n).
Proof. by apply: meetA. Qed.

Lemma affineTI : left_id affineT (@affineI R n).
Proof.
by move => P; apply/affine_eqP => x; rewrite in_affineI in_affineT.
Qed.

Lemma affineIT : right_id affineT (@affineI R n).
Proof.
by move => P; apply/affine_eqP => x; rewrite  in_affineI in_affineT andbT.
Qed.

Canonical affineI_monoid := Monoid.Law affineIA affineTI affineIT.
Canonical affineI_comonoid := Monoid.ComLaw affineIC.

Notation "\affineI_ ( i <- r | P ) F" :=
  (\big[affineI/affineT]_(i <- r | P%B) F).
Notation "\affineI_ ( i <- r ) F" :=
  (\big[affineI/affineT]_(i <- r) F).
Notation "\affineI_ ( i | P ) F" :=
  (\big[affineI/affineT]_(i | P%B) F).
Notation "\affineI_ i F" :=
  (\big[affineI/affineT]_i F).
Notation "\affineI_ ( i : I | P ) F" :=
  (\big[affineI/affineT]_(i : I | P%B) F) (only parsing).
Notation "\affineI_ ( i : I ) F" :=
  (\big[affineI/affineT]_(i : I) F) (only parsing).
Notation "\affineI_ ( m <= i < n | P ) F" :=
 (\big[affineI/affineT]_(m <= i < n | P%B) F).
Notation "\affineI_ ( m <= i < n ) F" :=
 (\big[affineI/affineT]_(m <= i < n) F).
Notation "\affineI_ ( i < n | P ) F" :=
 (\big[affineI/affineT]_(i < n | P%B) F).
Notation "\affineI_ ( i < n ) F" :=
 (\big[affineI/affineT]_(i < n) F).
Notation "\affineI_ ( i 'in' A | P ) F" :=
 (\big[affineI/affineT]_(i in A | P%B) F).
Notation "\affineI_ ( i 'in' A ) F" :=
 (\big[affineI/affineT]_(i in A) F).

Lemma big_affine_inf (I : finType) (j : I) (P : pred I) (F : I -> 'affine[R]_n) :
  P j -> (\affineI_(i | P i) F i <= F j)%O.
Proof. (* RK *)
move => ?; rewrite (bigD1 j) //=.
apply/affine_leP => v; rewrite in_affineI.
by move/andP => [? _].
Qed.

Lemma in_big_affineIP (I : finType) (P : pred I) (F : I -> 'affine[R]_n) x :
  reflect (forall i : I, P i -> x \in (F i)) (x \in \affineI_(i | P i) (F i)).
Proof. (* RK *)
apply: (iffP idP) => [? i Pi | x_in_F].
- by apply: (affine_leP (big_affine_inf F Pi)).
- elim/big_rec: _ => [|i V Pi ?]; first by rewrite in_affineT.
  by rewrite in_affineI; apply/andP; split; [apply: (x_in_F i) | done].
Qed.

Lemma in_big_affineI (I : finType) (P : pred I) (F : I -> 'affine[R]_n) x :
  (x \in \affineI_(i | P i) (F i)) = [forall i, P i ==> (x \in F i)].
Proof. (* RK *)
apply/in_big_affineIP/idP.
- by move => Hforall; apply/forallP => i; apply/implyP/Hforall.
- by move/forallP => Hforall i; apply/implyP/Hforall.
Qed.

Lemma big_affineIsP (I : finType) Q (P : pred I) (F : I -> 'affine[R]_n) :
  reflect (forall i : I, P i -> Q `<=` F i) (Q `<=` \affineI_(i | P i) F i).
apply: (iffP idP) => [/affine_leP Hsubset ? ?| Hsubset_forall];
  apply/affine_leP => ? in_Q.
- by apply: (in_big_affineIP _ _ _ (Hsubset _ in_Q)).
- by apply/in_big_affineIP => i Pi; apply/(affine_leP (Hsubset_forall i Pi)).
Qed.

Lemma affine_span (I : base_t[R,n]) :
  [affine <<I>>] = \affineI_(e : I) [hp (val e)].
Admitted.

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

Notation "'[' 'hp' e  ']'" := [affine <[e]> ] : poly_scope.
Notation "'[' 'line' d & Ω ']'" := [affine <[d]> & Ω] : poly_scope.
Notation "'[' 'pt' Ω ']'" := [affine 0%VS & Ω] : poly_scope.
Notation "'[' 'affineT' ']'" := (@affineT _ _) : poly_scope.

Notation "\affineI_ ( i <- r | P ) F" :=
  (\big[affineI/affineT]_(i <- r | P%B) F).
Notation "\affineI_ ( i <- r ) F" :=
  (\big[affineI/affineT]_(i <- r) F).
Notation "\affineI_ ( i | P ) F" :=
  (\big[affineI/affineT]_(i | P%B) F).
Notation "\affineI_ i F" :=
  (\big[affineI/affineT]_i F).
Notation "\affineI_ ( i : I | P ) F" :=
  (\big[affineI/affineT]_(i : I | P%B) F) (only parsing).
Notation "\affineI_ ( i : I ) F" :=
  (\big[affineI/affineT]_(i : I) F) (only parsing).
Notation "\affineI_ ( m <= i < n | P ) F" :=
 (\big[affineI/affineT]_(m <= i < n | P%B) F).
Notation "\affineI_ ( m <= i < n ) F" :=
 (\big[affineI/affineT]_(m <= i < n) F).
Notation "\affineI_ ( i < n | P ) F" :=
 (\big[affineI/affineT]_(i < n | P%B) F).
Notation "\affineI_ ( i < n ) F" :=
 (\big[affineI/affineT]_(i < n) F).
Notation "\affineI_ ( i 'in' A | P ) F" :=
 (\big[affineI/affineT]_(i in A | P%B) F).
Notation "\affineI_ ( i 'in' A ) F" :=
 (\big[affineI/affineT]_(i in A) F).

Section Dimension.

Context {R : realFieldType} {n : nat}.

Implicit Type (V : 'affine[R]_n).

Definition dim V :=
  if V == [affine0] then 0%N
  else (\dim (dir V)).+1%N.

Lemma dim0 : dim [affine0] = 0%N.
by rewrite /dim ifT //.
Qed.

Lemma dimN0 V : (dim V > 0)%N = (V `>` affine0).
Proof.
by rewrite /dim; case: ifP => [/eqP -> // |]; rewrite lt0x => ->.
Qed.

Lemma dim_eq0 V : (dim V = 0)%N -> V = [affine0].
Proof.
by rewrite /dim; case: ifP => [/eqP ->|].
Qed.

Lemma dimS : {homo dim : V V' / (V `<=` V') >-> (V <= V')%N}.
Proof.
move => V V' sub.
rewrite /dim; case: ifPn => // V_neq0.
have V'_neq0: V' != [affine0].
- move: V_neq0; apply/contra_neq => V'_eq0.
  by rewrite V'_eq0 lex0 in sub; move/eqP: sub.
rewrite ifF ?ltnS; last by apply/negbTE.
by apply/dimvS/dirS.
Qed.

Lemma dim_leqif_eq V V' :
  (V `<=` V') -> (dim V <= dim V' ?= iff (V == V'))%N.
Proof.
move => V_sub_V'; split; rewrite ?dimS //.
apply/eqP/eqP; last by move => ->.
rewrite {1}/dim; case: ifP.
- by move/eqP ->; symmetry; apply/dim_eq0.
- move/negbT => V_neq0.
  have V'_neq0: V' != [affine0].
    rewrite -!lt0x in V_neq0 *.
    by apply/lt_le_trans: V_sub_V'.
  rewrite /dim ifF; last by apply/negbTE.
  move/succn_inj => dim_dir_eq.
  suff: dir V = dir V'.
  - case/affineN0: V_neq0 => x x_in.
    by apply/(dir_eq x_in)/(affine_leP V_sub_V').
  - by apply/eqP; rewrite -(eq_leqif (dimv_leqif_eq (dirS _))) ?dim_dir_eq.
Qed.

Lemma sub_geq_dim V V' :
  (V `<=` V') -> (dim V >= dim V')%N -> V = V'.
Proof. (* RK *)
move => V_sub_V' dimV_gte_dimV'; apply/eqP/contraT => V_neq_V'.
by move/leqifP: (dim_leqif_eq V_sub_V'); rewrite ifF;
  [rewrite ltnNge dimV_gte_dimV' | apply/negbTE].
Qed.

Lemma sub_eq_dim V V' :
  (V `<=` V') -> dim V = dim V' -> V = V'.
Proof. (* RK *)
move => ? dimV_eq_dimV'.
by apply/sub_geq_dim; [done | rewrite dimV_eq_dimV'].
Qed.

Lemma dim_affine_lt V V' :
  (V `<` V') -> (dim V < dim V')%N.
Proof. (* RK *)
move/andP => [V'_neq_V ?].
rewrite ltn_neqAle; apply/andP; split; last by apply/dimS.
move: V'_neq_V; apply/contra_neqN => /eqP ?; symmetry.
by apply/sub_eq_dim.
Qed.

Lemma dim_line Ω d : dim [line d & Ω] = (d != 0).+1.
Proof.
rewrite /dim ifF; last by apply/negbTE/mk_affineN0.
by rewrite dir_mk_affine dim_vline.
Qed.

Lemma dim_pt Ω : dim [pt Ω] = 1%N.
Proof.
by rewrite dim_line eq_refl.
Qed.

Lemma dimv_eq1P (K : fieldType) (vT : vectType K) (V : {vspace vT}) :
  reflect (exists2 v, v != 0 & V = <[v]>%VS) (\dim V == 1%N).
(* RK: I added this result which I could not find but it is quite natural.
       If we keep it, I suppose it should be somewhere else. *)
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

Lemma dim2P V :
  dim V = 2%N -> exists Ω, exists2 d, d != 0 & V = [line d & Ω].
Proof. (* RK *)
move => dim_V_eq2.
have V_neq0 : V != affine0.
  apply/contraT => V_eq0; rewrite negbK in V_eq0.
  by rewrite (eqP V_eq0) dim0 in dim_V_eq2.
have dim_dir_V_eq1: (\dim (dir V)) = 1%N
  by apply/eq_add_S; rewrite /dim ifF // in dim_V_eq2; apply/negbTE.
move/eqP/dimv_eq1P: (dim_dir_V_eq1) => [d ? dir_V_eq].
move/affineN0: V_neq0 => [Ω Ω_in_V].
exists Ω; exists d; first by done.
by rewrite -dir_V_eq; apply/mk_affine_dir.
Qed.

Lemma dim1P V :
  dim V = 1%N -> exists Ω, V = [pt Ω].
Proof. (* RK *)
move => dim_V_eq1.
have V_neq0 : V != affine0.
  apply/contraT => V_eq0; rewrite negbK in V_eq0.
  by rewrite (eqP V_eq0) dim0 in dim_V_eq1.
move: (affineN0 _ V_neq0) => [Ω Ω_in_V].
exists Ω.
suff <-: (dir V) = 0%VS by apply/mk_affine_dir.
apply/eqP; rewrite -dimv_eq0.
by apply/eqP/eq_add_S; rewrite /dim ifF // in dim_V_eq1; apply/negbTE.
Qed.

Lemma dim_leSn V :
  (dim V <= n.+1)%N.
Proof. (* RK *)
rewrite /dim; case: (boolP (V == affine0)) => [_|_]; first by done.
rewrite ltnS.
by apply/(@leq_trans (n * 1)); [apply/rank_leq_col | rewrite muln1].
Qed.

Lemma dim_affine_le (U : {vspace lrel[R]_n}) :
  [affine U] `>` [affine0] -> (\dim U <= n)%N.
Proof. (* RK *)
move => affine_U_neq0; apply/contraT; rewrite -ltnNge => ?.
have U_eq_fullv: U = fullv
  by apply/eqP; rewrite eqEdim; apply/andP; split;
    [exact: subvf | rewrite dimvf /Vector.dim /= addn1].
pose e := [<0, 1>]: lrel[R]_n.
have e_in_U: e \in U by rewrite U_eq_fullv memvf.
rewrite (cond_affine0 e_in_U) in affine_U_neq0.
move/affine_proper0P: affine_U_neq0 => [?].
by rewrite in_affine0.
Qed.

Lemma dimT : (dim affineT = n.+1)%N.
Proof. (* RK *)
rewrite /dim ifF.
- by rewrite dir_affineT dimvf /Vector.dim /= muln1.
- apply/(contraFF _ (erefl false)).
  move/eqP/affine_eqP => aff_eq.
  by move: (aff_eq 0); rewrite in_affine0 in_affineT.
Qed.

Lemma dimTP V : dim V = n.+1%N -> V = affineT.
Proof. (* RK *)
rewrite -dimT => ?.
apply/sub_eq_dim; last by done.
by apply/affine_leP => ?; rewrite in_affineT.
Qed.

Lemma dim_hp e :
  [hp e] `>` [affine0] -> dim [hp e] = ((e.1 == 0%R) + n)%N.
Admitted.

End Dimension.

(*
Lemma affine_subset (U V : {vspace lrel[R]_n}) :
  (affine V `>` [poly0]) -> affine V `<=` affine U -> (U <= V)%VS.
Proof.
move/proper0P => [x x_in_affV] /poly_subsetP aff_sub.
have x_in_affU : x \in affine U by exact: aff_sub.
have: ((befst @: V)^OC <= (befst @: U)^OC)%VS.
- apply/subvP => d d_in.
  pose y := x + d.
  have /aff_sub: y \in affine V by apply/(in_affine_orth _ x_in_affV); exists d.
  by move/(in_affine_orth _ x_in_affU) => [d' d'_in /addrI ->].
rewrite orthS => /subvP fst_sub; apply/subvP => e e_in_U.
move/(memv_img befst)/fst_sub/memv_imgP: (e_in_U) => [e' e'_in_V fst_eq].
suff ->: e = e' by [].
rewrite !lfunE /= in fst_eq.
apply/(befst_inj (x := x) _ _ fst_eq).
- by apply: (poly_subsetP (affineS1 e_in_U)).
- by apply: (poly_subsetP (affineS1 e'_in_V)).
Qed.

Lemma affine_inj (U V : {vspace lrel[R]_n}) :
  (affine U `>` [poly0]) -> affine U = affine V -> U = V.
Proof.
move => affU_prop0 aff_eq.
have affV_prop0 : (affine V `>` [poly0]) by rewrite -aff_eq.
by apply/subv_anti/andP; split; apply/affine_subset => //; rewrite aff_eq poly_subset_refl.
Qed.*)
