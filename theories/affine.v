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

Declare Scope affine_scope.
Delimit Scope affine_scope with A.

Reserved Notation "''affine[' R ]_ n"
  (at level 8, n at level 2, format "''affine[' R ]_ n").
Reserved Notation "''affine[' R ]"
  (at level 8, format "''affine[' R ]").
Reserved Notation "''affine_' n"
  (at level 8, format "''affine_' n").
Reserved Notation "[ 'affine' I ]" (at level 0, format "[ 'affine'  I ]").
Reserved Notation "[ 'hp' e ]" (at level 0, format "[ 'hp'  e ]").

Section Solve.

Variable (R : realFieldType) (n : nat) (V : {vspace lrel[R]_n}).

Let base := vbasis V.

Definition sat x :=
   all (fun e : lrel => '[e.1, x] == e.2) base.

Lemma satP x :
  reflect (forall e, e \in V -> '[e.1, x] = e.2) (sat x).
Admitted.

Let A := (\matrix_i (tnth base i).1^T)^T.
Let b := (\row_i (tnth base i).2).

Lemma satE x : sat x = (b == x^T *m A).
Admitted.

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
Admitted.

Lemma be_liftE W x :
  sat W x -> ((be_lift x) @: (befst @: W))%VS = W.
Proof.
move => sat_x.
Admitted.

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

Import Core.Exports.
Notation "''affine[' R ]_ n" := (Core.type_of n (Phant R)).
Notation "''affine[' R ]"    := 'affine[R]_(_).
Notation "''affine_' n"      := 'affine[_]_n.
Notation "[ 'affine' I ]"    := (Core.affine I%VS).
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
rewrite /Core.affine; case: {-}_/idP => [// | /negP/is_satPn ->].
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
  rewrite /Core.affine; case: {-}_/idP => // ?.
  apply/congr1; exact: bool_irrelevance.
  suff h: exists x, x \in [affine U].
  + have /negbTE ->: [affine U] != affine0 by apply/affineN0.
    by constructor.
  + case/is_satP : U_sat => x x_in; exists x.
    by rewrite in_affineE.
Qed.

Lemma affine_is_sat U :
  [affine U] != affine0 = is_sat U.
Proof.
rewrite /Core.affine; case: {-}_/idP.
- move => is_sat; rewrite is_sat.
  by apply/eqP.
- move/negP/negbTE ->.
  by rewrite eq_refl.
Qed.

Definition mk_affine W Ω : 'affine[R]_n :=
  [affine ((be_lift Ω) @: W^OC)%VS].

Notation "'[' 'affine' W & Ω ']'" := (mk_affine W Ω).

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

Lemma mk_affine_prop0 W Ω :
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

Lemma in_affineI x V V' :
  x \in affineI V V' = (x \in V) && (x \in V').
Admitted.

Definition affine_le V V' := (V == affineI V V').
Lemma affine_leP V V' : reflect {subset V <= V'} (affine_le V V').
Proof.
apply/(iffP eqP).
- move/affine_eqP => eq x.
  by rewrite eq in_affineI => /andP[].
- move => sub; apply/affine_eqP => x.
  rewrite in_affineI.
  by apply/idP/andP => [?|[] //]; split => //; apply/sub.
Qed.

End Specs.

Notation "'[' 'affine' W & Ω ']'" := (mk_affine W Ω).

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
Admitted.

Fact affine_display : unit. Proof. exact: tt. Qed.

Definition affine_LtPOrderMixin :=
  LePOrderMixin  (fun _ _ => erefl _) affine_le_refl affine_le_anti affine_le_trans.

Canonical affine_LtPOrderType :=
  Eval hnf in POrderType affine_display 'affine[R]_n affine_LtPOrderMixin.

Lemma affine_leE V V' : (V <= V')%O = affine_le V V'.
Proof. by []. Qed.

Program Canonical affine_MeetSemilattice :=
  Eval hnf in MeetSemilatticeType 'affine[R]_n
    (@MeetSemilatticeMixin _ _ affineI _ _ _ _).

Next Obligation.
by move=> V V'; apply/affine_eqP=> x; rewrite !in_affineI andbC.
Qed.

Next Obligation.
by move=> V1 V2 V3; apply/affine_eqP=> x; rewrite !in_affineI andbA.
Qed.

Next Obligation.
by move=> V; apply/affine_eqP=> x; rewrite !in_affineI andbb.
Qed.

Next Obligation.
apply/affine_leP/eqP => [|<-]; last first.
+ by move=> c; rewrite in_affineI => /andP[].
move=> le_xy; apply/affine_eqP=> c; rewrite in_affineI.
by apply: andb_idr; apply: le_xy.
Qed.

Program Definition affine_bottomMixin :=
  @BottomMixin affine_display [porderType of 'affine[R]_n] affine0 _.
Next Obligation. by apply/affine_leP=> v; rewrite in_affine0. Qed.

Canonical affine_BSemilatticeType :=
  Eval hnf in BSemilatticeType 'affine[R]_n affine_bottomMixin.

End Order.

Module Import Exports.
Canonical affine_LtPOrderType.
Canonical affine_MeetSemilattice.
Canonical affine_BSemilatticeType.
End Exports.
End Order.

Import Order.Exports.

Section BasicObjects.

Context {R : realFieldType} {n : nat}.

Implicit Type (Ω d : 'cV[R]_n) (e : lrel[R]_n) (V : 'affine[R]_n).

Lemma mk_affineS Ω : { mono (mk_affine^~ Ω) : W W' / (W <= W')%VS >-> (W <= W')%O }.
Proof.
move => W W'; apply/affine_leP/subvP => [sub x x_in | sub x].
Admitted.

Lemma dirS V V' : V' != affine0 -> (V <= V')%O -> (dir V <= dir V')%VS.
Admitted.

Lemma mk_affine_neq0 Ω W : [affine W & Ω] != affine0.
Admitted.

Definition mk_hp e := [affine <[e]> ].
Notation "'[' 'hp' e  ']'" := (mk_hp e%PH).

Lemma in_hp :
  (forall e x, (x \in [hp e]) = ('[e.1,x] == e.2))
  * (forall c α x, (x \in [hp [<c, α>]]) = ('[c,x] == α)).
Admitted.

Definition affineT := [hp 0].

Lemma in_affineT x : x \in affineT = true.
Proof.
by rewrite in_hp vdot0l eq_refl.
Qed.

Definition mk_line d Ω := [affine <[d]> & Ω].
Notation "'[' 'line' d & Ω ']'" := (mk_line d Ω).

Lemma in_lineP {d Ω x : 'cV[R]_n} :
  reflect (exists μ, x = Ω + μ *: d) (x \in [line d & Ω]).
Proof.
rewrite /mk_line.
apply/(iffP in_mk_affineP) => [[y /vlineP [μ ->]]| [μ ->] ].
+ by exists μ.
+ by exists (μ *: d); rewrite ?memvZ ?memv_line.
Qed.

Lemma line_subset_hp e v v' :
  (v \in [hp e]) -> (v' \in [hp e]) -> ([line (v' - v) & v] <= [hp e])%O.
Proof.
rewrite !in_hp => /eqP v_in /eqP v'_in.
apply/affine_leP => ? /in_lineP [μ -> ]; rewrite in_hp.
by rewrite vdotDr vdotZr vdotBr v_in v'_in addrN mulr0 addr0.
Qed.

Definition mk_pt Ω := [affine 0%VS & Ω].

Notation "'[' 'pt' Ω ']'" := [affine 0%VS & Ω].

Lemma in_pt Ω x : (x \in [pt Ω]) = (x == Ω).
Proof.
by rewrite in_mk_affine memv0 subr_eq0.
Qed.

End BasicObjects.

Notation "'[' 'hp' e  ']'" := (mk_hp e%PH).
Notation "'[' 'line' d & Ω ']'" := (mk_line d Ω).
Notation "'[' 'pt' Ω ']'" := [affine 0%VS & Ω].

Section Dimension.

Context {R : realFieldType} {n : nat}.

Implicit Type (V : 'affine[R]_n).

Definition dim V :=
  if V == affine0 then 0%N
  else (\dim (dir V)).+1%N.

Lemma dim0 : dim affine0 = 0%N.
by rewrite /dim ifT //.
Qed.

Lemma dimN0 V : (dim V > 0)%N = (V != affine0).
by rewrite /dim; case: ifP.
Qed.

Lemma dim_eq0 V : (dim V = 0)%N -> V = affine0.
Proof.
by rewrite /dim; case: ifP => [/eqP ->|].
Qed.

Lemma dimS : {homo dim : V V' / (V <= V')%O >-> (V <= V')%N}.
Proof.
move => V V' sub.
rewrite /dim; case: ifPn => // V_neq0.
have V'_neq0: V' != affine0.
- move: V_neq0; apply/contra_neq => V'_eq0.
  by rewrite V'_eq0 lex0 in sub; move/eqP: sub.
rewrite ifF ?ltnS; last by apply/negbTE.
by apply/dimvS/dirS.
Qed.

Lemma dim_line Ω d : dim [line d & Ω] = (d != 0).+1.
Proof.
rewrite /dim ifF; last by apply/negbTE/mk_affine_neq0.
by rewrite dir_mk_affine dim_vline.
Qed.

Lemma dim_pt Ω : dim [pt Ω] = 1%N.
Proof.
by rewrite dim_line eq_refl.
Qed.

Lemma dim2P V :
  dim V = 2%N -> exists Ω, exists2 d, d != 0 & V = [line Ω & d].
Admitted.

Lemma dim1P V :
  dim V = 1%N -> exists Ω, V = [pt Ω].
Admitted.

Lemma dim_leSn V :
  (dim V <= n.+1)%N.
Admitted.

Lemma dimT : (dim affineT = n.+1)%N.
Admitted.

Lemma dimTP V : dim V = n.+1%N -> V = affineT.
Admitted.

Lemma dim_hp e :
  [hp e] != affine0 -> dim [hp e] = ((e.1 == 0%R) + n)%N.
Admitted.

End Dimension.
