(* This file was written by Erik Martin-Dorel, 2016 *)
From mathcomp Require Import all_ssreflect ssrmatching.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Tactic for rewriting under lambdas in MathComp *)

Module Private.

(** ** Preliminary tactics *)

Ltac clear_all h :=
  try unfold h in * |- *; try clear h.

Ltac clear_all3 h1 h2 h3 :=
  clear_all h1; clear_all h2; clear_all h3.

(** [do_pad_tac lem tac] pads lem with [_]s, as Ltac does not handle implicits *)
Ltac do_pad_tac lem tac :=
  match type of lem with
  | forall x1 : ?A, forall x2 : _, forall p : _, _ =>
    let a := fresh "_evar_a_" in
    evar (a : A);
    let lem' := eval unfold a in (lem a) in
    do_pad_tac lem' tac; clear_all a
    | forall x2 : _, forall p : _, _ => tac lem
    | _ => fail 100 "expecting a lemma whose type ends with a function and a side-condition."
               "Cannot proceed with:" lem
    end.

Ltac do_sides_tac equ taclr :=
  match type of equ with
  | forall p : _, ?a = ?b =>
    taclr a b
  | ?a = ?b =>
    taclr a b
  end.

(** [pretty_rename term i] is a convenience tactic that tries to
rename the index of [term] to [i], e.g. if [term] is a bigop expr. *)
Ltac pretty_rename term i :=
  rewrite -?[term]/(_ (fun i => _))
          -?[term]/(_ _ (fun i => _))
          -?[term]/(_ _ _ (fun i => _))
          -?[term]/(_ _ _ _ (fun i => _))
          -?[term]/(_ _ _ _ _ (fun i => _))
          -?[term]/(_ _ _ _ _ _ (fun i => _))
          -?[term]/(_ _ _ _ _ _ _ (fun i => _))
          -?[term]/(_ _ _ _ _ _ _ _ (fun i => _))
          -?[term]/(_ _ _ _ _ _ _ _ _ (fun i => _)).

(** [rew_tac pat x2 equ] uses [equ] to rewrite occurrences of [pat]
and uses [x2] to avoid "evars leaking".
Last argument [i] is used by [pretty_rename]. *)
Ltac rew_tac pat x2 equ i :=
  ((ssrpattern pat)
   || fail 100 "the specified pattern does not match any subterm of the goal");
  let top := fresh in move=> top;
  do_sides_tac
    equ
    ltac:(fun lhs rhs =>
            let top' := eval unfold top in top in
            let lhs' := eval unfold x2 in lhs in
            let rhs' := eval unfold x2 in rhs in
            unify top' lhs' with typeclass_instances;
            rewrite [top]equ; pretty_rename rhs' i);
  clear_all top.

Ltac do_pat pat tac :=
  match goal with
  | |- context [?x] =>
    unify pat x with typeclass_instances;
    tac x
  end.

(** [rew_tac1] is similar to [rew_tac] but ignores the [pat] variable.
Instead, it uses [equ] to rewrite the first occurrence of [equ]'s lhs.
Last argument [i] is used by [pretty_rename]. *)
Ltac rew_tac1 pat x2 equ i :=
  (* doing simply (* rewrite equ. *) would cause some evars leaking *)
  do_sides_tac
    equ
    ltac:(fun lhs rhs =>
            let lhs' := eval unfold x2 in lhs in
            let rhs' := eval unfold x2 in rhs in
            do_pat
              lhs'
              ltac:(fun x =>
                let top := fresh in set top := x;
                rewrite [top]equ; pretty_rename rhs' i; clear_all top)).

(** ** The main tactic *)
Ltac under_tac rew pat lem i intro_tac tac :=
  do_pad_tac
    lem
    ltac:(fun l =>
            let I := fresh "_evar_I_" in
            let R := fresh "_evar_R_" in
            let x2 := fresh "_evar_x2_" in
            evar (I : Type);
            evar (R : Type);
            evar (x2 : I -> R);
            let lx2 := constr:(l x2) in
            (rew pat x2 lx2 i
             || fail 100 "the lhs of" lx2 "does not match the selected subterms of the goal");
            [clear_all3 x2 R I
            |(intro_tac || fail 100 "under lemma" lem "we cannot introduce"
                                   "the identifier(s) you specified."
                                   "Maybe some identifier is already used.");
             (tac || fail 100 "cannot apply tactic under lemma" lem);
             clear_all3 x2 R I; try done]).

End Private.

Import Private.

(** ** The under tacticals, upto 3 vars to introduce in the context *)

(** *** with no ssr pattern argument *)

(** the tactic will rewrite [lem] (then apply [tac]) at the first term
matching [lem]'s lhs *)

(* Note: these 4 definitions must come first, before the 4 definitions
of the tacticals involving a ssrpatternarg *)

Tactic Notation "under"
       open_constr(lem) simple_intropattern(i) tactic3(tac) :=
  under_tac rew_tac1 false lem i ltac:(move=> i) tac.

(* Given the tactic grammar, we need to write "["..."]" below, else
the intro-pattern would lead to unwanted case analysis. *)

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) "]" tactic3(tac) :=
  under_tac rew_tac1 false lem i ltac:(move=> i) tac.

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) "]" tactic3(tac) :=
  under_tac rew_tac1 false lem i ltac:(move=> i j) tac.

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) simple_intropattern(k) "]" tactic3(tac) :=
  under_tac rew_tac1 false lem i ltac:(move=> i j k) tac.

(** *** with a ssr pattern argument *)

(** all occurrences matching [pat] will be rewritten using [lem] then [tac] *)

Tactic Notation "under"
       "[" ssrpatternarg(pat) "]" open_constr(lem) simple_intropattern(i) tactic3(tac) :=
  under_tac rew_tac pat lem i ltac:(move=> i) tac.

Tactic Notation "under"
       "[" ssrpatternarg(pat) "]" open_constr(lem) "[" simple_intropattern(i) "]" tactic3(tac) :=
  under_tac rew_tac pat lem i ltac:(move=> i) tac.

Tactic Notation "under"
       "[" ssrpatternarg(pat) "]" open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) "]" tactic3(tac) :=
  under_tac rew_tac pat lem i ltac:(move=> i j) tac.

Tactic Notation "under"
       "[" ssrpatternarg(pat) "]" open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) simple_intropattern(k) "]" tactic3(tac) :=
  under_tac rew_tac pat lem i ltac:(move=> i j k) tac.
