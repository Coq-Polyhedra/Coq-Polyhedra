From mathcomp Require Import all_ssreflect. (* all_algebra finmap.
Require Import vector_order extra_matrix row_submx.*)

Load order.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.*)

Section Abstract.

Variable (T : finType) (P : pred T) (R : rel T) (neighbour: T -> {set T}).
Hypothesis Pclosed : closed R P.
Hypothesis Hconnected : forall x, x \in P -> (P \subset closure R (pred1 x)).
Hypothesis Hneighbour : forall x y, R x y -> y \in neighbour x.

Variable (L : {set T}).
(* Check that L is precisely the set of inhabitants of T *)

Definition pivot_check x :=
  [forall y, (y \in neighbour x) ==> (y\in L)].

Definition closedness_check :=
  [forall x in L, pivot_check x].


Lemma foo :
  (L \subset P) -> L != set0 -> closedness_check -> L =i P.

Search "subset" "\in".

Proof.
move => LsubsetP LnotEmpty Lclosed.
apply /subset_eqP.
case /set0Pn: LnotEmpty => [x x_in_L].
unfold closedness_check in Lclosed.
unfold pivot_check in Lclosed.
apply /andP.
split.
  by [].





  
Qed.
End Abstract.

(*
Section Enumeration.

Context {R : realFieldType} {m n : nat}.
Context {A : 'M[R]_(m,n)} {b : 'cV[R]_m} {L : {fset 'cV[R]_n}}.

Lemma pivot_card (I : {set 'I_m}) (i j : 'I_m) :
  i \in I -> j \notin I -> #| j |: (I :\ i) | = n.
Admitted.

Definition is_basis_of (x : 'cV[R]_n) (I : {set 'I_m}) :=
  let A_I := row_submx A I in
  (#| I | == n) && (row_free A_I) && (A_I *m x == row_submx b I).

Definition pivot_check (I : {set 'I_m}) (i j : 'I_m) :=
  match @idP (i \in I), @idP (j \notin I) with
  | ReflectT i_in_I, ReflectT j_notin =>
    let J := j |: (I :\ i) in
    let A_J := row_submx A J in
    if row_free A_J then
      let y := (qinvmx (pivot_card i_in_I j_notin) A_J) *m (row_submx b J) in
      ((A *m y) >=m b ==> (y \in L))
    else
      true
  | _, _ => true
  end.

Definition neighborhood_check (x : 'cV[R]_n) :=
  [forall I, is_basis_of x I ==> [forall i, [forall j, pivot_check I i j]]].

Definition closedness_check (L : {fset 'cV[R]_n}) :=
  [forall x : L, neighborhood_check (val x)].

End Enumeration.
*)
