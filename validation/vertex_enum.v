From mathcomp Require Import all_ssreflect. (* all_algebra finmap.
Require Import vector_order extra_matrix row_submx.*)

Load order.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.*)

(*
On se donne un type fini T (par ex. les sous-ensembles de [m] de cardinal n), un predicat P sur T (par ex, le fait d'être une base admissible), et une relation R d'adjacence sur T.
On veut montrer qu'une liste L informellement calculée est précisément l'ensemble des x : T vérifiant P x.
On note R_P la relation induite par R sur P.
Hypothèse : P est connexe au sens de R_P, ie étant donnés x, y vérifiant P, il existe un chemin dans le graphe de R_P qui relie x et y.
Hypothese : on a une fonction qui, étant donné x : T, fournit un sur-ensemble des voisins de x selon R.
Hypothèse : pour tout x \in L, et pour tout voisin y de X selon R, y vérifie P -> y \in L

Thm : si L est non-vide et vérifie L \subset P, alors L =i P.
*)

Section IRelation.
Context {T : eqType} (R : rel T) (P : pred T).

Definition irelation :=
  [rel x y | [&& R x y, P x & P y]].

Lemma irel_refl : reflexive R -> {in P, reflexive irelation}.
Proof.
by move=> reflx x /= px; rewrite [P x]px reflx.
Qed.

Lemma irel_sym : symmetric R -> symmetric irelation.
Proof.
by move => symR x y /=; rewrite symR !andbA andbAC.
Qed.


Lemma irel_trans :transitive R -> transitive irelation.
Proof.
move => tr y x z /and3P [rxy px py] /and3P [ryz _ pz] /=.
by rewrite (tr y) // px pz.
Qed.





End IRelation.

Section Abstract.
Variable (T : finType) (P : pred T) (R : rel T) (neighbour: T -> {set T}).

Let R_P := irelation R P.

Hypothesis R_P_connected : forall x y, x \in P -> y \in P -> connect R_P x y.
Hypothesis Hneighbour : forall x y, R x y -> y \in neighbour x.

Variable (L : {set T}).
(* Check that L is precisely the set of inhabitants of T *)

Definition pivot_check x :=
  forall y, y \in neighbour x -> y \in P -> y \in L.

Definition closedness_check :=
  forall x, x \in L -> pivot_check x.

Lemma foo :
  (L \subset P) -> L != set0 -> closedness_check -> L =i P.
(*Search "subset" "\in".*)
Proof.
(*
tactic/view: pt-gen => pt-intro.
pt-gen -> view -> tactic -> pt-intro.
*)

move=> LsubsetP /set0Pn [x0 x0_in_L] Lclosed.
(* rewrite /closedness_check /pivot_check in Lclosed. *)
apply/subset_eqP/andP; split => //.
move/subsetP: (LsubsetP) => /(_ _ x0_in_L) x0_in_P.
suff closed_RL: closed R L.
+ apply: (subset_trans (Hconnected x0_in_P)).
  

apply/subsetP => x x_in_P.

move/(_ _ x0_in_P): Hconnected.

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
