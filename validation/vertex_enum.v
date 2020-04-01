From mathcomp Require Import all_ssreflect.

(*Load order.*)
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
Context (T : finType) (e : rel T) (P : {pred T}).

Definition irel :=
  [rel x y | [&& e x y, (x \in P) & (y \in P)]].


Lemma irel_refl : reflexive e -> {in P, reflexive irel}.
Proof.
by move=> reflx x /= px; rewrite px reflx.
Qed.

Lemma irel_sym : symmetric e -> symmetric irel.
Proof.
by move => symR x y /=; rewrite symR !andbA andbAC.
Qed.

Lemma irel_trans : transitive e -> transitive irel.
Proof.
move => tr y x z /and3P [rxy px py] /and3P [ryz _ pz] /=.
by rewrite (tr y) // px pz.
Qed.

Lemma irel_mem x y : irel x y -> ((x \in P) * (y \in P))%type.
Proof.
by case/and3P => _ -> ->.
Qed.

Lemma closed_irel : closed irel P.
Proof.
by move => x y /irel_mem h; rewrite !h.
Qed.

(*Definition connected := (n_comp irel P == 1)%N.

Lemma connectedP :
  connect_sym irel -> reflect (forall x y, x \in P -> y \in P -> (connect irel) x y) connected.
Proof.
Admitted.*)

Lemma connect_irel :
  closed e P -> forall x y, x \in P -> (connect e) x y -> (connect irel) x y.
Proof.
move => e_closed x y x_in_P.
case/connectP => p p_path ->.
elim: p x x_in_P p_path => [//= | x p /= ind].
move => {}y y_in_P /andP [e_xy p_path].
have x_in_P: x \in P by rewrite -(e_closed _ _ e_xy).
move/(_ _ x_in_P p_path): ind => /connectP [p' p'_path ->].
apply/connectP; exists (x :: p') => //=.
by apply/andP; split; first apply/and3P.
Qed.

Definition connected := forall x y, x \in P -> y \in P -> (connect irel) x y.

Lemma connectedW (Q : pred T) :
  connected -> closed irel Q -> forall x0, x0 \in P -> x0 \in Q -> {subset P <= Q}.
Proof.
move => (*/connectedP*) conn Q_closed x0 x0_in_P x0_in_Q x x_in_P.
move/(_ _ _  x0_in_P x_in_P): conn => conn.
by rewrite -(closed_connect Q_closed conn).
Qed.

End Connectedness.

Section Abstract.
Variable (T : finType) (P : pred T) (R : rel T) (neighbour: T -> {set T}).

Let R_P := irelation R P.

Hypothesis R_P_connected : forall x y, x \in P -> y \in P -> connect R_P x y.
Hypothesis Hneighbour : forall x y, R_P x y -> y \in neighbour x.

Variable (L : {set T}).
(* Check that L is precisely the set of inhabitants of T *)

Definition closedness_check :=
  forall x, x \in L -> forall y, y \in neighbour x -> y \in P -> y \in L.

Lemma foo :
  (L \subset P) -> L != set0 -> closedness_check -> L =i P.
Proof.
move=> LsubsetP /set0Pn [x0 x0_in_L] Lclosed.
apply/subset_eqP/andP; split => //.
move/subsetP: (LsubsetP) => /(_ _ x0_in_L) x0_in_P.
apply/subsetP/(connectedW R_P_connected x0_in_P) => //.
move => x y x_in_L R_P_x_y.
apply/(Lclosed _ x_in_L).
- exact: Hneighbour.
- by case/and3P: R_P_x_y.
Qed.

End Abstract.
