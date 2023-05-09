From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po G_simpl start.

Lemma diameter_check_ok : diameter_check G_simpl Po start.
Proof.
by rewrite -diameter_checkE; __COMPIL__ (erefl true).
Qed.
