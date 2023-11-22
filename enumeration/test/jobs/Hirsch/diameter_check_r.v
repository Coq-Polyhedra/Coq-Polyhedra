From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po G_vtx start.

Lemma diameter_check_ok : diameter_check G_vtx Po start.
Proof.
by rewrite -diameter_checkE; vm_cast_no_check (erefl true).
Qed.
