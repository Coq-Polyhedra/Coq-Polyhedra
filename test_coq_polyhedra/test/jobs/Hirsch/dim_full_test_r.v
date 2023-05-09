From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po map_lbl inv_lbl lbl_simpl origin.

Lemma inv_format_ok : inv_format Po inv_lbl.
Proof.
by rewrite -inv_formatE; __COMPIL__ (erefl true).
Qed.

Lemma dim_full_test_ok : dim_full_test lbl_simpl map_lbl origin inv_lbl Po.
Proof.
by rewrite -dim_full_testE; __COMPIL__ (erefl true).
Qed.
