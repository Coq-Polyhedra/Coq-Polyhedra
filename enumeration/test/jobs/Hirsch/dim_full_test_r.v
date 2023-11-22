From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po map_dim inv_dim lbl_vtx origin.

Lemma inv_format_ok : inv_format Po inv_dim.
Proof.
by rewrite -inv_formatE; vm_cast_no_check (erefl true).
Qed.

Lemma dim_full_test_ok : dim_full_test lbl_vtx map_dim origin inv_dim Po.
Proof.
by rewrite -dim_full_testE; vm_cast_no_check (erefl true).
Qed.
