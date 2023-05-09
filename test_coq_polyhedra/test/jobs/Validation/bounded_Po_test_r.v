From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo. 
From __DATA__ Require Import Po cert_pos cert_neg.

Lemma bounded_Po_test_ok : @bounded_Po_test Po cert_pos cert_neg.
Proof.
by rewrite -bounded_Po_testE; __COMPIL__ (erefl true).
Qed.
