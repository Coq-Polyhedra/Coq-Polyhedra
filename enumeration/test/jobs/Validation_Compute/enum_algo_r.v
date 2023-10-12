From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po G_lex lbl_lex. 

Lemma enum_algo_ok : enum_algo Po G_lex lbl_lex.
Proof.
by rewrite -enum_algoE; exact_no_check (erefl true).
Qed.
