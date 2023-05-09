From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo diameter enum_high_algo.
From Coq Require Import NArith.BinNat NArith.BinNatDef Uint63.
From __DATA__ Require Import Po G_simpl.

Lemma diameter_exact_ok : diameter_exact G_simpl Po __VALUE__%uint63.
Proof.
rewrite -diameter_exactE; vm_cast_no_check (erefl true).
Qed.
