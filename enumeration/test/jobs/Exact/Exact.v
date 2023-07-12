From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo diameter enum_high_algo enum_equiv enum_proof extra_int.
From Coq Require Import NArith.BinNat NArith.BinNatDef.
From __VALIDATION__ Require Import bounded_Po_test_r img_lex_graph_r format_r enum_algo_r.
From __DATA__ Require Import Po G_vtx.
Require Import diameter_exact_r.

Local Notation m' := (Com.m Po).-1.
Local Notation n' := (Com.n Po).-1.
Local Notation A := (spec_poly m' n' Po).1.
Local Notation b := (spec_poly m' n' Po).2.
Local Notation __NAME__ := (poly_of_syst (A, b)).

Lemma __NAME___diameter:  
    diameter (poly_graph __NAME__) = __VALUE__%nat.
Proof.
apply/diameter_of___NAME__.
- exact/poly_format_ok.
- exact/lex_graph_format_ok.
- exact/vert_graph_format_ok.
- exact/bound_pos_format_ok.
- exact/bound_neg_format_ok.
- exact/enum_algo_ok.
- exact/img_lex_graph_ok.
- exact/bounded_Po_test_ok.
- exact/graph_n0_ok.
- exact/diameter_exact_ok.
Qed.

Check __NAME___diameter.
