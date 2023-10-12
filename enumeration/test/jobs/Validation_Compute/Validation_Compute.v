From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_high_algo enum_algo.
Require Import enum_algo_r img_lex_graph_r format_r.
Require Import bounded_Po_test_r.

Definition validation :=
  Validation poly_format_ok lex_graph_format_ok
    vert_graph_format_ok bound_pos_format_ok
    bound_neg_format_ok enum_algo_ok
    img_lex_graph_ok bounded_Po_test_ok
    graph_n0_ok.

Check validation.
