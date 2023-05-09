From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po G_lex G_simpl lbl_lex lbl_simpl morf morf_inv edge_inv.

Lemma img_lex_graph_ok : img_lex_graph morf morf_inv edge_inv G_lex lbl_lex G_simpl lbl_simpl.
Proof.
by rewrite -img_lex_graphE; __COMPIL__ (erefl true).
Qed.
