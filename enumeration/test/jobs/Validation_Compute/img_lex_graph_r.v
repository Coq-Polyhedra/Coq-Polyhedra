From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo.
From __DATA__ Require Import Po G_lex G_vtx lbl_lex lbl_vtx morph morph_inv edge_inv.

Lemma img_lex_graph_ok : img_lex_graph morph morph_inv edge_inv G_lex lbl_lex G_vtx lbl_vtx.
Proof.
by rewrite -img_lex_graphE; exact_no_check (erefl true).
Qed.
