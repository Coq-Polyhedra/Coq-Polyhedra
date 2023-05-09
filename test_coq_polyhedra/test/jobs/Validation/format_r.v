From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo. 
From __DATA__ Require Import Po G_lex lbl_lex G_simpl lbl_simpl cert_pos cert_neg.

Lemma poly_format_ok : poly_format Po.
Proof. by rewrite -poly_formatE; __COMPIL__ (erefl true). Qed.

Lemma lex_graph_format_ok : lex_graph_format Po G_lex lbl_lex.
Proof. by rewrite -lex_graph_formatE; __COMPIL__ (erefl true). Qed.

Lemma vert_graph_format_ok : vert_graph_format Po G_simpl lbl_simpl.
Proof. by rewrite -vert_graph_formatE; __COMPIL__ (erefl true). Qed.

Lemma cert_pos_format_ok : bound_format Po cert_pos.
Proof. by rewrite -bound_formatE; __COMPIL__ (erefl true). Qed.

Lemma cert_neg_format_ok : bound_format Po cert_neg.
Proof. by rewrite -bound_formatE; __COMPIL__ (erefl true). Qed.

Lemma graph_n0_ok : lex_graph_n0 G_lex.
Proof. by rewrite -lex_graph_n0E; __COMPIL__ (erefl true). Qed.