From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo. 
From __DATA__ Require Import Po G_lex lbl_lex G_vtx lbl_vtx bound_pos bound_neg.

Lemma poly_format_ok : poly_format Po.
Proof. by rewrite -poly_formatE; vm_cast_no_check (erefl true). Qed.

Lemma lex_graph_format_ok : lex_graph_format Po G_lex lbl_lex.
Proof. by rewrite -lex_graph_formatE; vm_cast_no_check (erefl true). Qed.

Lemma vert_graph_format_ok : vert_graph_format Po G_vtx lbl_vtx.
Proof. by rewrite -vert_graph_formatE; vm_cast_no_check (erefl true). Qed.

Lemma bound_pos_format_ok : bound_format Po bound_pos.
Proof. by rewrite -bound_formatE; vm_cast_no_check (erefl true). Qed.

Lemma bound_neg_format_ok : bound_format Po bound_neg.
Proof. by rewrite -bound_formatE; vm_cast_no_check (erefl true). Qed.

Lemma graph_n0_ok : lex_graph_n0 G_lex.
Proof. by rewrite -lex_graph_n0E; vm_cast_no_check (erefl true). Qed.