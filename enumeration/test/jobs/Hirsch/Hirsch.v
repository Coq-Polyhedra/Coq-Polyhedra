From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import lrel affine polyhedron poly_base.
From PolyhedraHirsch Require Import extra_int high_graph enum_proof enum_algo enum_equiv enum_high_algo diameter.
From __VALIDATION__ Require Import bounded_Po_test_r img_lex_graph_r format_r enum_algo_r.
Require Import diameter_check_r dim_full_test_r.
From __DATA__ Require Import Po.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope polyh_scope.

Local Notation m' := (Com.m Po).-1.
Local Notation n' := (Com.n Po).-1.
Local Notation A := (spec_poly m' n' Po).1.
Local Notation b := (spec_poly m' n' Po).2.


Theorem Hirsch_was_wrong: exists (d : nat) (P : 'poly[rat]_d),
  ((diameter (poly_graph P)) > #|`facets P| - ((\pdim P).-1))%nat.
Proof.
pose P := poly_of_syst (A,b).
exists n'.+1, P.
apply/disprove_Hirsch.
- exact: poly_format_ok. 
- exact: lex_graph_format_ok.
- exact: vert_graph_format_ok. 
- exact: bound_pos_format_ok.
- exact: bound_neg_format_ok. 
- exact: enum_algo_ok.
- exact: img_lex_graph_ok. 
- exact: bounded_Po_test_ok.
- exact: graph_n0_ok. 
- exact: inv_format_ok.
- exact: dim_full_test_ok. 
- exact: diameter_check_ok.
Qed.
