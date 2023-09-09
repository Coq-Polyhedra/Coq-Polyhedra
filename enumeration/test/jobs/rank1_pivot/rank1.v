From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update_pivot.
From __DATA__ Require Import A b bases idx inv order pred x_I steps det.

Definition det := R1.get_num det.
Time Compute R1.vertex_certif A b bases pred idx x_I inv det order steps.