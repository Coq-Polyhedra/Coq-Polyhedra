From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update_lazy.
From __DATA__ Require Import A b bases pred root init heap dim morph vtx_eq.

Time Eval vm_compute in (R1.lazy_rank_1_update A b bases pred root init heap dim morph vtx_eq).
