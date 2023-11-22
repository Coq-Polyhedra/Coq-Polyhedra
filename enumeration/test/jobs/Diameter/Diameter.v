From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import enum_algo diameter.
From Coq Require Import NArith.BinNat NArith.BinNatDef.
From __DATA__ Require Import G_vtx.

Eval vm_compute in DC.diameter_BFS G_vtx.
