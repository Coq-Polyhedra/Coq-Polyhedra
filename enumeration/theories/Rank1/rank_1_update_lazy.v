Require Import String.
Require Import PArray Uint63.
From Bignums Require Import BigQ.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement enum_algo.
(* From ReductionEffect Require Import PrintingEffect. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* ---------------------------------------------------------------------------- *)

Local Notation int63 := Uint63.int.
Local Definition matrix := array (array bigQ).
Local Definition vector := array bigQ.
Local Definition basis := array int63.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

(* Definition print_debug {A : Type} (s : string) (a : A):= let x := print s in print_id a. *)

(* Definition cmp_vect (u : array bigQ) (v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq. *)

(* if ((M.[Ik].[l] - M'.[Ik].[l]) * Mrs ?= M.[Is].[l] * M.[Ik].[r])%bigQ is Eq then true else false) *)

Definition memory_update (memory : array (array (array (option bigQ))))
  (k i j :int63) (v : bigQ) : (array (array (array (option bigQ)))):=
  let col := memory.[k].[j].[i <- Some v] in
  let M := memory.[k].[j <- col] in
  memory.[k <- M].

Fixpoint eval
  (fuel : nat)
  (certif_bases : array basis)
  certif_pred
  (certif_updates : array bigQ)
  (kJ : int63) (i j : int63)
  (memory : array (array (array (option bigQ))))
  (current : int63):=
  if fuel is n.+1 then
    if memory.[kJ].[j].[i] is Some value then (Some value,memory,current) else
    let J := certif_bases.[kJ] in
    let '(kI, rs) := certif_pred.[kJ] in let '(r,s) := rs in let I := certif_bases.[kI] in
    let '(Mrs,memory,current) := eval n certif_bases certif_pred certif_updates kI r (I.[s]+1)%uint63 memory current in
    if Mrs is Some mrs then
      if (mrs ?= 0)%bigQ is Eq then (None, memory, current)
      else
        if (j =? r+1)%uint63 then
          let '(Mis,memory,current) := eval n certif_bases certif_pred certif_updates kI i (I.[s]+1)%uint63 memory current in
          if Mis is Some mis then
            let m'ir := certif_updates.[current] (*(-mis / mrs)%bigQ *) in
            if (mrs * m'ir ?= -mis)%bigQ is Eq then
              (Some m'ir, memory_update memory kJ i j m'ir, Uint63.succ current)
            else (None, memory, current)
          else (None, memory, current)
        else
          let '(Mij,memory,current) := eval n certif_bases certif_pred certif_updates kI i j memory current in
          if Mij is Some mij then
            let '(Mis,memory,current) := eval n certif_bases certif_pred certif_updates kI i (I.[s]+1)%uint63 memory current in
            if Mis is Some mis then
              let '(Mrj,memory,current) := eval n certif_bases certif_pred certif_updates kI r j memory current in
              if Mrj is Some mrj then
                let m'ij := certif_updates.[current] (*(mij - mis * mrj / mrs)%bigQ*) in
                if (((mij - m'ij) * mrs ?= mis * mrj)%bigQ) is Eq then
                  (Some m'ij, memory_update memory kJ i j m'ij, Uint63.succ current)
                else (None, memory, current)
              else (None, memory, current)
            else (None, memory, current)
          else (None, memory, current)
    else (None, memory, current)
  else (None, memory, current).

Definition lazy_sat_pert
  (certif_bases : array basis)
  certif_pred certif_updates (root_base : int63)
  (k : int63) (sat_vect : array comparison)
  memory current:=
  let I := certif_bases.[root_base] in
  let '(_,res,memory,current) := IFold.ifold
    (fun i '(j, acc, memory, current)=>
       if (I.[j] =? i)%uint63 then
         ((j+1)%uint63, acc, memory, current) (* no-op when i is a line in the basis *)
       else
         if acc.[i] is Eq then
           let '(value, memory, current) := eval Uint63.size certif_bases certif_pred certif_updates root_base i (I.[k]+1)%uint63 memory current in
           if value is Some v then
             (j, acc.[i <- (v ?= 0)%bigQ],memory,current)
           else
             (j, acc.[i <- Lt],memory,current) (* HACK here, to be fixed *)
         else
           (j, acc, memory,current) (* no-op since we only need to break inequality ties *)
    ) (length sat_vect) (0%uint63, sat_vect, memory, current)
  in
  (res,memory,current).

Definition lazy_check_basis (m : int63)
  (certif_bases : array basis)
  (certif_pred : array (int63 * (int63 * int63)))
  certif_updates
  (root_base : int63)
  memory current:=
  let I := certif_bases.[root_base] in
  let '(I0, (r, s)) := certif_pred.[root_base] in
  let '(Mrs, memory, current) :=
    eval Uint63.size certif_bases certif_pred certif_updates I0 r ((certif_bases.[I0]).[s]+1)%uint63 memory current in
  if Mrs is Some Mrs then
    if (Mrs ?= 0)%bigQ is Eq then (Some false, memory, current)
    else
      let '(_, sat_vect, memory, current) :=
        IFold.ifold
          (fun i '(j, acc, memory, current) =>
             if (I.[j] =? i)%uint63 then
               ((j+1)%uint63, acc, memory, current)
             else
               let '(Mi0, memory, current) := eval Uint63.size certif_bases certif_pred certif_updates root_base i 0%uint63 memory current in
               if Mi0 is Some mi0 then
                 (j, acc.[i <- (mi0 ?= 0)%bigQ], memory, current)
               else (j, acc.[i <- Lt], memory, current)) m (0%uint63, make m Eq, memory, current)
      in
      let '(_, sat_lex, memory,current) :=
        IFold.ifold
          (fun i '(j, acc, memory,current) =>
             if (I.[j] =? i)%uint63 then
               let '(acc,memory,current) :=
                 lazy_sat_pert certif_bases certif_pred certif_updates root_base j acc memory current
               in
               ((j+1)%uint63, acc, memory, current)
             else
               (j, acc.[i <- Gt], memory, current)) m (0%uint63, sat_vect, memory, current)
      in
      let '(_, res) :=
        IFold.ifold
          (fun i '(j, res) =>
             if res then
               if (i =? I.[j])%uint63 then ((j+1)%uint63, res)
               else
                 if sat_lex.[i] is Gt then (j, res)
                 else (j, false)
             else
               (j, false)) (length sat_lex) (0%uint63, true)
      in
      (Some res, memory, current)
  else
      (None, memory, current).

Definition build_initial_memory
  (certif_bases : array basis) (init : matrix) m N root :=
  let mem := PArrayUtils.mk_fun (fun _ => PArrayUtils.mk_fun (fun _ => make m None) (m+1)%uint63 (make m None)) N (make (m+1)%uint63 (make m None)) in
  let mem := IFold.ifold
              (fun i mem => memory_update mem root i 0 init.[0].[i])
              m mem in
  let I := certif_bases.[root] in
  IFold.ifold (fun i mem =>
                 IFold.ifold
                   (fun j mem =>
                      memory_update mem root i (I.[j]+1)%uint63 init.[I.[j]+1].[i])
                   (length I) mem)
    m mem.

Definition lazy_check_all_bases
  (A : matrix) (b : vector)
  (certif_bases : array basis)
  (certif_pred : array (int63 * (int63 * int63)))
  (root : int63) init certif_updates :=
  let memory := build_initial_memory certif_bases init (length A) (length certif_bases) root in
  IFold.ifold
    (fun i '(acc, memory, current) =>
       if (i =? root)%uint63 then (acc, memory, current)
       else
         match acc with
         | None => (acc, memory, current)
         | Some false => (acc, memory, current)
         | _ => lazy_check_basis (length A) certif_bases certif_pred certif_updates i memory current
         end) (length certif_bases) (Some true, memory, 0%uint63).

Definition full_dimensional (certif_dim : array int63) (memory : array (array (array (option bigQ)))):=
  IFold.iall (fun i=>
    let kI := certif_dim.[i] in
    if memory.[kI].[0].[i] is Some val then
      if (val ?= 0)%bigQ is Gt then true else false
    else false
  ) (length certif_dim).

Definition label_img 
  (morph : array int63) (certif_bases : array basis) (certif_img : array (array int63))
  (memory : array (array (array (option bigQ)))):=
  IFold.iall (fun i=>
    let j := morph.[i] in
    let indices := certif_img.[j] in
    let base := certif_bases.[i] in
    (IFold.ifold (fun k_idx '(k_bas,acc)=>
      if ~~ acc then (k_bas,acc) else
      let index := indices.[k_idx] in
      if (k_bas <? length base)%uint63 && (base.[k_bas] =? index)%uint63 then 
        (Uint63.succ k_bas, acc)
          (*vertex index = line index => don't have to be verified*)
      else 
        let Val := memory.[i].[0].[index] in
        if Val is Some val then
          if (val ?= 0)%bigQ is Eq then (k_bas, acc) else (k_bas, false)
          (*vertex index not in basis, the check has been done in memory*)
        else (k_bas, false)
    ) (length indices) (0%uint63,true)).2
  ) (length morph).

Definition lazy_rank_1_update A b certif_bases certif_pred root init certif_updates certif_dim morph certif_img:=
  let '(val, memory, _):= lazy_check_all_bases A b certif_bases certif_pred root init certif_updates in
  (val, full_dimensional certif_dim memory, label_img morph certif_bases certif_img memory).


End Rank1Certif.

Module R1 := Rank1Certif.

(* ---------------------------------------------------------------------------- *)

Module CertifPredVerif.

Definition adjacent (I J : array int63) (r s : int63):=
  (IFold.ifold (fun i '(kI,kJ,c)=>
    if c then
      if (kI <? length I)%uint63 then
        if (kJ <? length J)%uint63 then
          if (I.[kI] =? J.[kJ])%uint63 then
            ((Uint63.succ kI),(Uint63.succ kJ),c)
          else
            if (kI =? s)%uint63 then
              ((Uint63.succ kI), kJ, c)
            else
              if (J.[kJ] =? r)%uint63 then
                (kI, (Uint63.succ kJ), c)
              else (kI, kJ, false)
        else
          if (kI =? s)%uint63 then
            ((Uint63.succ kI), kJ, c)
          else (kI, kJ, false)
      else
        if (kJ <? length J)%uint63 then
          if (J.[kJ] =? r)%uint63 then
            (kI, (Uint63.succ kJ), c)
          else (kI,kJ,false)
        else (kI,kJ,true)
    else (kI,kJ,c))
  (length I + length J)%uint63 (0%uint63,0%uint63,true)).2.

Definition certif_pred_correct certif_bases certif_pred :=
  IFold.iall (fun i =>
    let J := certif_bases.[i] in
    let '(root, rs) := certif_pred.[i] in
    let '(r,s) := rs in
    let I := certif_bases.[root] in
    adjacent I J r s) (length certif_bases).

End CertifPredVerif.

Module CPV := CertifPredVerif.

(* ---------------------------------------------------------------------------- *)

(* Module OtherCertifications.

Definition bounded A b certif_bound_pos certif_bound_neg:=
  PBC.bounded_Po_test (A,b) certif_bound_pos certif_bound_neg.

Definition regularity (A : array (array bigQ)) graph_lex :=
  let n := length A.[0] in
  Com.compute_test graph_lex (fun i => (GraphUtils.nb_neighbours graph_lex i =? n)%uint63).

Definition adjacency (A : array (array bigQ)) graph_lex bases :=
  let n' := Uint63.pred (length A.[0]) in
  Com.compute_test graph_lex (fun i=> 
    GraphUtils.neighbour_all (fun j =>
      let c := (AIC.array_inter (fun i j => (i <? j)%uint63) bases.[i] bases.[j]) in
      (c =? n')%uint63
    ) graph_lex i).

Definition img_graph morph morph_inv edge_inv graph_lex graph_vtx :=
  IGC.img_graph morph morph_inv edge_inv graph_lex graph_vtx.

End OtherCertifications.

Module OC := OtherCertifications. *)
