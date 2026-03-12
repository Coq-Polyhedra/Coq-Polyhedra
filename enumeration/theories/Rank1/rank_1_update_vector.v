Require Import PArray Uint63.
From Bignums Require Import BigQ.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement enum_algo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* ---------------------------------------------------------------------------- *)

Local Notation int63 := Uint63.int.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

(* ------------------------------------------------------------------ *)
Definition sat_pert (Ax : (array bigQ)) (m : int63) (cmp : array comparison):=
  IFold.ifold (fun i cmp=>
    if cmp.[i] is Eq then
      if (i =? m)%uint63 then cmp.[i <- (Ax.[i] ?= -1)%bigQ] else cmp.[i <- (Ax.[i] ?= 0)%bigQ]
    else cmp
  ) (length cmp) cmp.

Definition cmp_vect (u : array bigQ) (v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq.

(*sat_lex Ax b I verifies that AX >=lex b and (AX)_I == b_I*)

Definition sat_cmp (Ax : array bigQ) (b : array bigQ)
  (M : array (array bigQ)):=
  IFold.ifold (fun i cmp=>
    sat_pert M.[i] i cmp) (length M) 
  (cmp_vect Ax b).
  
Definition sat_lex (A : array (array bigQ)) (b : array bigQ)
  (I : array int63) (x : array bigQ) (M : array (array bigQ)):=
  let Ax := BigQUtils.bigQ_mul_mx_col A x in
  let cmp := sat_cmp Ax b M in
  (IFold.ifold (fun i '(test,k)=>
    if test then
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k)
    else (test,k)
    ) (length cmp) (true, 0%uint63)).1.

(* ------------------------------------------------------------------ *)

Definition update
  (A : array (array bigQ))
  (I : array Uint63.int) (r s : Uint63.int)
  (M : array (array bigQ)) (u v: array bigQ): 
  (array (array bigQ)) :=
  let M' := PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M) in
  let Au := BigQUtils.bigQ_mul_mx_col A u in
  let Is := I.[s] in
  let Ms := M.[Is] in
  let Mrs := Ms.[r] in
  let M' := IFold.ifold (fun k M' =>
    if (k =? s)%uint63 then M' else
    let Ik := I.[k] in
    let M'Ik := make (length M.[Ik]) (default M.[Ik]) in
    let M'Ik := IFold.ifold (fun l c =>
      c.[l <- (M.[Ik].[l] + v.[k] * Au.[l])%bigQ]) (length M.[Ik]) M'Ik in M'.[Ik <- M'Ik]) 
    (length I) M' in
  let M'r := IFold.ifold (fun l c=>
    c.[l <- (M.[Is].[l] + v.[s] * Au.[l])%bigQ]
    ) (length M.[Is]) (make (length M.[Is]) 0%bigQ)
  in
  let M' := M'.[r <- M'r] in M'.


Definition explore
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_vtx : array (array bigQ))
  (certif_pred : array (int63 * (int63 * int63)))
  (certif_pred_vect : array (array bigQ * array bigQ))
  main (order : array int63) (steps : int63):=
  IFold.ifold
    (fun i main=>
       let (idx,rs) := certif_pred.[order.[i]] in
       let (r,s) := rs in
       let '(u, v) := certif_pred_vect.[order.[i]] in
       let I := certif_bases.[idx] in
       if main.[idx] is Some M then
         let M' := update A I r s M u v in
         if sat_lex A b certif_bases.[order.[i]] certif_vtx.[order.[i]] M' 
         then main.[order.[i] <- Some M'] else main
       else main) steps main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (inv : array (array bigQ)) :=
  let I := certif_bases.[idx] in
  let M := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (length A) (make (length A) 0%bigQ) in
  IFold.ifold (fun i M=> M.[I.[i] <- 
        BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])]) (length I) M.
(*
(x, B, M, q).
*)
Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_vtx : array (array bigQ))
  (idx : int63) (inv : array (array bigQ)):
  array (option (array (array bigQ))) :=
  let main := make (length certif_bases) None in
  let M := initial A b certif_bases idx inv in
  if sat_lex A b certif_bases.[idx] certif_vtx.[idx] M then 
  main.[idx <- Some M] else main.
(*
  let '(x, B, M, q) := initial A b certif_bases idx x inv q in
  if sat_lex M q b (certif_bases.[idx]) then main.[idx <- Some (x, B, M, q)] else main.
*)

Definition explore_from_initial
  A b certif_bases certif_vtx certif_pred certif_pred_vect idx inv order steps:=
  explore A b certif_bases certif_vtx certif_pred certif_pred_vect (initial_main A b certif_bases certif_vtx idx inv) order steps.

Definition vertex_certif A b certif_bases certif_vtx 
  certif_pred certif_pred_vect idx inv order steps:=
  let main := explore_from_initial A b certif_bases certif_vtx certif_pred certif_pred_vect idx inv order steps in
  IFold.ifold (fun i res => res && isSome main.[order.[i]]) steps true.


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
    let '(idx, rs) := certif_pred.[i] in
    let '(r,s) := rs in
    let I := certif_bases.[idx] in
    adjacent I J r s) (length certif_bases).

End CertifPredVerif.
