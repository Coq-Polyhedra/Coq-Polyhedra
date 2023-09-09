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

Definition sat_cmp (Ax : array (array bigQ)) (b : array bigQ) :=
  IFold.ifoldx (fun i cmp=>
    sat_pert Ax.[i] (Uint63.pred i) cmp
  ) 1%uint63 (length Ax) (cmp_vect Ax.[0] b).

Definition sat_lex (Ax : array (array bigZ)) (q : bigZ) (b : array bigQ) (I : array int63):=
  let Ax :=
    PArrayUtils.map (PArrayUtils.map (fun x => (BigQ.Qz x / BigQ.Qz q)%bigQ)) Ax
  in
  let cmp := sat_cmp Ax b in
  (IFold.ifold (fun i '(test,k)=>
    if test then
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k)
    else (test,k)
    ) (length cmp) (true, 0%uint63)).1.

(*sat_lex Ax b I verifies that AX >=lex b and (AX)_I == b_I*)

Definition sat_vtx (A : array (array bigQ)) (b : array bigQ) (x : array bigQ) (I : array int63) :=
    let Ax := BigQUtils.bigQ_mul_mx_col A x in
    let cmp := cmp_vect Ax b in
    (IFold.ifold (fun i '(test,k)=>
    if test then
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k)
    else (test,k)
    ) (length cmp) (true, 0%uint63)).1.

Definition all_sat_vtx A b certif_bases certif_vtx :=
  IFold.iall (fun i=> let I := certif_bases.[i] in let x := certif_vtx.[i] in
    sat_vtx A b x I) (length certif_bases).

(* ------------------------------------------------------------------ *)

Definition divQZ (x : bigQ) (q : bigZ) :=
  match x with
  | BigQ.Qz x =>
      let '(y, r) := BigZ.div_eucl x q in
      if (r =? 0)%bigZ then
        BigQ.Qz y
      else
        BigQ.Qq ((BigZ.sgn q) * x)%bigZ (BigZ.to_N q)
  | BigQ.Qq x d =>
      let '(y, r) := BigZ.div_eucl x q in
      if (r =? 0)%bigZ then
        BigQ.Qq y d
      else
        BigQ.Qq ((BigZ.sgn q) * x)%bigZ (d * BigZ.to_N q)%bigN
  end.

Definition get_num (x : bigQ) :=
  match x with
  | BigQ.Qz x => x
  | BigQ.Qq x _ => x
  end.

Definition update
  (b : array bigZ)
  (I : array Uint63.int) (r s : Uint63.int)
  (M : array (array bigZ)) (q : bigZ) :
  array (array bigZ) * bigZ * seq (bigZ * bigZ * bigZ * bigZ * bigZ) :=
  let M' := PArrayUtils.mk_fun (fun _ => make 1%uint63 0%bigZ) (length M) (default M) in
  (*
  (x : array bigQ) (B M : array (array bigQ)) (q : bigZ) :=
  let M' := PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M) in
  let B' := PArrayUtils.mk_fun (fun _ => make (length B.[0]) 0%bigQ) (length B) (default B) in
   *)
  let Is := I.[s] in
  (*let Bs := B.[Is] in*)
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let M0r := M.[0].[r] in
  (*let x' := PArrayUtils.mk_fun (fun k=> divQZ (x.[k] * Mrs + (M0r - (BigQ.Qz q) * b.[r]) * Bs.[k]) q) (length x) (default x) in*)
  let M'0 :=
    PArrayUtils.mk_fun
      (fun k => BigZ.div (M.[0].[k] * Mrs + (q * b.[r] - M0r) * Ms.[k])%bigZ q)
      (length M.[0]) (default M.[0]) in
  let M' := M'.[0 <- M'0] in
  let '(M', nums) := IFold.ifold (fun k '(M', nums) =>
    if (k =? s)%uint63 then (M', nums) else
    let Ik := I.[k] in
    let '(M'Ik, nums')  :=
      IFold.ifold (fun l '(MIk, nums) =>
                     let Mlk := M.[Uint63.succ Ik].[l] in
                     let Mls := M.[Uint63.succ Is].[l] in
                     let Mrk := M.[Uint63.succ Ik].[r] in
                     let z := (M.[Uint63.succ Ik].[l] * Mrs - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r])%bigZ in
                     (MIk.[l <- BigZ.div z q], (*(Mlk, Mrs, Mls, Mrk, q)::*)nums)) (length M.[Uint63.succ Ik]) (make (length M.[Uint63.succ Ik]) 0%bigZ, nums)
    in
      (*PArrayUtils.mk_fun
        (fun l => divQZ  q)
        (length M.[Uint63.succ Ik]) 0%bigQ in*)
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    (M', nums')) (length I) (M', [::]) in
  let M'r := PArrayUtils.mk_fun (fun l => (-Ms.[l])%bigZ) (length Ms) 0%bigZ in
  let M' := M'.[Uint63.succ r <- M'r] in
  (M', Mrs, nums).
(*
let '(B', M') := IFold.ifold (fun k '(B',M')=>
    if (k =? s)%uint63 then (B',M') else
    let Ik := I.[k] in
    let M'Ik :=
      PArrayUtils.mk_fun
        (fun l => divQZ (M.[Uint63.succ Ik].[l] * Mrs - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r])%bigQ q)
        (length M.[Uint63.succ Ik]) 0%bigQ in
    let B'Ik :=
      PArrayUtils.mk_fun
        (fun l => divQZ (B.[Ik].[l] * Mrs - Bs.[l] * M.[Uint63.succ Ik].[r])%bigQ q)
        (length B.[Ik]) 0%bigQ in
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    let B' := B'.[Ik <- B'Ik] in
    (B',M')) (length I) (B',M') in
  let M'r := PArrayUtils.mk_fun (fun l => (-Ms.[l])%bigQ) (length Ms) 0%bigQ in
  let B'r := PArrayUtils.mk_fun (fun l => (-Bs.[l])%bigQ) (length Bs) 0%bigQ in
  let M' := M'.[Uint63.succ r <- M'r] in
  let B' := B'.[r <- B'r] in
  (x', B', M', get_num Mrs).
 *)

Definition explore
  (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option ((array (array bigZ)) * bigZ * seq (bigZ * bigZ * bigZ * bigZ * bigZ))))
  (order : array int63) (steps : int63):=
  let b_int := PArrayUtils.map get_num b in
  IFold.ifold
    (fun i main=>
       let (idx,rs) := certif_pred.[order.[i]] in
       let (r,s) := rs in
       let I := certif_bases.[idx] in
       if main.[idx] is Some (M, q, _) then
        let Is := I.[s] in
        let Ms := M.[Uint63.succ Is] in
        let Mrs := Ms.[r] in
        if (Mrs ?= 0)%bigZ is Eq then main else
        let '(M', q', nums') := update b_int I r s M q in
        if sat_lex M' q' b certif_bases.[order.[i]] then main.[order.[i] <- Some (M', q', nums')] else main
        else main) steps main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) (q : bigZ) :=
  let I := certif_bases.[idx] in
  let B := PArrayUtils.mk_fun (fun _ => make (length inv.[0]) 0%bigQ) (length A) (make (length inv.[0]) 0%bigQ) in
  let M := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let M := M.[0 <- BigQUtils.bigQ_mul_mx_col A x] in
  let '(B,M) :=
    IFold.ifold (fun i '(B,M)=>
      let M := M.[Uint63.succ I.[i] <- BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])] in
      let B := B.[I.[i] <- copy inv.[i]] in
    (B,M)) (length I) (B,M)
  in
  (PArrayUtils.map (PArrayUtils.map get_num) M, q).
(*
(x, B, M, q).
*)
Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) q :
  array (option ((array (array bigZ)) * bigZ * seq (bigZ * bigZ * bigZ * bigZ * bigZ))) :=
  let main := make (length certif_bases) None in
  let '(M, q) := initial A b certif_bases idx x inv q in
  if sat_lex M q b (certif_bases.[idx]) then main.[idx <- Some (M, q, [::])] else main.
(*
  let '(x, B, M, q) := initial A b certif_bases idx x inv q in
  if sat_lex M q b (certif_bases.[idx]) then main.[idx <- Some (x, B, M, q)] else main.
*)

Definition explore_from_initial
  A b certif_bases certif_pred idx x inv q order steps:=
  explore b certif_bases certif_pred (initial_main A b certif_bases idx x inv q) order steps.

Definition vertex_certif
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) q
  (order : array int63) steps:=
  let main := explore_from_initial A b certif_bases certif_pred idx x inv q order steps in
  IFold.ifold (fun i res => res && isSome main.[order.[i]]) steps true.

Definition num_profile
  (main : array (option ((array (array bigZ)) * bigZ * seq (bigZ * bigZ * bigZ * bigZ * bigZ)))) (order : array int63) steps :=
  IFold.ifold (fun i res =>
                 match main.[order.[i]] with
                 | Some (_, _, s) =>
                     foldl (fun _ '(a, b, c, d, e) =>
                              let ab := (a * b)%bigZ in
                              let cd := (c * d)%bigZ in
                              (ab, cd, ab - cd)%bigZ) (0, 0, 0)%bigZ s
                 | None => res
                 end) steps (0, 0, 0)%bigZ.

(*
Definition update
  (b : array bigQ)
  (I : array Uint63.int) (r s : Uint63.int)
  (x : array bigQ) (B M : array (array bigQ)):=
  let '(B',M') :=
    (PArrayUtils.mk_fun (fun _ => make (length B.[0]) 0%bigQ) (length B) (default B),
     PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M)) in
  let Is := I.[s] in
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let Bs := B.[Is] in
  let M0r := M.[0].[r] in
  let x' := PArrayUtils.mk_fun
             (fun k => BigQ.red (x.[k] + ((M0r - b.[r])/Mrs) * Bs.[k])%bigQ) (length x) (default x) in
  let M'0 := PArrayUtils.mk_fun (fun k => BigQ.red (M.[0].[k] + ((b.[r] - M0r)/Mrs) * Ms.[k])%bigQ) (length M.[0]) (default M.[0]) in
  let M' := M'.[0 <- M'0] in
  let (B', M') := IFold.ifold (fun k '(B',M')=>
    if (k =? s)%uint63 then (B',M') else
    let Ik := I.[k] in
    let B'Ik := PArrayUtils.mk_fun (fun l => BigQ.red (B.[Ik].[l] - B.[Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ) (length B.[Ik]) 0%bigQ in
    let M'Ik := PArrayUtils.mk_fun (fun l => BigQ.red (M.[Uint63.succ Ik].[l] - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ) (length M.[Uint63.succ Ik]) 0%bigQ in
    let B' := B'.[Ik <- B'Ik] in
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    (B', M')) (length I) (B',M') in
  let B'r := PArrayUtils.mk_fun (fun l => BigQ.red (-Bs.[l] / Mrs)%bigQ) (length Bs) 0%bigQ in
  let M'r := PArrayUtils.mk_fun (fun l => BigQ.red (-Ms.[l] / Mrs)%bigQ) (length Ms) 0%bigQ in
  let B' := B'.[r <- B'r] in
  let M' := M'.[Uint63.succ r <- M'r] in
  (x', B', M').

Definition explore
  (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option (array bigQ * array (array bigQ) * array (array bigQ))))
  (order : array int63) (steps : int63):=
  IFold.ifold
    (fun i main=>
       let (idx,rs) := certif_pred.[order.[i]] in
       let (r,s) := rs in
       let I := certif_bases.[idx] in
       if main.[idx] is Some (x, B, M) then
         let '(x',B',M'):= update b I r s x B M in
         if sat_lex M' b certif_bases.[order.[i]] then main.[order.[i] <- Some(x', B', M')] else main
       else main) steps main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):=
  let I := certif_bases.[idx] in
  let M := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let B := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (length A) (make (length A) 0%bigQ) in
  let M := M.[0 <- BigQUtils.bigQ_mul_mx_col A x] in
  IFold.ifold (fun i '(B,M)=>
    let B := B.[I.[i] <- inv.[i]] in
    let M := M.[Uint63.succ I.[i] <- BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])] in (B,M))
  (length I) (B,M).

Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):=
  let main := make (length certif_bases) None in
  let (B,M) := initial A b certif_bases idx x inv in
  if sat_lex M b (certif_bases.[idx]) then main.[idx <- Some (x,B,M)] else main.

Definition explore_from_initial
  A b certif_bases certif_pred idx x inv order steps:=
  explore b certif_bases certif_pred (initial_main A b certif_bases idx x inv) order steps.


Definition make_basic_point (x : array bigQ) (B : array (array bigQ)):=
  let X := make (Uint63.succ (length B)) (make (length x) 0%bigQ) in
  let X := X.[0 <- copy x] in
  IFold.ifold
    (fun i acc=>
       let Bi := B.[i] in
       let x := PArrayUtils.mk_fun (fun k => BigQ.red (-Bi.[k])%bigQ) (length Bi) 0%bigQ in
       acc.[Uint63.succ i <- x])
    (length B) X.

Definition array_to_test (main : array (option (array bigQ * array (array bigQ) * array (array bigQ))))
  (certif_bases : array (array int63)) (order : array int63) (steps : int63) :=
  let res := make steps None in
  IFold.ifold (fun i acc=>
  if main.[order.[i]] is Some (x, B, _) then
    acc.[i <- Some (certif_bases.[order.[i]], make_basic_point x B)]
  else acc
  ) steps res.

Definition check_basic_point (A : array (array bigQ)) (b : array bigQ) (arr : array (option (array int63 * array (array bigQ)))):=
  let Po := (A,b) in
  PArrayUtils.all (fun x =>
                     if x is Some p then
                       (LCA.sat_Po Po p.2) && (LCA.mask_eq Po p.1 p.2)
                     else
                       false) arr.
*)
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
