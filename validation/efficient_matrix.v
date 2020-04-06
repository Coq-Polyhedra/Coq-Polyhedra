From Bignums Require Import BigQ BigN.
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
(*Require Import bases_list.*)

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bigQ_scope.

Section Row.

Definition row := seq bigQ.

Definition addr (x y : row) :=
  map (prod_curry BigQ.add_norm) (zip x y).

Definition subr (x y : row) :=
  map (prod_curry BigQ.sub_norm) (zip x y).

Definition scaler a0 x :=
  map (BigQ.mul_norm a0) x.

Definition dotr x y :=
  foldl (fun res p => BigQ.add_norm res (BigQ.mul_norm p.1 p.2)) 0 (zip x y).

Definition zeror n := nseq n 0.

Definition deltar n i :=
  mkseq (fun j => if (j == i)%N then 1 else 0) n.

End Row.

Section Matrix.

Definition matrix := seq row.

Definition addm (m m' : matrix) : matrix :=
  map (prod_curry addr) (zip m m').

Definition subm (m m' : matrix) : matrix :=
  map (prod_curry subr) (zip m m').

Definition mulmtr (m m' : matrix) : matrix := (* compute m * m'^T *)
  map (fun l => map (dotr l) m') m.

Definition scalem (a : bigQ) (m : matrix) :=
  map (scaler a) m.

Definition col_cons (l : row) (m : matrix) :=
  map (prod_curry cons) (zip l m).

Definition row_size (m : matrix) :=
  size m.

Definition col_size (m : matrix) :=
  size (head [::] m).

Definition trm (m : matrix) :=
  let m0 := nseq (col_size m) [::] in
  foldr col_cons m0 m.

Definition identity n :=
  mkseq (deltar n) n.

Definition col_block (m1 m2 : matrix) :=
  map (prod_curry cat) (zip m1 m2).

Definition col_vector (l : row) := trm [:: l].

Definition mapm (f : BigQ.t -> BigQ.t) (m : matrix) : matrix :=
  map (map f) m.

End Matrix.

Section Gauss.

Definition scale_extract x0 l0 (m : matrix) :=
  map (fun l => match l with
             | [::] => [::] (* cannot happen,
                                * since l and x0 :: l0 have the same length *)
             | x :: l' =>
               subr (scaler x0 l') (scaler x l0) (* can be simplied *)
             end) m.

Fixpoint find_pivot (top m : matrix) :=
  match m with
  | [::] => None
  | l :: bot =>
    match l with
    | [::] => None
    | x :: l' =>
      if x ?= 0 is Eq then
        find_pivot (l' :: top) bot
      else
        Some (x, l', bot, top)
    end
  end.

Fixpoint row_echelon (res m : matrix) n :=
  match n with
  | 0 => Some res
  | n'.+1 =>
    match find_pivot [::] m with
    | None => None
    | Some (x0, l0, bot, top) =>
      let bot' := scale_extract x0 l0 bot in
      (row_echelon ((x0 :: l0) :: res) (catrev top bot') n')
    end
  end.

Fixpoint back_substitution (res : row) (m : matrix) (b : row) :=
  match m, b with
  | [::], _ => res
  | _, [::] => res
  | l :: m', y :: b' =>
    match l with
    | [::] => [::]
    | x :: l' =>
      let z := BigQ.div_norm (BigQ.sub_norm y (dotr res l')) x in
      back_substitution (z :: res) m' b'
    end
  end.

Definition solvem (m : matrix) (b : row) : option row :=
  let mext := col_block m (col_vector b) in
  match row_echelon [::] mext (row_size m) with
  | None => None
  | Some mext =>
    let fix split_last (l : row) :=
        match l with
        | [::] => ([::], 0)
        | [:: x] => ([::], x)
        | x :: l' =>
          let p := split_last l' in
          (x :: p.1, p.2)
        end
    in
    let (mext', b') :=
        foldr
          (fun l acc => let: (l', x) := split_last l in
                     (l' :: acc.1, x :: acc.2))
           ([::], [::]) mext
    in
    Some (back_substitution [::] mext' b')
  end.

(* TODO: implement the inverse computation (in cubic time) *)
Definition invm (m : matrix) : option matrix :=
  let nb_row := row_size m in
  let mext := col_block m (identity nb_row) in
  match row_echelon [::] mext nb_row with
  | None => None
  | Some mext =>
    let fix split_last i (l : row) :=
        match i with
        | 0 => ([::], l)
        | i'.+1 =>
          match l with
          | [::] => ([::], [::]) (* cannot happen because i > 0 *)
          | x :: l' =>
            let p := split_last i' l' in
            (x :: p.1, p.2)
          end
        end
    in
    let: (_, (mext1, mext2)) :=
        foldr (fun l p =>
                 let: (i, res) := p in
                 let: (l1, l2) := split_last i l in
                 (i.-1, (l1 :: res.1, l2 :: res.2))) (nb_row, ([::], [::])) mext in
    Some (trm (map (back_substitution [::] mext1) (trm mext2)))
  end.

End Gauss.

(*Section Test.

Let ex0 := [:: [:: 1; 2; 3]; [:: 10; 5; 6]; [:: 7; 8; 9]].
Let pt0 := [:: 1; 4; 20].
Let sol0 := odflt [::] (solvem ex0 pt0).
Time Eval vm_compute in (subm (mapm BigQ.red (mulmtr ex0 [:: sol0])) (col_vector pt0)).
Let inv0 := odflt [::] (invm ex0).
Time Eval vm_compute in (mulmtr ex0 (trm inv0)).

Let sol1 : row := [:: 338062210884181229/33806221088630922900;-196000/1239561439916467173;-56000/338062210886309229;1189000000/1239561439916467173;3713440000/3718684319749401519;-44903800/3718684319749401519;-71504098/6197807199582335865;35301640/112687403628769743;-4438000/1239561439916467173;-16982000/3718684319749401519;-5530000/1239561439916467173;-1918000/413187146638822391;-22316000/3718684319749401519;0;0;0;0;0;0;0].

Time Eval vm_compute in (mapm BigQ.red (subm (mulmtr A [:: sol1]) (col_vector b))).
Let A' : matrix := map (nth [::] A) (11 :: (iota 21 19))%N.
Let b' : row := map (nth 0 b) (11 :: (iota 21 19))%N.
Time Eval vm_compute in (subr (solvem A' b') sol1).

End Test.
*)

Section CheckPoint.

Definition check_point (A : matrix) (b : row) (I : seq nat) :=
(* calcule le point de base associé à I, et vérifie qu'il satisfait toutes les inégalités *)
  let A' := map (fun i => nth [::] A (i-1)%N) I in
  let b' := map (fun i => (nth 0 b) (i-1)%N) I in
  match solvem A' b' with
  | None => false
  | Some x' =>
    let r := trm (mulmtr A [:: x']) in
    if r is [:: r0] then
      all (fun x => if x ?= 0 is Lt then false else true) (subr r0 b)
    else false
  end.

(*
Time Eval vm_compute in
    all (check_point A b) (take 10%N bases_list0).
*)
End CheckPoint.

Section Neighbour.

Definition neighbour (I J: seq nat) :bool :=
  ((count (fun p => ~~(p.1 == p.2)) (zip I J)) == 1%N).

End Neighbour.
