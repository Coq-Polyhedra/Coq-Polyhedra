From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

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
  | 0 => res
  | n'.+1 =>
    match find_pivot [::] m with
    | None => [::]
    | Some (x0, l0, bot, top) =>
      let bot' := scale_extract x0 l0 bot in
      (row_echelon ((x0 :: l0) :: res) (catrev top bot') n')
    end
  end.

Fixpoint back_substitution (res : row) (m : matrix) :=
  match m with
  | [::] => res
  | l :: m' =>
    match l with
    | [::] => [::]
    | x :: l' =>
      let b := last x l' in
      let y := BigQ.div_norm (BigQ.sub_norm b (dotr res l')) x in
      back_substitution (y :: res) m'
    end
  end.

Definition solvem (m : matrix) (b : row) : row :=
  let mext := col_block m (col_vector b) in
  let mre := row_echelon [::] mext (row_size m) in
  back_substitution [::] mre.

End Gauss.

Section Test.

Let ex0 := [:: [:: 1; 2; 3]; [:: 10; 5; 6]; [:: 7; 8; 9]].
Let pt0 := [:: 1; 4; 20].
Let sol0 := solvem ex0 pt0.
Time Eval vm_compute in (subm (mapm BigQ.red (mulmtr ex0 [:: sol0])) (col_vector pt0)).

Let A : matrix := [::
[::100;0;0;21;-7;0;0;0;0;0;0;0;0;0;0;1;1;0;0;0];
[::100;0;0;16;-15;0;0;0;0;0;0;0;0;0;0;0;1;1;0;0];
[::100;0;0;0;-32;0;0;0;0;0;0;0;0;0;0;0;0;1;1;0];
[::100;0;0;-16;-15;0;0;0;0;0;0;0;0;0;0;0;0;0;1;1];
[::100;0;0;-21;-7;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::100;0;0;-20;-4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1];
[::100;0;0;0;32;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::100;0;0;20;-4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::100;3/100;-1/50;0;-30;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::100;-3/100;-1/50;0;30;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::100;-3/2000;7/2000;0;318/10;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;100000000000;100000000000;100000000000;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;-10000000;0;0;0;0;0;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;-10000000;0;0;0;0;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;-10000000;0;0;0;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;-10000000000;0;0;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;-100000000000;0;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;-100000000000;0;0;1;0;0;0;0;0;0];
[::100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;100000000000;-100000000000;0;1;0;0;0;0;0;0];
[::100;3#2000;7#2000;0;-318#10;10000000;10000000;10000000;10000000000;100000000000;100000000000;100000000000;-100000000000;1;0;0;0;0;0;0];
[::-100;30;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0;0;0];
[::-100;4;-15;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0;0];
[::-100;0;-33#2;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0];
[::-100;-1;-16;0;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0];
[::-100;-55#2;0;0;0;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0];
[::-100;-17;18;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0];
[::-100;0;38;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;22;17;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;-10;0;1#5;-1#5;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;2999#100;0;-3#25;-1#5;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;299999#10000;0;0;1#100;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;-2745#100;0;1#5000;1#800;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;100000000;1000000000];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;-100000;0;0;0;0;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;-10000000;0;0;0;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;-10000000;0;0;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;-10000000;0;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;-100000000;0;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;-100000000;0];
[::-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;100000000;-1000000000]].
Let b := nseq 40%N (-1).

Let sol1 : row := [:: 338062210884181229/33806221088630922900;-196000/1239561439916467173;-56000/338062210886309229;1189000000/1239561439916467173;3713440000/3718684319749401519;-44903800/3718684319749401519;-71504098/6197807199582335865;35301640/112687403628769743;-4438000/1239561439916467173;-16982000/3718684319749401519;-5530000/1239561439916467173;-1918000/413187146638822391;-22316000/3718684319749401519;0;0;0;0;0;0;0].

Time Eval vm_compute in (mapm BigQ.red (subm (mulmtr A [:: sol1]) (col_vector b))).
Let A' : matrix := map (nth [::] A) (11 :: (iota 21 19))%N.
Let b' : row := map (nth 0 b) (11 :: (iota 21 19))%N.
Time Eval vm_compute in (subr (solvem A' b') sol1).


End Test.

Section CheckPoint.


Definition check_point (I : seq nat) (A : matrix) (b: row):=
(* calcule le point de base associé à I, et vérifie qu'il satisfait toutes les inégalités *)
let A' := map (nth [::] A) I in
let b' := map (nth 0 b) I in
let x' := [:: solvem A' b'] in
let r := trm (mulmtr A x') in
if r is [:: r0] then
  all (fun x => if x ?= 0 is Lt then false else true) (subr r0 b)
  else false.


End CheckPoint.
