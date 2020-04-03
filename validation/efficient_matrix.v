From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

Open Scope bigQ_scope.

Section Row.

Definition row := seq bigQ.

Definition addr (x y : row) :=
  map (prod_curry (fun a b => BigQ.red (BigQ.add a b))) (zip x y).

Definition subr (x y : row) :=
  map (prod_curry (fun a b => BigQ.red (BigQ.sub a b))) (zip x y).

Definition scaler a0 x :=
  map (BigQ.red \o (BigQ.mul a0)) x.

Definition dotr x y :=
  foldl (fun res p => BigQ.red (res + p.1 * p.2)) 0 (zip x y).

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
      back_substitution ((BigQ.red ((b - dotr res l') / x)) :: res) m'
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

Let ex1 : matrix := [::
[:: 1;100;0;0;21;-7;0;0;0;0;0;0;0;0;0;0;1;1;0;0;0];
[:: 1;100;0;0;16;-15;0;0;0;0;0;0;0;0;0;0;0;1;1;0;0];
[:: 1;100;0;0;0;-32;0;0;0;0;0;0;0;0;0;0;0;0;1;1;0];
[:: 1;100;0;0;-16;-15;0;0;0;0;0;0;0;0;0;0;0;0;0;1;1];
[:: 1;100;0;0;-21;-7;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;100;0;0;-20;-4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1];
[:: 1;100;0;0;0;32;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;100;0;0;20;-4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;100;3/100;-1/50;0;-30;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;100;-3/100;-1/50;0;30;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;100;-3/2000;7/2000;0;318/10;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;100000000000;100000000000;100000000000;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;-10000000;0;0;0;0;0;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;-10000000;0;0;0;0;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;-10000000;0;0;0;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;-10000000000;0;0;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;-100000000000;0;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;-100000000000;0;0;1;0;0;0;0;0;0];
[:: 1;100;3/2000;7/2000;0;-318/10;10000000;10000000;10000000;10000000000;100000000000;100000000000;-100000000000;0;1;0;0;0;0;0;0];
[:: 1;100;3#2000;7#2000;0;-318#10;10000000;10000000;10000000;10000000000;100000000000;100000000000;100000000000;-100000000000;1;0;0;0;0;0;0];
[:: 1;-100;30;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;4;-15;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;0;-33#2;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0;0];
[:: 1;-100;-1;-16;0;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0;0];
[:: 1;-100;-55#2;0;0;0;0;0;0;0;0;0;1;1;0;0;0;0;0;0;0];
[:: 1;-100;-17;18;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0];
[:: 1;-100;0;38;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;22;17;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;-10;0;1#5;-1#5;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;2999#100;0;-3#25;-1#5;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;299999#10000;0;0;1#100;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;-2745#100;0;1#5000;1#800;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;100000000;1000000000];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;-100000;0;0;0;0;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;-10000000;0;0;0;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;-10000000;0;0;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;-10000000;0;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;-100000000;0;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;-100000000;0];
[:: 1;-100;-27;0;1#500;-1#80;0;0;0;0;0;0;0;0;100000;10000000;10000000;10000000;100000000;100000000;-1000000000]].

Let pt1 : row := nseq 21%N 0.
Let sol1 : row := [:: 100;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Let sol2 : row := [:: 2303556749929373143925300;23035567499029657431253;457470000000;-347465800000;59561500000000;145851504000000;-1486524480000;-55314024346000;-17528770600000;-36326830200000;-4164304600000;-33709467600000;-2901898800000;1655348000000;0;0;0;0;0;0;0].
Let sol3 : row := [:: 371868431974940151900;3718684319725993519;-29400000;-30800000;356700000000;371344000000;-4490380000;-4290245880;116495412000;-1331400000;-1698200000;-1659000000;-1726200000;-2231600000;0;0;0;0;0;0;0].

Time Eval vm_compute in (mulmtr ex1 [:: sol1]).
Time Eval vm_compute in (mulmtr ex1 [:: sol2]).
Time Eval vm_compute in (mulmtr ex1 [:: sol3]).

Let ex2 := [::
             [:: 1;2;0;0];
          [:: 1;0;3;0];
          [:: 1;0;0;6];
          [:: 1;-10;0;0];
          [:: 1;0;0;-12];
          [:: 1;0;-5;0]].

Let sol20 := [:: 30;3;6;-5].
Time Eval vm_compute in (mulmtr ex2 [:: sol20]).


End Test.
