From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

Open Scope bigQ_scope.

Section Row.

Definition row := seq bigQ.

Definition addr (x y : row) :=
  map (prod_curry BigQ.add) (zip x y).

Definition subr (x y : row) :=
  map (prod_curry BigQ.sub) (zip x y).

Definition scaler a0 x :=
  map (fun a => a0 * a) x.

Definition dotr x y :=
  foldl (fun res p => res + p.1 * p.2) 0 (zip x y).

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
Let pt := [:: 1; 4; 20].
Let sol0 := solvem ex0 pt.
Time Eval vm_compute in (subm (mapm BigQ.red (mulmtr ex0 [:: sol0])) (col_vector pt)).

End Test.
