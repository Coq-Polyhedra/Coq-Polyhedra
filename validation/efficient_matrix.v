From Bignums Require Import BigQ BigN.
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
(*Require Import bases_list.*)
Require Import BinNums BinPos.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bigQ_scope.

Section Misc.

Definition zip2 {T1 T2 T3 : Type} (s1 : seq T1) (s2 : seq T2) (s3 : seq T3)
  := zip (zip s1 s2) s3.

Definition argmax {T: Type} (s: seq T) (p: T -> bool) (f: T -> bigQ) :=
  let fix argmax_aux s' max arg := match s' with
    |[::] => arg
    |h::t => if p h then
      match max with
      |None => argmax_aux t (Some (f h)) [:: h]
      |Some fmax => match fmax ?= (f h) with
        |Eq => argmax_aux t (Some fmax) (h::arg)
        |Lt => argmax_aux t (Some (f h)) [::h]
        |Gt => argmax_aux t (Some fmax) arg
        end
      end else argmax_aux t max arg
    end in argmax_aux s None [::].

Definition seq_equal (s1 s2 : seq (positive * positive)) := true.

End Misc.

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

(* Implement the transpose of the inverse matrix (in cubic time) *)
Definition invtrm (m : matrix) : option matrix :=
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
    Some (map (back_substitution [::] mext1) (trm mext2))
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

Section Bases.

Definition basis := seq positive.
(*Implements a sorted list of indexes associated to bases. We assume that manipulating them do not
change their size, as all bases of a polyhedron have the same size*)

Definition switch_elt (I:basis) (i:positive) (j:positive) := (*Compute I - i + j*)
  let fix switch I' i' oj' :=
    match I' with
      |[::] => if oj' is Some j' then [:: j'] else [::]
      |h::t => match (h ?= i')%positive with
        |Eq => switch t i' oj'
        |_ => match oj' with
          |None => h :: (switch t i oj')
          |Some j' =>
            match (h ?= j')%positive with
              |Eq => h:: switch t i' None
              |Lt => h:: switch t i' (Some j')
              |Gt => j:: (h :: switch t i' None)
            end
          end
        end
      end in switch I i (Some j).

Definition compl (I: basis) (m:nat):=
  let candidates := map (fun x => pos_of_nat x x) (iota 0 m) in
  let fix elimi I' C res := match I' with
    |[::] => catrev res C
    |i::I0 => match C with
      |[::] => rev res (*A priori, it should never happens*)
      |c::C' => match Pos.compare c i with
        |Lt => elimi I' C' (c::res)
        |Eq => elimi I0 C' res
        |Gt => rev res (*Same, it should never happens*)
        end
      end
    end in elimi I candidates [::].

(*Definition neighbour_search (I: seq positive) (m : nat) :=
  (*return a list of neighbours, with the form (i,j, (I - i + j) )*)
  let J :=  compl I m in
  let fix neigh acc I' res := match I' with
    |[::] => res
    |i::I'' => neigh (i::acc) I'' ((i, (map (add_elt (catrev acc I'')) J))::res)
  end in neigh [::] I [::].*)

(*
Compute neighbour_search [::1;2;3]%positive 5%nat.
Compute compl [::1;2;3]%positive 5%nat.
 *)

Definition subseq {T : Type} (s : seq T) (I : basis)  :=
  let fix subseq_aux s I (i0 : positive) :=
      match s with
      | [::] => [::]
      | x :: s' =>
        match I with
        | [::] => [::]
        | i :: I' =>
          match (i0 ?= i)%positive with
          | Lt => subseq_aux s' (i :: I') (i0+1)%positive
          | Eq => x :: (subseq_aux s' I' (i0+1)%positive)
          | Gt => [::]
          end
        end
      end
  in
  subseq_aux s I 1%positive.

End Bases.

Section Neighbour.

Variable (m n : nat).

Definition check_basis (A : matrix) (b : row) (I_s : basis * seq (positive * positive) ) :=
  let: (I0, s) := I_s in
  let AI := subseq A I0 in
  let bI := subseq b I0 in
  match invtrm AI with
  | None => false
  | Some A' =>
    let x :=
        foldl (fun res p => addr res (scaler p.2 p.1)) (zeror n) (zip A' bI)
    in
    let I' := compl I0 m in
    let AI' := subseq A I' in
    let bI' := subseq b I' in
    let r := map (fun p => BigQ.sub_norm (dotr p.1 x) (p.2)) (zip AI' bI') in
    if has (fun z => (if z ?= 0 is Lt then true else false)) r then
      false
    else
      let search_i res i_A' :=
          let: (i, A'_i) := i_A' in
          let c_i := map (dotr A'_i) AI' in
          let prd := fun x => if x.1.2 ?= 0 is Lt then true else false in
          let fct := fun x => BigQ.div_norm x.2 x.1.2 in
          let arg := map (fun x => x.1.1) (argmax (zip2 I' c_i r) prd fct) in
          foldl (fun res p => let: (j, c_ij, r_j) := p in
                if c_ij ?= 0 is Eq then
                  res
                else (* cij != 0 *)
                  (*let J := switch_elt I0 i j in*)
                  if r_j ?= 0 is Eq then
                    (i,j) :: res
                  else (* r_j > 0 *)
                    if has (fun k => if Pos.compare j k is Eq then true else false) arg then (* to be improved *)
                      (i,j) :: res
                    else
                      res) res (zip2 I' c_i r)
      in
      let res := foldl search_i [::] (zip I0 A') in
      seq_equal res s
  end.

End Neighbour.

(* TODO : test d'appartenance dans une base (simplification de check_point_and_neighbour) *)
(* TODO : au lieu des AVL, on prend en entrée un graphe d'adjacence calculé informellement. Son type est seq (basis * (seq basis)). Pour chaque élément (I, s), on vérifie que I est bien une base admissible, et que s est précisément la liste des bases adjacentes à I. Remarque : on peut prétrier s de manière à ce que l'ordre des bases adjacentes soit précisément celui de la visite.
   TODO : modifier le script python, trier la liste dans le bon sens
*)

(* TODO : Shermann-Morrisson *)
