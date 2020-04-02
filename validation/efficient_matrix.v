From mathcomp Require Import ssreflect ssrfun ssrbool seq ssrnat eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

Open Scope bigQ_scope.

Section Line.

Definition line := seq bigQ.

Definition addl (x y : line) :=
  map (fun p => p.1 + p.2) (zip x y).

Definition subl (x y : line) :=
  map (fun p => p.1 - p.2) (zip x y).

Definition scalel a0 x :=
  map (fun a => a0 * a) x.

Definition dotl x y :=
  foldl (fun res p => res + p.1 * p.2) 0 (zip x y).

Definition zerol n :=
  iter n (fun l => 0 :: l) [::].

Definition deltal n i :=
  iteri n (fun j l =>
             let a := if (j == i)%N then 1 else 0 in
             a :: l) [::].

End Line.

Section Matrix.

Definition matrix := seq line.

Definition addm (m m' : matrix) : matrix :=
  map (fun p => addl p.1 p.2) (zip m m').

Definition mulmtr (m m' : matrix) : matrix := (* compute m * m'^T *)
  map (fun l => map (dotl l) m') m.

Definition scalem (a : bigQ) (m : matrix) :=
  map (scalel a) m.

Definition col_cons (l : line) (m : matrix) :=
  map (fun p => p.1 :: p.2) (zip l m).

Definition trm (m : matrix) :=
  let m0 := map (fun _ => [::]) m in
  foldr col_cons m0 m.

Definition identity n :=
  iteri n (fun i l => (deltal n i) :: l) [::].

Definition ex := [:: [:: 1; 2; 3]; [:: 10; 5; 6]; [:: 7; 8; 9]].

(*
Eval compute in (trm ex).
Eval compute in (scalem 3 (addm ex (trm ex))).
Eval compute in (mulmtr ex ex).
*)

End Matrix.

Section Gauss.

Definition scale_extract a0 l0 (m : matrix) :=
  map (fun l => match l with
             | [ :: ] => [ :: ] (* cannot happen,
                                * since l and a0 :: l0 have the same length *)
             | b :: l' =>
               if b ?= 0 is Eq then l'
               else subl (scalel (a0 / b) l') l0
             end) m.

Fixpoint find_pivot acc (m : matrix) :=
  match m with
  | [ :: ] => None
  | l :: m' =>
    match l with
    | [ :: ] => None
    | a :: l' =>
      if a ?= 0 is Eq then
        find_pivot (l' :: acc) m'
      else
        Some (a, l', m', acc)
    end
  end.

Fixpoint is_invertible (m : matrix) n :=
  match n with
  | 0 => Some m
  | n'.+1 =>
    match find_pivot [::] m with
    | None => None
    | Some (a, l, m', acc) =>
      let mb := scale_extract a l m' in
      (is_invertible (catrev acc mb) n')
    end
  end.

Time Eval vm_compute in (is_invertible ex 3).

End Gauss.

(*
Fixpoint add_lines (A:Line) (B:Line) :=
  match A,B with
  | nil, nil => nil
  | nil, C => C
  | C, nil => C
  | cons a A0, cons b B0 => (a+b) :: (add_lines A0 B0)
  end.

Fixpoint add_all_lines (M:Matrix) :=
  match M with
  |nil => nil
  |L :: M0 => add_lines (L) (add_all_lines M0)
  end.

Fixpoint scale_line (a: bigQ) (A : Line) :=
  match A with
  |nil => nil
  |cons a0 A0 => a*a0 :: (scale_line a A0)
  end.

Fixpoint scale_matrix (a:bigQ) (M:Matrix) :=
  match M with
  |nil => nil
  |L :: M0 => (scale_line a L) :: (scale_matrix a M0)
  end.

Fixpoint scalar_product (A: seq bigQ) (B: seq bigQ) :=
  match A , B with
  |nil, _ => 0
  |_, nil => 0
  |cons a A0, cons b B0 => a*b + (scalar_product A0 B0)
end.


Fixpoint line_times_matrix (L:Line) (M:Matrix) :=
  match L,M with
  |nil, _ => nil
  |_ , nil => nil
  |cons a L0, cons L1 M0 => add_lines (scale_line a L1) (line_times_matrix L0 M0)
  end.

Fixpoint matrix_times_matrix (M:Matrix) (N:Matrix) :=
  match M with
  |nil => nil
  |cons L M0 => (line_times_matrix L N) :: (matrix_times_matrix M0 N)
  end.

(*Now we have basic tools on matrix, we can define data structures on polyhedrons.
There will be Polyhedron, understood as a set like {x | Ax \leq b}
And Basis, the set of the inequalities activated by a face, understood as {x | Ax = b} *)

Definition Equation := prod Line bigQ.
Definition System := seq Equation.
Inductive Face := Fa : System -> Face.
Inductive Polyhedron := Po : System -> Polyhedron.


Fixpoint isIn_system (x:Point) (S:System):= match S with
  | nil  => true
  | E :: S0 => match E with
    |pair L v  =>  match (scalar_product x L) ?= v with
      |Gt => false
      |_ => isIn_system x S0
       end
     end
  end.

Definition isIn (x:Line) (P : Polyhedron) := match P with
  |Po S' => isIn_system x S'
  end.


Fixpoint Point_to_Face_system (x:Point) (S:System) := match S with
  |nil => Fa nil
  |(pair L v)::S0=> match (scalar_product x L) ?= v with
    |Eq => match Point_to_Face_system x S0 with
      |Fa S1 => Fa ((pair L v)::S1)
      end
    |_ => Point_to_Face_system x S0
    end
  end.

Definition Point_to_Face (x:Line) (P : Polyhedron) := match P with
  |Po S' => Point_to_Face_system x S'
  end.

Fixpoint System_to_Matrix (S:System) :Matrix := match S with
  |nil => nil
  |(pair L v)::S0 => L :: (System_to_Matrix S0)
  end.

Fixpoint Matrix_to_System (A:Matrix) (b:Line) :System := match A,b with
  |nil,_ => nil
  |_, nil => nil
  |(L::A0), (v::b0) => (pair L v)::(Matrix_to_System A0 b0)
  end.

(*We compute here the Gauss Elimination*)

Fixpoint remove_column (S:System) :System:=
  match S with
  |nil => nil
  |(pair nil v)::S0 => (pair nil v)::(remove_column S0)
  |(pair (a::L) v)::S0 => (pair L v)::(remove_column S0)
  end.

Fixpoint finding_pivot (S:System):System:=
    match S with
    |nil => S
    |(pair L v)::S0=> match L with
      |nil => finding_pivot S0
      |a :: L0 => match a ?= BigQ.zero with
        |Eq => rcons (finding_pivot S0) (pair L v)
        |_ => (pair (scale_line (BigQ.inv a) L) ((BigQ.inv a) * v) ) :: S0
      end
    end
  end.


Fixpoint elimination (E:Equation) (S:System) :System:= match E with
  |pair L v => match S with
    |nil => nil
    |(pair L0 v0)::S0 => match L0 with
      |nil => elimination E S0
      |a :: L1 => match a ?= BigQ.zero with
        |Eq => (pair L0 v0)::(elimination E S0)
        |_ => (pair (add_lines L (scale_line (- BigQ.inv a) L0)) ((v0*(- BigQ.inv a) + v)))::(elimination E S0)
        end
      end
    end
  end.


Fixpoint add_column (S:System) :System:= match S with
  |nil => nil
  |(pair L v) :: S0 => (pair (0 :: L) v) :: (add_column S0)
  end.

Check add_column.

Definition Gauss (S'':System) :System:= let fix aux (S':System) (n:nat) :=
  match n with
  |O => nil
  |S(p) => match finding_pivot S' with
    |nil => nil
    |E :: S0=> match elimination E S0 with
      |S1 => E :: (add_column (aux (remove_column S1) p))
      end
    end
  end in
  aux S'' (length S'').


Definition Example : System := [::  ([:: 2; 1; 1], 1);
                              ([:: 1; 0; 1],2);
                              ([:: 1; 1; 0],3)].

Compute Gauss Example.


(*Now we have the reduced form, we will work on it to obtain what we want*)

Definition rank (A:Matrix) : nat := let fix aux (S':System) (n:nat): nat:= match n with
  |O => O
  |S(p) => match S' with
      |nil => O
      |(pair L v)::S0 => match L with
        |a::L0 => if BigQ.eq_bool BigQ.zero a
          then aux (remove_column S0) p
          else S (aux (remove_column S0) p)
        |_ => aux S0 p
        end
      end
  end
  in let S'' := (Gauss (Matrix_to_System A (nseq (length A) 0))) in  aux S''  (length S'').

Compute rank (System_to_Matrix Example).

Definition System_to_Point (S'':System) : Point:=
  let fix aux (S':System)  (n:nat):= match n with
    |O => nil
    |S(p) => match S' with
      |nil => nil
      |(pair L v)::S0 => let P := aux (remove_column S0) p in (BigQ.red (v - (scalar_product (0::P) L)))::P
      end
    end
  in aux (Gauss S'') (length S'').


Definition isVertex (x:Line) (P:Polyhedron) := match P with
  |Po (L::A0) b => match Point_to_ActiveFace x P with
      |AF A1 b1 => match Nat.compare (rank (AF A1 b1)) (length L) with
        |Eq => true
        |_ => false
        end
    end
  |Po _ _ => false
  end.

Definition Cube : Matrix := [:: [:: 1; 0; 0];
                                [:: -1; 0; 0];
                                [:: 0; 1; 0];
                                [:: 0; -1; 0];
                                [:: 0; 0; 1];
                                [:: 0; 0; -1]].
Definition PCube := Po Cube [:: 1; 0; 1; 0; 1; 0].
Definition PointEx := [:: 1; 1;1].

Compute isIn PointEx PCube.
Compute Point_to_ActiveFace PointEx PCube.
Compute isVertex PointEx PCube.

(*We assume that for this function, the rank of the matrix is n, ie it's a vertex*)



Definition AC := Point_to_ActiveFace PointEx PCube.
Compute ActiveFace_to_Point AC.

(*We compute here the notion of neighbourhood of a vertex.
Hence, we assume the ActiveFace here is a vertex*)

Definition Neighbours (Active:ActiveFace) (P:Polyhedron) :=
  let fix aux (Atop:Matrix) (Abot: Matrix) (btop:Line) (bbot:Line) (PA:Matrix) (Pb:Line) (n:nat) :=
    match Abot,bbot with
    |nil, _ => nil
    |_, nil => nil
    |(L::A0),(v::b0) => let fix aux2 (PA':Matrix) (Pb':Line) := match PA', Pb' with
      |nil, _ => nil
      |_, nil => nil
      |(L':: PA0'),(v'::Pb0') => if rank (AF ((rcons Atop L')++A0) ((rcons btop v')++b0)) == n
        then (AF ((rcons Atop L')++A0) ((rcons btop v')++b0))::(aux2 PA0' Pb0')
        else (aux2 PA0' Pb0')
      end
    in (aux2 PA Pb)++(aux (rcons Atop L) A0 (rcons btop v) b0 PA Pb n)
    end in match Active, P with
    |(AF A b),(Po PA Pb) => aux nil A nil b PA Pb (rank (AF A b))
    end.

Compute AC.
Compute Neighbours AC PCube.

Definition NeighboursPoint (x:Line) (P:Polyhedron) :=
  List.map ActiveFace_to_Point (Neighbours (Point_to_ActiveFace x P) P).

Fixpoint EqPoint (x :Line) (y : Line) :=
  match x, y with
    |nil, nil => true
    |_, nil => false
    |nil, _ => false
    |a::x0, b::y0 => match a ?= b with
      |Eq => EqPoint x0 y0
      |_ => false
      end
    end.

Definition PointIn (x:Line) (v : seq Line) := List.existsb (EqPoint x) v.

Definition VerificationVertex (P:Polyhedron) (v: seq Line) :=
  let fix aux (vtop:seq Line) (vbot:seq Line) := match vbot with
    |nil => true
    |x::v0 => if isVertex x P
      then if List.forallb (fun y => PointIn y (vtop++vbot)) (NeighboursPoint x P)
        then aux (rcons vtop x) v0
        else false
      else false
    end in aux nil v.

Compute VerificationVertex PCube  [:: [::1;1;1]; [::0;1;1]; [::1;0;1];[::1;1;0];
                                      [::1;0;0]; [::0;1;0]; [::0;0;1];[::0;0;0]
                                  ].
*)
