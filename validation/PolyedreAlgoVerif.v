From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

Open Scope bigQ_scope.



Fixpoint scalar_product (A: seq bigQ) (B: seq bigQ) :=
  match A , B with
  |nil, _ => 0
  |_, nil => 0
  |cons a A0, cons b B0 => a*b + (scalar_product A0 B0)
end.

Definition Line := seq bigQ.
Definition Matrix := seq (Line).

(*We assume that there is no size issues.
If it happens, i.e there is a nil vs a cons, we assume a value of 0*)


Fixpoint add_lines (A:Line) (B:Line) :=
  match A,B with
  |nil, nil => nil
  |nil, C => C
  |C, nil => C
  |cons a A0, cons b B0 => (a+b) :: (add_lines A0 B0)
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
And ActiveFace, the set of the inequalities activated by a face, understood as {x | Ax = b} *)

Record Polyhedron :=
  Po { A : Matrix ; b : Line }.

Record ActiveFace := AF {A' : Matrix; b' : Line}.

Fixpoint isIn_matrix (x:Line) (A:Matrix) (b: Line):=
  match A,b with
  | nil, _ => true
  | _, nil => true
  | (L :: A0), (v :: b0) => match (scalar_product x L) ?= v with
    |Gt => false
    |_ => isIn_matrix x A0 b0
    end
  end.

Definition isIn (x:Line) (P : Polyhedron) := match P with
  |Po A b => isIn_matrix x A b
  end.


Fixpoint Point_to_ActiveFace_matrix (x:Line) (A:Matrix) (b:Line) := match A,b with
  |nil, _ => (AF nil nil)
  |_, nil => (AF nil nil)
  |L :: A0, v :: b0 => match (scalar_product x L) ?= v with
    |Eq => match Point_to_ActiveFace_matrix x A0 b0 with
      |AF A1 b1 => AF (L::A1) (v::b1)
      end
    |_ => Point_to_ActiveFace_matrix x A0 b0
    end
  end.

Definition Point_to_ActiveFace (x:Line) (P : Polyhedron) := match P with
  |Po A b => Point_to_ActiveFace_matrix x A b
  end.

(*We need now the notion of matrix rank in order to compute the verification that a face is a vertex*)

(*We compute here the Gauss Elimination*)

Fixpoint remove_column (M:Matrix) :=
  match M with
  |nil => nil
  |L :: M0 => match L with
    |nil => nil :: (remove_column M0)
    |a :: L0 => L0 :: (remove_column M0)
    end
  end.

Print seq.

Fixpoint finding_pivot_aux (A : Matrix) (b: Line) :=
    match A, b with
    |nil, _ => AF nil nil
    |_, nil => AF nil nil
    |L :: A0, v::b0 => match L with
      |nil => finding_pivot_aux A0 b0
      |a :: L0 => match a ?= BigQ.zero with
        |Eq => match finding_pivot_aux A0 b0 with
          |AF A' b' => AF (rcons A' L) (rcons b' v)
          end
        |_ => AF ((scale_line (BigQ.inv a) L) :: A0) (((BigQ.inv a)*v) :: b0)
      end
    end
  end.

Definition finding_pivot (Active : ActiveFace) := match Active with
  |AF A b => finding_pivot_aux A b
  end.

Fixpoint elimination_aux (L:Line) (v:bigQ) (A:Matrix) (b : Line):=
  match A,b with
  |nil, _ => AF nil nil
  |_, nil => AF nil nil
  |L0 :: A0, v0 :: b0 => match L0 with
    |nil => elimination_aux L v A0 b0 
    |a :: L1 => match elimination_aux L v A0 b0 with
      |AF A1 b1 => match a ?= BigQ.zero with
        |Eq => AF (L0::A1) (v0::b1)
        |_ => AF ((add_lines L (scale_line (- BigQ.inv a) L0)) :: A1) ((v0*(- BigQ.inv a) + v):: b1)
        end
      end
    end
  end.

Definition elimination (L:Line) (v:bigQ) (Active:ActiveFace) := match Active with
  |AF A b => elimination_aux L v A b
  end.


Fixpoint add_column (M:Matrix) := match M with
  |nil => nil
  |L :: M0 => (0 :: L) :: (add_column M0)
  end.


Fixpoint Gauss_aux (Active: ActiveFace) (n:nat) := match n with
  |0 => AF nil nil
  |S(p) => match finding_pivot Active with
    |AF A b => match A,b with
      |nil, _ => AF nil nil
      |_, nil => AF nil nil
      |L :: A0, v :: b0 => match elimination L v (AF A0 b0) with
        |AF A1 b1 => match Gauss_aux (AF (remove_column A1) b1) p with
          |AF A2 b2 => AF (L :: (add_column A2)) (v :: b2)
          end
        end
      end
    end  
  end.

Definition Example : Matrix := [::  [:: 2; 1; 1];
                              [:: 1; 0; 1];
                              [:: 0; 0; 1]].

Definition Ac := AF Example [:: 1;2;3;4].

Compute Gauss_aux Ac 5.

Definition Gauss (Active : ActiveFace) := match Active with
  |AF A b => match A with
    |nil => AF nil nil
    |L :: A0 => Gauss_aux Active (length L)
    end
  end.

(*Now we have the reduced form, we will work on it to obtain what we want*)

Print List.forallb.
Print BigQ.eq_bool.



Definition rank (Active: ActiveFace) : nat := let fix aux (A:Matrix) (b:Line) : nat:= 
    match A,b with
      |nil, _ => Nat.zero
      |_, nil => Nat.zero
      |(L::A0), (v::b0) => match L with
        |a::L0 => if BigQ.eq_bool BigQ.zero a
          then aux (remove_column A0) b0
          else S (aux (remove_column A0) b0)
        |_ => aux A0 b0
        end
      end
  in match (Gauss Active) with
    |AF A b => aux A b
    end.

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

Definition ActiveFace_to_Point (Active : ActiveFace) :=
  let fix aux (A:Matrix) (b:Line) := match A,b with
    |nil, _ => nil
    |_, nil => nil
    |(L :: A0),(v::b0) => let P := aux (remove_column A0) b0 in (v - (scalar_product (0::P) L))::P
    end
  in match Gauss Active with
  |AF A b => aux A b
  end.

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







