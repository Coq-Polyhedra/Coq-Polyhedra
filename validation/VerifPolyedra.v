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

(*We compute here the Gauss Elimination*)

Fixpoint remove_column (M:Matrix) :=
  match M with
  |nil => nil
  |L :: M0 => match L with
    |nil => nil :: (remove_column M0)
    |a :: L0 => L0 :: (remove_column M0)
    end
  end.

Fixpoint finding_pivot (M:Matrix) :=
  match M with
  |nil => nil
  |L :: M0 => match L with
    |nil => finding_pivot M0
    |a :: L0 => match a ?= BigQ.zero with
      |Eq => match finding_pivot M0 with
        |nil => L :: nil
        |L1 :: M1 => L1 :: L :: M1
        end
      |_ => (scale_line (BigQ.inv a) L) :: M0
      end
    end
  end.



Fixpoint elimination (L:Line) (M:Matrix):=
  match M with
  |nil => nil
  |L0 :: M0 => match L0 with
    |nil => elimination L M0
    |a :: L1 => match a ?= BigQ.zero with
      |Eq => L0 :: (elimination L M0)
      |_ => (add_lines L (scale_line (- (BigQ.inv a)) L0)) :: (elimination L M0)
      end
    end
  end.


Fixpoint rank_n (M:Matrix) (n:nat) {struct n} : nat :=
  match n with
  |0 => 0
  |S(p) => match (finding_pivot M) with
    |nil => 0
    |L :: M0 => match L with
      |nil => 0
      |a :: L0 => match a ?= BigQ.zero with
        |Eq => rank_n (remove_column M) p
        |_ => 1 + (rank_n (remove_column (elimination L M0)) p)
        end
      end
    end
  end.

Definition rank (M:Matrix) : nat := 
  match M with
  |nil => 0
  |L :: M0 => match L with
    |nil => 0
    |_ => rank_n M (min (length M) (length L))
    end
  end.

Definition Example : Matrix := [::  [:: 2; 1; 1];
                              [:: 1; 0; 1];
                              [:: 1#2; 1#2; 0];
                              [:: 1; 1; 0]].

Eval compute in (rank Example).

Record Polyhedron :=
  Po { A : Matrix ; b : Line }.

Print comparison.

Definition PEx := Po Example [:: 1;2;3;4].

Print Polyhedron.

Fixpoint isIn_matrix (x:Line) (A:Matrix) (b: Line):=
  match A,b with
  | nil, _ => True
  | _, nil => True
  | (L :: A0), (v :: b0) => match (scalar_product x L) ?= v with
    |Gt => False
    |_ => isIn_matrix x A0 b0
    end
  end.

Definition isIn (x:Line) (P : Polyhedron) := match P with
  |Po A b => isIn_matrix x A b
  end.

Check isIn.

Compute isIn [:: 0;1;0] PEx.

Fixpoint ActiveFace_matrix (x:Line) (A:Matrix) (b:Line) := match A,b with
  |nil, _ => nil
  |_, nil => nil
  |L :: A0, v :: b0 => match (scalar_product x L) ?= v with
    |Eq => L :: (ActiveFace_matrix x A0 b0)
    |_ => ActiveFace_matrix x A0 b0
    end
  end.

Definition ActiveFace (x:Line) (P : Polyhedron) := match P with
  |Po A b => ActiveFace_matrix x A b
  end.

Definition isVertex (x:Line) (P:Polyhedron) := match P with
  |Po (L::A0) b => match Nat.compare (rank (ActiveFace x P)) (length L) with
    |Eq => True
    |_ => False
    end
  |Po _ _ => False
  end.

Definition Example0 : Matrix := [:: [:: 3; -2; 4];
                                    [:: 2; -4; 5];
                                    [:: 1; 8; 2]].
Definition PEx0 := Po Example0 [:: 66; 66; 66].
Definition PointEx0 := [:: 6; 4;14].

Compute isIn PointEx0 PEx0.
Compute ActiveFace PointEx0 PEx0.
Compute isVertex PointEx0 PEx0.











