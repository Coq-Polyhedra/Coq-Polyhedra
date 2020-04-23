From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bignums Require Import BigQ BigN.

Open Scope bigQ_scope.

Load PolyedreAlgoVerif.
Require Import PolyedreAlgoVerif.

Definition Equation := prod Line bigQ .
Definition Base := seq Equation.