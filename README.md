# Coq-Polyhedra
Formalizing convex polyhedra in Coq/SSReflect

----------

## Main features

* basic properties of convex polyhedra and their extreme points (`polyhedron.v`)
* formalization of the simplex algorithm (`simplex.v`), based on the lexicographic pivoting rule (symbolic pertubation) 
* strong duality theorem in linear programming (`duality.v`), and some corollaries (Farkas lemma, etc)
* a proof of Minkowski theorem for polyhedra (`minkowski.v`), based on Motzkin's double description method (`double_description_method.v`)

----------

## Authors

* Xavier Allamigeon (<xavier.allamigeon@inria.fr>)
* Ricardo D. Katz (<katz@cifasis-conicet.gov.au>)
