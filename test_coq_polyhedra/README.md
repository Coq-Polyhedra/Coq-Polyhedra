# Dependencies

  - Coq (8.16.x)
  - CoqPolyhedra
    - requires MathComp from
        [https://github.com/Coq-Polyhedra/mathcomp]
    - requires MathComp FinMap from
        [https://github.com/Coq-Polyhedra/finmap]
  - Coq Bignums (8.16)
  - Coq BinReader

The dependencies can be installed using opam:

    $> opam switch create hirsch ocaml-base-compiler.4.07.1
    $> opam repo add coq-released https://coq.inria.fr/opam/released
    $> opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    $> opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
    $> opam pin add -n coq 8.13.0
    $> opam pin add -n https://github.com/Coq-Polyhedra/mathcomp.git
    $> opam pin add -n coq-mathcomp-finmap https://github.com/Coq-Polyhedra/finmap.git
    $> opam pin add -n coq-binreader https://github.com/Coq-Polyhedra/coq-binreader.git
    $> opam install dune coq coq-mathcomp-algebra coq-mathcomp-finmap coq-bignums coq-binreader

We also provide a Docker image:

    $> make -C docker build
    $> make -C docker run

When running docker, the working directory is set to this repository.

# Compiling

The formal development can be built using `dune':

    $> dune build theories

It does not include the computational part of the formal disproof of
the Hirsch conjecture.

# Compiling (computational part)

We provide various pre-computed polytope definitions:

  - `cube_i` (`i` in `{2..7}`):
     
         the cube of dimension `i`.

  - `cross_i` (`i` in `{2..7}`):
     
         the cross-polytope or cocube of dimension `i`.

  - `spindle_i` (`i` in `{25, 28, 48}`):
     
         the spindle of dimension `i`.

  - `cyclic_i_j` (`(i, j)` = `(12, 6)` or `(i, j)` = `(20, 10)`)
     
         the cyclic polytope of dimension $j with $i points.

  - `poly20dim21`, `poly23dim24`:
     
        counter-examples to the Hirsch conjecture

For each of them, it is possible to compute (in Coq):

  - [Validation]: its graph
  - [Diameter]  : the diameter of its graph

For the last two ones, it is also possible to:

  - [Hirsch]: generates a computational proof that the given polytope is non-Hirsch.

All these polytope definitions can be found in:

    test/data/archives/$name.tar.bz2

To run the job $job ($job in {Validation, Diameter, Hirsch}) on the
polytope $polytope, change your working directory to `test/` and run
the following commands:

    $> tar -xof data/archives/$polytope.tar.bz2
    $> scripts/bin2coq.py $polytope
    $> scripts/coqjobs.py $polytope $job vm_compute
    $> dune build data/$polytope/coq        # Compile the polytope representation
    $> dune build data/$polytope/coq_$job   # Compile/execute the job
