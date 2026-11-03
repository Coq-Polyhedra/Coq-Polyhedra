# Coq-Polyhedra

Formalizing convex polyhedra in Rocq

## Installation

### Prerequisites

  * [Rocq](https://rocq-prover.org) (9.1)
  * The [Mathematical Components](https://github.com/math-comp/math-comp) library (2.6)
  * The [Mathematical Components Finite Map](https://github.com/math-comp/finmap) library (>= 2.2)
  * The [Mathematical Components Bigenough](https://github.com/math-comp/bigenough) library (>= 1.0.4)
  * [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) (>= 1.10)
  * [Bignums](https://github.com/rocq-community/bignums) (only for `enumeration/`)

### Installing prerequisites from opam

Starting with opam 2.x, you can install all the needed dependencies
via the opam OCaml packages manager.

  * Optionally, switch to a dedicated compiler:

        $> opam switch create coq-polyhedra ocaml-base-compiler.$OVERSION

     where $OVERSION is a valid OCaml version (e.g. 5.4.1)

  * Add the Rocq repository:

        $> opam repo add rocq-released https://rocq-prover.org/opam/released
        $> opam update

  * Installing the dependencies:

        $> opam install dune rocq-core.9.1.1 rocq-mathcomp-algebra rocq-mathcomp-finmap rocq-mathcomp-bigenough rocq-hierarchy-builder rocq-bignums

Opam can be easily installed from source or via your packages manager:

  * On Ubuntu and derivatives:

        $> apt-get install opam

  * On MacOSX using brew:

        $> brew install opam

See [https://opam.ocaml.org/doc/Install.html] for how to install opam.

See [https://opam.ocaml.org/doc/Usage.html] for how to initialize opam

### Compilation

We provide a Makefile. Simply type `make`.

## Authors

* Xavier Allamigeon (<xavier.allamigeon@inria.fr>)
* Ricardo D. Katz (<katz@cifasis-conicet.gov.ar>)
* Pierre-Yves Strub (<pierre-yves@strub.nu>)
