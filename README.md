# Coq-Polyhedra

Formalizing convex polyhedra in Coq

## Installation

### Prerequisites

  * [Coq](https://coq.inria.fr) (>= 8.12)
  * The [Mathematical Components](https://github.com/math-comp/math-comp) library (= local-branch)
  * The [Mathematical Components Finite Map](https://github.com/math-comp/finmap) library (= local-branch)

For the development packages, these source (git) are known to work:

  * Mathematical Components: https://github.com/Coq-Polyhedra/mathcomp.git 
  * Mathematical Components Finite Map: https://github.com/Coq-Polyhedra/finmap.git

### Installing prerequisites from opam

Starting with opam 2.x, you can install all the needed dependencies
via the opam OCaml packages manager.

  * Optionally, switch to a dedicated compiler:

        $> opam switch create ocaml-base-compiler.$OVERSION coq-polyhedra

     where $OVERSION is a valid OCaml version (e.g. 4.07.1)

  * Add the Coq repository:

        $> opam repo add coq-released https://coq.inria.fr/opam/released
        $> opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
        $> opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
        $> opam pin add -n https://github.com/Coq-Polyhedra/mathcomp.git
        $> opam pin add -n coq-mathcomp-finmap https://github.com/Coq-Polyhedra/finmap.git
        $> opam update

  * Installing the dependencies:

        $> opam install dune coq coq-mathcomp-field coq-mathcomp-finmap

Opam can be easily installed from source or via your packages manager:

  * On Ubuntu and derivatives:
  
        $> add-apt-repository ppa:avsm/ppa
        $> apt-get update
        $> apt-get install ocaml ocaml-native-compilers camlp4-extra opam
        
  * On MacOSX using brew:

        $> brew install ocaml opam

See [https://opam.ocaml.org/doc/Install.html] for how to install opam.

See [https://opam.ocaml.org/doc/Usage.html] for how to initialize opam

### Compilation

We provide a Makefile. Simply type `make`.

## Authors

* Xavier Allamigeon (<xavier.allamigeon@inria.fr>)
* Ricardo D. Katz (<katz@cifasis-conicet.gov.ar>)
* Pierre-Yves Strub (<pierre-yves@strub.nu>)
