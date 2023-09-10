# Testing the graph certification algorithm

## Requirements

- `zsh`
- [`lrs`](http://cgm.cs.mcgill.ca/%7Eavis/C/lrs.html) installed
- Python libraries: [`networkx`](https://networkx.org/), [`tqdm`](https://tqdm.github.io/) and [`sympy`](https://www.sympy.org/en/index.html)
- `Coq 8.16.0`
- `coq-bignums`, version `9.0.0+coq8.16`
- Pin these versions of [MathComp](https://github.com/Coq-Polyhedra/mathcomp), of [finmap](https://github.com/Coq-Polyhedra/finmap), and of [binreader](https://github.com/Coq-Polyhedra/coq-binreader)

## Presentation

This directory is organized as follows :
- `benchmark.py` is the main script to use
- `data` contains information relative to one polyhedron, such as H-representation and V-representation in `lrs`format, certificates in binary format, coq files...
- `benchmarks` contains for each task `.csv` files with the date in the format `name-month-day-hour-minutes-seconds`.
- `scripts` and `jobs` subdirectories are used internally.

The usage of `benchmark.py` is given by :
- `benchmark.py clean_data` remove all the entries in `data`, except the H-representation of `poly20dim21` and `poly23dim24`.
- `benchmark.py clean_coq` is equivalent to `dune clean`.
- `benchmark.py gen` generate `lrs` H-representation of predefined polytopes. If you require a custom set :
 
    `benchmark.py gen -p {name} {min} {max}`

  will generate polytopes given by `{name}` for every parameter between `{min}` and `{max}`, both included.

  Example : `benchmark.py gen -p cube 3 10`
  Available names :
    - `cube`, the hypercube
    - `cross`, the cross polytope
    - `cyclic`, the (polar of) cyclic polytope. It takes only one parameter `n`. Then the corresponding polytope is `n`-dimensional and has `2n` facets.
    - `permutohedron`, the permutohedron
- `benchmark.py task` performs the computation and generate a table according to the given `task`. It performs it on every polytopes in `data`. To restrict it on a subset of the polytopes available :

    - `benchmark.py task -p hirsch` only takes into account `poly20dim21` and `poly23dim24`.
    - `benchmark.py task -p {name} {min} {max}` only takes into account the corresponding polytopes.
  
  Available `task` are given by:
    - `theories`: compile the theories.
    - `lrs`: call `lrs` on the polytopes.
    - `certificates`: generate certificates of the polytopes.
    - `compilation`: compile the certificates.
    - `validation`: run the graph certification algorithm on the certificates.
    - `diameter`: compute the diameter of the polytopes.
    - `hirsch` and `exact`: for `poly20dim21` and `poly23dim24` only, computes a formal disproof to the Hirsch conjecture and compute a formal proof on the diameter of these polytopes.
  
  `benchmark.py all` executes all tasks in the correct order. It is the recommended command.
