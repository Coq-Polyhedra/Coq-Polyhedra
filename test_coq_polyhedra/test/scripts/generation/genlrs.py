#! /usr/bin/env python3

# --------------------------------------------------------------------
import os, argparse as argp, subprocess as sp, abc
import itertools as it, fractions as fc

from core import *

# --------------------------------------------------------------------
class LRS(abc.ABC):
    def __init__(self, kind, args):
        self.kind = kind
        self.args = args

    @abc.abstractmethod
    def generate(self, stream):
        pass

    def __call__(self):
        prefix  = f"{self.kind}_{'_'.join(str(x) for x in self.args)}"
        inefile = resource(prefix, "lrs", f"{prefix}.ine")
        extfile = resource(prefix, "lrs", f"{prefix}.ext")

        os.makedirs(resource(prefix, "lrs"), exist_ok = True)

        with open(inefile, "w") as stream:
            self.generate(stream)

        sp.check_call(["lrs", inefile, extfile])

# --------------------------------------------------------------------
class Cube(LRS):
    def __init__(self, n):
        super().__init__('cube', (n,))
        self.n = n

    def generate(self, stream):
        def output(x):
            print(x, file=stream)

        n = self.n

        output("H-representation")
        output("begin")
        output(f"{2*n} {n + 1} rational")
        for i in range(n):
            output("1 " + " ".join([str(int(j==i)) for j in range(n)]))
        for i in range(n):
            output("1 " + " ".join([str(- int(j==i)) for j in range(n)]))
        output("end")
        output("printcobasis 1")
        output("allbases")

# --------------------------------------------------------------------
class Cross(LRS):
    def __init__(self, n):
        super().__init__('cross', (n,))
        self.n = n

    def generate(self, stream):
        def output(x):
            print(x, file=stream)

        n = self.n

        output("H-representation")
        output("begin")
        output(f"{2**n} {n + 1} rational")
        for r in range(n+1):
            for part in it.combinations(range(n), r):
                output("1 " + " ".join(["1" if j in part else "-1" for j in range(n)]))
        output("end")
        output("printcobasis 1")
        output("allbases")

# --------------------------------------------------------------------
class Cyclic(LRS):
    def __init__(self, m, d):
        super().__init__('cyclic', (m, d))
        self.m, self.d = m, d

    def generate(self, stream):
        def output(x):
            print(x, file=stream)

        m, d = self.m, self.d

        output("H-representation")
        output("begin")
        output(f"{m} {d + 1} rational")
        mean = [0 for k in range(d)]
        for i in range(1, m+1):
            moments = [i**k for k in range(1,d+1)]
            mean = [mean[k] + moments[k] for k in range(d)]
        mean = [fc.Fraction(mean[k], m) for k in range(d)]
        for i in range(1, m+1):
            output("1 " + " ".join([str(- i**(k+1) + mean[k]) for k in range(d)]))
        output("end")
        output("printcobasis 1")
        output("allbases")

# --------------------------------------------------------------------
class Birkhoff(LRS):
    def __init__(self, n):
        super().__init__('birkhoff', (n,))
        self.n = n

    def generate(self, stream):
        def output(x):
            print(x, file=stream)

        n = self.n

        output("H-representation")
        output("begin")
        output(f"{2 * (n - 1) + (n-1)**2 + 1} {(n - 1) ** 2 + 1} rational")
        for i0 in range(n-1):
            output("1 " + " ".join(["-1" if i == i0 else "0" for i in range(n-1) for j in range(n-1)]))
        for j0 in range(n-1):
            output("1 " + " ".join(["-1" if j == j0 else "0" for i in range(n-1) for j in range(n-1)]))
        for k in range((n-1)**2):
            output("0 " + " ".join([str(int(k == elt)) for elt in range((n-1)**2)]))
        output(f"{2 - n} " + " ".join(["1" for _ in range((n-1)**2)]))
        output("end")
        output("printcobasis 1")
        output("allbases")

# --------------------------------------------------------------------
def optparser():
  parser = argp.ArgumentParser(
      description="Generate and compute polyhedron files, using lrs")

  subprs = parser.add_subparsers(dest="polytope", help="Polytope kind")
  subprs.required = True

  cube_parser = subprs.add_parser("cube", help="Generate a cube")
  cube_parser.add_argument("n", type=int, help="The dimension of the cube")

  cross_parser = subprs.add_parser("cross", help="Generate a cross polytope")
  cross_parser.add_argument("n", type=int, help="The dimension of the cross polytope")

  cyclic_parser = subprs.add_parser("cyclic", help="Generate a cyclic polytope")
  cyclic_parser.add_argument("m", type=int, help="The number of vertices of the cyclic polytope")
  cyclic_parser.add_argument("d", type=int, help="The dimension of the cyclic polytope")

  birkhoff_parser = subprs.add_parser("birkhoff", help="Generate a birkhoff polytope")
  birkhoff_parser.add_argument("n", type=int, help="The parameter n of the birkhoff polytope")

  return parser

# --------------------------------------------------------------------
COMMANDS = dict(
    cube      = ('Cube'    , ['n'     ]),
    cross     = ('Cross'   , ['n'     ]),
    cyclic    = ('Cyclic'  , ['m', 'd']),
    birkhoff = ('Birkhoff', ['n'     ]),
)

# --------------------------------------------------------------------
def main():
  args = optparser().parse_args()
  name, params = COMMANDS[args.polytope]
  globals()[name](*(getattr(args, x) for x in params))()

# --------------------------------------------------------------------
if __name__ == "__main__":
  main()
