#! /usr/bin/env python3

# --------------------------------------------------------------------
import os, argparse as argp, subprocess as sp, abc
import itertools as it, fractions as fc
import math

if __name__ == "__main__":
    import core
else:
    from . import core

def usage_and_exit():
    print("Incorrect usage of parameter")
    exit(1)

# --------------------------------------------------------------------
def powerset(n):
    if n == -1:
        yield set()
    else:
        for s in powerset(n-1):
            yield s
            yield (s | set([n]))

# --------------------------------------------------------------------
class LRS(abc.ABC):
    def __init__(self, kind, *args):
        self.kind = kind
        self.args = args

    @abc.abstractmethod
    def generate(self, stream):
        pass

    def __call__(self):
      prefix  = f"{self.kind}_" + "_".join([str(elt) for elt in self.args])
      inefile = core.resource(prefix, "lrs", f"{prefix}.ine")

      os.makedirs(core.resource(prefix, "lrs"), exist_ok = True)

      with open(inefile, "w") as stream:
        self.generate(stream)

# --------------------------------------------------------------------
class Cube(LRS):
    def __init__(self, n):
        super().__init__('cube', n)
        if len(self.args) != 1:
            usage_and_exit()
        self.n = self.args[0]

    def generate(self, stream):
        n = self.n
        def output(x):
            print(x, file=stream)

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
        super().__init__('cross', n)
        if len(self.args) != 1:
            usage_and_exit()
        self.n = self.args[0]

    def generate(self, stream):
        n = self.n
        def output(x):
            print(x, file=stream)

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
    def __init__(self, d, m):
        super().__init__('cyclic', d, m)
        if len(self.args) != 2:
            usage_and_exit()
        self.d, self.m = self.args[0], self.args[1]

    def generate(self, stream):
      m, d = self.m, self.d
      def output(x):
        print(x, file=stream)
    
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
# class Birkhoff(LRS):
#     def __init__(self, min, max):
#         super().__init__('birkhoff', min, max)

#     def generate(self, stream, n):
#         def output(x):
#             print(x, file=stream)

#         output("H-representation")
#         output("begin")
#         output(f"{4*n + n*n} {n*n + 1} rational")
#         for k in range(n):
#             output("-1 " + " ".join(["1" if i == k else "0" for i in range(n) for _ in range(n)]))
#             output("1 " + " ".join(["-1" if i == k else "0" for i in range(n) for _ in range(n)]))
#         for k in range(n):
#             output("-1 " + " ".join(["1" if j == k else "0" for _ in range(n) for j in range(n)]))
#             output("1 " + " ".join(["-1" if j == k else "0" for _ in range(n) for j in range(n)]))
#         for k in range(n*n):
#             output("0 " + " ".join(["1" if k==i else "0" for i in range(n*n)]))
#         # M = 2 * (n - 1) + (n-1)**2 + 1
#         # N = (n - 1) ** 2 + 1
#         # output(f"{M} {N} rational")
#         # epsilon = fc.Fraction(1,2 * math.factorial(M)**2)
#         # epsilon = fc.Fraction(1,10)
#         # eps = epsilon
#         # for i0 in range(n-1):
#         #     output(f"{str(1 + eps)} " + " ".join(["-1" if i == i0 else "0" for i in range(n-1) for _ in range(n-1)]))
#         #     eps *= epsilon
#         # for j0 in range(n-1):
#         #     output(f"{str(1 + eps)} " + " ".join(["-1" if j == j0 else "0" for _ in range(n-1) for j in range(n-1)]))
#         #     eps *= epsilon
#         # for k in range((n-1)**2):
#         #     output(f"{str(eps)} " + " ".join([str(int(k == elt)) for elt in range((n-1)**2)]))
#         #     eps *= epsilon
#         # output(f"{str(2 - n + eps)} " + " ".join(["1" for _ in range((n-1)**2)]))
#         output("end")
#         output("printcobasis 1")
#         output("allbases")

# --------------------------------------------------------------------
class Permutohedron(LRS):
    def __init__(self, n):
        super().__init__('permutohedron', n)
        if len(self.args) != 1:
            usage_and_ext()
        self.n = self.args[0]

    def generate(self, stream):
        n = self.n
        def output(x):
            print(x, file=stream)

        output("H-representation")
        output("begin")
        output(f"{2**n} {n + 1} rational")
        for J in powerset(n-1):
            card = len(J)
            if card not in [0,n]:
                output(f"-{(card * (card + 1)) // 2} " + " ".join([f"{int(j in J)}" for j in range(n)]))
        output(f"-{(n * (n+1)) // 2} " + " ".join(["1" for _ in range(n)]))
        output(f"{(n * (n+1)) // 2} " + " ".join(["-1" for _ in range(n)]))
        output("end")
        output("printcobasis 1")
        output("allbases")



# --------------------------------------------------------------------
def optparser():
  parser = argp.ArgumentParser(
      description="Generate and compute polyhedron files, using lrs")

  parser.add_argument(dest="polytope", help="Polytope kind", choices=["cube", "cross", "cyclic", "permutohedron"])
  parser.add_argument(dest="args", nargs="+", type=int, help="Polytope parameters")

  return parser

# --------------------------------------------------------------------
COMMANDS = dict(
    cube        = 'Cube',
    cross       = 'Cross',
    cyclic      = 'Cyclic',
    # birkhoff    = 'Birkhoff',
    permutohedron = 'Permutohedron'
)

# --------------------------------------------------------------------
def generate_lrs(polytope,*args):
    name = COMMANDS[polytope]
    globals()[name](*args)()

# --------------------------------------------------------------------
def main():
  parse = optparser().parse_args()
  polytope, args = parse.polytope, parse.args
  generate_lrs(polytope,*args)

# --------------------------------------------------------------------
if __name__ == "__main__":
  main()
