#! /usr/bin/env python3

# --------------------------------------------------------------------
import random, fractions as fc, sympy as sym
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

# --------------------------------------------------------------------
def to_gmp_matrix(m):
    M = sym.Matrix(m)
    c = M.shape
    M0 = [[QQ(M[i,j].p, M[i,j].q) for j in range(c[1])] for i in range(c[0])]
    res = DomainMatrix(M0, c, QQ)
    return res

def gmp_matrix_col(M,i):
    col = to_gmp_matrix([[1 if j == i else 0] for j in range(M.shape[1])])
    N = M.matmul(col)
    return N

def gmp_matrix_row(M,i):
    row = to_gmp_matrix([[int(j==i) for j in range(M.shape[0])]])
    N = row.matmul(M)
    return N
# --------------------------------------------------------------------
def farkas_gen(A, m, n, k):
    """
    farkas_gen generates a vector v such that:
    - A * v = (0,...,0,1,0,...0)^T, where 1 is on the k-th position
    - v is nonnegative
    If there is no such v, then farkas_gen return None

    Parameters are A a sympy matrix; m, n its dimension
    and k \in [0 .. m-1]

    """
    base = random.sample(range(n), m)
    base.sort()
    A_I = A.extract(range(m), base)
    while A_I.det() == 0:
        base = random.sample(range(n), m)
        base.sort()
        A_I = A.extract(range(m), base)
    # Now, we have a base of A
    A_I_inv = A_I.inv()
    A_I_inv_k = gmp_matrix_col(A_I_inv,k)
    i = next((i for i,v in enumerate([A_I_inv_k[i,0].element for i in range(m)]) if v < 0), m)
    #while there is one negative coordinate, we find the first variable outside the base which can contribute
    while i != m:
        line = gmp_matrix_row(A_I_inv,i)
        out = True
        for j in range(n):
            if j not in base:
                if (line * gmp_matrix_col(A,j))[0,0].element < 0:
                    try_base = base[:]; try_base.remove(base[i]); try_base.append(j); try_base.sort()
                    try_A_I = A.extract(range(m), try_base)
                    if try_A_I.det() != 0:
                        base = try_base[:]
                        A_I = try_A_I[:,:]
                        A_I_inv = A_I.inv()
                        A_I_inv_k = gmp_matrix_col(A_I_inv,k)
                        i = next((i for i,v in enumerate([A_I_inv_k[i,0].element for i in range(m)]) if v < 0), m)
                        out = False
                        break
        if out:
            return None #No good candidate for a pivot basis
    #here, A_I_inv_k is a good solution, now we can return our vector v
    res = iter([A_I_inv_k[i,0].element for i in range(m)])
    return [next(res) if i in base else 0 for i in range(n)]

# --------------------------------------------------------------------
def main():
    half = fc.Fraction(1,2)
    res = farkas_gen(
        - sym.Matrix([
            [0, -half, 0, half, 0],
            [0, 0, -half, 0, half],
            [1, -half, -half, -half, -half]
        ]),
        3, 5, 0)
    print(res)

# --------------------------------------------------------------------
if __name__ == '__main__':
    main()