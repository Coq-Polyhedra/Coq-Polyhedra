#! /usr/bin/env python3

# --------------------------------------------------------------------
import random, fractions as fc, sympy as sym, tqdm

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
    A_I_inv_k = A_I_inv.col(k)
    i = next((i for i,v in enumerate([A_I_inv_k[i,0] for i in range(m)]) if v < 0), m)
    #while there is one negative coordinate, we find the first variable outside the base which can contribute
    while i != m:
        line = A_I_inv.row(i)
        out = True
        for j in range(n):
            if j not in base:
                if (line * A.col(j))[0,0] < 0:
                    try_base = base[:]; try_base.remove(base[i]); try_base.append(j); try_base.sort()
                    try_A_I = A.extract(range(m), try_base)
                    if try_A_I.det() != 0:
                        base = try_base[:]
                        A_I = try_A_I[:,:]
                        A_I_inv = A_I.inv()
                        A_I_inv_k = A_I_inv.col(k)
                        i = next((i for i,v in enumerate([A_I_inv_k[i,0] for i in range(m)]) if v < 0), m)
                        out = False
                        break
        if out:
            return None #No good candidate for a pivot basis
    #here, A_I_inv_k is a good solution, now we can return our vector v
    res = iter([A_I_inv_k[i,0] for i in range(m)])
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
