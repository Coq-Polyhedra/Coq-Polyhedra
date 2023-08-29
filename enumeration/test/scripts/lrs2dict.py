#! /usr/bin/env python3

import json, os, time
import fractions as fc
import argparse as argp
import math, fractions, random as rd
import networkx as nx
import tqdm
import random as rd
from . import farkas as fk
from . import core

import sympy as sym
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

# Common functions
# -------------------------------------------------------------------
def bigq(x):
    return str(x)

# Extract polyhedron information from lrs files
# -------------------------------------------------------------------
def get_polyhedron_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ine")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po = [list(map(fc.Fraction, xs)) for xs in mx]

    Po = [([x for x in line[1:]], -line[0]) for line in Po]
    Po = [(list(map(bigq, p1)), bigq(p2)) for p1,p2 in Po]
    A,b = zip(*Po)
    return A, b

def get_bases_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ext")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        mx = [(x[x.index('facets')+1:x.index('det=')-1]) if x[0]!="1" else x[1:] for x in mx]
        couples = [(mx[i], mx[i+1]) for i in range(0,len(mx),2)]
        couples = [((list(map((lambda x : int(x) - 1), b))) ,v) for b,v in couples]
        couples = sorted(couples,key=(lambda x : x[0]))
    return zip(*couples)


# -------------------------------------------------------------------

def list_of_gmp_matrix(PM):
    p,q = PM.shape
    res = []
    for j in range(q):
        res.append([str(PM[i,j].element) for i in range(p)])
    return res

# Construct the graph of lex feasible bases
# -------------------------------------------------------------------

def get_lex_graph(m,n,bases):
    graph = [set() for _ in bases]
    bases_dic = {frozenset(elt) : i for i,elt in enumerate(bases)}
    reg = [0 for _ in bases]
    for kI,I in enumerate(tqdm.tqdm(bases,desc="Computing the graph of the lex-feasible bases : ")):
        I_set = set(I)
        s = 0
        while reg[kI] < n:
            Is = I[s]
            for r in range(m):
                if r not in I_set:
                    J = I_set - {Is} | {r}
                    if frozenset(J) in bases_dic:
                        kJ = bases_dic[frozenset(J)]
                        if kJ not in graph[kI]:
                            graph[kI].add(kJ)
                            graph[kJ].add(kI)
                            reg[kI]+=1
                            reg[kJ]+=1
                            break
            s += 1
    return [sorted(elt) for elt in graph]

# Visit the graph in order to construct the values required by the algorithm in the correct order
# -------------------------------------------------------------------

def get_entering_leaving(I,J):
    I_set, J_set = set(I), set(J)
    IJ = I_set & J_set
    s,r = (I_set - IJ).pop(), (J_set - IJ).pop()
    return (r, s)

def get_initial_inverse(A,I):
    A_I = [A[i] for i in I]
    gmp_A_I = fk.to_gmp_matrix(A_I)
    A_I_inv = gmp_A_I.inv()
    res = [None for _ in A]
    for i in range(len(I)):
        res[I[i]] = fk.gmp_matrix_col(A_I_inv, i)
    return res

def rank_1_update(A,inv,I,J):
    r,s = get_entering_leaving(I,J)
    A_r = fk.to_gmp_matrix([A[r]])
    inv_s = inv[s]
    Ars = ((A_r * inv_s)[0,0])
    res = [None for _ in A]
    for k in J:
        if k != r:
            res[k] = inv[k] - (((A_r * inv[k])[0,0] // Ars) * inv_s)
        else:
            res[r] = inv[s] / Ars
    return res

def from_inverse_to_lbl(n,bases,vertices,inverses):
    res = []
    for vtx, inv in zip(vertices,inverses):
        translate = [list_of_gmp_matrix(- col)[0] if col is not None else ["0" for _ in range(n)] for col in inv]
        res.append([vtx] + translate)
    return list(zip(bases,res))
        
def get_lbl_lex(A,bases,vertices,graph,root=0):
    graph_lex = nx.Graph({i:edges for i,edges in enumerate(graph)})
    inverses = [None for _ in bases]
    inverses[root] = get_initial_inverse(A,bases[root])
    for (node,pred) in tqdm.tqdm(nx.bfs_predecessors(graph_lex,root), desc="Computation of the labels of the lex-feasible bases graph : "):
        inverses[node] = rank_1_update(A,inverses[pred],bases[pred],bases[node])
    lbl = from_inverse_to_lbl(len(A[0]),bases, vertices,inverses)
    return lbl

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------

def get_lbl_vtx(vertices):
    vtx_list = sorted(set([tuple(map((lambda x : fractions.Fraction(x)), l)) for l in vertices]))
    return [list(map(str,elt)) for elt in vtx_list]

def get_morph(bases, dupl, vertices):
    bas2vtx = {frozenset(base) : vtx for (base,vtx) in zip(bases,dupl)}
    morph, morph_inv = [None for _ in bases], [None for _ in vertices]
    aux = {tuple(v) : i for (i,v) in enumerate(vertices)}
    for i,base in enumerate(bases):
        v = bas2vtx[frozenset(base)]
        j = aux[tuple(v)]
        morph[i] = j
        morph_inv[j] = i
    return morph, morph_inv


def get_graph_vtx(graph_lex, morf, length_vtx):
    graph = [[] for i in range(length_vtx)]
    for i in range(len(graph_lex)):
        tgt_i = morf[i]
        for j in graph_lex[i]:
            tgt_j = morf[j]
            if tgt_i != tgt_j and tgt_j not in graph[tgt_i]:
                graph[tgt_i].append(tgt_j)
    return [sorted(x) for x in graph]

def get_edge_inv(G_lex, G_simpl, morf):
    edge_inv = [[None for j in range(len(G_simpl[i]))] for i in range(len(G_simpl))]
    for i in range(len(G_lex)):
        for j in range(len(G_lex[i])):
            nei = G_lex[i][j]
            if morf[i] != morf[nei]:
                j_ = next(i for i,v in enumerate(G_simpl[morf[i]]) if v == morf[nei])
                edge_inv[morf[i]][j_] = (i,nei)
    return edge_inv

# Get final certificates (Farkas, dim_full)
# -------------------------------------------------------------------
def get_farkas_cert(A, m, n):
    A = fk.to_gmp_matrix(A).transpose()
    cert_pos, cert_neg = [], []
    for k in range(n):
        cert_pos.append(list(map(bigq,fk.farkas_gen(A, n, m, k))))
        cert_neg.append(list(map(bigq,fk.farkas_gen(-A, n, m, k))))
    return cert_pos, cert_neg

def make_dim_full(lbl_simpl, n):
    while True:
        map_lbl = rd.sample(range(len(lbl_simpl)), n+1)
        map_lbl.sort()
        M = fk.to_gmp_matrix([list(map(fc.Fraction, lbl_simpl[i])) for i in list(map_lbl)[1:]])
        N = fk.to_gmp_matrix([list(map(fc.Fraction, lbl_simpl[map_lbl[0]])) for _ in range(n)])
        Q = M - N
        Q_det = Q.det()
        if Q_det != 0:
            Q_inv = Q.inv()
            Q_res = list_of_gmp_matrix(Q_inv)
            return list(map_lbl)[0], list(map_lbl)[1:], Q_res
        
START_BFS = {"poly20dim21" : 394, "poly23dim24" : 7200}

# Debug functions
# -------------------------------------------------------------------
def lex_order_gmp(A,B):
    p,q = A.shape
    for i in range(p):
        for j in range(q):
            if A[i,j].element < B[i,j].element:
                return False, i
            if A[i,j].element > B[i,j].element:
                break
    return True, None


def lbl_lex_debug(A,b,lbl_lex,trials):
    print("Debug function : verifies that all given bases are lex-feasible")
    m = len(A)
    gmp_A = fk.to_gmp_matrix(A)
    b_pert = [[x] + [- int(k==i) for k in range(m)] for i,x in enumerate(b)]
    gmp_b_pert = fk.to_gmp_matrix(b_pert)
    concerned_vertices = {}
    res = []
    for i in tqdm.tqdm(range(trials), desc="Attempts to find non-feasible lex-bases"):
        basis, point = lbl_lex[i]
        gmp_X = fk.to_gmp_matrix([[fc.Fraction(x) for x in col] for col in point]).transpose()
        test, line = lex_order_gmp(gmp_A * gmp_X, gmp_b_pert)
        if not test:
            print(f"{basis} is not lex-feasible")
            print(gmp_X.transpose())
            print("line : ", line)

def print_lbl_lex(lbl_lex):
    for base, point in lbl_lex:
        print("Base : ", [i + 1 for i in base])
        print("Point : ",  point[0])
        print("Inverse : ")
        for i in range(len(point[0])):
            print([point[j+1][i] for j in base])
        print()



# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    parser.add_argument('--hirsch', help="option adding the certificates in order to disprove Hirsch conjecture", action="store_true")
    return parser

# -------------------------------------------------------------------
def lrs2dict(name, hirsch=False):

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    bases, dupl_vertices = get_bases_from_lrs(name)
    G_lex = get_lex_graph(len(A), len(A[0]), bases)
    lbl_lex = get_lbl_lex(A,bases,dupl_vertices,G_lex)
    # lbl_lex_debug(A,b,lbl_lex,len(lbl_lex)) #Todo : to use on birkhoff_4
    # print_lbl_lex(lbl_lex) #also in case of debug
    print(f"Computation of the vertex-edge graph together with image graph certificates : ", end="", flush=True)
    st = time.time()
    lbl_vtx = get_lbl_vtx(dupl_vertices)
    morph, morph_inv = get_morph(bases, dupl_vertices, lbl_vtx)
    G_vtx = get_graph_vtx(G_lex,morph,len(lbl_vtx))
    edge_inv = get_edge_inv(G_lex,G_vtx,morph)
    et = time.time()
    print(f"{et - st:.2f}s")
    print(f"Computation of the certificates of boundedness : ", end="", flush=True)
    st = time.time()
    bound_pos, bound_neg = get_farkas_cert(A,len(A),len(A[0]))
    et = time.time()
    print(f"{et - st:.2f}s")

    
    # Hirsch specific certificates
    if hirsch:
        print(f"Computation of the certficates of full-dimensionality : ", end="", flush=True)
        st = time.time()
        origin, map_dim, inv_dim = make_dim_full(lbl_vtx, len(A[0]))
        et = time.time()
        print(f"{et - st:.2f}s")
        start=0
        try:
            start = START_BFS[name]
        except KeyError:
            print("Only works with Hirsch counterexample : poly20dim21 or poly23dim24")

    # # Store in a dictionnary
    tgtdir =   {
                "Po"        : (A,b),
                "lbl_lex"   : lbl_lex,
                "lbl_vtx"   : lbl_vtx,
                "G_lex"     : G_lex,
                "G_vtx"     : G_vtx,
                "morph"     : morph,
                "morph_inv" : morph_inv,
                "edge_inv"  : edge_inv,
                "bound_pos" : bound_pos,
                "bound_neg" : bound_neg
                }
    if hirsch:
        tgtdir["origin"] = origin
        tgtdir["map_dim"] = map_dim
        tgtdir["inv_dim"] = inv_dim
        tgtdir["start"] = start

    return tgtdir

def write_json(tgtjson):
    tgtdir = core.resource(name)

    with open(os.path.join(tgtdir, f"{name}.json"), "w") as stream:
        json.dump(tgtjson, stream, indent=2)

def main(name,hirsch):
    write_json(lrs2dict(name,hirsch))

# -------------------------------------------------------------------
if __name__ == '__main__':
    args   = optparser().parse_args()
    name   = args.name
    hirsch = args.hirsch
    main(name,hirsch)
