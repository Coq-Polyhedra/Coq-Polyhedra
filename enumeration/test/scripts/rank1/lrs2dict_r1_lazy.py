#! /usr/bin/env python3

import json, os, time
import fractions as fc
import argparse as argp
import math, fractions, random as rd
import networkx as nx
from .. import farkas as fk
from .. import core

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
        mx = [(x[x.index('facets')+1:x.index('det=')-1], x[x.index('det=')+1]) if x[0]!="1" else x[1:] for x in mx]
        couples = [(mx[i], mx[i+1]) for i in range(0,len(mx),2)]
        couples = [(((list(map((lambda x : int(x) - 1), b))), d) ,v) for (b,d),v in couples]
        bas2vtx = {frozenset(b) : v for ((b,_),v) in couples}
        bas2det = {frozenset(b) : d for ((b,d),_) in couples}
    return sorted([b for (b,_),_ in couples]), bas2vtx, bas2det

#rewrite A and b to be integer matrices
# -------------------------------------------------------------------
def to_gmp_matrix(m):
    M = sym.Matrix(m)
    c = M.shape
    M0 = [[QQ(M[i,j].p, M[i,j].q) for j in range(c[1])] for i in range(c[0])]
    res = DomainMatrix(M0, c, QQ)
    return res

def list_of_gmp_matrix(PM):
    PM = PM.to_Matrix()
    (p,q)=PM.shape
    res = []
    for j in range(q):
        res.append([bigq(fc.Fraction(PM[k,j].p, PM[k,j].q)) for k in range(p)])
    return res

def poly_scale(A,b):
    gmp_A, gmp_b = to_gmp_matrix(A), to_gmp_matrix(b)
    ca, cb = gmp_A.shape, gmp_b.shape
    scale = [None for _ in range(ca[0])]
    for i in range(ca[0]):
        mult, div = gmp_b[i,0].element.denominator, gmp_b[i,0].element.numerator
        for j in range(ca[1]):
            mult = QQ.lcm(mult, gmp_A[i,j].element.denominator)
            div = QQ.gcd(div, gmp_A[i,j].element.numerator)
        scale[i] = (mult/div)
    A, b = gmp_A.to_Matrix(), gmp_b.to_Matrix()
    res_A, res_b = [], []
    for i in range(ca[0]):
        aux_A = []
        for j in range(ca[1]):
            aux_A.append(bigq(fc.Fraction(scale[i] * A[i,j])))
        res_A.append(aux_A)
        res_b.append(bigq(fc.Fraction(scale[i] *  b[i,0])))
    return res_A, res_b

# Compute the initial basing point from which we compute our vertex certification
# -------------------------------------------------------------------

# def get_idx(bases, bas2det):
#     min = math.inf
#     idx = 0
#     for i in range(len(bases)):
#         bas = bases[i]
#         det = fc.Fraction(bas2det[frozenset(bas)])
#         if det < min:
#             min = det
#             idx = i
#     return idx

# Construct the graph of lex feasible bases
# -------------------------------------------------------------------

def get_lex_graph(m,n,bases):
    graph = [set() for _ in bases]
    bases_dic = {frozenset(elt) : i for i,elt in enumerate(bases)}
    reg = [0 for _ in bases]
    for kI,I in enumerate(bases):
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
    return (r, I.index(s))

def get_initial_basing_point(A,b,bases,idx):
    base = bases[idx]
    A_I = [A[i] for i in base]
    gmp_A_I = to_gmp_matrix(A_I)
    inv = gmp_A_I.inv()
    gmp_A = to_gmp_matrix(A)
    M = - gmp_A * inv
    b_I = [b[i] for i in base]
    init = [[None for _ in range(len(A))] for _ in range(len(A)+1)]
    init[0] = [(((gmp_A * inv * to_gmp_matrix(b_I)) - to_gmp_matrix(b))[i,0]).element for i in range(len(A))]
    for j in range(len(base)):
        init[base[j]+1] = [M[i,j].element for i in range(len(A))]
    return init

def get_pred(bases,graph_lex,idx):
    G = nx.Graph({i:edges for i,edges in enumerate(graph_lex)})
    pred = [None for _ in graph_lex]
    pred[idx] = (idx,0,0)
    for u,v in nx.bfs_edges(G,idx):
        I,J = bases[u], bases[v]
        r,s = get_entering_leaving(I,J)
        pred[v] = (u,r,s)
    return pred


def get_heap(A,bases,idx,pred,init):
    m = len(A)
    memory=[[[None for _ in range(m)] for _ in range(m+1)] for _ in bases]
    memory[idx]=init
    heap = []
    def eval(kJ,p,q):
        val = memory[kJ][q][p]
        if val is not None:
            return val
        kI,r,s = pred[kJ]
        I = bases[kI]
        Mrs = eval(kI,r,I[s]+1)
        new_val = None
        if q == 1+r:
            Msp = eval(kI,p,I[s]+1)
            new_val = - Msp/Mrs
        else:
            Mpq = eval(kI,p,q)
            Mps = eval(kI,p,I[s]+1)
            Mrq = eval(kI,r,q)
            new_val = (Mrs * Mpq - Mrq * Mps) / Mrs
        memory[kJ][q][p] = new_val
        heap.append(new_val)
        return new_val

    for kJ in range(len(bases)):
        if kJ != idx:
            J = frozenset(bases[kJ])
            (kI,r,s) = pred[kJ]
            I = bases[kI]
            Mrs = eval(kI,r,I[s]+1)
            sat_vect = [None for _ in A]
            for p in range(m):
                if p not in J:
                    val = eval(kJ,p,0)
                    sat_vect[p] = 1 if val > 0 else 0
            for q in range(m):
                if q not in J:
                    sat_vect[q] = 1
                else:
                    for p in range(m):
                        if p not in J:
                            if sat_vect[p] == 0:
                                val = eval(kJ,p,1+q)
                                sat_vect[p] = 1 if val > 0 else 0
    return [bigq(elt) for elt in heap]

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------

def get_vtx(bas2vtx):
    vtx_list = [i for i in bas2vtx.values()]
    vtx_list = sorted(set([tuple(map((lambda x : fractions.Fraction(x)), l)) for l in vtx_list]))
    return [list(map(str,elt)) for elt in vtx_list]

def get_morph(bases, vtx, bas2vtx):
    morph, morph_inv = [None for _ in bases], [None for _ in vtx]
    aux = {tuple(vtx[i]) : i for i in range(len(vtx))}
    for i in range(len(bases)):
        bas = bases[i]
        v = bas2vtx[frozenset(bas)]
        j = aux[tuple(v)]
        morph[i] = j
        morph_inv[j] = i
    return morph, morph_inv

def get_vtx_eq(bases, morph, lenvtx):
    res = [set() for _ in range(lenvtx)]
    for i,base in enumerate(bases):
        tgt = morph[i]
        res[tgt].update(base)
    return [sorted(elt) for elt in res]

def get_dim(m,vtx_eq,morph_inv):
    res = []
    for p in range(m):
        j = next(i for i,elt in enumerate(vtx_eq) if p not in set(elt))
        res.append(morph_inv[j])
    return res


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
    A = to_gmp_matrix(A).transpose()
    cert_pos, cert_neg = [], []
    for k in range(n):
        cert_pos.append(list(map(bigq,fk.farkas_gen(A, n, m, k))))
        cert_neg.append(list(map(bigq,fk.farkas_gen(-A, n, m, k))))
    return cert_pos, cert_neg


# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    return parser

# -------------------------------------------------------------------
def lrs2dict(name,hirsch=""):

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    A,b = poly_scale(A,b)
    bases, bas2vtx, bas2det = get_bases_from_lrs(name)
    print("Build the lex graph...",end='',flush=True)
    st = time.time()
    graph_lex = get_lex_graph(len(A), len(A[0]), bases)
    et = time.time()
    print(f" in {(et-st):.2f}s")
    root = 0
    pred = get_pred(bases, graph_lex, root)
    init = get_initial_basing_point(A,b,bases,root)
    st = time.time()
    heap = get_heap(A,bases,root,pred,init)
    et = time.time()
    h = len(heap)
    print(f"heap for root={root}: time={(et-st):.2f}s & size={h}")
    init = [[bigq(elt) if elt is not None else '0' for elt in col] for col in init]

    vtx = get_vtx(bas2vtx)
    morph, morph_inv = get_morph(bases,vtx,bas2vtx)
    vtx_eq = get_vtx_eq(bases,morph,len(vtx))
    dim = get_dim(len(A),vtx_eq,morph_inv)
    graph_vtx = get_graph_vtx(graph_lex,morph,len(vtx))
    edge_inv = get_edge_inv(graph_lex,graph_vtx,morph)
    bound_pos, bound_neg = get_farkas_cert(A,len(A),len(A[0]))


    # Store in a dictionnary

    tgtjson = {}
    tgtjson['A'] = A
    tgtjson['b'] = b
    tgtjson['bases'] = bases
    tgtjson['pred'] = pred
    tgtjson['root'] = root
    tgtjson['heap'] = heap
    tgtjson['init'] = init
    tgtjson['graph_lex'] = graph_lex
    tgtjson['graph_vtx'] = graph_vtx
    tgtjson['morph'] = morph
    tgtjson['morph_inv'] = morph_inv
    tgtjson['edge_inv'] = edge_inv
    tgtjson['bound_pos'] = bound_pos
    tgtjson['bound_neg'] = bound_neg
    tgtjson['dim'] = dim
    tgtjson['vtx_eq'] = vtx_eq
    return tgtjson

def dict2json(name,tgtdict):
    tgtdir = core.resource(name)
    
    with open(os.path.join(tgtdir, f"{name}.json"), "w") as stream:
        json.dump(tgtdict,stream, indent=2)

def main(name):
    dict2json(name,lrs2dict(name))

# -------------------------------------------------------------------
if __name__ == '__main__':
    args   = optparser().parse_args()
    name   = args.name
    main(name)