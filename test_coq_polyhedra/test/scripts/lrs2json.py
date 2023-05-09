#! /usr/bin/env python3

# --------------------------------------------------------------------
import argparse as argp
from typing import Tuple
import fractions as fc
import itertools as it
import json
import networkx as nx
import os
import random as rd
import re
import subprocess as sp
import sympy as sym
import sys
import time
import tqdm

from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

from prerequisite import core, farkas as fk

# --------------------------------------------------------------------
def bigq(x):
    return str(x)

# --------------------------------------------------------------------
# Extract the polyhedron to a json file
def make_Po(name):
    input_ine = core.resource(name, "lrs", f"{name}.ine")

    with open(input_ine, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po_aux = [list(map(fc.Fraction, xs)) for xs in mx]

    m = len(Po_aux)
    n = len(Po_aux[0]) - 1
    ine = [([x for x in line[1:]], -line[0]) for line in Po_aux]
    ine = [(list(map(bigq, p1)), bigq(p2)) for p1,p2 in ine]
    A,b = zip(*ine)

    return m, n, A, b

# ------------------------------------------------------------------------------------------
# Extract the vertices data from the .ext file
def extract_ineqs(line):
    line, i = line[line.index('facets')+1:], 0

    try:
        line.remove(":")
    except ValueError:
        pass

    while i < len(line):
        if not re.match('^\d+$', line[i]):
            break
        i += 1

    return sorted([int(i) - 1 for i in line[:i]])

def extract_vertices(name):
    poly_ext = core.resource(name, "lrs", f"{name}.ext")
    with open(poly_ext, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx if x[0] in ["V", "1"] and x[1] != "-"]
    bas_vtx = [(extract_ineqs(mx[i]), mx[i+1][1:]) for i in range(0, len(mx), 2)]
    res_vtx, res_bas = {}, {}
    for bas,vtx in bas_vtx:
        if tuple(vtx) in res_vtx:
            res_vtx[tuple(vtx)].append(bas)
        else:
            res_vtx[tuple(vtx)] = [bas]
        res_bas[frozenset(bas)] = vtx 
    return res_vtx, res_bas

# --------------------------------------------------------------------
def matrix_of_bas(A, bas):
    extracted = [A[i] for i in bas]
    return sym.Matrix(extracted)

# --------------------------------------------------------------------
def bas_adj(bas1, bas2):
    return len(set.intersection(set(bas1), set(bas2))) == len(bas1) - 1

# --------------------------------------------------------------------
def has_bas_adj(l1, l2):
    for bas1 in l1:
        for bas2 in l2:
            if bas_adj(bas1, bas2):
                return True
    return False

# --------------------------------------------------------------------
def inverse_big(M):
    c = M.shape
    M0 = [[QQ(M[i,j].p, M[i,j].q) for j in range(c[0])] for i in range(c[0])]
    big = DomainMatrix(M0, c, QQ)
    return big.inv().to_Matrix()

# --------------------------------------------------------------------
def perturbated_matrix(x, mask, A, m):
    A_r = matrix_of_bas(A, mask)
    M = inverse_big(A_r)
    M = -M
    (n,c) = M.shape
    N = sym.zeros(n, m)
    for j in range(c):
        for i in range(n):
            N[i,mask[j]] = M[i,j]
    v = sym.Matrix(n,1,x)
    return N.col_insert(0,v)

# --------------------------------------------------------------------
def is_feasible(Po, point):
    for line in Po:
        A_i = sym.Matrix([line[0]])
        res_mat = A_i * point
        res = res_mat.tolist()[0]
        if res < [fc.Fraction(x) for x in line[1]]:
            return False
    return True

# --------------------------------------------------------------------
def convert_pert_matrix(PM):
    (p,q)=PM.shape
    res = []
    for j in range(q):
        res.append([bigq(fc.Fraction(PM[k,j].p, PM[k,j].q)) for k in range(p)])
    return res

# --------------------------------------------------------------------
def make_vertices_lex(dic_bas, m, A):
    res = []
    for (p1, p2) in tqdm.tqdm([(list(bas), vtx) for bas,vtx in dic_bas.items()], desc="Extraction of lexicographic feasible basis"):
        PM = perturbated_matrix(p2, p1, A, m)
        # if is_feasible(Po, PM):
        res.append((p1, convert_pert_matrix(PM)))
    def key_lex(x): return x[0]
    res.sort(key=key_lex)
    return res

def make_vertices_simpl(dic_vtx):
    res = list(dic_vtx.keys())
    def key_simpl(x): return [fc.Fraction(e) for e in x]
    res.sort(key=key_simpl)
    return res
# --------------------------------------------------------------------
# def make_vertices_simpl(aux):
#     res = []
#     def key_simpl(x): return [fc.Fraction(e) for e in x[1]]
#     aux.sort(key=key_simpl)
#     last_one = None
#     for (p1, p2) in tqdm.tqdm(aux, desc="Extraction of vertices and their bases"):
#         if p2 == last_one:
#             bases, point = res[-1]
#             res[-1] = bases + [p1], p2
#         else:
#             res += [([p1],p2)]
#             last_one = p2
#     return res

# --------------------------------------------------------------------
def make_graph_lex(dic_lex_index, m, n):
    graph= [[] for _ in dic_lex_index.keys()]
    for (base, index) in tqdm.tqdm(dic_lex_index.items(), desc="Extraction of the graph lex..."):
        reg = len(graph[index])
        for i in base:
            if reg >= n:
                break
            minus_i = base - {i}
            for j in range(m):
                if j not in base:
                    candidate = minus_i | {j}
                    res = dic_lex_index.get(candidate,None)
                    if res is not None and index < res:
                        graph[index] += [res]
                        graph[res] += [index]
                        reg += 1

    return [sorted(elt) for elt in graph]

# --------------------------------------------------------------------
def make_morf(dic_lex_index, dic_simpl_index, dic_bas):
    morf, morf_inv = [None for _ in range(len(dic_lex_index))], [None for _ in range(len(dic_simpl_index))]
    for base, i in dic_lex_index.items():
        vtx = dic_bas[base]
        j = dic_simpl_index[tuple(vtx)]
        morf[i] = j
        morf_inv[j] = i
    return morf, morf_inv

# --------------------------------------------------------------------
def make_graph_simpl(G_lex, morf, K):
    graph = [[] for i in range(K)]
    for i in range(len(G_lex)):
        tgt_i = morf[i]
        for j in G_lex[i]:
            tgt_j = morf[j]
            if tgt_i != tgt_j and tgt_j not in graph[tgt_i]:
                graph[tgt_i].append(tgt_j)
    return [sorted(x) for x in graph]

        

    # for i in tqdm.tqdm(range(len(vertices)), desc="Extraction of the graph of vertices..."):
    #     for j in range(len(vertices)):
    #         if i < j and has_bas_adj(vertices[i][0], vertices[j][0]):
    #             graph[i] += [j]
    #             graph[j] += [i]
    # return graph
        

    

# --------------------------------------------------------------------
def make_edge_inv(G_lex, G_simpl, morf):
    edge_inv = [[None for j in range(len(G_simpl[i]))] for i in range(len(G_simpl))]
    for i in tqdm.tqdm(range(len(G_lex))):
        for j in range(len(G_lex[i])):
            nei = G_lex[i][j]
            if morf[i] != morf[nei]:
                j_ = next(i for i,v in enumerate(G_simpl[morf[i]]) if v == morf[nei])
                edge_inv[morf[i]][j_] = (i,nei)
    return edge_inv

# --------------------------------------------------------------------
def make_cert(A, m, n):
    A = sym.Matrix(A).transpose()
    cert_pos, cert_neg = [], []
    for k in tqdm.tqdm(range(n), desc="Extraction of farkas certificates"):
        cert_pos.append(list(map(bigq,fk.farkas_gen(A, n, m, k))))
        cert_neg.append(list(map(bigq,fk.farkas_gen(-A, n, m, k))))
    return cert_pos, cert_neg

# --------------------------------------------------------------------
def make_dim_full(lbl_simpl, n):
    while True:
        map_lbl = rd.sample(range(len(lbl_simpl)), n+1)
        map_lbl.sort()
        M = sym.Matrix([list(map(fc.Fraction, lbl_simpl[i])) for i in list(map_lbl)[1:]])
        N = sym.Matrix([list(map(fc.Fraction, lbl_simpl[map_lbl[0]])) for _ in range(n)])
        Q = M - N
        Q_det = Q.det()
        if Q_det != 0:
            Q_inv = inverse_big(Q)
            Q_res = [[bigq(Q_inv[i,j]) for i in range(n)] for j in range(n)]
            return list(map_lbl)[0], list(map_lbl)[:1], Q_res

# --------------------------------------------------------------------
def make_start(G, thre):
    g = nx.Graph({i : G[i] for i in range(len(G))})
    for i in tqdm.tqdm(range(len(G))):
        L = nx.eccentricity(g,v=[i])
        dist = [i for i in L.values()][0]
        if dist > thre:
            return i

# --------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(
      description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    parser.add_argument('--hirsch',
          help="Additional data extraction if it is a counterexample to the hirsch conjecture",
          action="store_true")
    return parser

# --------------------------------------------------------------------
def main():
    args   = optparser().parse_args()
    name   = args.name
    hirsch = args.hirsch

    # jsondir = resource(name, 'json')

    # if os.path.exists(jsondir):
    #     print(f'remove {jsondir} first', file=sys.stderr)
    #     exit(1)

    # os.makedirs(jsondir)

    tgtjson = {}

    m, n, A, b = make_Po(name)
    tgtjson["Po"] = (A,b)
    dic_vtx, dic_bas= extract_vertices(name)
    lbl_lex = make_vertices_lex(dic_bas, m, A)
    tgtjson["lbl_lex"] = lbl_lex
    lbl_simpl = make_vertices_simpl(dic_vtx)
    tgtjson["lbl_simpl"] = lbl_simpl
    dic_lex_index = {frozenset(lbl_lex[i][0]) : i for i in range(len(lbl_lex))}
    dic_simpl_index = {tuple(lbl_simpl[i]) : i for i in range(len(lbl_simpl))}
    G_lex = make_graph_lex(dic_lex_index, m, n)
    tgtjson["G_lex"] = G_lex
    morf, morf_inv = make_morf(dic_lex_index, dic_simpl_index, dic_bas)
    tgtjson["morf"] = morf
    tgtjson["morf_inv"] = morf_inv
    G_simpl = make_graph_simpl(G_lex, morf, len(dic_vtx))
    tgtjson["G_simpl"] = G_simpl
    edge_inv = make_edge_inv(G_lex, G_simpl, morf)
    tgtjson["edge_inv"] = edge_inv
    cert_pos, cert_neg = make_cert(A, m, n)
    tgtjson["cert_pos"] = cert_pos
    tgtjson["cert_neg"] = cert_neg
    if hirsch:
        origin, map_lbl, inv_lbl = make_dim_full(lbl_simpl, n)
        tgtjson["origin"] = origin
        tgtjson["map_lbl"] = map_lbl
        tgtjson["inv_lbl"] = inv_lbl
        start = make_start(G_simpl,m-n)
        tgtjson["start"] = start

    tgtdir = core.resource(name)
    
    with open(os.path.join(tgtdir, f"{name}.json"), "w") as stream:
        json.dump(tgtjson,stream, indent=2)

# --------------------------------------------------------------------
if __name__ == '__main__':
    main()
