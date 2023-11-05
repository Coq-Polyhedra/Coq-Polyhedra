#! /usr/bin/env python3

import json, os
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

def QQ_red(x):
    d = QQ.gcd(x.numerator,x.denominator)
    return QQ(x.numerator/d,x.denominator/d)

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

# Construct the graph of lex feasible bases + order of construction
# -------------------------------------------------------------------
def get_idx(graph_lex):
    Graph = nx.Graph({ i : tuple(graph_lex[i]) for i in range(len(graph_lex))})
    dic = nx.closeness_centrality(Graph)
    return max(dic,key=dic.get)

def get_initial_basing_point(A, bases, idx):
    base = bases[idx]
    A_I = [A[i] for i in base]
    gmp_A_I = to_gmp_matrix(A_I)
    inv = gmp_A_I.inv()
    return inv


def update(m, n, gmp_A, I, r, s, inv):
    res = [None for i in range(m)]
    v = [QQ(0) for i in range(n)]
    Ar = gmp_A[r,:]
    Mrs = (Ar * inv[I[s]])[0,0]
    u = inv[I[s]]
    res[r] = u/Mrs
    v[s] = (Mrs.element -1)/(Mrs.element)
    for k in range(n):
        if k != s:
            Mrk = (Ar * inv[I[k]])[0,0]
            res[I[k]] = (Mrs * inv[I[k]] - Mrk * inv[I[s]])/Mrs
            v[k] = Mrk.element / (Mrs.element)
    gmp_v = DomainMatrix([v],(1,n),QQ)
    return list_of_gmp_matrix(gmp_A * u * gmp_v),res
        

def get_lex_graph(A,bases):
    m,n = len(A), len(A[0])
    bases_dic = {frozenset(base) : i for (i,base) in enumerate(bases)}
    graph = [set() for _ in bases]
    for idx, base in enumerate(bases):
        reg = len(graph[idx])
        base_set = set(base)
        for i in base:
            if reg >= n:
                break
            for j in range(m):
                if j not in base_set:
                    nei_set = frozenset(base_set - {i} | {j})
                    if nei_set in bases_dic.keys(): 
                        idx_nei = bases_dic[nei_set]
                        if idx_nei not in graph[idx]:
                            graph[idx].add(idx_nei)
                            reg += 1
                            break
    return [sorted(elt) for elt in graph]

def enter_exit(I,J):
    IJ = I ^ J
    return (J & IJ).pop(), (I & IJ).pop()

def visit_lex_graph(A,bases,graph_lex,idx,inv):
    m,n = len(A), len(A[0])
    gmp_A = to_gmp_matrix(A)
    base_init = bases[idx]
    invs = [None for _ in bases]
    invs[idx] = [None for _ in range(m)]
    for k,Ik in enumerate(base_init): 
        invs[idx][Ik] = inv[:,k]
    pred = [(0,0,0) for _ in bases]
    pred_vect = [[['0']] for _ in bases]
    visited = [False for _ in bases]
    queue = [(idx,None)]
    counter = 0
    order = []
    pointer = 0
    while pointer < len(queue):
        idx_base, idx_pred = queue[pointer]
        if not visited[idx_base]:
            counter += 1
            visited[idx_base] = True
            for idx_nei in graph_lex[idx_base]:
                if not visited[idx_nei]:
                    queue.append((idx_nei, idx_base))
            if idx_pred is not None:
                order.append(idx_base)
                J = bases[idx_base]
                I = bases[idx_pred]
                r,s_ = enter_exit(set(I),set(J))
                s = I.index(s_)
                inv_pred = invs[idx_pred]
                M, inv_base = update(m,n,gmp_A,I,r,s,inv_pred)
                invs[idx_base] = inv_base
                pred[idx_base] = (idx_pred,r,s)
                pred_vect[idx_base] = M
        pointer += 1
    return order, pred, pred_vect


# def get_lex_graph(A,bases,idx,inv):
#     m,n = len(A), len(A[0])
#     gmp_A = to_gmp_matrix(A)
#     invs = [None for _ in bases]
#     base = bases[idx]
#     invs[idx] = [inv[:,i] if i in set(base) else None for i in range(len(A))]
#     bases_dic = {frozenset(base) : i for (i,base) in enumerate(bases)}
#     graph = [set() for _ in bases]
#     order = []
#     pred = [(0,0,0) for _ in bases]
#     pred_vect = [[['0']] for _ in bases]
#     visited = {i : False for i in bases_dic.keys()}
#     visited[frozenset(bases[idx])] = True
#     queue = [idx]
#     pointer = 0
#     while True:
#         if pointer >= len(queue):
#             break
#         idx_base = queue[pointer]
#         order.append(idx_base)
#         reg = len(graph[idx_base])
#         if reg < n:
#             base = bases[idx_base]
#             base_set = set(base)
#             for s in range(len(bases[idx_base])):
#                 for r in range(m):
#                     if r not in base_set:
#                         nei_set = frozenset(base_set - {base[s]} | {r})
#                         if nei_set in bases_dic:
#                             idx_nei = bases_dic[nei_set]
#                             graph[idx_base].add(idx_nei)
#                             if not visited[nei_set]:
#                                 visited[nei_set] = True
#                                 queue.append(idx_nei)
#                                 pred[idx_nei] = (idx_base,r,s)
#                                 M, inv = update(m, n, gmp_A, base, r, s, invs[idx_base])
#                                 invs[idx_nei] = inv
#                                 pred_vect[idx_nei] = M
#         pointer += 1
#         print(pointer)
#     return idx, [sorted(elt) for elt in graph], order[1:], pred, pred_vect

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------
def get_unsrt_vtx(bases,bas2vtx):
    vtx_list = [None for _ in bases]
    for i in range(len(bases)):
        bas = bases[i]
        vtx = bas2vtx[frozenset(bas)]
        vtx_list[i] = vtx
    return vtx_list

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

def get_dim_full(vtx, n):
    while True:
        map_lbl = rd.sample(range(len(vtx)), n+1)
        map_lbl.sort()
        M = sym.Matrix([list(map(fc.Fraction, vtx[i])) for i in list(map_lbl)[1:]])
        N = sym.Matrix([list(map(fc.Fraction, vtx[map_lbl[0]])) for _ in range(n)])
        Q = M - N
        Q_gmp = to_gmp_matrix(Q)
        Q_det = Q_gmp.det()
        if Q_det != 0:
            Q_inv = Q.gmp_inv()
            Q_res = list_of_gmp_matrix(Q_inv)
            return list(map_lbl)[0], list(map_lbl)[:1], Q_res


# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    return parser

# -------------------------------------------------------------------
def lrs2dict(name, hirsch=""):

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    A,b = poly_scale(A,b)
    bases, bas2vtx, bas2det = get_bases_from_lrs(name)
    print("Ok")
    # init = get_initial_basing_point(A, bases, idx)
    # m,n = len(A), len(A[0])
    graph_lex = get_lex_graph(A, bases)
    idx = get_idx(graph_lex)
    inv = get_initial_basing_point(A,bases,idx)

    order, pred, pred_vect = visit_lex_graph(A,bases,graph_lex,idx,inv)
    # idx, graph_lex, order, pred, pred_vect = get_lex_graph(A,bases,idx,inv)
    vtx = get_unsrt_vtx(bases, bas2vtx)

    # morph, morph_inv = get_morph(bases,vtx,bas2vtx)
    # graph_vtx = get_graph_vtx(graph_lex,morph,len(vtx))
    # edge_inv = get_edge_inv(graph_lex,graph_vtx,morph)
    # farkas_cert_pos, farkas_cert_neg = get_farkas_cert(A,m,n)


    # Store in a dictionnary

    tgtjson = {}
    tgtjson['A'] = A
    tgtjson['b'] = b
    tgtjson['bases'] = bases
    tgtjson['graph_lex'] = graph_lex
    tgtjson['idx'] = idx
    tgtjson['inv'] = list_of_gmp_matrix(inv)
    tgtjson['order'] = order
    tgtjson['steps'] = len(order)
    tgtjson['pred'] = pred
    tgtjson['pred_vect'] = pred_vect
    tgtjson['vtx'] = vtx
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