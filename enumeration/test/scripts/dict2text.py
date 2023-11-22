#! /usr/bin/env python3

# --------------------------------------------------------------------
import os

# --------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name}_DATA_TEXT)
 (theories Polyhedra PolyhedraHirsch)
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()

IMPORT = r'''
Require Import Uint63 PArray.
From Bignums Require Import BigQ.

(* -------------------------------------------------------------------- *)
Local Open Scope array_scope.
Local Notation int63 := Uint63.int.
'''.lstrip()

# --------------------------------------------------------------------
def printer(stream):
  def output(x):
    print(x,file=stream)
  return output

# --------------------------------------------------------------------
def bigQ2text(a):
  return a.replace('/', '#')

def int632text(a):
  return str(a)

def array2text(elt2text,dflt,scope):
  def job(a):
    return "[| " + "; ".join([elt2text(elt) for elt in a]) + f"|{dflt}|]{scope}"
  return job

def couple2text(elt12text, elt22text):
  def job(a):
    return "(" + elt12text(a[0]) + ", " + elt22text(a[1]) + ")"
  return job

# --------------------------------------------------------------------
default_int_arr = "[|0%uint63|0%uint63|]"
default_bigQ_arr = "[|0%bigQ|0%bigQ|]"
default_bigQ_mx = f"[|{default_bigQ_arr}|{default_bigQ_arr}|]"
default_lbl_lex = f"({default_int_arr},{default_bigQ_mx})"
default_edge_inv = "[|(0,0)|(0,0)|]"
bigQ_scope = "%bigQ"
int63_scope = "%uint63"

TYPE = dict(
    Po        = 'array (array bigQ) * (array bigQ)',
    lbl_lex   = 'array (array int63 * array (array bigQ))',
    lbl_vtx = 'array (array bigQ)',
    G_lex     = 'array (array int63)',
    G_vtx     = 'array (array int63)',
    morph      = 'array int63',
    morph_inv  = 'array int63',
    edge_inv  = 'array (array (int63 * int63))',
    bound_pos  = 'array (array bigQ)',
    bound_neg  = 'array (array bigQ)',
    origin    = 'int63',
    start     = 'int63',
    map_dim   = 'array int63',
    inv_dim   = 'array (array bigQ)',
)

TEXT = dict(
  Po = couple2text(
    array2text(array2text(bigQ2text,"0",""),"[|0|0|]", bigQ_scope),
    array2text(bigQ2text, "0", bigQ_scope)),

  lbl_lex = array2text(
    couple2text(
      array2text(int632text, "0",int63_scope), 
      array2text(
        array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope)),default_lbl_lex,""),
  
  lbl_vtx = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  G_lex = array2text(array2text(int632text,"0",""),default_int_arr,int63_scope),
  G_vtx = array2text(array2text(int632text,"0",""),default_int_arr,int63_scope),
  morph = array2text(int632text,"0",int63_scope),
  morph_inv = array2text(int632text,"0",int63_scope),
  edge_inv = array2text(array2text(couple2text(int632text,int632text),"(0,0)",""),default_edge_inv,int63_scope),
  bound_pos = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  bound_neg = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  origin = int632text,
  start = int632text,
  map_dim = array2text(int632text,"0",int63_scope),
  inv_dim = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope)
)
# --------------------------------------------------------------------

def dict2text(name, contents):
  srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)
  coqdir = os.path.join(srcdir, "coq_text")

  os.makedirs(coqdir, exist_ok = True)
  res = {}
  for key, value in contents.items():
    if key not in TYPE.keys():
      print("Error, dictionary contains invalid data")
      exit(1)
    tgtfile = os.path.join(coqdir, f"{key}.v")
    with open(tgtfile, "w") as stream:
      output = printer(stream)
      stream.write(IMPORT)
      output(f"Definition {key} : {TYPE[key]} := Eval vm_compute in")
      output(TEXT[key](value) + ".")
    res[f"Size of {key}.v"] = float(os.path.getsize(tgtfile)/1000000)
  with open(os.path.join(coqdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = name.upper()))
  return res
      



    