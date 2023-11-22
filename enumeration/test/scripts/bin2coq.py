#! /usr/bin/env python3

# --------------------------------------------------------------------------------
import os, sys

# --------------------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name}_DATA)
 (theories Polyhedra PolyhedraHirsch)
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()
# --------------------------------------------------------------------------------
def usage_and_exit():
    print(f'Usage: {sys.argv[0]} [NAME]')
    exit(1)

def bin2coq(name):
    
    srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)
    tgtdir = os.path.join(srcdir, 'coq')
    bindir = os.path.join(srcdir,'bin')

    os.makedirs(tgtdir, exist_ok = True)

    def writer(stream):
        def output(str=''): 
            print(str,file=stream)
        return output

    for binfile in os.listdir(bindir):
        certname,ext = os.path.splitext(binfile) 
        if ext != ".bin":
            print(f"remove any non binary file in {os.path.join(name, 'bin')}")
            exit(1)
        with open(os.path.join(tgtdir,f"{certname}.v"), "w") as stream:
            output = writer(stream)
            output("From BinReader Require Import BinReader.")
            output()
            output(f'LoadData "../../enumeration/test/data/{name}/bin/{certname}.bin" As {certname}.')
    
    with open(os.path.join(tgtdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = name.upper()))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        usage_and_exit()
    name = sys.argv[1]
    main(name) 


