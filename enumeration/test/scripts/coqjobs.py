#! /usr/bin/env python3

# --------------------------------------------------------------------
import json, sys, re, os, argparse as argp
import subprocess as sp, shutil as sh

from . import core

# --------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name}_{job})
 (theories Polyhedra PolyhedraHirsch {name}_DATA{validation})
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()

# --------------------------------------------------------------------
JOBS = ('Diameter', 'Hirsch', 'Validation', 'Exact')
COMPIL = ('vm_compute', 'compute')
COMPIL_TARGET = {'vm_compute' : 'vm_cast_no_check', 'compute' : 'exact_no_check'}

# --------------------------------------------------------------------
def usage_and_exit():
    print(f'Usage: {sys.argv[0]} [NAME] {"|".join(JOBS)} {"|".join(COMPIL)}')
    exit(1)

# --------------------------------------------------------------------
def parse_args():
    if len(sys.argv)-1 != 3:
        usage_and_exit()
    name, job, compil = sys.argv[1:]
    if job not in JOBS or compil not in COMPIL:
        usage_and_exit()
    return name, job, compil

# --------------------------------------------------------------------
def main(name, job):

    srcdir = os.path.join(os.path.dirname(__file__), '..', 'jobs', job)
    jobdir = core.resource(name, f'coq_{job}')

    os.makedirs(jobdir, exist_ok=True)

    for filename in os.listdir(srcdir):
        if os.path.splitext(filename)[1] != '.v':
            continue
        with open(os.path.join(srcdir, filename)) as stream:
            contents = stream.read()
        contents = contents.replace('__DATA__', f'{name.upper()}_DATA')
        contents = contents.replace('__VALIDATION__', f'{name.upper()}_VALIDATION')
        contents = contents.replace('__NAME__', f'{name}')
        contents = contents.replace('__VALUE__', f'{21 if name == "poly20dim21" else 24}')
        with open(os.path.join(jobdir, filename), 'w') as stream:
            stream.write(contents)

    with open(os.path.join(jobdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = name.upper(), job = job.upper(), validation = "" if job not in ["Exact","Hirsch"] else f" {name.upper()}_VALIDATION"))

# --------------------------------------------------------------------
if __name__ == "__main__":
    name, job, compil = parse_args()
    main(name,job,compil)
