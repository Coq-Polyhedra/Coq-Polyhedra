#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, subprocess as sp, os

from core import *

# --------------------------------------------------------------------
KINDS = dict(
    cube    = 1,
    cross   = 1,
    cyclic  = 2,
)

# --------------------------------------------------------------------
def usage_and_exit():
    kinds  = ', '.join([f'{k}:{v}' for k, v in KINDS.items()])
    # checks = ', '.join(CHECKS)

    print(f'Usage: {sys.argv[0]} [kind] <params...>')
    print(f'  kind in [{kinds}]')

    exit(1)

# --------------------------------------------------------------------
def parse_args():
    if len(sys.argv)-1 < 1:
        usage_and_exit()

    kind = sys.argv[1]
    args = sys.argv[2:]

    if kind not in KINDS:
        usage_and_exit()

    if len(args) != KINDS[kind]:
        usage_and_exit()

    try:
        args = [int(x) for x in args]
    except ValueError:
        usage_and_exit()

    if not all(x > 0 for x in args):
        usage_and_exit()

    return kind, args

# --------------------------------------------------------------------
def exec_(prgm, *args):
    cmd = [prgm] + list(args)
    print(f'=====> {" ".join(cmd)}', file=sys.stderr)
    sp.check_call(cmd)

# --------------------------------------------------------------------
def main():
    kind, args = parse_args()
    fname = "_".join([kind] + [str(x) for x in args])

    def bin(name):
        root = os.path.realpath(os.path.dirname(__file__))
        return os.path.join(root, name)

    outdir = resource(fname)

    if os.path.exists(outdir):
        print(f'Remove {outdir} first', file=sys.stderr)
        exit(1)

    os.makedirs(outdir)

    with open(os.path.join(outdir, "dune"), "w") as stream:
        print('(dirs coq coq_*)', file=stream)

    exec_(bin("genlrs.py"), kind, *[str(x) for x in args])
    exec_(bin("lrs2json.py"), fname)
    exec_(bin("json2coq.py"), fname)

# --------------------------------------------------------------------
if __name__ == "__main__":
    main()
