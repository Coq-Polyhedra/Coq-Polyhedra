#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, json, tqdm

# --------------------------------------------------------------------
from .. import binreader

# --------------------------------------------------------------------
DESCRIPTORS = dict(
    A = "[[Q]]",
    b = "[Q]",
    bases = "[[I]]",
    pred = "[(I,I,I)]",
    root = "I",
    heap = "[Q]",
    init = "[[Q]]",
    graph_lex = "[[I]]",
    graph_vtx = "[[I]]",
    morph = "[I]",
    morph_inv = "[I]",
    edge_inv = "[[(I,I)]]",
    bound_pos = "[[Q]]",
    bound_neg = "[[Q]]",
    dim = "[I]",
    vtx_eq = "[[I]]"
)

DESCRIPTORS = {
    k: binreader.descriptor_of_string(v) for k, v in DESCRIPTORS.items()
}

# --------------------------------------------------------------------
def json2dict(name):
    srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)

    with open(os.path.join(srcdir, f'{name}.json')) as stream:
        contents = json.load(stream)
    
    return contents

def dict2bin(name,contents):
    srcdir = os.path.join(os.path.dirname(__file__), '..', '..', 'data', name)
    bindir = os.path.join(srcdir, 'bin')

    res = {}

    os.makedirs(bindir, exist_ok = True)
    for key, descr in tqdm.tqdm(DESCRIPTORS.items(), desc="Serializing certificates : "):
        if key not in contents:
            print(f'Ignoring {key}', file = sys.stderr)
            continue
        binfile = os.path.join(bindir, f'{key}.bin')
        with open(binfile, 'w+b') as stream:
            descr.descriptor(stream)
            descr.pickle(contents[key], stream)
        res[f"Size of {key}.bin"] = os.path.getsize(binfile)
    return res

def main(name):
    dict2bin(name,json2dict(name))
# --------------------------------------------------------------------
if __name__ == '__main__':
    if len(sys.argv)-1 != 1:
        print('Usage: convert [file]', file = sys.stderr)
        exit(1)

    name = sys.argv[1]
    main(name)
