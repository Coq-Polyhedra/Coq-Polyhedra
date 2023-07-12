#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, json
import tqdm
import struct
import gc

# --------------------------------------------------------------------
sys.path.append(os.path.realpath(os.path.join(
    os.path.dirname(__file__),
    *'../../binreader/scripts'.split('/')
)))

from . import binreader

# --------------------------------------------------------------------
DESCRIPTORS = dict(
    Po        = '([[Q]],[Q])',
    lbl_lex   = '[([I],[[Q]])]',
    lbl_vtx = '[[Q]]',
    G_lex     = '[[I]]',
    G_vtx   = '[[I]]',
    morph      = '[I]',
    morph_inv  = '[I]',
    edge_inv  = '[[(I,I)]]',
    bound_pos  = '[[Q]]',
    bound_neg  = '[[Q]]',
    origin    = 'I',
    start     = 'I',
    map_dim   = '[I]',
    inv_dim   = '[[Q]]',
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
    srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)
    bindir = os.path.join(srcdir, 'bin')

    os.makedirs(bindir, exist_ok = True)
    for key, descr in tqdm.tqdm(DESCRIPTORS.items(), desc="Serializing certificates : "):
        if key not in contents:
            print(f'Ignoring {key}', file = sys.stderr)
            continue
        with open(os.path.join(bindir, f'{key}.bin'), 'w+b') as stream:
            descr.descriptor(stream)
            descr.pickle(contents[key], stream)

def main(name):
    dict2bin(name,json2dict(name))
# --------------------------------------------------------------------
if __name__ == '__main__':
    if len(sys.argv)-1 != 1:
        print('Usage: convert [file]', file = sys.stderr)
        exit(1)

    name = sys.argv[1]
    main(name)
