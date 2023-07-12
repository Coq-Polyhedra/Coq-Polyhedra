#! /usr/bin/env python3

# --------------------------------------------------------------------
import abc
import fractions
import json
import math
import os
import struct
import sys

# --------------------------------------------------------------------
class Descriptor(abc.ABC):
    @property
    @abc.abstractmethod
    def default(self):
        pass

    @abc.abstractmethod
    def pickle(self, value, stream):
        pass

    @abc.abstractmethod
    def descriptor(self, stream):
        pass

# --------------------------------------------------------------------
class D_Int63(Descriptor):
    default = property(lambda self : 0)

    def pickle(self, value, stream):
        assert(value in range(1 << 63))
        stream.write(struct.pack('<Q', value))

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x00))

D_Int63.INSTANCE = D_Int63()

# --------------------------------------------------------------------
class D_BigN(Descriptor):
    default = property(lambda self : 0)

    def pickle(self, value, stream):
        assert(value >= 0)
        nlimbs = 0 if value == 0 else (math.floor(math.log2(value)) + 1)
        nlimbs = 0 if nlimbs == 0 else ((nlimbs-1) // 63 + 1)
        D_Int63.INSTANCE.pickle(nlimbs, stream)
        for _ in range(nlimbs):
            assert(value != 0)
            D_Int63.INSTANCE.pickle(value & ((1 << 63) - 1), stream)
            value >>= 63
        assert(value == 0)

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x01))

D_BigN.INSTANCE = D_BigN()

# --------------------------------------------------------------------
class D_BigZ(Descriptor):
    default = property(lambda self : 0)

    def pickle(self, value, stream):
        stream.write(struct.pack('<Q', int(value >= 0)))
        D_BigN.INSTANCE.pickle(abs(value), stream)

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x02))

D_BigZ.INSTANCE = D_BigZ()

# --------------------------------------------------------------------
class D_BigQ(Descriptor):
    default = property(lambda self : fractions.Fraction(0, 1))

    def pickle(self, value, stream):
        if isinstance(value, str):
            value = fractions.Fraction(value) # Irk
        if isinstance(value, int):
            num, den = value, 1
        else:
            num, den = value.numerator, value.denominator
        D_BigZ.INSTANCE.pickle(num, stream)
        D_BigN.INSTANCE.pickle(den, stream)

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x03))

D_BigQ.INSTANCE = D_BigQ()

# --------------------------------------------------------------------
class D_Pair(Descriptor):
    def __init__(self, fst : Descriptor, snd : Descriptor):
        self._fst = fst
        self._snd = snd

    default = property(lambda self : (self._fst.default, self._snd.default))

    def pickle(self, value, stream):
        assert(len(value) >= 2)
        self._fst.pickle(value[0], stream)
        self._snd.pickle(value[1] if len(value) == 2 else value[1:], stream)

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x04))
        self._fst.descriptor(stream)
        self._snd.descriptor(stream)

# --------------------------------------------------------------------
class D_Array(Descriptor):
    def __init__(self, elem : Descriptor, default : any):
        self._elem    = elem
        self._default = default

    default = property(lambda self : [self._default])

    def pickle(self, value, stream):
        assert(len(value) < (1 << 63))
        D_Int63.INSTANCE.pickle(len(value), stream)
        self._elem.pickle(self._default, stream)
        for v in value:
            self._elem.pickle(v, stream)

    def descriptor(self, stream):
        stream.write(struct.pack('<Q', 0x05))
        self._elem.descriptor(stream)

# --------------------------------------------------------------------
def descriptor_of_string(s : str) -> Descriptor:
    def invalid_input(i : int):
        return ValueError(f'input = {s}, position = {i}')

    def doit(i : int):
        if i == len(s):
            raise invalid_input(i)
        if s[i] == 'I':
            return (D_Int63.INSTANCE, i+1)
        if s[i] == 'N':
            return (D_BigN.INSTANCE, i+1)
        if s[i] == 'Z':
            return (D_BigZ.INSTANCE, i+1)
        if s[i] == 'Q':
            return (D_BigQ.INSTANCE, i+1)

        if s[i] == '[':
            elem, i = doit(i+1)
            if i == len(s) or s[i] != ']':
                raise invalid_input(i)
            return (D_Array(elem, elem.default), i+1)

        if s[i] == '(':
            elem, i = doit(i+1); elems = [elem]
            while i < len(s) and s[i] == ',':
                elem, i = doit(i+1)
                elems.append(elem)
            if i == len(s) or s[i] != ')':
                raise invalid_input(i)
            if len(elems) == 0:
                raise invalid_input(i)
            while len(elems) > 1:
                snd = elems.pop()
                fst = elems.pop()
                elems.append(D_Pair(fst, snd))
            return elems[0], i+1

        raise invalid_input(i)

    return doit(0)[0]

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 != 2:
        print(f'Usage: {os.path.basename(sys.argv[0])} [file.json] [file.bin]')
        exit(1)

    jsonfile, binfile = sys.argv[1:]

    with open(jsonfile) as stream:
        data = json.load(stream)

    descriptor = descriptor_of_string(data['descriptor'])

    with open(binfile, 'w+b') as stream:
        descriptor.descriptor(stream)
        descriptor.pickle(data['data'], stream)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
