# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes the expected output of each case of `edges.txt` that `a64-wasi emit` writes, from the
shim's specification of `args_sizes_get` and `args_get` (`sizesInvoke` and `stringsInvoke` of
Verified/Shim/Strings.lean): `strings-edges.py EDGES OUTDIR ARG...` writes OUTDIR/NAME.want for
each case and prints `NAME 0` for a return and `NAME 2` for a trap, the status of a trap.  The
memory is one page of zeros with the byte 0xAA from 0x100 to 0x200 and from 0xFF00 to 0x10000, as
the modules' data places it.  A return writes the errno's four bytes and the 256 bytes of the
case's window; a trap writes nothing.  The arguments are byte strings without their zeros."""
import os
import sys

SIZE = 65536


def initial():
    mem = bytearray(SIZE)
    mem[0x100:0x200] = b"\xaa" * 256
    mem[0xFF00:0x10000] = b"\xaa" * 256
    return mem


def le4(value):
    return (value % 2**32).to_bytes(4, "little")


def main():
    edges, outdir, args = sys.argv[1], sys.argv[2], [os.fsencode(a) for a in sys.argv[3:]]
    count = len(args)
    size = sum(len(a) + 1 for a in args)
    for line in open(edges, encoding="utf-8"):
        name, kind, p, q, window = line.split()
        p, q, window = int(p), int(q), int(window)
        mem = initial()
        if kind == "sizes":
            if not (p + 4 <= SIZE and q + 4 <= SIZE):
                print(name, 2)
                open(os.path.join(outdir, name + ".want"), "wb").close()
                continue
            mem[p : p + 4] = le4(count)
            mem[q : q + 4] = le4(size)
        else:
            if not (p + 4 * count <= SIZE and q + size <= SIZE):
                print(name, 2)
                open(os.path.join(outdir, name + ".want"), "wb").close()
                continue
            offset = 0
            for i, a in enumerate(args):
                mem[p + 4 * i : p + 4 * i + 4] = le4(q + offset)
                offset += len(a) + 1
            strings = b"".join(a + b"\0" for a in args)
            mem[q : q + len(strings)] = strings
        with open(os.path.join(outdir, name + ".want"), "wb") as f:
            f.write(le4(0) + bytes(mem[window : window + 256]))
        print(name, 0)


main()
