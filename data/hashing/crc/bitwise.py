# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Write bitwise.txt: calls of the bitwise CRC-32 functions of Library.Hashing.Crc.Bitwise with
the results that Python's zlib.crc32 gives.

Each line names a function, its arguments as sixteen hexadecimal digits each, and the result as
eight: `reg R B RESULT` for crc32Reg, `byte CRC B RESULT` for crc32Byte, and `word CRC W N RESULT`
for crc32Word.  zlib.crc32(data, value) continues the CRC `value` of earlier bytes with `data`.  A
CRC argument with bits above the low 32 continues from its low 32 bits, a byte argument contributes
its low byte, and a word with the count N contributes its first min(N, 8) bytes from the most
significant.  The register of crc32Reg is the ones complement of a CRC, so its result is the
complement of zlib's CRC continued from the complemented register, for registers below 2^32.  The
script stops if zlib disagrees with the check value of the CRC catalogue.  Run it with
`uv run data/hashing/crc/bitwise.py`.
"""

import random
import sys
import zlib

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF

if zlib.crc32(b"123456789") != 0xCBF43926:
    sys.exit("zlib disagrees with the check value of the CRC catalogue")

rng = random.Random(3720)
check8 = zlib.crc32(b"12345678")

registers = [0, 1, 0x80000000, M32] + [rng.getrandbits(32) for _ in range(6)]
starts = [0, M32, check8, 0x5A5A5A5A, M64, 0x123456789ABCDEF0] + \
    [rng.getrandbits(32) for _ in range(6)]
byte_args = [0, 1, 0x31, 0x39, 0x7F, 0x80, 0xFF, 0x1234, M64, 0xFFFFFFFFFFFFFF00] + \
    [rng.getrandbits(8) for _ in range(5)]
words = [0, M64, 0x3132333435363738, 0x3900000000000000, 0x0102030405060708,
         0x8000000000000001] + [rng.getrandbits(64) for _ in range(6)]
counts = list(range(10)) + [2 ** 32 + 3, 2 ** 63, M64]


def reg(r, b):
    return zlib.crc32(bytes([b & 0xFF]), r ^ M32) ^ M32


def byte(crc, b):
    return zlib.crc32(bytes([b & 0xFF]), crc & M32)


def word(crc, w, n):
    return zlib.crc32(w.to_bytes(8, "big")[:min(n, 8)], crc & M32)


if word(word(0, 0x3132333435363738, 8), 0x3900000000000000, 1) != 0xCBF43926:
    sys.exit("the words of 123456789 do not give the check value")

out = ["# Calls of the bitwise CRC-32 with results by zlib.crc32; see NOTICE."]
for r in registers:
    for b in byte_args[:8]:
        out.append("reg %016x %016x %08x" % (r, b, reg(r, b)))
for crc in starts:
    for b in byte_args:
        out.append("byte %016x %016x %08x" % (crc, b, byte(crc, b)))
for i, w in enumerate(words):
    for j, n in enumerate(counts):
        crc = starts[(i + j) % len(starts)]
        out.append("word %016x %016x %016x %08x" % (crc, w, n, word(crc, w, n)))
out.append("word %016x %016x %016x %08x" % (check8, 0x3900000000000000, 1, 0xCBF43926))

with open(sys.argv[1] if len(sys.argv) > 1 else "data/hashing/crc/bitwise.txt", "w") as f:
    f.write("\n".join(out) + "\n")
