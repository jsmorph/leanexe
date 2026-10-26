"""Write vectors.txt: CRC-32 by Python's zlib and CRC-32C by the Linux kernel's crypto API.

Each line is `label crc32 crc32c message`, with the CRCs as eight hexadecimal digits of the value
and the message in hexadecimal, `-` when empty.  The labels are `catalogue` for the check string
of the CRC catalogue, `rfc3720` for the examples of RFC 3720 Appendix B.4, and `random` for
pseudorandom messages.  The script stops if zlib or the kernel disagrees with the values that
those sources publish.  Run it with `python3 -I data/hashing/crc/generate.py` on Linux.
"""

import random
import socket
import sys
import zlib


def crc32c(data):
    with socket.socket(socket.AF_ALG, socket.SOCK_SEQPACKET, 0) as s:
        s.bind(("hash", "crc32c"))
        op, _ = s.accept()
        with op:
            op.sendall(data)
            return int.from_bytes(op.recv(4), "little")


def le(text):
    return int.from_bytes(bytes.fromhex(text), "little")


catalogue = [(b"123456789", 0xCBF43926, 0xE3069283)]

read10 = bytes.fromhex(
    "01c00000" "00000000" "00000000" "00000000" "14000000" "00000400"
    "00000014" "00000018" "28000000" "00000000" "02000000" "00000000")

rfc3720 = [
    (bytes(32), le("aa36918a")),
    (bytes([0xFF] * 32), le("43aba862")),
    (bytes(range(32)), le("4e79dd46")),
    (bytes(range(31, -1, -1)), le("5cdb3f11")),
    (read10, le("563a96d9")),
]

rng = random.Random(3720)
lengths = list(range(257)) + [511, 512, 513, 1000, 1023, 1024, 1025, 4095, 4096, 4097]
messages = [bytes(rng.randrange(256) for _ in range(n)) for n in lengths]


def line(label, m):
    return "%s %08x %08x %s" % (label, zlib.crc32(m), crc32c(m), m.hex() or "-")


out = ["# CRC-32 by zlib and CRC-32C by the Linux kernel; see NOTICE."]
for m, a, c in catalogue:
    if (zlib.crc32(m), crc32c(m)) != (a, c):
        sys.exit("the catalogue's check values disagree")
    out.append(line("catalogue", m))
for m, c in rfc3720:
    if crc32c(m) != c:
        sys.exit("an example of RFC 3720 disagrees")
    out.append(line("rfc3720", m))
for m in messages:
    out.append(line("random", m))

with open(sys.argv[1] if len(sys.argv) > 1 else "data/hashing/crc/vectors.txt", "w") as f:
    f.write("\n".join(out) + "\n")
