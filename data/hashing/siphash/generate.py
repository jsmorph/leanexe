# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Write vectors.txt: SipHash-2-4 and SipHash-1-3 by the SIPHASH MAC of OpenSSL 3.

Each line is `key tag24 tag13 message`: the 16-byte key in hexadecimal, the SipHash-2-4 and
SipHash-1-3 tags as sixteen hexadecimal digits of their 64-bit values, and the message in
hexadecimal, `-` when empty.  OpenSSL writes the tag's eight bytes from the least significant.
The keys and messages are pseudorandom.  The script stops if OpenSSL disagrees with the 64
SipHash-2-4 vectors of the reference implementation in vectors.h or with the test value of
Appendix A of the SipHash paper.  Run it with `uv run data/hashing/siphash/generate.py`.
"""

import random
import re
import subprocess
import sys

ROUNDS = {"2-4": (2, 4), "1-3": (1, 3)}


def openssl(variant, key, message):
    c, d = ROUNDS[variant]
    out = subprocess.run(
        ["openssl", "mac", "-macopt", "hexkey:" + key.hex(), "-macopt", "size:8",
         "-macopt", "c-rounds:%d" % c, "-macopt", "d-rounds:%d" % d, "SIPHASH"],
        input=message, capture_output=True, check=True).stdout
    return int.from_bytes(bytes.fromhex(out.decode().strip()), "little")


def reference(path):
    text = open(path).read()
    body = text[text.index("vectors_sip64"):text.index("vectors_sip128")]
    data = bytes(int(t, 16) for t in re.findall(r"0x([0-9a-f]{2})", body))
    return [int.from_bytes(data[8 * i:8 * i + 8], "little") for i in range(64)]


here = sys.argv[1] if len(sys.argv) > 1 else "data/hashing/siphash"
key = bytes(range(16))
for i, tag in enumerate(reference(here + "/vectors.h")):
    if openssl("2-4", key, bytes(range(i))) != tag:
        sys.exit("OpenSSL disagrees with vector %d of vectors.h" % i)
if openssl("2-4", key, bytes(range(15))) != 0xA129CA6149BE45E5:
    sys.exit("OpenSSL disagrees with Appendix A of the paper")

rng = random.Random(2012)
lengths = list(range(257)) + [511, 512, 513, 1000, 1023, 1024, 1025, 4095, 4096, 4097]
out = ["# SipHash-2-4 and SipHash-1-3 by OpenSSL; see NOTICE."]
for n in lengths:
    k = bytes(rng.randrange(256) for _ in range(16))
    m = bytes(rng.randrange(256) for _ in range(n))
    out.append("%s %016x %016x %s" % (k.hex(), openssl("2-4", k, m), openssl("1-3", k, m),
                                      m.hex() or "-"))

with open(here + "/vectors.txt", "w") as f:
    f.write("\n".join(out) + "\n")
