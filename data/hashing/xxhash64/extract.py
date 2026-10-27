# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Write xxh64.txt from the xxHash repository's tests/sanity_test_vectors.h.

Each line of XSUM_XXH64_testdata, `{ len, seed, result }`, becomes `len seed result`, with the
seed and the result as sixteen hexadecimal digits.  Run it with
`uv run data/hashing/xxhash64/extract.py PATH/sanity_test_vectors.h`.
"""

import re
import sys

text = open(sys.argv[1]).read()
body = text[text.index("XSUM_XXH64_testdata[] = {"):]
body = body[:body.index("};")]
rows = re.findall(r"\{\s*(\d+),\s*0x([0-9A-F]{16})ULL,\s*0x([0-9A-F]{16})ULL\s*\}", body)
out = ["# XXH64 vectors of xxHash's tests/sanity_test_vectors.h; see NOTICE."]
out += ["%s %s %s" % (n, s.lower(), r.lower()) for n, s, r in rows]
with open(sys.argv[2] if len(sys.argv) > 2 else "data/hashing/xxhash64/xxh64.txt", "w") as f:
    f.write("\n".join(out) + "\n")
