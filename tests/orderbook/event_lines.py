# /// script
# requires-python = ">=3.10"
# ///
"""Print a file of little-endian unsigned 64-bit words as event records, one
`event W0 W1 W2 W3 W4 W5 W6` line for each seven words, in the format of
reference.py.  A file whose length is not a multiple of 56 bytes produces a
message on stderr and exit status 2."""

import struct
import sys


def main():
    if len(sys.argv) != 2:
        print("usage: event_lines.py FILE", file=sys.stderr)
        sys.exit(2)
    with open(sys.argv[1], "rb") as f:
        data = f.read()
    if len(data) % 56 != 0:
        print(f"event_lines.py: {sys.argv[1]}: length {len(data)} is not a multiple of 56",
              file=sys.stderr)
        sys.exit(2)
    lines = []
    for offset in range(0, len(data), 56):
        words = struct.unpack_from("<7Q", data, offset)
        lines.append("event " + " ".join(str(w) for w in words) + "\n")
    sys.stdout.write("".join(lines))


if __name__ == "__main__":
    main()
