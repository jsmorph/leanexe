# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks the `openat2` calls of scenario 'f' of the module of files-cases.py against the `open_how`
records that the shim's specification gives.

Usage: files-flags.py FLAGS.txt STRACE.log

STRACE.log is the output of `strace -X raw -e trace=openat2` of the scenario.  Each call must name
descriptor 3, the path of the corresponding line of FLAGS.txt, its `flags` word, the mode 0666
exactly when the flags hold `O_CREAT`, the resolution 0xa, `RESOLVE_BENEATH` with
`RESOLVE_NO_MAGICLINKS`, and the size 24.  Prints `pass` or `fail` with the first difference.
"""

import re
import sys

CALL = re.compile(r'openat2\(3, "([^"]*)", \{flags=(0x[0-9a-f]+)(?:, mode=(0[0-7]*))?, '
                  r'resolve=(0x[0-9a-f]+)\}, 24\)')


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit("usage: files-flags.py FLAGS.txt STRACE.log")
    expected = [line.split() for line in open(sys.argv[1]) if line.strip()]
    calls = [line for line in open(sys.argv[2]) if "openat2(" in line]
    if len(calls) != len(expected):
        print(f"fail: the open_how records: {len(calls)} calls where {len(expected)} are due")
        sys.exit(1)
    for index, (line, (name, word)) in enumerate(zip(calls, expected)):
        found = CALL.search(line)
        flags = int(word, 16)
        mode = "0666" if flags & 0x40 else None
        if (found is None or found.group(1) != name or int(found.group(2), 16) != flags
                or found.group(3) != mode or found.group(4) != "0xa"):
            print(f"fail: the open_how records: call {index}, {line.strip()}, where {name} "
                  f"with flags {word} and mode {mode} is due")
            sys.exit(1)
    print(f"pass: the open_how records of {len(calls)} calls")


if __name__ == "__main__":
    main()
