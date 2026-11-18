# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks that a run of the module of files-cases.py names only standard streams and descriptors
that the shim holds, the property `NamesHeld` of Verified/Shim/Descriptors.lean, from the run's
strace log of openat, openat2, close, read, and write.

Usage: files-names.py NAME LOG

The executable's startup calls `openat` on descriptor 3 and, when it returns a descriptor, closes
that descriptor; descriptor 3 is then held.  After the startup, the descriptor of each `read` and
`write` must be 0, 1, or 2 or held, and the descriptor of each `close` and the directory of each
`openat2` must be held.  An `openat2` that returns a descriptor adds it, and a `close` removes its
descriptor whatever its result.  Prints `pass` or `fail` with NAME and exits with status 1 on a
call that names another number or on a log without the startup's `openat`.
"""

import re
import sys

LINE = re.compile(r"^(openat2|openat|close|read|write)\((\d+)\b.*\)\s+=\s+(-?\d+)")


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit("usage: files-names.py NAME LOG")
    name, log = sys.argv[1:]
    held: set[int] = set()
    startup = None
    calls = 0
    bad = []
    for line in open(log):
        m = LINE.match(line)
        if not m:
            continue
        call, fd, result = m.group(1), int(m.group(2)), int(m.group(3))
        if startup is None:
            if call != "openat" or fd != 3:
                bad.append(f"before the startup's openat: {line.strip()}")
                break
            startup = result
            if result >= 0:
                held.add(3)
            continue
        if startup >= 0 and call == "close" and fd == startup:
            startup = -1
            continue
        calls += 1
        if call in ("read", "write"):
            if fd not in (0, 1, 2) and fd not in held:
                bad.append(line.strip())
        elif call in ("close", "openat2"):
            if fd not in held:
                bad.append(line.strip())
            if call == "close":
                held.discard(fd)
            elif result >= 0:
                held.add(result)
        else:
            bad.append(f"a second openat: {line.strip()}")
    if startup is None:
        bad.append("no openat of the startup")
    if bad:
        for b in bad:
            print(f"fail: {name}: {b}")
        sys.exit(1)
    print(f"pass: {name}: {calls} calls name only standard streams and held descriptors")


if __name__ == "__main__":
    main()
