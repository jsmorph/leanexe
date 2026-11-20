# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Copies the Isla trace on standard input to standard output with the fields of each struct value
sorted by name, and every other character unchanged.  Isla e9b5d945 holds a struct's fields in a
HashMap with ahash's RandomState (isla-lib/src/ir.rs line 247) and prints them in the map's
iteration order (lines 376-391).  ahash 0.8.11, with its default feature runtime-rng, derives the
keys of every RandomState from bytes that getrandom draws once per process (src/random_state.rs
lines 73-85 and 239-243), so the order of a struct's fields changes from run to run.  The trace
scripts of tests/isla pass Isla's output through this script, so that the trace of a form depends
only on the inputs of Isla's run.  The script fails on a struct whose text differs from Isla's layout,
"(_ struct (|f| v) (|g| w))" with one space between fields, and on a symbolic constructor
"(_ ctor ...)", whose possibilities Isla also prints from a hash map (ir.rs lines 397-412) and
which no committed trace holds.
"""

import re
import sys

TOKEN = re.compile(r'[()]|\|[^|]*\||"[^"]*"|;[^\n]*')
FIELD = re.compile(r"\(\|([^|]*)\| ")


def render(parts: list[str], start: int) -> str:
    texts, kids = parts[0::2], parts[1::2]
    if texts[0].startswith("_ ctor"):
        raise ValueError(f"symbolic constructor at offset {start}")
    if not texts[0].startswith("_ struct") or texts == ["_ struct nil"]:
        return "(" + "".join(parts) + ")"
    if not kids or texts != ["_ struct "] + [" "] * (len(kids) - 1) + [""]:
        raise ValueError(f"struct at offset {start} without Isla's layout")
    names = []
    for kid in kids:
        m = FIELD.match(kid)
        if m is None:
            raise ValueError(f"struct at offset {start} with a field without a name")
        names.append(m.group(1))
    if len(set(names)) != len(names):
        raise ValueError(f"struct at offset {start} with a repeated field")
    fields = [kid for _, kid in sorted(zip(names, kids))]
    return "(_ struct " + " ".join(fields) + ")"


def canonical(text: str) -> str:
    frames: list[list[str]] = [[]]
    starts: list[int] = []
    pos = 0
    for m in TOKEN.finditer(text):
        if m.group() == "(":
            frames[-1].append(text[pos : m.start()])
            frames.append([])
            starts.append(m.start())
            pos = m.end()
        elif m.group() == ")":
            if not starts:
                raise ValueError(f"unmatched ) at offset {m.start()}")
            frames[-1].append(text[pos : m.start()])
            pos = m.end()
            parts = frames.pop()
            frames[-1].append(render(parts, starts.pop()))
    if starts:
        raise ValueError(f"unmatched ( at offset {starts[-1]}")
    frames[0].append(text[pos:])
    return "".join(frames[0])


def main() -> None:
    try:
        sys.stdout.write(canonical(sys.stdin.read()))
    except ValueError as e:
        sys.exit(f"canonical-trace: {e}")


if __name__ == "__main__":
    main()
