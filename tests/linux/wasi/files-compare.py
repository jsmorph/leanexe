# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compares two runs of a scenario of the module of files-cases.py, case by case.

Usage: files-compare.py CASES.txt EXPECTED.txt SCENARIO NAME A.out B.out

Splits each output at the bytes 0xFE that start the cases and compares the cases in order,
reading their descriptions from CASES.txt.  EXPECTED.txt lists the cases whose outputs may differ,
one per line as the scenario, the description, and the reason, separated by tabs; lines that
start with `#` are comments.  Prints `pass` or `fail` with NAME, each difference, and each
expected difference that did not occur, and exits with status 1 when a run has the wrong number
of cases or a case differs that EXPECTED.txt does not list.
"""

import sys


def cases(path: str) -> list[bytes]:
    data = open(path, "rb").read()
    return data.split(b"\xfe")[1:]


def show(record: bytes) -> str:
    return " ".join(f"{b:02x}" for b in record)


def main() -> None:
    if len(sys.argv) != 7:
        sys.exit("usage: files-compare.py CASES.txt EXPECTED.txt SCENARIO NAME A.out B.out")
    cases_path, expected_path, scenario, name, a_path, b_path = sys.argv[1:]
    descriptions = [line.rstrip("\n").split("\t")[2] for line in open(cases_path)
                    if line.split("\t")[0] == scenario]
    expected = {}
    for line in open(expected_path):
        if line.startswith("#") or not line.strip():
            continue
        s, description, reason = line.rstrip("\n").split("\t")
        if s == scenario:
            expected[description] = reason
    a, b = cases(a_path), cases(b_path)
    status = 0
    if len(a) != len(descriptions) or len(b) != len(descriptions):
        print(f"fail: {name}: {len(a)} and {len(b)} cases where {len(descriptions)} are due")
        status = 1
    seen = set()
    for index, (x, y) in enumerate(zip(a, b)):
        if x == y:
            continue
        description = descriptions[index]
        if description in expected:
            seen.add(description)
            print(f"note: {name}: case {index}, {description}: {show(x)} | {show(y)}, "
                  f"as expected: {expected[description]}")
        else:
            print(f"fail: {name}: case {index}, {description}: {show(x)} | {show(y)}")
            status = 1
    for description in expected:
        if description not in seen and description in descriptions[:min(len(a), len(b))]:
            print(f"note: {name}: {description}: no difference, where one is expected")
    if status == 0:
        print(f"pass: {name}: {len(a)} cases agree but for those expected")
    sys.exit(status)


if __name__ == "__main__":
    main()
