# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Map the differences between two sail-arm source trees to the definitions of a translation.

Usage: uv run tools/sail/srcdiff.py OLD_SRC NEW_SRC LEAN_FILE FILE...

For each FILE, the script compares OLD_SRC/FILE with NEW_SRC/FILE line by line, assigns each
changed line to the top-level item that holds it (the last line before it that starts a
function, val, register, type, mapping, or other declaration at column 0), and prints one line
per item: the file, the item's name, whether LEAN_FILE defines it (`def`), mentions it
(`named`), or neither (`absent`), and the changed line numbers in each tree.  A missing file
counts as empty.
"""
import difflib
import re
import sys

old_dir, new_dir, lean_file = sys.argv[1], sys.argv[2], sys.argv[3]
files = sys.argv[4:]
start = re.compile(r"^(function|val|register|struct|enum|type|bitfield|overload|mapping|let|union|"
                   r"instantiation|scattered|end|termination_measure|\$)")
name_re = re.compile(r"^(?:function(?: clause)?|val|register|struct|enum|type|bitfield|overload|"
                     r"mapping|let|union|instantiation|termination_measure)\s+"
                     r"([A-Za-z_][A-Za-z0-9_']*)")
lean = open(lean_file).read()
lean_defs = set(re.findall(r"^(?:noncomputable )?def ([A-Za-z_][A-Za-z0-9_']*)", lean, re.M))
lean_words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", lean))


def owner(lines, i):
    for j in range(i, -1, -1):
        if start.match(lines[j]):
            m = name_re.match(lines[j])
            return (m.group(1) if m else lines[j].strip()[:60]), j + 1
    return "(file start)", 0


def read(path):
    try:
        return open(path).read().split("\n")
    except FileNotFoundError:
        return []


for f in files:
    a = read(f"{old_dir}/{f}")
    b = read(f"{new_dir}/{f}")
    items = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        for i in range(i1, max(i2, i1 + 1)):
            if a and i < len(a):
                n, line = owner(a, i)
                items.setdefault(n, set()).add(f"old {line}")
        for j in range(j1, max(j2, j1 + 1)):
            if b and j < len(b):
                n, line = owner(b, j)
                items.setdefault(n, set()).add(f"new {line}")
    for n in sorted(items):
        where = "def" if n in lean_defs else ("named" if n in lean_words else "absent")
        print(f"{f}\t{n}\t{where}\t{','.join(sorted(items[n]))}")
