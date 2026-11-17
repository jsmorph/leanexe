# /// script
# requires-python = ">=3.12"
# ///
"""Check the generated Linux call table against a second, independent lowering of the pinned
syzlang descriptions.

Usage: uv run python -I tests/linux/syzlang-lowering.py [SYZLANG_DIR [CALL_TABLE]]

The lowering below was written from sys.txt, sys.txt.const, and syzkaller's pkg/compiler/gen.go
and const_file.go for the first review of the design of step 5, without the generator
`tools/linux-calls.py`, and extended for openat2, exit_group, and the x86-64 numbers.  It reads
sys.txt and sys.txt.const of SYZLANG_DIR (by default tests/linux/syzlang), lowers the calls of
CALLS, and compares them with CALL_TABLE (by default LeanExe/Linux/CallTable.lean): the names and
order of `table`, each description's numbers on arm64 and amd64, its kinds, whether it returns a
descriptor, and whether it ends the process; the layout of each structure that a description
names; and the right sides of each `regions_` lemma.  It exits with status 1 on a difference.
"""
import re
import sys
from pathlib import Path

CALLS = ["openat", "close", "read", "write", "exit_group", "clock_gettime", "getrandom",
         "openat2"]
TERMINAL = {"exit_group"}
ARCHES = ["arm64", "amd64"]
PTR = 8
INT_SIZES = {"int8": 1, "int16": 2, "int32": 4, "int64": 8, "intptr": PTR}


def parse_consts(path):
    arches, out = None, {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        name, _, val = (s.strip() for s in line.partition("="))
        if arches is None:
            assert name == "arches"
            arches = [a.strip() for a in val.split(",")]
            continue
        vals, default = {}, None
        for pair in val.split(","):
            fields = [f.strip() for f in pair.split(":")]
            if len(fields) == 1:
                default = fields[0]
            else:
                for a in fields[:-1]:
                    vals[a] = fields[-1]
        out[name] = {}
        for arch in ARCHES:
            v = vals.get(arch, default)
            if v is not None and v != "???":
                out[name][arch] = int(v, 0)
    return out


def split_top(s, sep=","):
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def parse_type(t):
    m = re.fullmatch(r"(\w+)(?:\[(.*)\])?", t.strip())
    assert m, t
    return m.group(1), split_top(m.group(2)) if m.group(2) else []


def parse_sys(path):
    resources, structs, calls = {}, {}, {}
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].split("#")[0].rstrip()
        m = re.fullmatch(r"resource (\w+)\[(\w+)\](?::\s*(.*))?", line)
        if m:
            values = [v.strip() for v in (m.group(3) or "").split(",") if v.strip()]
            resources[m.group(1)] = (m.group(2), values, i + 1)
        m = re.fullmatch(r"(\w+) \{", line)
        if m:
            fields, j = [], i + 1
            while not lines[j].strip().startswith("}"):
                f = lines[j].split("#")[0].split()
                if f:
                    fields.append((f[0], " ".join(f[1:])))
                j += 1
            structs[m.group(1)] = (fields, lines[j].strip(), i + 1, j + 1)
            i = j
        m = re.fullmatch(r"(\w+)\((.*)\)\s*(\w+)?(?:\s*\(.*\))?", line)
        if m and m.group(1) in CALLS:
            args = []
            for a in split_top(m.group(2)):
                name, _, typ = a.partition(" ")
                args.append((name, typ.strip()))
            assert m.group(1) not in calls, m.group(1)
            calls[m.group(1)] = (args, m.group(3), i + 1)
        i += 1
    return resources, structs, calls


def resource_chain(resources, r):
    chain, vals = [], []
    while r in resources:
        base, v, _ = resources[r]
        chain.append(r)
        vals = v + vals
        r = base
    return chain, r, vals


def field_size(resources, t):
    name, params = parse_type(t)
    if name in INT_SIZES:
        return INT_SIZES[name]
    if name in ("flags", "const"):
        return INT_SIZES[params[1]]
    if name in resources:
        return INT_SIZES[resource_chain(resources, name)[1]]
    raise ValueError(t)


def layout(structs, resources, name):
    fields, close, first, last = structs[name]
    assert close == "}", close
    off, align, out = 0, 1, []
    for fname, ft in fields:
        s = field_size(resources, ft)
        off = (off + s - 1) // s * s
        out.append((fname, off, s))
        off += s
        align = max(align, s)
    return (name, (off + align - 1) // align * align, align, out, first, last)


def lower(resources, structs, calls, consts):
    out, layouts = {}, {}
    for c in CALLS:
        args, ret, _ = calls[c]
        kinds, used = [], set()
        for k, (name, typ) in enumerate(args):
            if k in used:
                continue
            tname, params = parse_type(typ)
            nxt = args[k + 1] if k + 1 < len(args) else None
            if tname in resources:
                chain, _, special = resource_chain(resources, tname)
                assert "fd" in chain, (c, typ)
                opt = "opt" in params
                assert not opt or "AT_FDCWD" in special, (c, typ)
                kinds.append("dirfd" if opt else "fd")
            elif tname == "ptr" and params[1] == "filename":
                assert params[0] == "in" and len(params) == 2, (c, typ)
                kinds.append("path")
            elif tname == "buffer":
                assert nxt and parse_type(nxt[1]) == ("len", [name]), (c, name)
                used.add(k + 1)
                kinds.append("output" if params[0] == "out" else "input")
            elif tname == "ptr" and params[0] == "in":
                assert nxt and parse_type(nxt[1]) == ("bytesize", [name]), (c, name)
                assert len(params) == 2 and params[1] in structs, (c, typ)
                used.add(k + 1)
                layouts[params[1]] = layout(structs, resources, params[1])
                kinds.append("input")
            elif tname == "ptr":
                assert params[0] == "out" and len(params) == 2, (c, typ)
                lay = layout(structs, resources, params[1])
                layouts[params[1]] = lay
                kinds.append(f"record {lay[1]}")
            elif tname in ("flags", "const") or tname in INT_SIZES:
                kinds.append("value")
            else:
                raise ValueError((c, typ))
        opens = ret is not None and "fd" in resource_chain(resources, ret)[0]
        numbers = tuple(consts["__NR_" + c][arch] for arch in ARCHES)
        out[c] = (numbers, kinds, opens, c in TERMINAL)
    return out, layouts


def regions(kinds):
    """The right sides of a call's region lemma: its input regions and its output regions."""
    ins, outs, w = [], [], 0
    for kind in kinds:
        if kind == "path":
            ins.append(f"(x{w}, I.pathLength m x{w})")
        elif kind == "input":
            ins.append(f"(x{w}, x{w + 1}.toNat)")
        elif kind == "output":
            outs.append(f"(x{w}, x{w + 1}.toNat)")
        elif kind.startswith("record "):
            outs.append(f"(x{w}, {kind.split()[1]})")
        w += 2 if kind in ("input", "output") else 1
    return "[" + ", ".join(ins) + "]", "[" + ", ".join(outs) + "]"


def camel(name):
    head, *rest = name.split("_")
    return head + "".join(p.capitalize() for p in rest)


DESCRIPTION = re.compile(r'def (\w+)Call : Call :=\s*⟨"(\w+)", (\d+), (\d+), \[([^\]]*)\], '
                         r'(true|false), (true|false)⟩')
LAYOUT = re.compile(r'def (\w+)Layout : Layout :=\s*⟨"(\w+)", (\d+), (\d+), \[(.*?)\]⟩')
FIELD = re.compile(r'⟨"(\w+)", (\d+), (\d+)⟩')
DOC = re.compile(r"/-- `(\w+)` \(`sys.txt` lines (\d+) to (\d+)\)")
LEMMA = re.compile(r"theorem regions_(\w+) .*?inputRegions I m \[[^\]]*\] 0 (\w+)Call\.params =\s*"
                   r"(\[.*?\]) ∧\s*outputRegions \[[^\]]*\] 0 (\w+)Call\.params =\s*(\[.*?\]) "
                   r":= ⟨rfl, rfl⟩", re.S)


def main():
    syz = Path(sys.argv[1] if len(sys.argv) > 1 else "tests/linux/syzlang")
    table = Path(sys.argv[2] if len(sys.argv) > 2 else "LeanExe/Linux/CallTable.lean")
    resources, structs, calls = parse_sys(syz / "sys.txt")
    consts = parse_consts(syz / "sys.txt.const")
    expected, layouts = lower(resources, structs, calls, consts)
    text = table.read_text()
    failures = []
    described = {}
    for lean, name, arm64, amd64, params, opens, terminal in DESCRIPTION.findall(text):
        if name in described:
            failures.append(f"{name}: described twice")
        if lean != camel(name):
            failures.append(f"{name}: named {lean}Call")
        kinds = [p.strip().lstrip(".") for p in params.split(",") if p.strip()]
        described[name] = ((int(arm64), int(amd64)), kinds, opens == "true", terminal == "true")
    for name in sorted(set(expected) | set(described)):
        if name not in described:
            failures.append(f"{name}: admitted but not described")
        elif name not in expected:
            failures.append(f"{name}: described but not admitted")
        elif described[name] != expected[name]:
            failures.append(f"{name}: described {described[name]}, "
                            f"independent lowering {expected[name]}")
    listed = re.search(r"def table : List Call :=\s*\[([^\]]*)\]", text)
    names = [n.strip() for n in listed.group(1).split(",")] if listed else []
    if names != [f"{camel(c)}Call" for c in CALLS]:
        failures.append(f"table lists {names}")
    found = {}
    for lean, name, size, align, fields in LAYOUT.findall(text):
        found[name] = (name, int(size), int(align),
                       [(f, int(o), int(w)) for f, o, w in FIELD.findall(fields)])
        if lean != camel(name):
            failures.append(f"layout {name}: named {lean}Layout")
    lines = {name: (int(first), int(last)) for name, first, last in DOC.findall(text)}
    for name in sorted(set(layouts) | set(found)):
        want = layouts.get(name)
        if want is None or found.get(name) != want[:4]:
            failures.append(f"layout {name}: described {found.get(name)}, independent lowering "
                            f"{want and want[:4]}")
        elif lines.get(name) != want[4:]:
            failures.append(f"layout {name}: lines {lines.get(name)}, independent lowering "
                            f"{want[4:]}")
    lemmas = {}
    for name, first, inputs, second, outputs in LEMMA.findall(text):
        if not first == second == name:
            failures.append(f"regions_{name}: states the regions of {first} and {second}")
        lemmas[name] = (inputs, outputs)
    for c in CALLS:
        want = regions(expected[c][1])
        if lemmas.get(camel(c)) != want:
            failures.append(f"regions_{camel(c)}: states {lemmas.get(camel(c))}, independent "
                            f"lowering {want}")
    for failure in failures:
        print(failure)
    print(f"{len(described)} descriptions, {len(found)} layouts, and {len(lemmas)} region lemmas "
          f"checked against the independent lowering")
    sys.exit(1 if failures else 0)


main()
