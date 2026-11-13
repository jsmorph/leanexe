# /// script
# requires-python = ">=3.12"
# ///
"""Check the generated flat call descriptions against a second, independent lowering of the
pinned Preview 1 witx.

Usage: uv run tests/wasi/witx-lowering.py [WITX_DIR [CALL_TABLE]]

The lowering below was written from the witx for the design review of increment 2 of the flat
calls, without the generator `tools/wasi-calls.py`, and names the kinds w32, w64, e N, f32 M,
f64 M, in, out, r32, r64, rep SCALE ALIGN SHOWN, and rec SIZE ALIGN [(offset, width)].  The check
lowers every function, reads every description of CALL_TABLE (by default
LeanExe/Wasi/CallTable.lean), and exits with status 1 when a flat function has no description, a
description names no flat function, or the kinds differ.
"""
import re
import sys
from pathlib import Path


def tokens(text):
    text = re.sub(r";;[^\n]*", "", text)
    return re.findall(r'\(|\)|"[^"]*"|[^\s()]+', text)


def parse(toks):
    stack = [[]]
    for t in toks:
        if t == "(":
            stack.append([])
        elif t == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(t)
    return stack[0]


def load(witx_dir):
    types = {}
    for form in parse(tokens((witx_dir / "typenames.witx").read_text())):
        if form[0] == "typename":
            types[form[1]] = form[2]
    module = None
    for form in parse(tokens((witx_dir / "wasi_snapshot_preview1.witx").read_text())):
        if form[0] == "module":
            module = form
    return types, module


INT_WIDTH = {"u8": 1, "u16": 2, "u32": 4, "u64": 8, "s8": 1, "s16": 2, "s32": 4, "s64": 8}


def resolve(types, t):
    while isinstance(t, str) and t.startswith("$"):
        t = types[t]
    return t


def annotation(form, key):
    for item in form:
        if isinstance(item, list) and len(item) == 3 and item[0] == "@witx" and item[1] == key:
            return item[2]
    return None


def layout(types, t):
    """Size and alignment of a type in linear memory, after the witx layout rules."""
    t = resolve(types, t)
    if isinstance(t, str):
        if t in INT_WIDTH:
            return INT_WIDTH[t], INT_WIDTH[t]
        if t == "string":
            return 8, 4
        raise ValueError(t)
    head = t[0]
    if head == "enum":
        w = INT_WIDTH[annotation(t, "tag")]
        return w, w
    if head == "flags":
        w = INT_WIDTH[annotation(t, "repr")]
        return w, w
    if head == "handle":
        return 4, 4
    if head == "record":
        fields = [f for f in t[1:] if isinstance(f, list) and f[0] == "field"]
        off, align, _ = record_fields(types, fields)
        return round_up(off, align), align
    if head == "union":
        tag, cases = union_parts(types, t)
        tw, ta = layout(types, tag)
        psize = max([layout(types, c)[0] for c in cases] + [0])
        palign = max([layout(types, c)[1] for c in cases] + [1])
        align = max(ta, palign)
        size = round_up(round_up(tw, palign) + psize, align)
        return size, align
    if head == "@witx" and t[1] in ("pointer", "const_pointer"):
        return 4, 4
    if head == "list":
        return 8, 4
    raise ValueError(t)


def round_up(n, a):
    return (n + a - 1) // a * a


def record_fields(types, fields):
    off = 0
    align = 1
    out = []
    for f in fields:
        size, a = layout(types, f[2])
        off = round_up(off, a)
        out.append((f[1], off, size, a, f[2]))
        off += size
        align = max(align, a)
    return off, align, out


def union_parts(types, t):
    tag = None
    cases = []
    for item in t[1:]:
        if isinstance(item, list) and item[0] == "@witx" and item[1] == "tag":
            tag = item[2]
        elif isinstance(item, str):
            cases.append(item)
    return tag, cases


def leaf_fields(types, t, base=0, prefix=""):
    """(name, offset, width) of each scalar field of a record or union result."""
    t0 = t
    t = resolve(types, t)
    if isinstance(t, list) and t[0] == "record":
        fields = [f for f in t[1:] if isinstance(f, list) and f[0] == "field"]
        _, _, laid = record_fields(types, fields)
        out = []
        for name, off, size, a, ft in laid:
            out += leaf_fields(types, ft, base + off, prefix + name + ".")
        return out
    if isinstance(t, list) and t[0] == "union":
        tag, cases = union_parts(types, t)
        tw, _ = layout(types, tag)
        palign = max(layout(types, c)[1] for c in cases)
        out = [(prefix + "tag", base, tw)]
        poff = round_up(tw, palign)
        # one variant here; several variants would overlap at poff
        for c in cases:
            out += leaf_fields(types, c, base + poff, prefix + c + ".")
        return out
    size, _ = layout(types, t0)
    return [(prefix.rstrip("."), base, size)]


def scalar_kind(types, t):
    r = resolve(types, t)
    if isinstance(r, str):
        if r in INT_WIDTH:
            return "w64" if INT_WIDTH[r] == 8 else "w32"
        return None
    if r[0] == "enum":
        n = len([x for x in r[1:] if isinstance(x, str)])
        return f"e{n}"
    if r[0] == "flags":
        bits = len([x for x in r[1:] if isinstance(x, str)])
        mask = (1 << bits) - 1
        w = INT_WIDTH[annotation(r, "repr")]
        return f"f{64 if w == 8 else 32} {mask:#x}"
    if r[0] == "handle":
        return "w32"
    return None


def lower(types, func):
    name = func[2][1].strip('"')
    params = [x for x in func[3:] if isinstance(x, list) and x[0] == "param"]
    results = [x for x in func[3:] if isinstance(x, list) and x[0] == "result"]
    noreturn = any(isinstance(x, list) and x[:2] == ["@witx", "noreturn"] for x in func[3:])
    if noreturn:
        return name, None, "does not return", None
    kinds = []
    core = []
    i = 0
    while i < len(params):
        pname, ptype = params[i][1], params[i][2]
        r = resolve(types, ptype)
        sk = scalar_kind(types, ptype)
        nxt = params[i + 1][2] if i + 1 < len(params) else None
        if r == "string":
            kinds.append("in")
            core += ["i32", "i32"]
        elif isinstance(r, list) and r[0] == "list":
            return name, None, f"{pname} is a list", None
        elif isinstance(r, list) and r[0] == "@witx" and r[1] in ("pointer", "const_pointer"):
            pointee = r[2]
            if pointee == "u8" and nxt is not None and resolve(types, nxt) == "u32" and nxt == "$size":
                kinds.append("in" if r[1] == "const_pointer" else "out")
                core += ["i32", "i32"]
                i += 1
            elif isinstance(pointee, list) and pointee[:2] == ["@witx", "pointer"] and pointee[2] == "u8":
                kinds.append("rep 4 4 false")
                core.append("i32")
            elif pointee == "u8":
                kinds.append("rep 1 1 true")
                core.append("i32")
            else:
                return name, None, f"{pname} points to {pointee}", None
        elif sk is not None:
            kinds.append(sk)
            core.append("i64" if sk.startswith("w64") or sk.startswith("f64") else "i32")
        else:
            return name, None, f"{pname} of type {ptype}", None
        i += 1
    # result: (expected T? (error $errno))
    res = results[0][2]
    assert res[0] == "expected"
    ok = [x for x in res[1:] if not (isinstance(x, list) and x[0] == "error")]
    for t in ok:
        comps = t[1:] if isinstance(t, list) and t[0] == "tuple" else [t]
        for c in comps:
            r = resolve(types, c)
            if isinstance(r, list) and r[0] in ("record", "union"):
                size, align = layout(types, c)
                fields = leaf_fields(types, c)
                kinds.append(f"rec {size} {align} " + str([(o, w) for _, o, w in fields]))
            else:
                size, _ = layout(types, c)
                kinds.append("r64" if size == 8 else ("r32" if size == 4 else f"r{size*8}"))
            core.append("i32")
    return name, kinds, None, core



LEAN_KINDS = {"word32": "w32", "word64": "w64", "input": "in", "output": "out",
              "result32": "r32", "result64": "r64"}
DESCRIPTION = re.compile(r'name := "([^"]+)",\s*params := \[(.*?)\](?:,|\s*\})', re.S)


def lean_kinds(params):
    """The review's names of the kinds of a description's parameter list."""
    kinds = []
    for item in re.findall(r"\.(\w+)((?:\s+(?:0x[0-9a-f]+|\d+|true|false|\[[^\]]*\]))*)", params):
        name, rest = item[0], item[1].split()
        if name in LEAN_KINDS:
            kinds.append(LEAN_KINDS[name])
        elif name == "enum32":
            kinds.append(f"e{rest[0]}")
        elif name in ("flags32", "flags64"):
            kinds.append(f"f{name[5:]} {int(rest[0], 16):#x}")
        elif name == "reported":
            kinds.append(f"rep {rest[0]} {rest[1]} {rest[2]}")
        elif name == "record":
            fields = " ".join(rest[2:])
            kinds.append(f"rec {rest[0]} {rest[1]} {fields}")
    return kinds


def main():
    witx = Path(sys.argv[1] if len(sys.argv) > 1 else "tests/wasi/witx")
    table = Path(sys.argv[2] if len(sys.argv) > 2 else "LeanExe/Wasi/CallTable.lean")
    types, module = load(witx)
    expected = {}
    for function in [f for f in module if isinstance(f, list) and f[0] == "@interface"]:
        name, kinds, _, _ = lower(types, function)
        if kinds is not None and name != "proc_exit":
            expected[name] = kinds
    described = {name: lean_kinds(params) for name, params in DESCRIPTION.findall(table.read_text())}
    failed = False
    for name in sorted(set(expected) | set(described)):
        if name not in described:
            print(f"{name}: flat in the witx but not described")
            failed = True
        elif name not in expected:
            print(f"{name}: described but not a flat witx function")
            failed = True
        elif described[name] != expected[name]:
            print(f"{name}: described {described[name]}, independent lowering {expected[name]}")
            failed = True
    print(f"{len(described)} descriptions checked against the independent lowering")
    sys.exit(1 if failed else 0)


main()
