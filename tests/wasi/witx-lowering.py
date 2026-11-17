# /// script
# requires-python = ">=3.12"
# ///
"""Check the generated flat call descriptions against a second, independent lowering of the
pinned Preview 1 witx.

Usage: uv run tests/wasi/witx-lowering.py [WITX_DIR [CALL_TABLE]]

The lowering below was written from the witx for the design review of increment 2 of the flat
calls, without the generator `tools/wasi-calls.py`, and names the kinds w32, w64, e N, f32 M,
f64 M, in, out, r32, r64, rep SCALE ALIGN SHOWN, and rec SIZE ALIGN [(offset, width)].  A
parameter of a handle type, such as $fd, is h.  A function with reported regions, NAME_get, has the
reporter NAME_sizes_get, a function of two r32 results.  For increment 3, a list of records whose
fields are a pointer to bytes and its $size is iov in when the pointer is a const_pointer, which
the call reads, and iov out when the host fills the bytes, and a const_pointer to records followed
by a pointer to records and a $size is subs.

The check lowers every function, reads every description of CALL_TABLE (by default
LeanExe/Wasi/CallTable.lean), and exits with status 1 when a flat function has no description, a
description names no flat function, a function other than poll_oneoff has more than one, or the
kinds or the reporters differ.  sock_recv and sock_send have no description by decision F2 of
increment 3, since Wasmtime 44 implements no Preview 1 socket function.  Each subscription record of
a description of poll_oneoff must hold the userdata at its offset and width as a constant, distinct
among the description's records, the union tag as a constant that names a case, and each field of
that case at its offset and width, taken from a handle argument when the field is a handle and
otherwise from a word argument or a constant that fits the width, and nothing else.  The fields of
the first event that `eventFields` of Verified/Wasi/SysForm.lean lists must be the scalar fields of
$event at their offsets and widths.
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
        return "h"
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
            element = resolve(types, r[1])
            fields = ([f for f in element[1:] if isinstance(f, list) and f[0] == "field"]
                      if isinstance(element, list) and element[0] == "record" else [])
            pointer = resolve(types, fields[0][2]) if fields else None
            if (len(fields) == 2 and isinstance(pointer, list) and pointer[0] == "@witx"
                    and pointer[2] == "u8" and fields[1][2] == "$size"):
                kinds.append("iov in" if pointer[1] == "const_pointer" else "iov out")
                core += ["i32", "i32"]
            else:
                return name, None, f"{pname} is a list of {r[1]}", None
        elif isinstance(r, list) and r[0] == "@witx" and r[1] in ("pointer", "const_pointer"):
            pointee = r[2]
            if (pointee == "u8" and nxt is not None and resolve(types, nxt) == "u32"
                    and nxt == "$size"):
                kinds.append("in" if r[1] == "const_pointer" else "out")
                core += ["i32", "i32"]
                i += 1
            elif (isinstance(pointee, list) and pointee[:2] == ["@witx", "pointer"]
                  and pointee[2] == "u8"):
                kinds.append("rep 4 4 false")
                core.append("i32")
            elif pointee == "u8":
                kinds.append("rep 1 1 true")
                core.append("i32")
            elif (r[1] == "const_pointer" and i + 2 < len(params)
                  and isinstance(nxt, list) and nxt[:2] == ["@witx", "pointer"]
                  and params[i + 2][2] == "$size"):
                kinds.append("subs")
                core += ["i32", "i32", "i32"]
                i += 2
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



LEAN_KINDS = {"word32": "w32", "handle": "h", "word64": "w64", "input": "in", "output": "out",
              "result32": "r32", "result64": "r64"}
NAME = re.compile(r'name := "([^"]+)"')
REPORTER = re.compile(r'reporter := some "([^"]+)"')
FIELD = re.compile(r"⟨(\d+), (\d+), \.(?:const (\d+)|(word)|(handle))⟩")
# The functions that have no description by decision F2 of increment 3.
EXCLUDED = {"sock_recv", "sock_send"}


def bracketed(text, start):
    """The text between the bracket at `start` and the bracket that closes it."""
    depth = 0
    for index in range(start, len(text)):
        depth += {"[": 1, "]": -1}.get(text[index], 0)
        if depth == 0:
            return text[start + 1:index]
    raise ValueError(text[start:])


def descriptions(table):
    """The name, parameter list, subscription records, and reporter of each description: each
    record a list of (offset, width, source), the source an integer for a constant or "word" or
    "handle"."""
    found = []
    for block in table.split("\ndef ")[1:]:
        named = NAME.search(block)
        if not named:
            continue
        params = bracketed(block, block.index("params := [") + len("params := "))
        records = None
        if ".subscriptions [" in params:
            start = params.index(".subscriptions [")
            inner = bracketed(params, start + len(".subscriptions "))
            records = [[(int(o), int(w), int(c) if c else word or handle)
                        for o, w, c, word, handle in FIELD.findall(record)]
                       for record in re.findall(r"\[([^\[\]]*)\]", inner)]
            params = (params[:start] + ".subscriptions" +
                      params[start + len(".subscriptions ") + len(inner) + 2:])
        reporter = REPORTER.search(block)
        found.append((named.group(1), params, records, reporter.group(1) if reporter else None))
    return found


def subscription_cases(types):
    """For each value of the tag of $subscription's union, the scalar fields of its case at their
    offsets in the record, with whether each is a handle, and the offsets and widths of the
    userdata and the tag."""
    record = resolve(types, "$subscription")
    fields = [f for f in record[1:] if isinstance(f, list) and f[0] == "field"]
    _, _, laid = record_fields(types, fields)
    (_, user_offset, user_width, _, _), (_, union_offset, _, _, union_type) = laid
    tag, cases = union_parts(types, resolve(types, union_type))
    tag_width, _ = layout(types, tag)
    payload = union_offset + round_up(tag_width, max(layout(types, c)[1] for c in cases))
    found = []
    for case in cases:
        case_fields = [f for f in resolve(types, case)[1:] if isinstance(f, list)
                       and f[0] == "field"]
        _, _, case_laid = record_fields(types, case_fields)
        found.append({payload + offset: (size, scalar_kind(types, ft) == "h")
                      for _, offset, size, _, ft in case_laid})
    return (user_offset, user_width), (union_offset, tag_width), found


def check_records(types, name, records):
    """The failures of the subscription records of the description `name`."""
    user, tag, cases = subscription_cases(types)
    failures, userdata = [], []
    if not records:
        failures.append(f"{name}: no subscription records")
    for number, record in enumerate(records or []):
        where = f"{name} record {number}"
        fields = {offset: (width, source) for offset, width, source in record}
        if len(fields) != len(record):
            failures.append(f"{where}: two fields at one offset")
        for offset, width, source in record:
            if isinstance(source, int) and source >= 1 << (8 * width):
                failures.append(f"{where}: constant {source} does not fit {width} bytes")
        head = [fields.get(user[0]), fields.get(tag[0])]
        if (head[0] is None or head[0][0] != user[1] or not isinstance(head[0][1], int)
                or head[1] is None or head[1][0] != tag[1] or not isinstance(head[1][1], int)
                or head[1][1] >= len(cases)):
            failures.append(f"{where}: no constant userdata or tag of a case")
            continue
        userdata.append(head[0][1])
        case = cases[head[1][1]]
        rest = {o: f for o, f in fields.items() if o not in (user[0], tag[0])}
        if sorted(rest) != sorted(case):
            failures.append(f"{where}: fields at {sorted(rest)}, case fields at {sorted(case)}")
            continue
        for offset, (width, source) in rest.items():
            size, handle = case[offset]
            if width != size or (source == "handle") != handle:
                failures.append(f"{where}: field at {offset} of width {width} from {source}")
    if len(set(userdata)) != len(userdata):
        failures.append(f"{name}: two subscriptions with one userdata")
    return failures


# The strides of the arrays of poll_oneoff, (size, alignment) of a subscription and of an event,
# which the Lean definitions use as constants and the kernel tests of the nested layout state.
STRIDES = {"$subscription": (48, 8), "$event": (32, 8)}


def check_strides(types):
    """The failures of the strides of poll_oneoff's arrays against the witx layout."""
    return [f"{name}: stride {stride}, independent layout {layout(types, name)}"
            for name, stride in STRIDES.items() if layout(types, name) != stride]


def check_events(types, form):
    """The failures of `eventFields` of `form`, the text of Verified/Wasi/SysForm.lean."""
    listed = re.search(r"def eventFields : List \(Nat × Nat\) :=\s*\[([^\]]*)\]", form)
    if not listed:
        return ["Verified/Wasi/SysForm.lean: no eventFields"]
    fields = [(int(o), int(w)) for o, w in re.findall(r"\((\d+), (\d+)\)", listed.group(1))]
    expected = [(o, w) for _, o, w in leaf_fields(types, "$event")]
    if fields != expected:
        return [f"eventFields {fields}, independent layout of $event {expected}"]
    return []


def lean_kinds(params):
    """The review's names of the kinds of a description's parameter list."""
    kinds = []
    for item in re.findall(r"\.(\w+)((?:\s+(?:0x[0-9a-f]+|\d+|true|false|\[[^\]]*\]))*)", params):
        name, rest = item[0], item[1].split()
        if name in LEAN_KINDS:
            kinds.append(LEAN_KINDS[name])
        elif name == "iovec":
            kinds.append("iov in" if rest[0] == "true" else "iov out")
        elif name == "subscriptions":
            kinds.append("subs")
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
    failures = [f"{name}: excluded but not lowered" for name in EXCLUDED if name not in expected]
    for name in EXCLUDED:
        expected.pop(name, None)
    found = descriptions(table.read_text())
    described, reporters = {}, {}
    for name, params, records, reporter in found:
        if name in described and name != "poll_oneoff":
            failures.append(f"{name}: described twice")
        described[name] = lean_kinds(params)
        reporters[name] = reporter
        if records is not None:
            failures += check_records(types, name, records)
        elif "subs" in described[name]:
            failures.append(f"{name}: subscriptions without records")
    if "subs" in expected.get("poll_oneoff", []):
        failures += check_events(types, Path("Verified/Wasi/SysForm.lean").read_text())
        failures += check_strides(types)
    for failure in failures:
        print(failure)
    failed = bool(failures)
    for name in sorted(set(expected) | set(described)):
        if name not in described:
            print(f"{name}: flat in the witx but not described")
            failed = True
        elif name not in expected:
            print(f"{name}: described but not a flat witx function")
            failed = True
        elif any(lean_kinds(params) != expected[name]
                 for named, params, _, _ in found if named == name):
            print(f"{name}: described {described[name]}, independent lowering {expected[name]}")
            failed = True
        else:
            reported = any(kind.startswith("rep ") for kind in expected[name])
            reporter = name.removesuffix("_get") + "_sizes_get" if reported else None
            if reported and expected.get(reporter) != ["r32", "r32"]:
                print(f"{name}: no reporter {reporter} with two 32-bit results")
                failed = True
            if reporters.get(name) != reporter:
                print(f"{name}: reporter {reporters.get(name)}, independent lowering {reporter}")
                failed = True
    print(f"{len(found)} descriptions checked against the independent lowering")
    sys.exit(1 if failed else 0)


main()
