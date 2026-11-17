# /// script
# requires-python = ">=3.12"
# ///
"""Generate the Linux call table, the layouts of the structures that it names, its region lemmas,
and its frame test from the pinned syzlang descriptions.

Usage: uv run python -I tools/linux-calls.py [--check | --frame-faults DIR] [SYZLANG_DIR]

SYZLANG_DIR holds sys.txt, sys.txt.const, and LICENSE of syzkaller commit
a3e64cfc0d091fba81397847a5ab9790a4a944ca, by default tests/linux/syzlang.  The script checks the
files' SHA-256 digests, parses the subset of syzlang that the admitted calls use (resource,
structure, flag, type-template, and call lines, the built-in templates `filename` and `buffer` of
syzkaller's pkg/compiler/types.go lines 1143 and 1146, and the architecture columns of the const
file), lowers the calls of ADMITTED with their arm64 and x86-64 numbers, and writes
LeanExe/Linux/CallTable.lean and the frame test tests/linux/sys/frame.c.  With --check it compares
each rendering with the committed file instead, printing a unified diff and exiting with status 1
when one differs or when a Lean file of LeanExe/Linux other than the table has a definition
`def NAME : Call`.  With --frame-faults DIR it writes to DIR one frame test for each seeded fault
of FAULTS and prints the fault's name, the exit status that the test must give, and "native" when
the step that the fault reaches first does not run under QEMU.

The lowering: a resource argument derived from `fd` is fd, and with `[opt]` it is dirfd when its
special values, which include those of each parent resource (pkg/compiler/gen.go lines 34 to 47),
hold AT_FDCWD; `ptr[in, filename]` is path; a pointer of direction in or out followed by the `len`
of it, over an array of one-byte elements, is input or output by its direction, and a `ptr[in, T]`
followed by the `bytesize` of it is input; a `ptr[out, T]` of fixed size without a length is
record of T's size; flags, const, and integer arguments are value.  A call returns a descriptor
when its result is a resource derived from `fd`, and exit_group, which ends the process, is
terminal.  The script refuses a call whose lowering needs anything else: a length that does not
follow its pointer, a `len` over an array whose element has more than one byte, a nested pointer,
an optional pointer, the direction inout, a `ptr[in, T]` without a length, an output pointer with
a `bytesize`, another resource, or more than one output region.  A structure's fields lie at the
next multiple of their size, and its size is rounded up to its largest field; integers and
pointers have 8 bytes on arm64 and x86-64 (sys/targets/targets.go lines 270 and 302).
"""
import difflib
import hashlib
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path

COMMIT = "a3e64cfc0d091fba81397847a5ab9790a4a944ca"
DIGESTS = {
    "sys.txt": "61486b87ae2792b8d526220293c2f9d6da2330b7edb64eca87fddb8bf5bfdd98",
    "sys.txt.const": "51122282e5c1b25a27fa821cab02c85e30fe34a8071a73ea8ce713e4090ea696",
    "LICENSE": "cc4d4de0920b0d3912203b5d9aa76728ac4a11087f55da9ea00576db7d1e34e2",
}
# The calls of the table, in its order.  The frame of the trusted base holds for this set of calls
# together, so a call joins it only after a review of its effect on the others.
ADMITTED = ["openat", "close", "read", "write", "exit_group", "clock_gettime", "getrandom",
            "openat2"]
TERMINAL = {"exit_group"}
# Syzkaller's built-in templates (pkg/compiler/types.go lines 1143 and 1146).
BUILTIN = {"filename": ([], "string[filename]"), "buffer": (["DIR"], "ptr[DIR, array[int8]]")}
INTEGERS = {"int8": 1, "int16": 2, "int32": 4, "int64": 8, "intptr": 8}
WIDTH = 100
TABLE = "LeanExe/Linux/CallTable.lean"
FRAME = "tests/linux/sys/frame.c"


class Refusal(Exception):
    pass


@dataclass
class Type:
    name: str
    args: list

    def __str__(self):
        shown = [str(arg) if isinstance(arg, Type) else ":".join(map(str, arg[1:]))
                 for arg in self.args]
        return self.name + (f"[{', '.join(shown)}]" if shown else "")


@dataclass
class Description:
    name: str
    line: int
    arm64: int
    amd64: int
    params: list
    opens: bool
    terminal: bool
    records: list


@dataclass
class Layout:
    name: str
    first: int
    last: int
    size: int
    align: int
    fields: list


def check_digests(directory):
    for name, digest in DIGESTS.items():
        found = hashlib.sha256((directory / name).read_bytes()).hexdigest()
        if found != digest:
            sys.exit(f"{directory / name}: SHA-256 {found}, expected {digest}")


def read_consts(path):
    """The const file as a map from each name to its value on each architecture, None where it
    is undefined (pkg/compiler/const_file.go, parseConst)."""
    arches, consts = None, {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        name, _, text = (part.strip() for part in line.partition("="))
        if arches is None:
            if name != "arches":
                raise Refusal(f"{path}: no arches header")
            arches = [arch.strip() for arch in text.split(",")]
            continue
        values, default = {}, None
        for pair in text.split(","):
            fields = [field.strip() for field in pair.split(":")]
            value = None if fields[-1] == "???" else int(fields[-1], 0)
            if len(fields) == 1:
                default = {arch: value for arch in arches}
            else:
                for arch in fields[:-1]:
                    values[arch] = value
        consts[name] = (default or {}) | values
    return consts


TOKEN = re.compile(r'\s*("[^"]*"|`[^`]*`|-?0x[0-9a-fA-F]+|-?[0-9]+|[A-Za-z_][\w$]*|[\[\],:])')


def tokens(text):
    out, position, text = [], 0, text.strip()
    while position < len(text):
        match = TOKEN.match(text, position)
        if not match:
            raise Refusal(f"cannot read the type {text!r}")
        out.append(match.group(1))
        position = match.end()
    return out


def parse_type(text):
    items = tokens(text)
    result, end = type_at(items, 0)
    if end != len(items):
        raise Refusal(f"cannot read the type {text!r}")
    return result


def type_at(items, index):
    """The type, number, string, or range at items[index], and the index after it."""
    item = items[index]
    if item[0] in "\"`":
        return ("string", item[1:-1]), index + 1
    if item[0].isdigit() or item[0] == "-":
        value, index = int(item, 0), index + 1
        if index < len(items) and items[index] == ":":
            return ("range", value, int(items[index + 1], 0)), index + 2
        return ("number", value), index
    args, index = [], index + 1
    if index < len(items) and items[index] == "[":
        index += 1
        while items[index] != "]":
            arg, index = type_at(items, index)
            args.append(arg)
            if items[index] == ",":
                index += 1
        index += 1
    if index < len(items) and items[index] == ":":
        return ("range", item, items[index + 1]), index + 2
    return Type(item, args), index


def split_top(text):
    """The parts of `text` separated by commas outside brackets and parentheses."""
    parts, depth, current = [], 0, ""
    for ch in text:
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current.strip())
    return parts


def closing(text):
    """The index in `text` of the parenthesis that closes one opened before it."""
    depth, quoted = 1, False
    for index, ch in enumerate(text):
        quoted ^= ch == '"'
        if not quoted:
            depth += (ch == "(") - (ch == ")")
            if depth == 0:
                return index
    raise Refusal(f"no closing parenthesis in {text!r}")


def uncomment(line):
    quoted = False
    for index, ch in enumerate(line):
        quoted ^= ch == '"'
        if ch == "#" and not quoted:
            return line[:index].rstrip()
    return line.rstrip()


@dataclass
class Struct:
    fields: list
    attrs: str
    first: int
    last: int
    union: bool


@dataclass
class Spec:
    resources: dict
    structs: dict
    struct_templates: dict
    flags: dict
    templates: dict
    calls: dict


def parse_sys(path):
    """The resource, structure, union, flag, template, and call lines of a syzlang file; every
    other top-level line must be an include, incdir, define, or meta line."""
    spec = Spec({}, {}, {}, {}, {}, {})
    lines = path.read_text().splitlines()
    index = 0
    while index < len(lines):
        number, line = index + 1, uncomment(lines[index])
        index += 1
        if not line or re.fullmatch(r"(include|incdir) <[^>]+>|(define|meta) .*", line):
            continue
        if match := re.fullmatch(r"resource (\w+)\[(\w+)\](?:\s*:\s*(.*))?", line):
            values = [v.strip() for v in (match.group(3) or "").split(",") if v.strip()]
            spec.resources[match.group(1)] = (match.group(2), values, number)
        elif match := re.fullmatch(r"(type )?(\w+)(?:\[[\w, ]*\])? ([{[])", line):
            close = "}" if match.group(3) == "{" else "]"
            fields = []
            while not lines[index].startswith(close):
                if body := uncomment(lines[index]).strip():
                    fields.append(tuple(re.split(r"\s+", body, maxsplit=1)))
                index += 1
            index += 1
            struct = Struct(fields, lines[index - 1][1:].strip(), number, index, close == "]")
            target = spec.struct_templates if match.group(1) else spec.structs
            target[match.group(2)] = struct
        elif match := re.fullmatch(r"type (\w+)(?:\[([\w, ]*)\])? (.+)", line):
            params = [p.strip() for p in (match.group(2) or "").split(",") if p.strip()]
            spec.templates[match.group(1)] = (params, match.group(3))
        elif match := re.fullmatch(r"(\w+) = (.+)", line):
            spec.flags[match.group(1)] = (split_top(match.group(2)), number)
        elif match := re.match(r"([\w$]+)\(", line):
            close = match.end() + closing(line[match.end():])
            spec.calls.setdefault(match.group(1), []).append(
                (line[match.end():close], line[close + 1:].strip(), number))
        else:
            raise Refusal(f"{path} line {number}: unrecognized line {line!r}")
    return spec


def substitute(t, binding):
    if isinstance(t, Type):
        if not t.args and t.name in binding:
            return binding[t.name]
        return Type(t.name, [substitute(arg, binding) for arg in t.args])
    return t


def expand(spec, t):
    """`t` with each template at its head replaced by its body."""
    while isinstance(t, Type):
        if t.name in BUILTIN:
            params, body = BUILTIN[t.name]
        elif t.name in spec.templates:
            params, body = spec.templates[t.name]
        elif t.name in spec.struct_templates:
            raise Refusal(f"the structure template {t.name}")
        else:
            return t
        if len(params) != len(t.args):
            raise Refusal(f"{t.name} takes {len(params)} arguments")
        t = substitute(parse_type(body), dict(zip(params, t.args)))
    return t


def resource_chain(spec, name):
    """The resources from `name` to its root, its integer base, and its special values with those
    of each parent first (pkg/compiler/gen.go lines 34 to 47)."""
    chain, values = [], []
    while name in spec.resources:
        base, own, _ = spec.resources[name]
        chain.append(name)
        values = own + values
        name = base
    return chain, name, values


def scalar_size(spec, t):
    """The size of an integer, flags, const, or resource type, or None for another type."""
    if not isinstance(t, Type):
        return None
    if t.name in INTEGERS:
        return INTEGERS[t.name]
    if t.name in ("flags", "const"):
        if len(t.args) != 2 or not isinstance(t.args[1], Type):
            raise Refusal(f"{t.name} without its integer type")
        return INTEGERS.get(t.args[1].name)
    if t.name in spec.resources:
        return INTEGERS.get(resource_chain(spec, t.name)[1])
    return None


def struct_layout(spec, name):
    if name not in spec.structs:
        raise Refusal(f"no structure {name}")
    struct = spec.structs[name]
    if struct.union or struct.attrs:
        raise Refusal(f"{name}: a union or a structure with attributes")
    offset, align, out = 0, 1, []
    for field, text in struct.fields:
        size = scalar_size(spec, expand(spec, parse_type(text)))
        if size is None:
            raise Refusal(f"{name}.{field}: a field that is not an integer")
        offset = (offset + size - 1) // size * size
        out.append((field, offset, size))
        offset += size
        align = max(align, size)
    return Layout(name, struct.first, struct.last, (offset + align - 1) // align * align, align,
                  out)


def has_pointer(spec, t, seen=()):
    """Whether a type holds a pointer: a pointer, an array of a type that holds one, or a
    structure or union with a field that holds one."""
    t = expand(spec, t)
    if not isinstance(t, Type):
        return False
    if t.name in ("ptr", "ptr64", "vma", "vma64"):
        return True
    if t.name == "array":
        return has_pointer(spec, t.args[0], seen)
    if t.name in spec.structs and t.name not in seen:
        return any(has_pointer(spec, parse_type(text), seen + (t.name,))
                   for _, text in spec.structs[t.name].fields)
    return False


def size_of(spec, t):
    """The size of a type of fixed size, the structure's layout or None, for a record."""
    size = scalar_size(spec, t)
    if size is not None:
        return size, None
    if isinstance(t, Type) and t.name in spec.structs:
        layout = struct_layout(spec, t.name)
        return layout.size, layout
    raise Refusal(f"{t} has no fixed size")


def lower(spec, consts, name):
    found = spec.calls.get(name, [])
    if len(found) != 1:
        raise Refusal(f"{len(found)} descriptions without a variant")
    text, result, line = found[0]
    args = []
    for part in split_top(text):
        arg, _, kind = part.partition(" ")
        args.append((arg, expand(spec, parse_type(kind))))
    params, records, used = [], [], set()
    for position, (arg, t) in enumerate(args):
        if position in used:
            continue
        follow = args[position + 1][1] if position + 1 < len(args) else None
        length = (follow if isinstance(follow, Type) and follow.name in ("len", "bytesize")
                  and len(follow.args) == 1 and follow.args[0] == Type(arg, []) else None)
        if t.name in ("len", "bytesize", "bitsize"):
            raise Refusal(f"the length {arg} does not follow its pointer")
        if t.name == "ptr":
            direction, inner, options = t.args[0].name, expand(spec, t.args[1]), t.args[2:]
            if options:
                raise Refusal(f"the optional pointer {arg}")
            if direction not in ("in", "out"):
                raise Refusal(f"the direction {direction} of {arg}")
            if has_pointer(spec, inner):
                raise Refusal(f"the nested pointer {arg}")
            if inner == Type("string", [Type("filename", [])]) and direction == "in" \
                    and length is None:
                params.append(("path",))
            elif length is not None and length.name == "len":
                element = inner.args[0] if inner.name == "array" else None
                if inner.name != "array" or scalar_size(spec, expand(spec, element)) != 1:
                    raise Refusal(f"a len over {arg}, whose elements are not bytes")
                params.append(("input",) if direction == "in" else ("output",))
                used.add(position + 1)
            elif length is not None:
                if direction != "in":
                    raise Refusal(f"the output pointer {arg} with a bytesize")
                if isinstance(inner, Type) and inner.name in spec.structs:
                    records.append((struct_layout(spec, inner.name), "input"))
                params.append(("input",))
                used.add(position + 1)
            elif direction == "in":
                raise Refusal(f"the input pointer {arg} without a length")
            else:
                size, layout = size_of(spec, inner)
                if layout is not None:
                    records.append((layout, "output"))
                params.append(("record", size))
        elif t.name in spec.resources:
            chain, _, values = resource_chain(spec, t.name)
            optional = t.args == [Type("opt", [])]
            if "fd" not in chain or (t.args and not optional):
                raise Refusal(f"the resource {t.name} of {arg}")
            if optional and "AT_FDCWD" not in values:
                raise Refusal(f"the optional descriptor {arg} without AT_FDCWD")
            params.append(("dirfd",) if optional else ("fd",))
        elif t.name in ("flags", "const") or t.name in INTEGERS:
            params.append(("value",))
        else:
            raise Refusal(f"the argument {arg} of type {t.name}")
    if sum(p[0] in ("output", "record") for p in params) > 1:
        raise Refusal("more than one output region")
    returned = result.split("(")[0].strip()
    if returned and "fd" not in resource_chain(spec, returned)[0]:
        raise Refusal(f"the result {returned}")
    numbers = consts.get(f"__NR_{name}", {})
    if numbers.get("arm64") is None or numbers.get("amd64") is None:
        raise Refusal("no number on arm64 or amd64")
    return Description(name, line, numbers["arm64"], numbers["amd64"], params, bool(returned),
                       name in TERMINAL, records)


def load(directory):
    check_digests(directory)
    spec = parse_sys(directory / "sys.txt")
    consts = read_consts(directory / "sys.txt.const")
    descriptions = []
    for name in ADMITTED:
        try:
            descriptions.append(lower(spec, consts, name))
        except Refusal as refusal:
            raise Refusal(f"{name}: {refusal}") from None
    return descriptions, consts


def camel(name):
    head, *rest = name.split("_")
    return head + "".join(part.capitalize() for part in rest)


def wrap(head, items, tail, indent):
    """`head`, the `items` separated by commas, and `tail` on one line, or broken before an item,
    with continuation lines indented by `indent` spaces, when the line exceeds the width."""
    line = head + ", ".join(items) + tail
    if len(line) <= WIDTH:
        return [line]
    lines, current = [], head
    for index, item in enumerate(items):
        piece = item + ("," if index + 1 < len(items) else tail)
        if len(current) + len(piece) + 1 > WIDTH and current.strip():
            lines.append(current.rstrip())
            current = " " * indent
        current += ("" if current.endswith(("[", " ", "{")) else " ") + piece
    lines.append(current)
    return lines


def definition(head, value):
    """`head := value` on one line, or broken after `:=` when it exceeds the width."""
    line = f"{head} := {value}"
    return [line] if len(line) <= WIDTH else [f"{head} :=", f"  {value}"]


def lean_param(param):
    return f".record {param[1]}" if param[0] == "record" else f".{param[0]}"


def words(param):
    return 2 if param[0] in ("input", "output") else 1


def regions(params):
    """The regions of the parameters `params`, as `inputRegions` and `outputRegions` of
    LeanExe/Linux/Call.lean compute them: for each, its parameter's position, whether the kernel
    may write it, the argument of its address, and its size, ("path",) for the name's length,
    ("word", r) for argument r, or ("bytes", n); and the number of argument words."""
    out, word = [], 0
    for position, param in enumerate(params):
        match param[0]:
            case "path":
                out.append((position, False, word, ("path",)))
            case "input" | "output":
                out.append((position, param[0] == "output", word, ("word", word + 1)))
            case "record":
                out.append((position, True, word, ("bytes", param[1])))
        word += words(param)
    return out, word


def lean_region(region):
    _, _, address, size = region
    match size:
        case ("path",):
            return f"(x{address}, I.pathLength m x{address})"
        case ("word", word):
            return f"(x{address}, x{word}.toNat)"
        case ("bytes", n):
            return f"(x{address}, {n})"


def equation(indent, left, right, tail):
    line = f"{indent}{left} = {right}{tail}"
    if len(line) <= WIDTH:
        return [line]
    return [f"{indent}{left} =", f"{indent}    {right}{tail}"]


def region_lemma(description):
    found, count = regions(description.params)
    xs = [f"x{i}" for i in range(count)]
    name, args = camel(description.name), f"[{', '.join(xs)}]"
    inputs = "[" + ", ".join(lean_region(r) for r in found if not r[1]) + "]"
    outputs = "[" + ", ".join(lean_region(r) for r in found if r[1]) + "]"
    head = (f"theorem regions_{name} {{M : Type}} (I : Memory M) (m : M) ({' '.join(xs)} : "
            f"UInt64) :")
    assert len(head) <= WIDTH, head
    return [head,
            *equation("    ", f"inputRegions I m {args} 0 {name}Call.params", inputs, " ∧"),
            *equation("      ", f"outputRegions {args} 0 {name}Call.params", outputs,
                      " := ⟨rfl, rfl⟩")]


TABLE_HEAD = f"""import LeanExe.Linux.Call

/-!
The described calls of the Linux call layer and the layouts of the structures that they name,
generated by `tools/linux-calls.py` from `tests/linux/syzlang/sys.txt` and
`tests/linux/syzlang/sys.txt.const` of syzkaller commit
`{COMMIT}`.  Do not edit; run the generator.
-/

namespace LeanExe.Linux
"""

TABLE_TYPES = """/-- A field of a structure: its name, its offset, and its width in bytes. -/
structure Field where
  name : String
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- The layout of a structure on arm64 and x86-64: its name, size, alignment, and fields, each a
little-endian integer. -/
structure Layout where
  name : String
  size : Nat
  align : Nat
  fields : List Field
  deriving DecidableEq, Repr
"""

TABLE_ONE_OUTPUT = """/-- Whether a parameter gives an output region. -/
def Param.writes : Param → Bool
  | .output | .record _ => true
  | _ => false

/-- Every described call has at most one output region, which `step` writes. -/
theorem table_one_output : ∀ c ∈ table, (c.params.filter Param.writes).length ≤ 1 := by
  decide
"""


def render_table(descriptions):
    out = TABLE_HEAD.splitlines()
    for d in descriptions:
        value = (f"⟨\"{d.name}\", {d.arm64}, {d.amd64}, "
                 f"[{', '.join(lean_param(p) for p in d.params)}], "
                 f"{str(d.opens).lower()}, {str(d.terminal).lower()}⟩")
        out += ["", f"/-- `{d.name}` (`sys.txt` line {d.line}). -/",
                *definition(f"def {camel(d.name)}Call : Call", value)]
    out += ["", "/-- The described calls. -/", "def table : List Call :=",
            *wrap("  [", [f"{camel(d.name)}Call" for d in descriptions], "]", 4), ""]
    out += TABLE_TYPES.splitlines()
    roles = {}
    for d in descriptions:
        for layout, role in d.records:
            roles.setdefault(layout.name, (layout, []))[1].append((role, d.name))
    for layout, uses in roles.values():
        fields = ", ".join(f"⟨\"{n}\", {o}, {w}⟩" for n, o, w in layout.fields)
        used = " and ".join(f"the {role} record of `{name}`" for role, name in uses)
        out += ["", f"/-- `{layout.name}` (`sys.txt` lines {layout.first} to {layout.last}), "
                    f"{used}. -/",
                *definition(f"def {camel(layout.name)}Layout : Layout",
                            f"⟨\"{layout.name}\", {layout.size}, {layout.align}, [{fields}]⟩")]
    out += [""] + TABLE_ONE_OUTPUT.splitlines()
    for d in descriptions:
        out += [""] + region_lemma(d)
    out += ["", "end LeanExe.Linux", ""]
    return "\n".join(out)


# The frame test.  DATA is the content of the file `data` that the test writes first; its bytes
# differ from every fill.
DATA = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-+"
# The fills of the runs of each placement.  The coverage check requires each byte of an output
# region that a step makes the call write to differ from the fill in one of the runs, so a correct
# kernel fails it only where a byte that varies equals the fill of every run, which for a uniformly
# random byte has probability 256^-k for k fills.  The bytes that vary are getrandom's 8 and the low
# 4 bytes of tv_sec and of tv_nsec: 8 at each of the 2 placements of each of the two steps, 32 in
# a run of the frame test that reaches both.  tests/linux/sys-run.sh makes 2 such runs, natively
# and under QEMU, and 3 runs of seeded faults pass the coverage check of clock_gettime before they
# fail (getrandom-short natively and under QEMU, openat2-record-short natively), 112 bytes in all.
# The other faults stop before that check or, for the record of 24 bytes, fail it with the predicted
# status whatever the varying bytes hold.  Three fills give a rate of 112 * 256^-3, about 6.7 *
# 10^-6, for a run of tests/linux/sys-run.sh, and four give 112 * 256^-4, about 2.6 * 10^-8.  The
# fills differ pairwise, so a fixed byte of a reply equals at most one of them, and none is 0, the
# value of the high bytes of tv_sec and tv_nsec.  A byte that follows the clock matches them only if
# it advances by 181, 226, and 135 units between consecutive runs, the differences of the fills
# modulo 256, which runs of nearly equal duration do not produce.
FILLS = (0xA5, 0x5A, 0x3C, 0xC3)
VARYING = 112
RATE = VARYING * 256.0 ** -len(FILLS)
assert RATE < 1e-6 and len(set(FILLS)) == len(FILLS) and 0 not in FILLS
CHECKS = {"return": 1, "registers": 2, "frame": 3, "value": 4, "reply": 5, "coverage": 6}
QEMU_OPENAT2 = "QEMU 8.2.2 does not implement openat2 and returns ENOSYS"
QEMU_EXECUTABLE = "QEMU 8.2.2 lets a guest open its own executable for writing"


def record_bytes(layout, values):
    out = bytearray(layout.size)
    for name, offset, width in layout.fields:
        out[offset:offset + width] = values.get(name, 0).to_bytes(width, "little")
    return bytes(out)


def steps(consts, layouts):
    """The frame test's steps, in the order in which it runs them.  Each step names a call and
    gives the argument of each parameter: for value and dirfd an integer or the names of
    constants of the const file whose bits it ORs, for fd the slot of a descriptor that the
    step's setup opens, for path a file name, for input the bytes, for output the count, and None
    for a record.  `expect` is the result: "opened" for a descriptor, ("errno", NAME) for a
    negated error number, ("status", N) for the exit status of a terminal call, or a count.
    `fills` is the number of leading bytes of the output region that the call must write, "all"
    for the region; `setup` and `check` name C functions of the test; `native` gives the reason
    why the step does not run under QEMU."""
    how = record_bytes(layouts["open_how"],
                       {"flags": consts["O_RDONLY"]["arm64"] | consts["O_CLOEXEC"]["arm64"]})
    created = ["O_WRONLY", "O_CREAT", "O_EXCL", "O_CLOEXEC"]
    mode = ["S_IRUSR", "S_IWUSR", "S_IRGRP", "S_IROTH"]
    return [
        {"label": "openat of a new file with mode 0644", "call": "openat",
         "args": ["AT_FDCWD", "created", created, mode], "expect": "opened", "setup": "hole",
         "check": "created", "mode": mode},
        {"label": "openat of the executable for writing", "call": "openat",
         "args": ["AT_FDCWD", "/proc/self/exe", ["O_WRONLY"], 0],
         "expect": ("errno", "ETXTBSY"), "native": QEMU_EXECUTABLE},
        {"label": "close", "call": "close", "args": [0], "expect": 0, "setup": "data",
         "check": "closed"},
        {"label": "read of 16 bytes", "call": "read", "args": [0, 16], "expect": 16,
         "fills": "all", "setup": "data", "offset": 0, "check": "data"},
        {"label": "read of 16 bytes 10 before the end", "call": "read", "args": [0, 16],
         "expect": 10, "fills": 10, "setup": "data", "offset": 54, "check": "data"},
        {"label": "write of 16 bytes", "call": "write", "args": [0, DATA[16:32]], "expect": 16,
         "setup": "written", "check": "written", "expected": DATA[16:32]},
        {"label": "clock_gettime of CLOCK_REALTIME", "call": "clock_gettime",
         "args": ["CLOCK_REALTIME", None], "expect": 0, "fills": "all", "setup": "clock",
         "check": "clock"},
        {"label": "openat2 with open_how of 24 bytes", "call": "openat2",
         "args": ["AT_FDCWD", "data", how], "expect": "opened", "setup": "hole",
         "native": QEMU_OPENAT2},
        {"label": "openat2 with a nonzero byte after open_how", "call": "openat2",
         "args": ["AT_FDCWD", "data", how + bytes([1, 0, 0, 0, 0, 0, 0, 0])],
         "expect": ("errno", "E2BIG"), "native": QEMU_OPENAT2},
        {"label": "openat2 with a size of 16", "call": "openat2",
         "args": ["AT_FDCWD", "data", how[:16]], "expect": ("errno", "EINVAL"),
         "native": QEMU_OPENAT2},
        {"label": "getrandom of 8 bytes", "call": "getrandom", "args": [8, 0], "expect": 8,
         "fills": "all"},
        {"label": "exit_group with 0x12A", "call": "exit_group", "args": [0x12A],
         "expect": ("status", 0x2A)},
    ]


# The seeded faults of --frame-faults: the call whose description changes, the position of the
# parameter, the change, and the check that fails first.  ("kind", P) declares the parameter as P,
# ("size", n) declares its region n bytes longer, and ("start", n) declares it to start n bytes
# after the address that the call receives.  The first placement of each step puts its first
# region at the end of the pages.  There a record of 8 bytes or an output, input, or path one byte
# short makes the call fault, so its result differs; a record of 24 bytes or an output one byte
# long keeps bytes that the call does not write; an output one byte late leaves out the byte that
# the call writes before it; and a write's input declared as an output receives no bytes, so the
# file holds the fill.  openat2's record lies inside the pages at that placement, and the byte
# after its 23 declared bytes, the fill, makes `resolve` invalid, so the call returns EINVAL.
FAULTS = {
    "clock-record-8": ("clock_gettime", 1, ("kind", ("record", 8)), "return"),
    "clock-record-24": ("clock_gettime", 1, ("kind", ("record", 24)), "coverage"),
    "read-late": ("read", 1, ("start", 1), "frame"),
    "read-long": ("read", 1, ("size", 1), "coverage"),
    "getrandom-short": ("getrandom", 0, ("size", -1), "return"),
    "write-short": ("write", 1, ("size", -1), "return"),
    "write-as-output": ("write", 1, ("kind", ("output",)), "value"),
    "openat2-record-short": ("openat2", 2, ("size", -1), "return"),
    "path-short": ("openat", 1, ("size", -1), "return"),
}


def constant(consts, datum):
    if isinstance(datum, int):
        return datum % 2 ** 64
    if isinstance(datum, str):
        return consts[datum]["arm64"]
    value = 0
    for name in datum:
        value |= consts[name]["arm64"]
    return value


def c_string(data):
    return '"' + "".join(chr(b) if 32 <= b < 127 and chr(b) not in '"\\?' else f"\\{b:03o}"
                         for b in data) + '"'


def declare(step, params, consts, fault):
    """The argument words and the declared regions of a step for the parameters `params`: each
    word a source and a value, and each region whether the call may write it, its size, the bytes
    from the address that the call receives to its start, and its first bytes.  `fault` (a
    parameter position and a change) alters the region of that parameter."""
    found, count = regions(params)
    args = [None] * count
    word = 0
    for param, datum in zip(params, step["args"], strict=True):
        if param[0] in ("value", "dirfd"):
            args[word] = ("CONSTANT", constant(consts, datum))
        elif param[0] == "fd":
            args[word] = ("DESCRIPTOR", datum)
        word += words(param)
    declared = []
    for position, output, address, size in found:
        datum = step["args"][position]
        if isinstance(datum, str):
            content = datum.encode() + b"\0"
        else:
            content = datum if isinstance(datum, bytes) and not output else b""
        match size:
            case ("path",):
                length = len(content)
            case ("word", counted):
                length = len(datum) if isinstance(datum, bytes) else datum
                args[counted] = ("CONSTANT", length)
            case ("bytes", n):
                length = n
        shift = 0
        if fault and fault[0] == position:
            change, amount = fault[1]
            if change == "size":
                length += amount
            elif change == "start":
                shift = amount
        assert 0 < length <= 256, (step["label"], length)
        args[address] = ("REGION", len(declared))
        declared.append((output, length, shift, content[:length]))
    assert None not in args, step["label"]
    return args, declared


def c_step(index, step, description, consts, fault=None):
    """The initializer of a step of the frame test."""
    params = list(description.params)
    if fault and fault[1][0] == "kind":
        params[fault[0]] = fault[1][1]
    args, declared = declare(step, params, consts, fault)
    match step["expect"]:
        case "opened":
            expect, ret = "OPENED", "0"
        case ("errno", name):
            expect, ret = "EXACT", f"-{name}"
        case ("status", n):
            expect, ret = "STATUS", str(n)
        case int(n):
            expect, ret = "EXACT", str(n)
    fills = step.get("fills", 0)
    if fills == "all":
        fills = next(length for output, length, _, _ in declared if output)
    kinds = ", ".join(lean_param(p)[1:] for p in params)
    head = [f".label = {c_string(step['label'].encode())}", f".call = \"{description.name}\"",
            f".number = {description.arm64}"]
    if description.opens:
        head.append(".opens = 1")
    if description.terminal:
        head.append(".terminal = 1")
    head.append(f".nargs = {len(args)}")
    slots = [f"{{{source}, {value:#x}ULL}}" if source == "CONSTANT" else f"{{{source}, {value}}}"
             for source, value in args]
    tail = [f".expect = {expect}"] + ([] if expect == "OPENED" else [f".ret = {ret}"])
    if fills:
        tail.append(f".fills = {fills}")
    tail += [f".setup = setup_{step.get('setup', 'none')}",
             f".check = check_{step.get('check', 'none')}"]
    if "offset" in step:
        tail.append(f".offset = {step['offset']}")
    if "expected" in step:
        tail += [f".expected = {c_string(step['expected'])}",
                 f".expected_length = {len(step['expected'])}"]
    if "mode" in step:
        tail.append(f".mode = 0{constant(consts, step['mode']):o}")
    if "native" in step:
        tail.append(f".native = {c_string(step['native'].encode())}")
    lines = [f"  /* {index}: {description.name} [{kinds}] */", *wrap("  {", head, ",", 3),
             *wrap("   .args = {", slots, "},", 4)]
    if declared:
        lines.append(f"   .nregions = {len(declared)}, .regions = {{")
        for number, (output, length, shift, content) in enumerate(declared):
            close = "}}," if number + 1 == len(declared) else "},"
            head = f"     {{{int(output)}, {length}, {shift}, {len(content)}, "
            pieces = [c_string(content[i:i + 16]) for i in range(0, len(content), 16)] or ['""']
            if len(head) + len(" ".join(pieces)) + len(close) <= WIDTH:
                lines.append(head + " ".join(pieces) + close)
            else:
                lines += [head.rstrip()] + [f"      {piece}" for piece in pieces]
                lines[-1] += close
    return lines + wrap("   ", tail, "},", 3)


FRAME_HEAD = r"""/* The frame test of the Linux call layer, generated by tools/linux-calls.py
   from the syzlang descriptions of tests/linux/syzlang/, syzkaller commit
   COMMIT.  Do not edit; run the generator.

   Each step issues one described call through do_svc, which loads X0 to X30, NZCV, and V0 to V31,
   issues SVC #0, and stores X0 to X30, SP, NZCV, FPCR, FPSR, TPIDR_EL0, and V0 to V31.  The
   description sets X8 and the argument registers; every other general register holds a pattern,
   and each of X0 to X5 that the description leaves unset holds a value whose low 32 bits,
   0xFFFFFFF7, are a negative descriptor, an invalid clock, invalid flags of getrandom, and open
   flags with O_PATH, which Linux reduces to O_PATH, O_DIRECTORY, O_NOFOLLOW, and O_CLOEXEC, so that
   openat fails on the test's files, none of which is a directory.  Each region of the description lies in two
   read-write pages between PROT_NONE pages, once ending at the upper PROT_NONE page and once
   beginning after the lower one, with the step's other region inside the pages, and each
   placement runs once with the pages filled with each of FILL_LIST.
   The checks of a run, in order: (1) the result; (2) every register but X0 kept its value; (3)
   every byte of the two pages outside the output region kept its value; (4) the step's value
   check; and (5) the properties of LeanExe/Linux/Replies.lean for the run's event.
   After the runs of a placement, (6) each of the leading bytes of the output region that the step
   makes the call write must differ from the fill in one of the runs.  A correct kernel fails that
   check only where a byte that varies, a random byte or a low byte of the clock, equals the fill
   of every run, with probability 256^-FILL_COUNT for a uniformly random byte; the comment on FILLS
   in tools/linux-calls.py derives a rate of RATE_TEXT for a run of
   tests/linux/sys-run.sh.  A terminal call runs once, in a child process, whose exit status is its
   result.  The descriptors that a step opens before its call, its files, and its output use the C
   library.

   Build: cc -O1 -static -o frame frame.c.  Run in an empty directory: frame [--qemu].  With
   --qemu the steps that QEMU 8.2.2 does not run as Linux does are skipped, each with its reason.
   Exit status: 0 when every step passes, 10 * STEP + CHECK at the first check that fails, 1 when
   the test itself fails, and 2 for a usage error. */
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

struct regs {
  uint64_t x[31];
  uint64_t sp;
  uint64_t nzcv;
  uint64_t fpcr;
  uint64_t fpsr;
  uint64_t tpidr;
  uint64_t pad[2];
  __uint128_t v[32];
} __attribute__((aligned(16)));

_Static_assert(__builtin_offsetof(struct regs, sp) == 248, "sp");
_Static_assert(__builtin_offsetof(struct regs, nzcv) == 256, "nzcv");
_Static_assert(__builtin_offsetof(struct regs, v) == 304, "v");

uint64_t g_sp;
uint64_t g_before[3];

/* do_svc(in, out): loads V0 to V31, NZCV, and X0 to X30 from in, with SP at out, issues SVC #0,
   and stores X0 to X30, SP, NZCV, FPCR, FPSR, TPIDR_EL0, and V0 to V31 through SP.  FPCR, FPSR,
   and TPIDR_EL0 before the call go to g_before. */
__asm__(
    ".text\n.global do_svc\n.type do_svc, %function\ndo_svc:\n"
    "stp x29, x30, [sp, #-176]!\n"
    "stp x19, x20, [sp, #16]\nstp x21, x22, [sp, #32]\nstp x23, x24, [sp, #48]\n"
    "stp x25, x26, [sp, #64]\nstp x27, x28, [sp, #80]\n"
    "stp d8, d9, [sp, #96]\nstp d10, d11, [sp, #112]\nstp d12, d13, [sp, #128]\n"
    "stp d14, d15, [sp, #144]\n"
    "adrp x9, g_sp\nadd x9, x9, :lo12:g_sp\nmov x10, sp\nstr x10, [x9]\n"
    "adrp x9, g_before\nadd x9, x9, :lo12:g_before\n"
    "mrs x10, fpcr\nstr x10, [x9, #0]\nmrs x10, fpsr\nstr x10, [x9, #8]\n"
    "mrs x10, tpidr_el0\nstr x10, [x9, #16]\n"
    "mov sp, x1\n"
    "add x9, x0, #304\n"
    "ldp q0, q1, [x9, #0]\nldp q2, q3, [x9, #32]\nldp q4, q5, [x9, #64]\nldp q6, q7, [x9, #96]\n"
    "ldp q8, q9, [x9, #128]\nldp q10, q11, [x9, #160]\nldp q12, q13, [x9, #192]\n"
    "ldp q14, q15, [x9, #224]\nldp q16, q17, [x9, #256]\nldp q18, q19, [x9, #288]\n"
    "ldp q20, q21, [x9, #320]\nldp q22, q23, [x9, #352]\nldp q24, q25, [x9, #384]\n"
    "ldp q26, q27, [x9, #416]\nldp q28, q29, [x9, #448]\nldp q30, q31, [x9, #480]\n"
    "ldr x9, [x0, #256]\nmsr nzcv, x9\n"
    "ldp x2, x3, [x0, #16]\nldp x4, x5, [x0, #32]\nldp x6, x7, [x0, #48]\nldp x8, x9, [x0, #64]\n"
    "ldp x10, x11, [x0, #80]\nldp x12, x13, [x0, #96]\nldp x14, x15, [x0, #112]\n"
    "ldp x16, x17, [x0, #128]\nldp x18, x19, [x0, #144]\nldp x20, x21, [x0, #160]\n"
    "ldp x22, x23, [x0, #176]\nldp x24, x25, [x0, #192]\nldp x26, x27, [x0, #208]\n"
    "ldp x28, x29, [x0, #224]\nldr x30, [x0, #240]\nldp x0, x1, [x0, #0]\n"
    "svc #0\n"
    "stp x0, x1, [sp, #0]\nstp x2, x3, [sp, #16]\nstp x4, x5, [sp, #32]\nstp x6, x7, [sp, #48]\n"
    "stp x8, x9, [sp, #64]\nstp x10, x11, [sp, #80]\nstp x12, x13, [sp, #96]\n"
    "stp x14, x15, [sp, #112]\nstp x16, x17, [sp, #128]\nstp x18, x19, [sp, #144]\n"
    "stp x20, x21, [sp, #160]\nstp x22, x23, [sp, #176]\nstp x24, x25, [sp, #192]\n"
    "stp x26, x27, [sp, #208]\nstp x28, x29, [sp, #224]\nstr x30, [sp, #240]\n"
    "mov x0, sp\nstr x0, [sp, #248]\n"
    "mrs x0, nzcv\nstr x0, [sp, #256]\nmrs x0, fpcr\nstr x0, [sp, #264]\n"
    "mrs x0, fpsr\nstr x0, [sp, #272]\nmrs x0, tpidr_el0\nstr x0, [sp, #280]\n"
    "add x0, sp, #304\n"
    "stp q0, q1, [x0, #0]\nstp q2, q3, [x0, #32]\nstp q4, q5, [x0, #64]\nstp q6, q7, [x0, #96]\n"
    "stp q8, q9, [x0, #128]\nstp q10, q11, [x0, #160]\nstp q12, q13, [x0, #192]\n"
    "stp q14, q15, [x0, #224]\nstp q16, q17, [x0, #256]\nstp q18, q19, [x0, #288]\n"
    "stp q20, q21, [x0, #320]\nstp q22, q23, [x0, #352]\nstp q24, q25, [x0, #384]\n"
    "stp q26, q27, [x0, #416]\nstp q28, q29, [x0, #448]\nstp q30, q31, [x0, #480]\n"
    "adrp x9, g_sp\nadd x9, x9, :lo12:g_sp\nldr x9, [x9]\nmov sp, x9\n"
    "ldp x19, x20, [sp, #16]\nldp x21, x22, [sp, #32]\nldp x23, x24, [sp, #48]\n"
    "ldp x25, x26, [sp, #64]\nldp x27, x28, [sp, #80]\n"
    "ldp d8, d9, [sp, #96]\nldp d10, d11, [sp, #112]\nldp d12, d13, [sp, #128]\n"
    "ldp d14, d15, [sp, #144]\n"
    "ldp x29, x30, [sp], #176\nret\n.size do_svc, .-do_svc\n");
void do_svc(struct regs *in, struct regs *out);

#define UNSET 0x77777770FFFFFFF7ULL

/* An argument word: a constant, the descriptor of a slot that the setup opens, or the address
   that the call receives for a region. */
enum source { CONSTANT, DESCRIPTOR, REGION };
enum expect { EXACT, OPENED, STATUS };
enum check { RETURN = 1, REGISTERS, FRAME, VALUE, REPLY, COVERAGE };

struct arg {
  enum source source;
  uint64_t value;
};

/* A region as the description declares it: whether the call may write it, its size, the bytes
   from the address that the call receives to its start, and its first bytes. */
struct region {
  int output;
  long size;
  long shift;
  long length;
  const char *bytes;
};

struct step;
typedef int setup_fn(const struct step *);
typedef const char *check_fn(const struct step *, uint64_t, const unsigned char *);

struct step {
  const char *label;
  const char *call;
  uint64_t number;
  int opens;
  int terminal;
  int nargs;
  struct arg args[6];
  int nregions;
  struct region regions[2];
  enum expect expect;
  int64_t ret;
  long fills;
  setup_fn *setup;
  check_fn *check;
  long offset;
  const char *expected;
  long expected_length;
  unsigned mode;
  const char *native;
};

static const char data[] = DATA;
static const unsigned char fills[] = FILL_ARRAY;
static long page;
static unsigned char *rw;
static unsigned char *prior;
static unsigned char *covered;
static int qemu;
static int fds[2];
static int lowest;
static struct timespec now;
static struct regs rin, rout;

static void harness(const char *what) {
  printf("harness: %s: %s\n", what, strerror(errno));
  exit(1);
}

static int is_error(uint64_t r) { return r > (uint64_t)-4096; }

static uint64_t le(const unsigned char *p, long n) {
  uint64_t v = 0;
  for (long i = n - 1; i >= 0; i--) v = v << 8 | p[i];
  return v;
}

static int lowest_free(void) {
  int d = 0;
  while (fcntl(d, F_GETFD) != -1) d++;
  if (errno != EBADF) harness("fcntl");
  return d;
}

static int setup_none(const struct step *s) {
  (void)s;
  return 0;
}

/* Removes created and opens data twice, closing the first descriptor, so that the lowest free
   descriptor lies below an open one. */
static int setup_hole(const struct step *s) {
  (void)s;
  if (unlink("created") != 0 && errno != ENOENT) return -1;
  int first = open("data", O_RDONLY);
  if (first < 0) return -1;
  fds[1] = open("data", O_RDONLY);
  if (fds[1] < 0) return -1;
  return close(first);
}

/* Opens data at the step's offset in slot 0. */
static int setup_data(const struct step *s) {
  fds[0] = open("data", O_RDONLY);
  if (fds[0] < 0 || lseek(fds[0], s->offset, SEEK_SET) != s->offset) return -1;
  return 0;
}

/* Opens the empty file written in slot 0. */
static int setup_written(const struct step *s) {
  (void)s;
  fds[0] = open("written", O_WRONLY | O_CREAT | O_TRUNC, 0600);
  return fds[0] < 0 ? -1 : 0;
}

/* Reads the C library's realtime clock. */
static int setup_clock(const struct step *s) {
  (void)s;
  return clock_gettime(CLOCK_REALTIME, &now);
}

static const char *check_none(const struct step *s, uint64_t ret, const unsigned char *out) {
  (void)s, (void)ret, (void)out;
  return NULL;
}

static const char *check_created(const struct step *s, uint64_t ret, const unsigned char *out) {
  struct stat st;
  (void)out;
  if (fstat((int)ret, &st) != 0) harness("fstat");
  if (!S_ISREG(st.st_mode) || (st.st_mode & 07777) != s->mode)
    return "the created file is not a regular file of the step's mode";
  return NULL;
}

static const char *check_closed(const struct step *s, uint64_t ret, const unsigned char *out) {
  struct regs again;
  (void)s, (void)ret, (void)out;
  do_svc(&rin, &again);
  return (int64_t)again.x[0] == -EBADF ? NULL : "a second close did not return EBADF";
}

static const char *check_data(const struct step *s, uint64_t ret, const unsigned char *out) {
  return memcmp(out, data + s->offset, ret) == 0 ? NULL : "the bytes read differ from the file";
}

static const char *check_written(const struct step *s, uint64_t ret, const unsigned char *out) {
  char got[256];
  (void)ret, (void)out;
  int d = open("written", O_RDONLY);
  if (d < 0) harness("open written");
  ssize_t n = read(d, got, sizeof got);
  if (n < 0 || close(d) != 0) harness("read written");
  if (n != s->expected_length || memcmp(got, s->expected, n) != 0)
    return "the file holds other bytes than the input region";
  return NULL;
}

static const char *check_clock(const struct step *s, uint64_t ret, const unsigned char *out) {
  int64_t sec = (int64_t)le(out, 8);
  (void)s, (void)ret;
  if (sec + 5 < now.tv_sec || sec > now.tv_sec + 5)
    return "tv_sec is not within 5 seconds of the C library's realtime clock";
  return NULL;
}

"""

FRAME_ENGINE = r"""
/* The properties of LeanExe/Linux/Replies.lean for the event of a run: FreshOpens, with the
   lowest free descriptor that Linux gives; the release of the descriptor of a close, which the
   next open receives; NsecBound; RandomCount; and WrittenPrefix.  `out` and `before` are the
   output region's bytes after and before the call. */
static const char *replies(const struct step *s, uint64_t ret, const unsigned char *out,
                           const unsigned char *before, long size) {
  int closes = strcmp(s->call, "close") == 0, reads = strcmp(s->call, "read") == 0;
  int random = strcmp(s->call, "getrandom") == 0;
  if (s->opens && !is_error(ret) && (ret >= (uint64_t)1 << 31 || (int)ret != lowest))
    return "FreshOpens: the descriptor is not the lowest one that was not open";
  if (closes) {
    int d = (int)(rin.x[0] & 0xFFFFFFFF);
    if (fcntl(d, F_GETFD) != -1 || errno != EBADF) return "the closed descriptor is open";
    int next = open("data", O_RDONLY);
    if (next < 0 || close(next) != 0) harness("open data");
    fds[0] = -1;
    if (next != d) return "the next open did not receive the closed descriptor";
  }
  if (strcmp(s->call, "clock_gettime") == 0 && ret == 0 && out && size > 8 &&
      le(out + 8, size < 16 ? size - 8 : 8) >= 1000000000)
    return "NsecBound: tv_nsec is not below 10^9";
  if (random && !is_error(ret) && !(ret <= rin.x[1] && (rin.x[1] == 0 || ret > 0)))
    return "RandomCount: the count lies above the length or is 0";
  if ((reads || random) && out && ret <= (uint64_t)size &&
      memcmp(out + ret, before + ret, size - ret) != 0)
    return "WrittenPrefix: a byte after the returned count changed";
  return NULL;
}

static void fail(int n, const struct step *s, int p, int fill, enum check c, const char *why) {
  printf("fail: step %d (%s), ", n, s->label);
  if (s->nregions) printf("region %d at the %s, ", p / 2, p % 2 ? "start" : "end");
  if (fill >= 0) printf("fill 0x%02X, ", fill);
  printf("check %d: %s\n", c, why);
  exit(10 * n + c);
}

static uint64_t pattern(int i) { return 0x1111111111111111ULL * (uint64_t)(i % 15 + 1) + i; }

static void registers(const struct step *s, unsigned char *const at[2]) {
  for (int i = 0; i < 31; i++) rin.x[i] = pattern(i);
  for (int i = 0; i < 6; i++) rin.x[i] = UNSET + ((uint64_t)i << 32);
  for (int i = 0; i < s->nargs; i++) {
    const struct arg *a = &s->args[i];
    switch (a->source) {
    case CONSTANT: rin.x[i] = a->value; break;
    case DESCRIPTOR: rin.x[i] = (uint64_t)(int64_t)fds[a->value]; break;
    case REGION: rin.x[i] = (uint64_t)(at[a->value] - s->regions[a->value].shift); break;
    }
  }
  rin.x[8] = s->number;
  rin.nzcv = 0x60000000;
  for (int i = 0; i < 32; i++) rin.v[i] = (__uint128_t)pattern(i) << 64 | ~pattern(i);
}

static const char *changed_register(void) {
  static char why[32];
  for (int i = 1; i < 31; i++)
    if (rout.x[i] != rin.x[i]) {
      snprintf(why, sizeof why, "X%d changed", i);
      return why;
    }
  if (rout.sp != (uint64_t)&rout) return "SP changed";
  if (rout.nzcv != rin.nzcv) return "NZCV changed";
  if (rout.fpcr != g_before[0]) return "FPCR changed";
  if (rout.fpsr != g_before[1]) return "FPSR changed";
  if (rout.tpidr != g_before[2]) return "TPIDR_EL0 changed";
  for (int i = 0; i < 32; i++)
    if (rout.v[i] != rin.v[i]) {
      snprintf(why, sizeof why, "V%d changed", i);
      return why;
    }
  return NULL;
}

/* Runs step n at placement p with the pages filled with fill and checks the run.  Returns the
   output region's address, or NULL when the step has none. */
static unsigned char *run_once(int n, const struct step *s, int p, int fill) {
  unsigned char *at[2] = {NULL, NULL}, *out = NULL;
  long size = 0;
  char why[96];
  const char *found;
  memset(rw, fill, 2 * page);
  for (int r = 0; r < s->nregions; r++) {
    const struct region *g = &s->regions[r];
    if (r == p / 2) at[r] = p % 2 ? rw : rw + 2 * page - g->size;
    else at[r] = rw + page - 256 + 512 * r;
    if (g->length) memcpy(at[r], g->bytes, g->length);
    if (g->output) out = at[r], size = g->size;
  }
  fds[0] = fds[1] = -1;
  if (s->setup(s) != 0) harness("setup");
  memcpy(prior, rw, 2 * page);
  lowest = lowest_free();
  registers(s, at);
  do_svc(&rin, &rout);
  uint64_t ret = rout.x[0];
  if (s->expect == EXACT ? ret != (uint64_t)s->ret : is_error(ret) || ret >= (uint64_t)1 << 31) {
    snprintf(why, sizeof why, "the call returned %lld", (long long)ret);
    fail(n, s, p, fill, RETURN, why);
  }
  if ((found = changed_register())) fail(n, s, p, fill, REGISTERS, found);
  for (long i = 0; i < 2 * page; i++)
    if (rw[i] != prior[i] && !(out && rw + i >= out && rw + i < out + size)) {
      snprintf(why, sizeof why, "byte %ld of the pages, outside the output region, changed", i);
      fail(n, s, p, fill, FRAME, why);
    }
  if ((found = s->check(s, ret, out))) fail(n, s, p, fill, VALUE, found);
  if ((found = replies(s, ret, out, out ? prior + (out - rw) : NULL, size)))
    fail(n, s, p, fill, REPLY, found);
  if (s->opens && !is_error(ret) && close((int)ret) != 0) harness("close");
  for (int i = 0; i < 2; i++)
    if (fds[i] >= 0 && close(fds[i]) != 0) harness("close");
  return out;
}

static void run_terminal(int n, const struct step *s) {
  unsigned char *const none[2] = {NULL, NULL};
  int status;
  registers(s, none);
  fflush(stdout);
  pid_t pid = fork();
  if (pid < 0) harness("fork");
  if (pid == 0) {
    do_svc(&rin, &rout);
    _exit(255);
  }
  if (waitpid(pid, &status, 0) != pid) harness("waitpid");
  if (!WIFEXITED(status) || WEXITSTATUS(status) != s->ret)
    fail(n, s, 0, -1, RETURN, "the process did not exit with the expected status");
}

/* Runs step n and returns 1, or 0 when it does not run under QEMU. */
static int run_step(int n, const struct step *s) {
  if (qemu && s->native) {
    printf("skip: step %d (%s): %s\n", n, s->label, s->native);
    return 0;
  }
  if (s->terminal) {
    run_terminal(n, s);
    printf("pass: step %d (%s), 1 run\n", n, s->label);
    return 1;
  }
  int placements = s->nregions ? 2 * s->nregions : 1;
  for (int p = 0; p < placements; p++) {
    memset(covered, 0, 2 * page);
    for (unsigned f = 0; f < sizeof fills; f++) {
      int fill = fills[f];
      unsigned char *out = run_once(n, s, p, fill);
      for (long i = 0; i < s->fills; i++) covered[i] |= out[i] != fill;
    }
    for (long i = 0; i < s->fills; i++)
      if (!covered[i]) {
        char why[96];
        snprintf(why, sizeof why, "byte %ld of the output region kept the fill in every run", i);
        fail(n, s, p, -1, COVERAGE, why);
      }
  }
  printf("pass: step %d (%s), %d runs\n", n, s->label, (int)sizeof fills * placements);
  return 1;
}

int main(int argc, char **argv) {
  if (argc > 2 || (argc == 2 && strcmp(argv[1], "--qemu") != 0)) {
    fprintf(stderr, "Usage: %s [--qemu]\n", argv[0]);
    return 2;
  }
  qemu = argc == 2;
  page = sysconf(_SC_PAGESIZE);
  unsigned char *lo = mmap(NULL, 4 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS,
                           -1, 0);
  if (lo == MAP_FAILED) harness("mmap");
  if (mprotect(lo, page, PROT_NONE) != 0 || mprotect(lo + 3 * page, page, PROT_NONE) != 0)
    harness("mprotect");
  rw = lo + page;
  prior = malloc(2 * page);
  covered = malloc(2 * page);
  if (!prior || !covered) harness("malloc");
  umask(0);
  int d = open("data", O_WRONLY | O_CREAT | O_EXCL, 0644);
  if (d < 0 || write(d, data, sizeof data - 1) != sizeof data - 1 || close(d) != 0)
    harness("write data in an empty directory");
  int passed = 0, skipped = 0;
  for (unsigned i = 0; i < sizeof steps / sizeof steps[0]; i++) {
    if (run_step(i + 1, &steps[i])) passed++;
    else skipped++;
  }
  printf("frame test: %d steps passed, %d skipped\n", passed, skipped);
  return 0;
}
"""


def render_frame(descriptions, consts, plan, fault=None):
    """The frame test of the steps `plan`.  `fault`, an entry of FAULTS, alters the regions that
    its call's description declares."""
    by_name = {d.name: d for d in descriptions}
    missing = [d.name for d in descriptions if d.name not in {s["call"] for s in plan}]
    assert not missing, f"no step calls {missing}"
    assert 10 * len(plan) + max(CHECKS.values()) < 128, "too many steps for distinct statuses"
    body = ["static const struct step steps[] = {"]
    for index, step in enumerate(plan, 1):
        change = fault[1:3] if fault and fault[0] == step["call"] else None
        body += c_step(index, step, by_name[step["call"]], consts, change)
    body += ["};"]
    exponent = math.floor(math.log10(RATE))
    names = [f"{fill:#04X}".replace("0X", "0x") for fill in FILLS]
    head = (FRAME_HEAD.replace("COMMIT", COMMIT).replace("DATA;", c_string(DATA) + ";")
            .replace("FILL_ARRAY", "{" + ", ".join(names) + "}")
            .replace("FILL_LIST", ", ".join(names[:-1]) + ", and " + names[-1])
            .replace("FILL_COUNT", str(len(FILLS)))
            .replace("RATE_TEXT", f"about {RATE / 10 ** exponent:.1f} * 10^{exponent}"))
    return head + "\n".join(body) + "\n" + FRAME_ENGINE


def fault_status(plan, fault):
    """The exit status that the frame test with `fault` must give, the failure of the fault's
    check at the first step of its call, and whether that step runs only natively."""
    call, _, _, check = fault
    index = next(i for i, step in enumerate(plan, 1) if step["call"] == call)
    return 10 * index + CHECKS[check], "native" in plan[index - 1]


def option(rest, name):
    if name not in rest:
        return None
    index = rest.index(name)
    value = Path(rest[index + 1])
    del rest[index:index + 2]
    return value


def main():
    check = "--check" in sys.argv
    rest = [a for a in sys.argv[1:] if a != "--check"]
    faults = option(rest, "--frame-faults")
    directory = Path(rest[0] if rest else "tests/linux/syzlang")
    try:
        descriptions, consts = load(directory)
    except Refusal as refusal:
        sys.exit(f"refused: {refusal}")
    layouts = {layout.name: layout for d in descriptions for layout, _ in d.records}
    plan = steps(consts, layouts)
    if faults is not None:
        faults.mkdir(parents=True, exist_ok=True)
        for name, fault in FAULTS.items():
            (faults / f"{name}.c").write_text(render_frame(descriptions, consts, plan, fault))
            status, native = fault_status(plan, fault)
            print(name, status, "native" if native else "any")
        return
    generated = {TABLE: render_table(descriptions),
                 FRAME: render_frame(descriptions, consts, plan)}
    failed = False
    for path, text in generated.items():
        target = Path(path)
        if not check:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
            print(f"wrote {path}")
            continue
        current = target.read_text() if target.exists() else ""
        if current != text:
            sys.stdout.writelines(difflib.unified_diff(
                current.splitlines(keepends=True), text.splitlines(keepends=True),
                f"{path} (committed)", f"{path} (generated)"))
            failed = True
    for source in sorted(Path("LeanExe/Linux").glob("*.lean")):
        if str(source) == TABLE:
            continue
        for name in re.findall(r"^\s*def (\w+) : Call\b", source.read_text(), re.M):
            print(f"{source}: {name} is a description outside the generated file")
            failed = True
    if check:
        print(f"{len(descriptions)} descriptions; generated files "
              f"{'differ' if failed else 'match the syzlang descriptions'}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
