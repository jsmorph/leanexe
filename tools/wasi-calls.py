# /// script
# requires-python = ">=3.12"
# ///
"""Generate the flat call descriptions, typed functions, reflection equations, and frame test from
the pinned witx.

Usage: uv run tools/wasi-calls.py [--write | --frame-faults DIR | --reject-sweep DIR] [WITX_DIR]

WITX_DIR holds wasi_snapshot_preview1.witx and typenames.witx of WebAssembly/WASI commit
fae981bae14809d91f9bc2d63852d461f331d161, by default tests/wasi/witx.  The script lowers every
function of the witx to core parameter kinds, renders the Lean descriptions of the flat functions,
their typed functions and record result types, the reflection equations of the typed functions
and Flat instances of records, and the frame test of tests/wasi/sys, and compares each rendering
with the committed file, printing a unified diff and exiting with status 1 when one differs.  With
--write it writes the files instead.  With --frame-faults DIR it writes to DIR one frame test for
each seeded fault of FAULTS and prints the fault's name and the exit status that the test must
give: 1, the host's status for a trap, when the fault moves a record, and else the status of the
frame check of the altered step.  With --reject-sweep DIR it writes to DIR one module for each
value of the rejection sweep, the last value of each enum parameter and the next one and each
single bit of each flags parameter, and prints the module's name, "trap" when the description's
rule rejects the value, which Wasmtime 44 must then trap on, or "errno" when the call must return,
and the call's name and arguments, from which tests/wasi/SysSweep.lean computes Call.reject.  It
also fails when a Lean file of LeanExe/Wasi other than the generated one has a definition
`def NAME : Call`.

The lowering: an enum of n values is enum32 n whatever its tag width, a flags type is flags32 or,
with a 64-bit representation, flags64, with the mask of its flags, and another parameter whose
representation is 64 bits wide is word64 and else word32; a string, or a const_pointer followed by
a $size parameter, is input; a pointer to bytes followed by a $size parameter is output; another
pointer is reported, with scale and alignment 4 and not shown when it points to pointers, whose
entries are guest addresses, and with scale and alignment 1 and shown when it points to bytes; each
component of an expected result is result32 or result64 by its width, or a record of its size,
alignment, and fields when it is a record or a union.  A record's fields lie at the next multiple of
their alignment, a union's payload after its tag at the payload's alignment, and the size is rounded
up to the largest alignment.  A function with reported regions NAME_get has the reporter
NAME_sizes_get.  A function that takes a list or a pointer to records, or does not return, is not
flat.
"""
import difflib
import re
import sys
from pathlib import Path

SIZES = {"u8": 1, "u16": 2, "u32": 4, "u64": 8, "s8": 1, "s16": 2, "s32": 4, "s64": 8,
         "char8": 1}
WIDTH = 100


def tokens(text):
    text = re.sub(r";;[^\n]*", "", text)
    return re.findall(r'\(|\)|"[^"]*"|[^\s()]+', text)


def parse(text):
    stack = [[]]
    for token in tokens(text):
        if token == "(":
            stack.append([])
        elif token == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(token)
    return stack[0]


def resolve(table, ty):
    while isinstance(ty, str) and ty.startswith("$"):
        ty = table[ty]
    return ty


def annotation(form, keys):
    for x in form[1:]:
        if isinstance(x, list) and x[:1] == ["@witx"] and x[1] in keys:
            return x[2]
    return None


def cases(form):
    return [x for x in form[1:] if isinstance(x, str) and x.startswith("$")]


def is_pointer(ty):
    return isinstance(ty, list) and ty[:2] in (["@witx", "pointer"], ["@witx", "const_pointer"])


def scalar_size(table, ty):
    """The size in bytes of a scalar, enum, flags, or handle type, or None for another type."""
    ty = resolve(table, ty)
    if isinstance(ty, str):
        return SIZES.get(ty)
    if ty[0] in ("enum", "flags"):
        return SIZES[annotation(ty, ("tag", "repr")) or "u32"]
    if ty[0] == "handle":
        return 4
    return None


def layout(table, ty):
    """The size, alignment, and fields (name, offset, width) of a type in linear memory."""
    resolved = resolve(table, ty)
    size = scalar_size(table, resolved)
    if size is not None:
        return size, size, [("", 0, size)]
    if resolved[0] == "record":
        offset, align, fields = 0, 1, []
        for field in [x for x in resolved[1:] if isinstance(x, list) and x[0] == "field"]:
            fsize, falign, inner = layout(table, field[2])
            offset = (offset + falign - 1) // falign * falign
            name = field[1].lstrip("$")
            fields += [(name + ("_" + n if n else ""), offset + o, w) for n, o, w in inner]
            offset += fsize
            align = max(align, falign)
        return (offset + align - 1) // align * align, align, fields
    if resolved[0] == "union":
        tag_size = scalar_size(table, annotation(resolved, ("tag",)))
        variants = [layout(table, case) for case in cases(resolved)]
        payload_align = max(a for _, a, _ in variants)
        payload_size = max(s for s, _, _ in variants)
        offset = (tag_size + payload_align - 1) // payload_align * payload_align
        align = max(tag_size, payload_align)
        fields = [("tag", 0, tag_size)]
        for case, (_, _, inner) in zip(cases(resolved), variants):
            fields += [(n or case.lstrip("$"), offset + o, w) for n, o, w in inner]
        return (offset + payload_size + align - 1) // align * align, align, fields
    raise ValueError(f"no layout for {resolved}")


def word_kind(table, ty):
    resolved = resolve(table, ty)
    if isinstance(resolved, list) and resolved[0] == "enum":
        return ("enum32", len(cases(resolved)))
    if isinstance(resolved, list) and resolved[0] == "flags":
        mask = (1 << len(cases(resolved))) - 1
        return ("flags64" if annotation(resolved, ("repr",)) == "u64" else "flags32", mask)
    size = scalar_size(table, ty)
    if size is None:
        return None
    return ("word64",) if size == 8 else ("word32",)


class Function:
    """A witx function: its name, its kinds or the reason it is not flat, and the witx names of
    the arguments its typed function takes."""

    def __init__(self, table, form):
        self.name = form[2][1].strip('"')
        self.kinds, self.reason, self.arguments = None, None, []
        try:
            self.kinds = self.lower(table, form)
        except NotFlat as error:
            self.reason = str(error)

    def lower(self, table, form):
        if any(isinstance(x, list) and x[:2] == ["@witx", "noreturn"] for x in form):
            raise NotFlat("does not return")
        params = [x for x in form if isinstance(x, list) and x[:1] == ["param"]]
        kinds, index = [], 0
        while index < len(params):
            name, ty = params[index][1], params[index][2]
            following = params[index + 1] if index + 1 < len(params) else None
            sized = following is not None and following[2] == "$size"
            resolved = resolve(table, ty)
            if resolved == "string":
                kinds.append(("input",))
                self.arguments.append(name)
            elif is_pointer(resolved):
                pointee = resolve(table, resolved[2])
                if resolved[1] == "const_pointer" and sized:
                    kinds.append(("input",))
                    self.arguments.append(name)
                    index += 1
                elif resolved[1] == "pointer" and sized and pointee == "u8":
                    kinds.append(("output",))
                    self.arguments.append(following[1])
                    index += 1
                elif is_pointer(pointee):
                    kinds.append(("reported", 4, 4, False))
                elif pointee == "u8":
                    kinds.append(("reported", 1, 1, True))
                else:
                    raise NotFlat(f"parameter {name} points to {pointee}")
            else:
                kind = word_kind(table, ty)
                if kind is None:
                    raise NotFlat(f"parameter {name} has type {resolved}")
                kinds.append(kind)
                self.arguments.append(name)
            index += 1
        for result in [x for x in form if isinstance(x, list) and x[:1] == ["result"]]:
            expected = result[2]
            values = [x for x in expected[1:] if not (isinstance(x, list) and x[:1] == ["error"])]
            for value in values:
                parts = value[1:] if isinstance(value, list) and value[0] == "tuple" else [value]
                for part in parts:
                    resolved = resolve(table, part)
                    if isinstance(resolved, list) and resolved[0] in ("record", "union"):
                        kinds.append(("record", *layout(table, part), part.lstrip("$")))
                    else:
                        size = scalar_size(table, part)
                        if size is None:
                            raise NotFlat(f"result component {part} is not a word")
                        kinds.append(("result64",) if size == 8 else ("result32",))
        return kinds

    @property
    def lean(self):
        return camel(self.name)

    @property
    def reporter(self):
        if any(kind[0] == "reported" for kind in self.kinds):
            return self.name.removesuffix("_get") + "_sizes_get"
        return None


class NotFlat(Exception):
    pass


def functions(directory):
    table = {}
    for form in parse((directory / "typenames.witx").read_text()):
        if isinstance(form, list) and form and form[0] == "typename":
            table[form[1]] = form[2]
    found = []

    def walk(form):
        if isinstance(form, list):
            if form[:2] == ["@interface", "func"]:
                found.append(Function(table, form))
            for x in form:
                walk(x)

    walk(parse((directory / "wasi_snapshot_preview1.witx").read_text()))
    return found


def camel(name):
    head, *rest = name.lstrip("$").split("_")
    return head + "".join(part.capitalize() for part in rest)


def pascal(name):
    camelled = camel(name)
    return camelled[0].upper() + camelled[1:]


def wrap(head, items, tail, indent, separator=","):
    """`head`, the `items` separated by `separator` and a space, and `tail` on one line, or broken
    before an item, with continuation lines indented by `indent` spaces, when the line exceeds the
    width."""
    line = head + (separator + " ").join(items) + tail
    if len(line) <= WIDTH:
        return [line]
    lines, current = [], head
    for index, item in enumerate(items):
        piece = item + (separator if index + 1 < len(items) else tail)
        if len(current) + len(piece) + 1 > WIDTH and current.strip():
            lines.append(current.rstrip())
            current = " " * indent
        current += ("" if current.endswith(("[", " ", "⟨")) else " ") + piece
    lines.append(current)
    return lines


def lean_param(kind):
    match kind:
        case ("enum32", count):
            return f".enum32 {count}"
        case ("flags32" | "flags64" as name, mask):
            return f".{name} 0x{mask:x}"
        case ("reported", scale, align, shown):
            return f".reported {scale} {align} {'true' if shown else 'false'}"
        case ("record", size, align, fields, _):
            return f".record {size} {align} [{', '.join(f'({o}, {w})' for _, o, w in fields)}]"
        case (name,):
            return f".{name}"


def description(function):
    params = [lean_param(kind) for kind in function.kinds]
    reporter = function.reporter
    lines = [f"def {function.lean} : Call :="]
    head = f'  {{ name := "{function.name}", params := ['
    tail = "]" + ("," if reporter else " }")
    lines += wrap(head, params, tail, 6)
    if reporter:
        lines.append(f'    reporter := some "{reporter}" }}')
    return "\n".join(lines) + "\n"


def render_calls(flat):
    return "\n".join([
        "import LeanExe.Wasi.Calls",
        "",
        "/-!",
        "The descriptions of the flat Preview 1 functions, which `tools/wasi-calls.py` generates "
        "from the",
        "pinned witx (WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`).  Its "
        "check fails",
        "when this file differs from its output.",
        "-/",
        "",
        "namespace LeanExe.Wasi.Call",
        "",
        "\n".join(description(function) for function in flat),
        "end LeanExe.Wasi.Call",
        "",
    ])


HAND_WRITTEN = {"clock_time_get", "random_get", "args_sizes_get", "args_get", "environ_get"}
RESULT_TYPES = {
    (): "UInt64",
    ("result32",): "WordResult",
    ("result64",): "WordResult",
    ("result32", "result32"): "ArgsSizes",
    ("output",): "BytesResult",
    ("output", "result32"): "BytesCountResult",
}


def outputs(function):
    return [kind for kind in function.kinds
            if kind[0] in ("output", "result32", "result64", "record")]


def result_type(function):
    record = [kind for kind in function.kinds if kind[0] == "record"]
    if record:
        return pascal(record[0][4]) + "Result"
    return RESULT_TYPES[tuple(kind[0] for kind in outputs(function))]


def result_value(function):
    shapes = [kind[0] for kind in outputs(function)]
    if not shapes:
        return "reply.errno"
    if shapes == ["record"]:
        fields = [f"reply.field 0 {offset} {width}" for _, offset, width in outputs(function)[0][3]]
        return "⟨reply.errno, " + ", ".join(fields) + "⟩"
    parts = [f"reply.bytes {i}" if shape == "output" else f"reply.word {i}"
             for i, shape in enumerate(shapes)]
    return "⟨reply.errno, " + ", ".join(parts) + "⟩"


def typed_function(function):
    takes = [kind for kind in function.kinds
             if kind[0] not in ("result32", "result64", "record", "reported")]
    names = [camel(name) for name in function.arguments]
    binders = [f"({name} : {'Bytes' if kind[0] == 'input' else 'UInt64'})"
               for name, kind in zip(names, takes)]
    args = [f".bytes {name}" if kind[0] == "input" else
            f".space {name}" if kind[0] == "output" else f".word {name}"
            for name, kind in zip(names, takes)]
    head = f"def {function.lean}" + "".join(" " + b for b in binders) + \
        f" : Action {result_type(function)} :="
    lines = [head] if len(head) <= WIDTH else \
        wrap(f"def {function.lean} ", binders, f" : Action {result_type(function)} :=", 4)
    lines = [line.replace(",", "") for line in lines] if len(head) > WIDTH else lines
    lines += wrap(f"  .sys .{function.lean} [", args, f"] fun reply =>", 4)
    value = result_value(function)
    if value.startswith("⟨"):
        lines += wrap("    .pure ⟨", value[1:-1].split(", "), "⟩", 6)
    else:
        lines.append(f"    .pure {value}")
    return "\n".join(lines) + "\n"


def record_structure(kind):
    name = pascal(kind[4]) + "Result"
    fields = "\n".join(f"  {camel(field)} : UInt64" for field, _, _ in kind[3])
    return f"structure {name} where\n  errno : UInt64\n{fields}\n"


def render_typed(flat):
    records = {}
    for function in flat:
        for kind in function.kinds:
            if kind[0] == "record":
                records[kind[4]] = kind
    return "\n".join([
        "import LeanExe.Wasi.CallTable",
        "import LeanExe.Wasi.Sys",
        "",
        "/-!",
        "Typed functions of the flat Preview 1 functions, which `tools/wasi-calls.py` generates "
        "from the",
        "pinned witx with the descriptions of `LeanExe/Wasi/CallTable.lean`.  A record result "
        "holds the",
        "errno and the record's fields as words.  Its check fails when this file differs from its "
        "output.",
        "-/",
        "",
        "namespace LeanExe.Wasi",
        "",
        "\n".join(record_structure(kind) for kind in records.values()),
        "\n".join(typed_function(f) for f in flat if f.name not in HAND_WRITTEN),
        "end LeanExe.Wasi",
        "",
    ])


FLATTEN = {
    "UInt64": "(fun value : UInt64 => value)",
    "WordResult": "(Flat.flat : WordResult → UInt64 × UInt64)",
    "ArgsSizes": "(Flat.flat : ArgsSizes → UInt64 × UInt64 × UInt64)",
    "BytesResult": "(Flat.flat : BytesResult → UInt64 × LeanExe.Bytes)",
    "BytesCountResult": "(Flat.flat : BytesCountResult → UInt64 × UInt64 × LeanExe.Bytes)",
}


def reflected(function):
    """Whether `reflect` maps the generated typed function to one `sys` command."""
    return function.name not in HAND_WRITTEN


def record_kind(function):
    """The function's record kind, or None."""
    return next((kind for kind in function.kinds if kind[0] == "record"), None)


def form(function):
    """The call's `SysForm` as a term of its equation and as an expression of its table entry."""
    record = record_kind(function)
    if record is not None:
        return f"(.record {len(record[3])})", f"recordForm {len(record[3])}"
    words = sum(1 for kind in function.kinds if kind[0] in ("result32", "result64"))
    output = "true" if any(kind[0] == "output" for kind in function.kinds) else "false"
    return f"(.flat {words} {output})", f"flatForm {words} {output}"


def flatten(function):
    """The tokens of the map from the typed function's result to the command's value."""
    record = record_kind(function)
    if record is None:
        return [FLATTEN[result_type(function)]]
    words = " × ".join(["UInt64"] * (len(record[3]) + 1))
    return f"(Flat.flat : {result_type(function)} → {words})".split(" ")


def flat_instance(kind):
    """The `Flat` instance of a record result type: the errno and the fields as a tuple."""
    name = pascal(kind[4]) + "Result"
    fields = ["errno"] + [camel(field) for field, _, _ in kind[3]]
    words = " × ".join(["UInt64"] * len(fields))
    head = f"instance : Flat {name} ({words}) :="
    lines = [head] if len(head) <= WIDTH else [f"instance : Flat {name}", f"    ({words}) :="]
    items = [f"result.{field}" for field in fields]
    items[0], items[-1] = "(" + items[0], items[-1] + ")"
    lines += wrap("  ⟨fun result => ", items, "⟩", 4)
    return "\n".join(lines) + "\n"


KEYWORDS = {"at", "by", "do", "else", "end", "for", "from", "fun", "have", "if", "in", "let",
            "match", "show", "then", "to", "with"}


def variable(name):
    """`name` as a Lean identifier, quoted when it is a keyword."""
    return f"«{name}»" if name in KEYWORDS else name


def reflection_equation(function):
    takes = [kind for kind in function.kinds
             if kind[0] not in ("result32", "result64", "record", "reported")]
    names = [camel(name) for name in function.arguments]
    inputs = [kind[0] == "input" for kind in takes]
    variables = [f"({variable(name)} : Var context .{'bytes' if input else 'word'})"
                 for name, input in zip(names, inputs)]
    values = [f"({name}Value : {'LeanExe.Bytes' if input else 'UInt64'})"
              for name, input in zip(names, inputs)]
    hypotheses = [f"(h{name[0].upper() + name[1:]} : env.get {variable(name)} = {name}Value)"
                  for name in names]
    term, _ = form(function)
    lines = [f"theorem {function.lean}_eq (pureFuns : Funs pureSigs) "
             "(effectFuns : EffectFuns effectSigs)"]
    if names:
        lines += wrap("    (env : Env context) ", variables + values + hypotheses, " :", 4,
                      separator="")
    else:
        lines.append("    (env : Env context) :")
    word_list = ", ".join(variable(name) for name, input in zip(names, inputs) if not input)
    input_list = ", ".join(variable(name) for name, input in zip(names, inputs) if input)
    tokens = ["(Command.sys", "(pureSigs := pureSigs)", "(effectSigs := effectSigs)"]
    tokens += [] if names else ["(context := context)"]
    tokens += [f"Call.{function.lean}", term,
               f"[{word_list}]", f"[{input_list}]).denote", "pureFuns", "effectFuns", "env", "="]
    lines += wrap("    ", tokens, "", 6, separator="")
    call = [f"({function.lean}"] + [f"{name}Value" for name in names]
    call[-1] += ")"
    if not names:
        call = [function.lean]
    tokens = ["flattenAction", *flatten(function), *call, ":= by" if names else ":= rfl"]
    lines += wrap("      ", tokens, "", 8, separator="")
    if names:
        lines.append("  subst " + " ".join(f"h{name[0].upper() + name[1:]}" for name in names))
        lines.append("  rfl")
    return "\n".join(lines) + "\n"


def operation_entry(function):
    takes = [kind for kind in function.kinds
             if kind[0] not in ("result32", "result64", "record", "reported")]
    inputs = ", ".join("true" if kind[0] == "input" else "false" for kind in takes)
    _, expression = form(function)
    return (f"(``LeanExe.Wasi.{function.lean}, ⟨``LeanExe.Wasi.Call.{function.lean},\n"
            f"    {expression}, [{inputs}], ``{function.lean}_eq⟩)")


def render_reflect(flat):
    functions = [function for function in flat if reflected(function)]
    entries = [operation_entry(function) for function in functions]
    records = {}
    for function in flat:
        record = record_kind(function)
        if record is not None:
            records[record[4]] = record
    return "\n".join([
        "import Verified.Wasi.ReflectLemmas",
        "import Verified.Wasi.ReflectSysOperation",
        "import LeanExe.Wasi.SysCalls",
        "",
        "/-!",
        "The `Flat` instances of the record result types, the reflection equations of the "
        "generated typed",
        "functions, and the table of the equations that `reflect` reads, which "
        "`tools/wasi-calls.py`",
        "generates from the pinned witx.  Each equation states that the `sys` command of the call "
        "denotes",
        "the typed function followed by the `Flat` form of its result.  Its check fails when this "
        "file",
        "differs from its output.",
        "-/",
        "",
        "namespace LeanExe.Wasi",
        "",
        "open LeanExe.Pipeline",
        "",
        "\n".join(flat_instance(kind) for kind in records.values()),
        "end LeanExe.Wasi",
        "",
        "namespace Verified.Wasi.Reflect",
        "",
        "open LeanExe.Wasi LeanExe.Pipeline",
        "",
        "variable {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty}",
        "",
        "-- With `Reply.field` folded, `rfl` unfolds the command's side of a record equation to "
        "the",
        "-- typed function's fields instead of unfolding the fields' byte readers.",
        "attribute [local irreducible] Reply.field",
        "",
        "\n".join(reflection_equation(function) for function in functions),
        "/-- The generated typed functions that `reflect` maps to one `sys` command. -/",
        "def generatedSysOperations : List (Lean.Name × SysOperation) := [",
        *[f"  {entry}{',' if index + 1 < len(entries) else ']'}"
          for index, entry in enumerate(entries)],
        "",
        "end Verified.Wasi.Reflect",
        "",
    ])


RIGHTS = (1 << 30) - 1
# The frame test's steps, run with a directory preopened at descriptor 3 and the arguments `prog`
# and `a`.  Each step names a function and gives the arguments of the parameters that take one, in
# order: an integer, the name of a local that an earlier step set, a string for an input, or a
# capacity for an output.  `errno` is Wasmtime 44's errno for the step, `keep` names the locals that
# take its result words, and `values` lists what the call must write: (region, offset, width, value)
# for a byte, half-word, word, or double word at `offset` of its output buffer or its result word
# `result N`, and ("field", name, value) for the field `name` of its record, read at the offset and
# with the width that the description gives.
STEPS = [
    {"call": "args_sizes_get", "keep": ["count", "size"],
     "values": [("result 0", 0, 4, 2), ("result 1", 0, 4, 7)]},
    {"call": "args_get"},
    {"call": "environ_sizes_get", "keep": ["count", "size"],
     "values": [("result 0", 0, 4, 0), ("result 1", 0, 4, 0)]},
    {"call": "environ_get"},
    {"call": "clock_res_get", "args": [1]},
    {"call": "clock_time_get", "args": [0, 1]},
    {"call": "random_get", "args": [32]},
    {"call": "sched_yield"},
    {"call": "proc_raise", "args": [1], "errno": 58},
    {"call": "fd_prestat_get", "args": [3],
     "values": [("field", "tag", 0), ("field", "pr_name_len", 1)]},
    {"call": "fd_prestat_dir_name", "args": [3, 1], "values": [("output", 0, 1, ord("."))]},
    {"call": "fd_fdstat_get", "args": [3], "values": [("field", "fs_filetype", 3)]},
    {"call": "fd_filestat_get", "args": [3], "values": [("field", "filetype", 3)]},
    {"call": "path_create_directory", "args": [3, "d"]},
    {"call": "path_open", "args": [3, 0, "f", 1, RIGHTS, RIGHTS, 0], "keep": ["file"]},
    {"call": "fd_allocate", "args": ["file", 0, 16], "errno": 58},
    {"call": "fd_filestat_set_size", "args": ["file", 4294967301]},
    {"call": "fd_filestat_set_times", "args": ["file", 0, 0, 0]},
    {"call": "fd_fdstat_set_flags", "args": ["file", 0]},
    {"call": "fd_fdstat_set_rights", "args": ["file", RIGHTS, RIGHTS], "errno": 58},
    {"call": "fd_advise", "args": ["file", 0, 0, 0]},
    {"call": "fd_seek", "args": ["file", 5, 0], "values": [("result 0", 0, 8, 5)]},
    {"call": "fd_tell", "args": ["file"], "values": [("result 0", 0, 8, 5)]},
    {"call": "fd_datasync", "args": ["file"]},
    {"call": "fd_sync", "args": ["file"]},
    {"call": "path_filestat_get", "args": [3, 0, "f"],
     "values": [("field", "filetype", 4), ("field", "nlink", 1), ("field", "size", 4294967301)]},
    {"call": "path_filestat_set_times", "args": [3, 0, "f", 0, 0, 0]},
    {"call": "path_link", "args": [3, 0, "f", 3, "g"]},
    {"call": "path_symlink", "args": ["f", 3, "s"]},
    {"call": "path_readlink", "args": [3, "s", 1],
     "values": [("output", 0, 1, ord("f")), ("result 1", 0, 4, 1)]},
    {"call": "fd_readdir", "args": [3, 16, 0]},
    {"call": "path_rename", "args": [3, "g", 3, "h"]},
    {"call": "path_open", "args": [3, 0, "h", 0, RIGHTS, RIGHTS, 0], "keep": ["second"]},
    {"call": "fd_renumber", "args": ["file", "second"]},
    {"call": "fd_close", "args": ["second"]},
    {"call": "path_unlink_file", "args": [3, "h"]},
    {"call": "path_unlink_file", "args": [3, "s"]},
    {"call": "path_unlink_file", "args": [3, "f"]},
    {"call": "path_remove_directory", "args": [3, "d"]},
    {"call": "sock_accept", "args": [3, 0], "errno": 57},
    {"call": "sock_shutdown", "args": [3, 1], "errno": 57},
]
WORKING, SHADOW, CONSTANTS = 0, 65536, 2 * 65536
# Each result word and record lies at a multiple of its alignment that is not a multiple of twice
# it, so that Wasmtime traps when a description gives it a smaller alignment.
INPUTS, OUTPUT, STRINGS = 1024, 4096, 12288
RESULT32, RESULT64, RECORDS, POINTERS = (20, 28), (24, 40), 64, 8196
# The seeded faults of --frame-faults: a step, the region whose declaration changes, and how.
FAULTS = {
    "record-short": ("fd_fdstat_get", "record", "size", -1),
    "result64-as-32": ("clock_time_get", "result 0", "size", -4),
    "output-short": ("path_readlink", "output", "size", -1),
    "output-late": ("fd_prestat_dir_name", "output", "start", 1),
    "record-half-aligned": ("fd_filestat_get", "record", "address", -4),
}


def core_types(kind):
    if kind[0] in ("word64", "flags64"):
        return ["i64"]
    if kind[0] in ("input", "output"):
        return ["i32", "i32"]
    return ["i32"]


def frame_step(index, step, function, constants, fault=None):
    """The code of one step: the inputs, the snapshot, the call and its errno, the frame check, the
    value checks, and the result words that later steps use.  `fault` (a region, a field, and a
    change) moves the region's address or changes its declared start or size."""
    lines = [f"    ;; {index}: {function.name}", "    (call $prepare)"]
    args = list(step.get("args", []))
    pushes, regions, places, fields = [], [], {}, {}
    inputs = reported = 0
    results = {"result32": 0, "result64": 0}
    for kind in function.kinds:
        match kind[0]:
            case "word32" | "enum32" | "flags32" | "word64" | "flags64":
                value = args.pop(0)
                width = "i64" if kind[0] in ("word64", "flags64") else "i32"
                pushes.append(f"(local.get ${value})" if isinstance(value, str)
                              else f"({width}.const {value})")
            case "input":
                text = args.pop(0).encode()
                address = INPUTS + 256 * inputs
                inputs += 1
                source = constants.setdefault(text, CONSTANTS + 256 * len(constants))
                lines.append(f"    (memory.copy (i32.const {address}) (i32.const {source}) "
                             f"(i32.const {len(text)}))")
                pushes += [f"(i32.const {address})", f"(i32.const {len(text)})"]
            case "output":
                capacity = args.pop(0)
                pushes += [f"(i32.const {OUTPUT})", f"(i32.const {capacity})"]
                regions.append((OUTPUT, f"(i32.const {capacity})"))
                places["output"] = OUTPUT
            case "result32" | "result64":
                slots = RESULT32 if kind[0] == "result32" else RESULT64
                address = slots[results[kind[0]]]
                results[kind[0]] += 1
                pushes.append(f"(i32.const {address})")
                regions.append((address, f"(i32.const {4 if kind[0] == 'result32' else 8})"))
                places[f"result {len(regions) - 1}"] = address
            case "record":
                address = RECORDS + kind[2]
                if fault and fault[0] == "record" and fault[1] == "address":
                    address += fault[2]
                pushes.append(f"(i32.const {address})")
                regions.append((address, f"(i32.const {kind[1]})"))
                places["record"] = address
                fields = {name: (offset, width) for name, offset, width in kind[3]}
            case "reported":
                address = POINTERS if reported == 0 else STRINGS
                size = "(i32.mul (local.get $count) (i32.const 4))" if reported == 0 \
                    else "(local.get $size)"
                pushes.append(f"(i32.const {address})")
                regions.append((address, size))
                reported += 1
    assert not args, (function.name, args)
    if fault and fault[1] in ("size", "start"):
        position = [a for a, _ in regions].index(places[fault[0]])
        start, size = regions[position]
        if fault[1] == "size":
            regions[position] = (start, f"(i32.add {size} (i32.const {fault[2]}))")
        else:
            regions[position] = (start + fault[2], f"(i32.sub {size} (i32.const {fault[2]}))")
    regions += [(0, "(i32.const 0)")] * (2 - len(regions))
    lines.append("    (call $snapshot)")
    lines += wrap(f"    (call $errno (i32.const {index}) (call ${function.name} ", pushes,
                  f") (i32.const {step.get('errno', 0)}))", 6, "")
    lines.append(f"    (call $check (i32.const {index}) (i32.const {regions[0][0]}) "
                 f"{regions[0][1]}")
    lines.append(f"      (i32.const {regions[1][0]}) {regions[1][1]})")
    loads = {1: "i64.load8_u", 2: "i64.load16_u", 4: "i64.load32_u", 8: "i64.load"}
    for check in step.get("values", []):
        if check[0] == "field":
            offset, width = fields[check[1]]
            address, value = places["record"] + offset, check[2]
        else:
            region, offset, width, value = check
            address = places[region] + offset
        lines.append(f"    (call $value (i32.const {index}) ({loads[width]} (i32.const "
                     f"{address})) (i64.const {value}))")
    for local, address in zip(step.get("keep", []), [a for a, _ in regions]):
        lines.append(f"    (local.set ${local} (i32.load (i32.const {address})))")
    return lines


def render_frame(flat, fault=None):
    functions = {function.name: function for function in flat}
    missing = sorted(set(functions) - {step["call"] for step in STEPS})
    assert not missing, f"no step calls {missing}"
    assert 84 + len(STEPS) < 126, "too many steps for distinct statuses"
    constants, body = {}, []
    seeded = None
    for index, step in enumerate(STEPS, 1):
        here = fault[1:] if fault and fault[0] == step["call"] and not seeded else None
        seeded = seeded or here
        body += frame_step(index, step, functions[step["call"]], constants, here)
    assert fault is None or seeded, f"no step calls {fault[0]}"
    imports = []
    for function in flat:
        params = " ".join(t for kind in function.kinds for t in core_types(kind))
        signature = f"(param {params}) (result i32)" if params else "(result i32)"
        imports.append(f'  (import "wasi_snapshot_preview1" "{function.name}"')
        imports.append(f"    (func ${function.name} {signature}))")
    data = [f'  (data (i32.const {address}) "{text.decode()}")'
            for text, address in constants.items()]
    return "\n".join([
        ";; Frame test of every flat Preview 1 function, which tools/wasi-calls.py generates from",
        ";; the pinned witx and its list of steps.  Each step fills the working memory [0, 65536)",
        ";; with the guard byte 0xA5, writes the call's inputs, copies the working memory to the",
        ";; shadow copy at 65536, and calls the function.  A result word or record lies at a",
        ";; multiple of its alignment that is not a multiple of twice it, so that Wasmtime traps",
        ";; when a description gives it a smaller alignment.  The step then checks the errno,",
        ";; that every byte outside the call's declared regions equals the shadow copy, and the",
        ";; values the step lists.  The exit status names the first failed check: the step's",
        ";; number for the errno, 42 plus it for a byte outside the regions, and 84 plus it for",
        ";; a value.",
        "(module",
        *imports,
        '  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))',
        '  (memory (export "memory") 3)',
        *data,
        "  (func $fail (param $status i32)",
        "    (call $proc_exit (local.get $status))",
        "    (unreachable))",
        "  (func $prepare",
        f"    (memory.fill (i32.const {WORKING}) (i32.const 0xA5) (i32.const 65536)))",
        "  (func $snapshot",
        f"    (memory.copy (i32.const {SHADOW}) (i32.const {WORKING}) (i32.const 65536)))",
        "  (func $errno (param $step i32) (param $got i32) (param $want i32)",
        "    (if (i32.ne (local.get $got) (local.get $want))",
        "      (then (call $fail (local.get $step)))))",
        "  (func $value (param $step i32) (param $got i64) (param $want i64)",
        "    (if (i64.ne (local.get $got) (local.get $want))",
        "      (then (call $fail (i32.add (i32.const 84) (local.get $step))))))",
        "  (func $inside (param $address i32) (param $start i32) (param $length i32) (result i32)",
        "    (i32.and (i32.ge_u (local.get $address) (local.get $start))",
        "      (i32.lt_u (local.get $address) (i32.add (local.get $start) (local.get $length)))))",
        "  (func $check (param $step i32) (param $s1 i32) (param $n1 i32) (param $s2 i32)",
        "      (param $n2 i32)",
        "    (local $index i32)",
        "    (block $done",
        "      (loop $next",
        "        (br_if $done (i32.ge_u (local.get $index) (i32.const 65536)))",
        "        (if (i32.eqz (i32.or",
        "              (call $inside (local.get $index) (local.get $s1) (local.get $n1))",
        "              (call $inside (local.get $index) (local.get $s2) (local.get $n2))))",
        "          (then",
        "            (if (i32.ne (i32.load8_u (local.get $index))",
        f"                  (i32.load8_u (i32.add (local.get $index) (i32.const {SHADOW}))))",
        "              (then (call $fail (i32.add (i32.const 42) (local.get $step)))))))",
        "        (local.set $index (i32.add (local.get $index) (i32.const 1)))",
        "        (br $next))))",
        '  (func (export "_start")',
        "    (local $count i32) (local $size i32) (local $file i32) (local $second i32)",
        *body,
        "    (call $proc_exit (i32.const 0)))",
        ")",
        "",
    ])


def sweep_values(kind):
    """The values of an enum or flags parameter that the rejection sweep passes, each with whether
    `Param.reject` rejects it: the last value of an enum and the next one, and each single bit of a
    flags type."""
    match kind[0]:
        case "enum32":
            return [(kind[1] - 1, False), (kind[1], True)]
        case "flags32" | "flags64":
            bits = range(32 if kind[0] == "flags32" else 64)
            return [(1 << bit, not kind[1] >> bit & 1) for bit in bits]
    return []


def sweep_module(function, position, value):
    """A module that calls `function` once with `value` at parameter `position` and exits with its
    errno, and its arguments in the form that tests/wasi/SysSweep.lean reads: `w:N` for a word,
    `b:HEX` for an input, and `s:N` for an output's capacity.  The other parameters take descriptor
    3, zero, the input `x`, a 16-byte output, and regions 64 bytes apart at multiples of 8."""
    pushes, regions, args = [], 0, []
    for index, kind in enumerate(function.kinds):
        match kind[0]:
            case "word32" | "enum32" | "flags32" | "word64" | "flags64":
                default = 3 if kind[0] == "word32" else 0
                word = value if index == position else default
                width = "i64" if kind[0] in ("word64", "flags64") else "i32"
                pushes.append(f"({width}.const {word})")
                args.append(f"w:{word}")
            case "input":
                pushes += ["(i32.const 1024)", "(i32.const 1)"]
                args.append(f"b:{b'x'.hex()}")
            case "output":
                pushes += ["(i32.const 2048)", "(i32.const 16)"]
                args.append("s:16")
            case _:
                pushes.append(f"(i32.const {4096 + 64 * regions})")
                regions += 1
    params = " ".join(t for kind in function.kinds for t in core_types(kind))
    signature = f"(param {params}) (result i32)" if params else "(result i32)"
    return args, "\n".join([
        "(module",
        f'  (import "wasi_snapshot_preview1" "{function.name}" (func $call {signature}))',
        '  (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))',
        '  (memory (export "memory") 1)',
        '  (data (i32.const 1024) "x")',
        '  (func (export "_start")',
        *wrap("    (call $exit (call $call ", pushes, ")))", 6, ""),
        ")",
        "",
    ])


def reject_sweep(flat):
    """The modules of the rejection sweep: a name, the module, whether Wasmtime must trap, and the
    call's name and arguments."""
    for function in flat:
        for position, kind in enumerate(function.kinds):
            for value, rejected in sweep_values(kind):
                args, module = sweep_module(function, position, value)
                yield (f"{function.name}-{position}-{value:#x}", module, rejected,
                       " ".join([function.name, *args]))


GENERATED = {
    "LeanExe/Wasi/CallTable.lean": render_calls,
    "LeanExe/Wasi/SysCalls.lean": render_typed,
    "Verified/Wasi/ReflectSysCalls.lean": render_reflect,
    "tests/wasi/sys/frame-all.wat": render_frame,
}


def option(rest, name):
    """Remove `name DIR` from the arguments `rest` and return DIR, or None without `name`."""
    if name not in rest:
        return None
    at = rest.index(name)
    value = Path(rest[at + 1])
    del rest[at:at + 2]
    return value


def main():
    write = "--write" in sys.argv
    rest = [a for a in sys.argv[1:] if a != "--write"]
    faults, sweep = option(rest, "--frame-faults"), option(rest, "--reject-sweep")
    directory = Path(rest[0] if rest else "tests/wasi/witx")
    flat = [function for function in functions(directory) if function.kinds is not None]
    if sweep is not None:
        sweep.mkdir(parents=True, exist_ok=True)
        for name, text, rejected, call in reject_sweep(flat):
            (sweep / f"{name}.wat").write_text(text)
            print(name, "trap" if rejected else "errno", call)
        return
    if faults is not None:
        faults.mkdir(parents=True, exist_ok=True)
        for name, fault in FAULTS.items():
            (faults / f"{name}.wat").write_text(render_frame(flat, fault))
            index = next(i for i, step in enumerate(STEPS, 1) if step["call"] == fault[0])
            print(name, 1 if fault[2] == "address" else 42 + index)
        return
    failed = False
    for path, render in GENERATED.items():
        text = render(flat)
        target = Path(path)
        if write:
            target.write_text(text)
            print(f"wrote {path}")
            continue
        current = target.read_text() if target.exists() else ""
        if current != text:
            sys.stdout.writelines(difflib.unified_diff(
                current.splitlines(keepends=True), text.splitlines(keepends=True),
                f"{path} (committed)", f"{path} (generated)"))
            failed = True
    for source in sorted(Path("LeanExe/Wasi").glob("*.lean")):
        if str(source) in GENERATED:
            continue
        for name in re.findall(r"^\s*def (\w+) : Call\b", source.read_text(), re.M):
            print(f"{source}: {name} is a description outside the generated file")
            failed = True
    if not write:
        print(f"{len(flat)} flat functions; generated files "
              f"{'differ' if failed else 'match the witx'}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
