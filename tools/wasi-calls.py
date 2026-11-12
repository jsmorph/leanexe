# /// script
# requires-python = ">=3.10"
# ///
"""Check the flat call descriptions of LeanExe/Wasi/Calls.lean against the pinned Preview 1 witx.

Usage: uv run tools/wasi-calls.py [WITX_DIR [CALLS_LEAN]]

WITX_DIR holds wasi_snapshot_preview1.witx and typenames.witx of WebAssembly/WASI commit
fae981bae14809d91f9bc2d63852d461f331d161, by default tests/wasi/witx.  The script lowers each
function of the witx to core parameter kinds and compares the kinds of every description in
CALLS_LEAN (default LeanExe/Wasi/Calls.lean) with the lowering of the function it names.  An enum
with a 32-bit tag and n values is `enum32 n`; another parameter whose representation is 64 bits wide
is word64, and other integer, flags, and handle parameters are word32; a string, or a const_pointer
followed by a $size parameter, is input; a pointer followed by a $size parameter is output; another
pointer is reported, with scale and alignment 4 and not shown when it points to pointers, whose
entries are guest addresses, and with scale and alignment 1 and shown when it points to bytes; each
component of an expected result is result32 or result64 by its width.  A description has a reporter
exactly when it has reported parameters, and the reporter of a function NAME_get is NAME_sizes_get,
the Preview 1 convention of args_get and environ_get, whose results are one result32 for each
reported parameter.  The script prints one line per description and exits with status 1 when a
description differs, names no witx function, names a function that is not flat, has a wrong
reporter, or when a definition of type Call is not written as `def NAME : Call := { name := ...,
params := [...] }` with an optional `reporter := some "..."`.
"""
import re
import sys
from pathlib import Path


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


WIDTHS = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "s8": 8, "s16": 16, "s32": 32, "s64": 64,
          "char8": 8}


def type_table(forms):
    table = {}
    for form in forms:
        if isinstance(form, list) and form and form[0] == "typename":
            table[form[1]] = form[2]
    return table


def resolve(table, ty):
    while isinstance(ty, str) and ty.startswith("$"):
        ty = table[ty]
    return ty


def width(table, ty):
    """The bit width of a scalar type, or None for a type that is not a scalar."""
    ty = resolve(table, ty)
    if isinstance(ty, str):
        return WIDTHS.get(ty)
    head = ty[0]
    if head in ("enum", "flags"):
        repr_ = [x for x in ty[1:] if isinstance(x, list) and x[:1] == ["@witx"]]
        for annotation in repr_:
            if annotation[1] in ("tag", "repr"):
                return WIDTHS[annotation[2]]
        return 32
    if head == "handle":
        return 32
    return None


def is_pointer(ty):
    return isinstance(ty, list) and ty[:2] in (["@witx", "pointer"], ["@witx", "const_pointer"])


def lower(table, function):
    """The core kinds of a witx function, or a reason why it is not flat."""
    params = [x for x in function if isinstance(x, list) and x[:1] == ["param"]]
    result = [x for x in function if isinstance(x, list) and x[:1] == ["result"]]
    kinds = []
    index = 0
    while index < len(params):
        name, ty = params[index][1], params[index][2]
        following = params[index + 1] if index + 1 < len(params) else None
        sized = following is not None and following[2] == "$size"
        resolved = resolve(table, ty)
        if resolved == "string":
            kinds.append("input")
        elif is_pointer(resolved):
            pointee = resolve(table, resolved[2])
            if resolved[1] == "const_pointer" and sized:
                kinds.append("input")
                index += 1
            elif resolved[1] == "pointer" and sized and pointee == "u8":
                kinds.append("output")
                index += 1
            elif is_pointer(pointee):
                kinds.append("reported 4 4 false")
            elif pointee == "u8":
                kinds.append("reported 1 1 true")
            else:
                return None, f"parameter {name} points to {pointee}"
        elif isinstance(resolved, list) and resolved[0] == "enum" and width(table, ty) == 32:
            values = [x for x in resolved[1:] if isinstance(x, str) and x.startswith("$")]
            kinds.append(f"enum32 {len(values)}")
        else:
            bits = width(table, ty)
            if bits is None:
                return None, f"parameter {name} has type {resolved}"
            kinds.append("word64" if bits == 64 else "word32")
        index += 1
    for form in result:
        expected = form[2]
        if not (isinstance(expected, list) and expected[0] == "expected"):
            return None, "result is not expected"
        values = [x for x in expected[1:] if not (isinstance(x, list) and x[:1] == ["error"])]
        for value in values:
            components = value[1:] if isinstance(value, list) and value[0] == "tuple" else [value]
            for component in components:
                bits = width(table, component)
                if bits == 64:
                    kinds.append("result64")
                elif bits == 32:
                    kinds.append("result32")
                else:
                    return None, f"result component {component} is not a 32- or 64-bit word"
    if any(isinstance(x, list) and x[:2] == ["@witx", "noreturn"] for x in function):
        return None, "does not return"
    return kinds, None


def witx_functions(directory):
    table = type_table(parse((directory / "typenames.witx").read_text()))
    module = parse((directory / "wasi_snapshot_preview1.witx").read_text())
    functions = {}

    def walk(form):
        if isinstance(form, list):
            if form[:2] == ["@interface", "func"]:
                export = form[2]
                functions[export[1].strip('"')] = lower(table, form)
            for x in form:
                walk(x)

    walk(module)
    return functions


LEAN_DEF = re.compile(
    r'def (\w+) : Call :=\s*\{\s*name := "([^"]+)",\s*params := \[([^\]]*)\]'
    r'(?:,\s*reporter := some "([^"]+)")?\s*\}', re.S)
CALL_DEF = re.compile(r'^\s*def (\w+) : Call\b', re.M)


def lean_kinds(params):
    kinds = []
    for item in [x.strip() for x in params.split(",") if x.strip()]:
        item = item.lstrip(".")
        parts = item.split()
        if parts[0] == "reported":
            kinds.append(f"reported {parts[1]} {parts[2]} {parts[3]}")
        elif parts[0] == "enum32":
            kinds.append(f"enum32 {parts[1]}")
        else:
            kinds.append(parts[0])
    return kinds


def main():
    directory = Path(sys.argv[1] if len(sys.argv) > 1 else "tests/wasi/witx")
    calls = Path(sys.argv[2] if len(sys.argv) > 2 else "LeanExe/Wasi/Calls.lean")
    functions = witx_functions(directory)
    failed = False
    text = calls.read_text()
    definitions = LEAN_DEF.findall(text)
    if not definitions:
        print(f"no descriptions in {calls}")
        sys.exit(1)
    checked = {definition[0] for definition in definitions}
    for lean_name in CALL_DEF.findall(text):
        if lean_name not in checked:
            print(f"{lean_name}: the description is not in the checked form")
            failed = True
    for lean_name, name, params, reporter in definitions:
        kinds = lean_kinds(params)
        reported = sum(1 for kind in kinds if kind.startswith("reported"))
        if reported and reporter != name.removesuffix("_get") + "_sizes_get":
            print(f"{lean_name}: {name} has reporter {reporter or 'none'}")
            failed = True
            continue
        if reporter and (not reported or functions.get(reporter, (None, None))[0] !=
                         ["result32"] * reported):
            print(f"{lean_name}: {name} has reporter {reporter} without matching results")
            failed = True
            continue
        if name not in functions:
            print(f"{lean_name}: {name} is not a witx function")
            failed = True
            continue
        expected, reason = functions[name]
        if expected is None:
            print(f"{lean_name}: {name} is not flat: {reason}")
            failed = True
        elif kinds != expected:
            print(f"{lean_name}: {name} differs: description {kinds}, witx {expected}")
            failed = True
        else:
            print(f"{lean_name}: {name} {kinds}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
