#!/usr/bin/env python3
"""Generate folded-frame access lemmas for a Locals-valued frame definition.

Usage: gen-frame-lemmas.py NAME NPARAMS ARGS...
  NAME     frame definition name (e.g. vFrame)
  NPARAMS  how many of the definition's slots are WASM params
  ARGS     the definition's argument names, in slot order

Emits get, set?, and validIndex lemmas for every slot to stdout.  The
proofs are `rfl` (or `decide` for validIndex): the frame's field lists
are literals, so the index arithmetic computes.
"""
import sys

name = sys.argv[1]
nparams = int(sys.argv[2])
args = sys.argv[3:]
n = len(args)
binder = " ".join(args)
app = f"{name} {binder}"

print(f"section {name}Lemmas")
print(f"variable ({binder} : UInt64)")
print()
for i in range(n):
    print(f"@[frame_step] theorem {name}_get_{i} :")
    print(f"    Wasm.Locals.get ({app}) {i} = some (.i64 {args[i]}) := rfl")
print()
for i in range(n):
    newargs = list(args)
    newargs[i] = "w"
    napp = f"{name} {' '.join(newargs)}"
    print(f"@[frame_step] theorem {name}_set_{i} (w : UInt64) :")
    print(f"    Wasm.Locals.set? ({app}) {i} (.i64 w) = some ({napp}) := rfl")

print()
print(f"@[frame_step] theorem {name}_params_length :")
print(f"    ({app}).params.length = {nparams} := rfl")
print(f"@[frame_step] theorem {name}_locals_length :")
print(f"    ({app}).locals.length = {n - nparams} := rfl")
print()
for k in range(nparams):
    newargs = list(args)
    newargs[k] = "w"
    napp = f"{name} {' '.join(newargs)}"
    print(f"@[frame_step] theorem {name}_setp_{k} (w : UInt64) (vs : List Wasm.Value) :")
    print(f"    ({{ params := ({app}).params.set {k} (.i64 w),")
    print(f"        locals := ({app}).locals,")
    print(f"        values := vs }} : Wasm.Locals) =")
    print(f"      {{ {napp} with values := vs }} := rfl")
print()
for k in range(n - nparams):
    newargs = list(args)
    newargs[nparams + k] = "w"
    napp = f"{name} {' '.join(newargs)}"
    print(f"@[frame_step] theorem {name}_setl_{k} (w : UInt64) (vs : List Wasm.Value) :")
    print(f"    ({{ params := ({app}).params,")
    print(f"        locals := ({app}).locals.set {k} (.i64 w),")
    print(f"        values := vs }} : Wasm.Locals) =")
    print(f"      {{ {napp} with values := vs }} := rfl")

print()
print(f"@[frame_step] theorem {name}_params :")
print(f"    ({app}).params = [{', '.join('.i64 ' + a for a in args[:nparams])}] := rfl")
print(f"@[frame_step] theorem {name}_locals :")
print(f"    ({app}).locals = [{', '.join('.i64 ' + a for a in args[nparams:])}] := rfl")
print(f"@[frame_step] theorem {name}_values :")
print(f"    ({app}).values = [] := rfl")

print()
print(f"@[frame_step] theorem {name}_validIndex (i : Nat) (h : i < {n}) :")
print(f"    Wasm.Locals.validIndex ({app}) i := by")
print(f"  simp only [{name}, Wasm.Locals.validIndex]")
print(f"  simp")
print(f"  omega")
print()
print(f"end {name}Lemmas")
