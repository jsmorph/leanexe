import Library.Numerics.Bignum.Compiled
import LeanExe.Native.ClightCheck

/-!
Writes and checks the C text of the bignum module.

`emit DIR` writes `DIR/bignum.c`, the translation of `compiled.module` with `lx_mem` of `nativeCap`
pages, the program of the theorems of `Native.lean`.  `check DIR` compares the Clight that
`clightgen` wrote for that text, `DIR/bignum.v`, with the translation, up to a renaming of
identifiers, and exits with status 1 when it differs.
Usage: lake env lean --run tests/bignum/EmitNative.lean emit|check DIR
-/

open LeanExe.Native Library.Numerics.Bignum

def translation (m : Wasm.Module) (name : String) : IO Translation :=
  match translate nativeCap m with
  | some t => pure t
  | none => throw <| IO.userError s!"emit-native: {name}: the module does not translate"

def writeText (path : String) (text : Except String String) : IO Unit :=
  match text with
  | .ok s => IO.FS.writeFile path s
  | .error e => throw <| IO.userError s!"emit-native: {path}: {e}"

def emit (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let t ← translation compiled.module "bignum"
  writeText s!"{dir}/bignum.c" t.text
  IO.println s!"emit-native: bignum: {t.funcs.length} of {compiled.module.funcs.length} functions"

def check (dir : String) : IO UInt32 := do
  let t ← translation compiled.module "bignum"
  match ClightCheck.check t (← IO.FS.readFile s!"{dir}/bignum.v") [] with
  | .error e =>
      IO.eprintln s!"emit-native: bignum: {e}"
      pure 1
  | .ok [] =>
      IO.println "emit-native: bignum: the clightgen program matches the program of the theorem"
      pure 0
  | .ok errors =>
      for e in errors do IO.eprintln s!"emit-native: bignum: {e}"
      pure 1

def main : List String → IO UInt32
  | ["emit", dir] => do emit dir; pure 0
  | ["check", dir] => check dir
  | _ => throw <| IO.userError "usage: EmitNative.lean emit|check DIR"
