import Library.Numerics.Bignum.Second.Compiled
import LeanExe.Native.ClightCheck

/-!
Writes and checks the C text of the second iteration's module.

`emit DIR` writes `DIR/bignum2.c`, the translation of `compiled.module` with `lx_mem` of `nativeCap`
pages, the program of the theorems of `Native.lean`.  `check DIR` compares the Clight that
`clightgen` wrote for it, `DIR/bignum2.v`, with the translation, its globals by name and its call
temporaries up to renaming, and exits with status 1 when they differ.  Both steps evaluate
`translate` in compiled Lean code, which leanexe's trusted base lists as the evaluation of the
translation: no step compares the file with the kernel's `compiled.translation`.
-/

open LeanExe.Native Library.Numerics.Bignum.Second

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
  let t ← translation compiled.module "bignum2"
  writeText s!"{dir}/bignum2.c" t.text
  IO.println s!"emit-native: bignum2: {t.funcs.length} of {compiled.module.funcs.length} functions"

/-- Compares the Clight of `DIR/NAME.v` with the translation `t` followed by `tail`. -/
def compare (t : Translation) (dir name : String)
    (tail : List (LClight.ident × LClight.globdef (LClight.fundef LClight.function) LClight.type))
    : IO Bool := do
  match ClightCheck.check t (← IO.FS.readFile s!"{dir}/{name}.v") tail with
  | .error e =>
      IO.eprintln s!"emit-native: {name}: {e}"
      pure false
  | .ok [] =>
      IO.println s!"emit-native: {name}: the clightgen program matches the program of the theorem"
      pure true
  | .ok errors =>
      for e in errors do IO.eprintln s!"emit-native: {name}: {e}"
      pure false

def check (dir : String) : IO UInt32 := do
  let a ← compare (← translation compiled.module "bignum2") dir "bignum2" []
  pure (if a then 0 else 1)

def main : List String → IO UInt32
  | ["emit", dir] => do emit dir; pure 0
  | ["check", dir] => check dir
  | _ => throw <| IO.userError "usage: EmitNative.lean emit|check DIR"
