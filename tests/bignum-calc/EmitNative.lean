import Demos.BignumCalc.MessageCompiled
import LeanExe.Native.ClightCheck

/-!
Writes and checks the C text of the calculator's bare-metal program.

`emit DIR` writes `DIR/message.c`, the translation of `messageCompiled.module` with `lx_mem` of
`nativeCap` pages followed by `lx_in`, `lx_out`, and the `main` of `inMain` around function 44,
`calcWords`, the program of `calc_program`, with `DIR/message.depth`, the C names of its functions
that take the call depth.  `check DIR` compares the Clight that `clightgen` wrote for that text,
`DIR/message.v`, with the whole program of the theorem, up to a renaming of identifiers, and exits
with status 1 when it differs.
Usage: lake env lean --run tests/bignum-calc/EmitNative.lean emit|check DIR
-/

open LeanExe.Native Demos.BignumCalc

def translation (m : Wasm.Module) (name : String) : IO Translation :=
  match translate nativeCap m with
  | some t => pure t
  | none => throw <| IO.userError s!"emit-native: {name}: the module does not translate"

/-- The entry of the program with input: `calcWords`, function 44 of `messageCompiled`. -/
def messageEntry : Nat := 44

def writeText (path : String) (text : Except String String) : IO Unit :=
  match text with
  | .ok s => IO.FS.writeFile path s
  | .error e => throw <| IO.userError s!"emit-native: {path}: {e}"

def emit (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let tm ← translation messageCompiled.module "message"
  writeText s!"{dir}/message.c" (tm.inText nativeCap messageEntry .array)
  IO.FS.writeFile s!"{dir}/message.depth"
    (String.join ((tm.depthNames messageCompiled.module).map (· ++ "\n")))
  IO.println s!"emit-native: message: {tm.funcs.length} of \
    {messageCompiled.module.funcs.length} functions"

def check (dir : String) : IO UInt32 := do
  let tm ← translation messageCompiled.module "message"
  match ClightCheck.check tm (← IO.FS.readFile s!"{dir}/message.v")
      (inTail (inMain nativeCap messageEntry .array)) with
  | .error e =>
      IO.eprintln s!"emit-native: message: {e}"
      pure 1
  | .ok [] =>
      IO.println "emit-native: message: the clightgen program matches the program of the theorem"
      pure 0
  | .ok errors =>
      for e in errors do IO.eprintln s!"emit-native: message: {e}"
      pure 1

def main : List String → IO UInt32
  | ["emit", dir] => do emit dir; pure 0
  | ["check", dir] => check dir
  | _ => throw <| IO.userError "usage: EmitNative.lean emit|check DIR"
