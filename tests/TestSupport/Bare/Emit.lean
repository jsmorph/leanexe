import TestSupport.Bare.Gcd
import LeanExe.Native.ClightCheck

/-!
The executable of the bare-metal programs' test (`tests/baremetal/programs.sh`).  `native-bare
emit DIR` writes, for each program of `cases`, the C text of its translation with `lx_mem` of
`nativeCap` pages followed by `lx_out` and `main` as `DIR/NAME.c`, and the bytes that `main`
must write as `DIR/NAME.expected`: `encodeWord` or `encodeArray` of the Lean function's result.
It also runs the module's entry in Talos from the module's initial store and fails unless Talos's
result has the same bytes.  `native-bare check DIR` compares each whole program with the Clight
that `clightgen` wrote for it as `DIR/NAME.v`, `main` and `lx_out` included.  The executable
imports the programs' theorems, so that building it checks them.
-/

open LeanExe.Native Wasm

structure BareCase where
  name : String
  module : Module
  entry : String
  args : List UInt64
  kind : OutKind
  /-- The bytes of the Lean function's result. -/
  expected : List UInt8

def cases : List BareCase := [
  { name := "gcd", module := TestSupport.Native.Gcd.loopCompiled.module, entry := "gcd",
    args := [1071, 462], kind := .word,
    expected := encodeWord (TestSupport.Native.Gcd.gcd 1071 462) }]

def fuel : Nat := 100000000

def exportIndex (m : Module) (name : String) : Except String Nat :=
  match m.exports.find? (·.name == name) with
  | some e => pure e.funcIdx
  | none => throw s!"no export {name}"

/-- The bytes of Talos's result of the entry: a word's, or those of the array at the address it
returns. -/
def talosBytes (c : BareCase) (k : Nat) : Except String (List UInt8) := do
  let st : Store Unit := { (c.module.initialStore : Store Unit) with memoryCaps := [nativeCap] }
  match run fuel c.module k st (c.args.reverse.map Value.i64) with
  | .Success [.i64 x] st' =>
      match c.kind with
      | .word => pure (encodeWord x)
      | .array =>
          let n := (st'.mem.read64 x.toUInt32).toNat
          pure ((List.range (8 * n + 8)).map fun i => st'.mem.bytes (x.toNat + i))
  | .Success vs _ => throw s!"Talos returned {vs.length} values"
  | .Trap _ msg => throw s!"Talos trapped: {msg}"
  | _ => throw "Talos did not finish"

def emitCase (dir : String) (c : BareCase) : IO Unit := do
  let some t := translate nativeCap c.module
    | throw <| IO.userError s!"native-bare: {c.name}: the module does not translate"
  let k ← IO.ofExcept (exportIndex c.module c.entry)
  match t.bareText nativeCap k c.args c.kind with
  | .error e => throw <| IO.userError s!"native-bare: {c.name}: {e}"
  | .ok text => IO.FS.writeFile s!"{dir}/{c.name}.c" text
  let talos ← IO.ofExcept (talosBytes c k)
  if talos != c.expected then
    throw <| IO.userError s!"native-bare: {c.name}: Talos gives {talos}, Lean {c.expected}"
  IO.FS.writeBinFile s!"{dir}/{c.name}.expected" (ByteArray.mk c.expected.toArray)
  IO.println s!"native-bare: {c.name}: {c.expected.length} bytes, as Talos gives them"

def check (dir : String) : IO UInt32 := do
  let mut failed := false
  for c in cases do
    let some t := translate nativeCap c.module
      | throw <| IO.userError s!"native-bare: {c.name}: the module does not translate"
    let k ← IO.ofExcept (exportIndex c.module c.entry)
    let text ← IO.FS.readFile s!"{dir}/{c.name}.v"
    match ClightCheck.check t text (bareTail (bareMain nativeCap k c.args c.kind)) with
    | .error e =>
        IO.eprintln s!"native-bare: {c.name}: {e}"
        failed := true
    | .ok [] => IO.println s!"native-bare: {c.name}: the clightgen program matches the whole program"
    | .ok errors =>
        for e in errors do IO.eprintln s!"native-bare: {c.name}: {e}"
        failed := true
  pure (if failed then 1 else 0)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      IO.FS.createDirAll dir
      for c in cases do emitCase dir c
      pure 0
  | ["check", dir] => check dir
  | ["names"] => do
      for c in cases do IO.println c.name
      pure 0
  | _ => throw <| IO.userError "usage: native-bare emit|check DIR, or native-bare names"
