import TestSupport.Bare.Gcd
import TestSupport.Bare.Theorems
import LeanExe.Native.ClightCheck

/-!
The executable of the bare-metal programs' test (`tests/baremetal/programs.sh`).  Each case
holds the theorem `p.f.program` of its program, whose type fixes the entry, the arguments, the
kind of result, and the bytes of the trace, so that the C text that the executable writes is
that of the program of the theorem.  `native-bare emit DIR` writes, for each case, the C text of
its translation with `lx_mem` of `nativeCap` pages followed by `lx_out` and `main` as
`DIR/NAME.c`, the C names of its functions that take the call depth as `DIR/NAME.depth`, the
bytes that `main` must write as `DIR/NAME.expected`, and the exit status as `DIR/NAME.status`.
It runs the entry in Talos from the module's initial store: when Talos returns, its result
must have the bytes of the theorem and the status is 0; when it traps at `unreachable`, which
the theorem allows only for an entry that may abort, no byte is expected and the status is the
code of `unreachable`.  `native-bare check DIR` compares each whole program with the Clight that
`clightgen` wrote for it as `DIR/NAME.v`, `main` and `lx_out` included.
-/

open LeanExe.Native LClight Wasm

structure BareCase where
  name : String
  module : Module
  k : Nat
  args : List UInt64
  kind : OutKind
  bytes : List UInt8
  aborts : Bool
  thm : ∀ T, translate nativeCap module = some T → ∀ (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)), PrefixOk pre →
    bigstep_program_terminates A X (bareProgram pre T (bareMain nativeCap k args kind))
        (outTrace bytes) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X (bareProgram pre T
        (bareMain nativeCap k args kind)) E0 (UInt32.ofNat trapUnreachable))

theorem thm_of {m : Module} {T0 : Translation} (h : translate nativeCap m = some T0)
    {P : Translation → Prop} (hp : P T0) : ∀ T, translate nativeCap m = some T → P T := by
  intro T hT
  rw [h] at hT
  cases hT
  exact hp

def cases : List BareCase := [
  { name := "gcd", module := TestSupport.Native.Gcd.loopCompiled.module, k := 2,
    args := [1071, 462], kind := .word, aborts := false,
    bytes := encodeWord (TestSupport.Native.Gcd.gcd 1071 462),
    thm := thm_of TestSupport.Native.Gcd.loopCompiled.translation_eq
      TestSupport.Native.Gcd.loopCompiled.gcd.program },
  { name := "crc32", module := TestSupport.Bare.crcCompiled.module, k := 5,
    args := [0x3837363534333231, 0x39], kind := .word, aborts := true,
    bytes := encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39),
    thm := thm_of TestSupport.Bare.crcCompiled.translation_eq
      TestSupport.Bare.crcCompiled.crcCheck.program },
  { name := "sha256", module := TestSupport.Bare.shaCompiled.module, k := 11,
    args := [0x636261], kind := .array, aborts := true,
    bytes := encodeArray (TestSupport.Bare.shaCheck 0x636261),
    thm := thm_of TestSupport.Bare.shaCompiled.translation_eq
      TestSupport.Bare.shaCompiled.shaCheck.program },
  { name := "euler", module := Demos.Euler.Verified.compiled.module, k := 23,
    args := [16], kind := .array, aborts := true,
    bytes := encodeArray (Demos.Euler.solve 16),
    thm := thm_of Demos.Euler.Verified.compiled.translation_eq
      Demos.Euler.Verified.compiled.solve.program },
  { name := "depth", module := Verified.Examples.Fold.compiled.module, k := 13,
    args := [1000], kind := .word, aborts := true,
    bytes := encodeWord (Verified.Examples.Fold.recursive 1000),
    thm := thm_of Verified.Examples.Fold.compiled.translation_eq
      Verified.Examples.Fold.compiled.recursive.program }]

def fuel : Nat := 100000000

/-- The bytes of Talos's result of the entry, a word's or those of the array at the address it
returns, or `none` when it traps at `unreachable`. -/
def talosBytes (c : BareCase) : Except String (Option (List UInt8)) := do
  let st : Store Unit := { (c.module.initialStore : Store Unit) with memoryCaps := [nativeCap] }
  match run fuel c.module c.k st (c.args.reverse.map Value.i64) with
  | .Success [.i64 x] st' =>
      match c.kind with
      | .word => pure (some (encodeWord x))
      | .array =>
          let n := (st'.mem.read64 x.toUInt32).toNat
          pure (some ((List.range (8 * n + 8)).map fun i => st'.mem.bytes (x.toNat + i)))
  | .Success vs _ => throw s!"Talos returned {vs.length} values"
  | .Trap _ msg => if msg == "unreachable" then pure none else throw s!"Talos trapped: {msg}"
  | _ => throw "Talos did not finish"

def emitCase (dir : String) (c : BareCase) : IO Unit := do
  let some t := translate nativeCap c.module
    | throw <| IO.userError s!"native-bare: {c.name}: the module does not translate"
  match t.bareText nativeCap c.k c.args c.kind with
  | .error e => throw <| IO.userError s!"native-bare: {c.name}: {e}"
  | .ok text => IO.FS.writeFile s!"{dir}/{c.name}.c" text
  IO.FS.writeFile s!"{dir}/{c.name}.depth"
    (String.join ((t.depthNames c.module).map (· ++ "\n")))
  match ← IO.ofExcept (talosBytes c) with
  | some talos =>
      if talos != c.bytes then
        throw <| IO.userError s!"native-bare: {c.name}: Talos gives {talos}, Lean {c.bytes}"
      IO.FS.writeBinFile s!"{dir}/{c.name}.expected" (ByteArray.mk c.bytes.toArray)
      IO.FS.writeFile s!"{dir}/{c.name}.status" "0\n"
      IO.println s!"native-bare: {c.name}: {c.bytes.length} bytes, as Talos gives them"
  | none =>
      unless c.aborts do
        throw <| IO.userError s!"native-bare: {c.name}: Talos traps, and the entry cannot abort"
      IO.FS.writeBinFile s!"{dir}/{c.name}.expected" ByteArray.empty
      IO.FS.writeFile s!"{dir}/{c.name}.status" s!"{trapUnreachable}\n"
      IO.println s!"native-bare: {c.name}: Talos traps at unreachable"

def check (dir : String) : IO UInt32 := do
  let mut failed := false
  for c in cases do
    let some t := translate nativeCap c.module
      | throw <| IO.userError s!"native-bare: {c.name}: the module does not translate"
    let text ← IO.FS.readFile s!"{dir}/{c.name}.v"
    match ClightCheck.check t text (bareTail (bareMain nativeCap c.k c.args c.kind)) with
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
