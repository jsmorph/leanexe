import TestSupport.Bare.Gcd
import TestSupport.Bare.Theorems
import TestSupport.Bare.Input
import TestSupport.Bare.Ctl
import TestSupport.Bare.Req
import TestSupport.Bare.Records
import Demos.Energy.Loop
import LeanExe.Native.Bare

/-!
Writes, for each instance that `clightn/check.sh` names, the C text of its whole program to
`DIR/NAME/NAME.c`, as `native-bare` writes it (`tests/TestSupport/Bare/Emit.lean`), and, for a
bare-metal program, the bytes of its output, separated by commas, to `DIR/NAME/NAME.bytes`.  The
program of each instance is that of the theorem that its Lean proof carries: the entry, the
arguments, and the kind of result of a bare-metal program, the entry of a program with input,
the step and the initial state of a controller, and the step and the words of the initial state
of a program with requests.  The emitter is untrusted, since each proof checks that renaming the
theorem's program gives the program of `clightgen`'s file.  `clightn/check.sh` runs it with
`lake env lean --run`.
-/

open LeanExe.Native LClight

/-- An instance's module, the pages of `lx_mem` of its translation, the C text of the whole
program from the translation, and the bytes of a bare-metal program's output. -/
structure Instance where
  module : Wasm.Module
  cap : Nat
  text : Translation → Except String String
  bytes : Option (List UInt8) := none

def instances : List (String × Instance) := [
  ("gcd",
    { module := TestSupport.Native.Gcd.loopCompiled.module, cap := nativeCap,
      text := (·.bareText nativeCap 2 [1071, 462] .word),
      bytes := some (encodeWord (TestSupport.Native.Gcd.gcd 1071 462)) }),
  ("crc32",
    { module := TestSupport.Bare.crcCompiled.module, cap := nativeCap,
      text := (·.bareText nativeCap 5 [0x3837363534333231, 0x39] .word),
      bytes := some (encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39)) }),
  ("sha256",
    { module := TestSupport.Bare.shaCompiled.module, cap := nativeCap,
      text := (·.bareText nativeCap 11 [0x636261] .array),
      bytes := some (encodeArray (TestSupport.Bare.shaCheck 0x636261)) }),
  ("depth",
    { module := Verified.Examples.Fold.compiled.module, cap := nativeCap,
      text := (·.bareText nativeCap 13 [1000] .word),
      bytes := some (encodeWord (Verified.Examples.Fold.recursive 1000)) }),
  ("sha",
    { module := Library.Hashing.Sha256.compiled.module, cap := nativeCap,
      text := (·.inText nativeCap 11 (.words 4)) }),
  ("ctl", { module := TestSupport.Bare.ctlCompiled.module, cap := 1, text := (·.ctlText 2 0) }),
  ("echo",
    { module := TestSupport.Bare.reqCompiled.module, cap := 1, text := (·.reqText 5 [3]) }),
  ("deadline",
    { module := TestSupport.Bare.reqCompiled.module, cap := 1, text := (·.reqText 8 [5]) }),
  ("records",
    { module := TestSupport.Bare.sumCompiled.module, cap := 1,
      text := (·.reqText 5 (TestSupport.Bare.sumWords TestSupport.Bare.sumInit)) }),
  ("gateway",
    { module := Demos.Energy.gwCompiled.module, cap := 1,
      text := (·.reqText 33 (Demos.Energy.gwWords Demos.Energy.gwInit)) })]

def main (args : List String) : IO UInt32 := do
  let dir :: names := args
    | IO.eprintln "usage: lean --run clightn/emit.lean DIR NAME..."; return 2
  for name in names do
    let some i := instances.lookup name
      | IO.eprintln s!"clightn: no instance {name}"; return 1
    let some t := translate i.cap i.module
      | IO.eprintln s!"clightn: the module of {name} does not translate"; return 1
    match i.text t with
    | .error e => IO.eprintln s!"clightn: {name}: {e}"; return 1
    | .ok text => IO.FS.writeFile s!"{dir}/{name}/{name}.c" text
    if let some bs := i.bytes then
      IO.FS.writeFile s!"{dir}/{name}/{name}.bytes"
        (",".intercalate (bs.map (toString ·.toNat)) ++ "\n")
  return 0
