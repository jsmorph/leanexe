import TestSupport.Native.Gcd
import LeanExe.Native.Bare

/-!
Writes the C text of the bare-metal program of `gcd 1071 462`, as `native-bare emit` writes it
(`tests/TestSupport/Bare/Emit.lean`), to `DIR/gcd.c`, and the bytes of its output, separated by
commas, to `DIR/gcd.bytes`.  `clightn/check.sh` runs it with `lake env lean --run`.
-/

open LeanExe.Native LClight

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  let some t := translate nativeCap TestSupport.Native.Gcd.loopCompiled.module
    | IO.eprintln "clightn: the module of gcd does not translate"; return 1
  match t.bareText nativeCap 2 [1071, 462] .word with
  | .error e => IO.eprintln s!"clightn: {e}"; return 1
  | .ok text => IO.FS.writeFile s!"{dir}/gcd.c" text
  let bytes := encodeWord (TestSupport.Native.Gcd.gcd 1071 462)
  IO.FS.writeFile s!"{dir}/gcd.bytes" (",".intercalate (bytes.map (toString ·.toNat)) ++ "\n")
  return 0
