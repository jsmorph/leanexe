import Library.Hashing.Sha256.Compiled
import LeanExe.Native.Bare

/-!
Writes the C text of the program with input around the export `sha256` of
`Library.Hashing.Sha256.compiled`, function 11, whose `main` writes the four words of the digest
from the result globals, as `native-bare emit-in` writes it (`tests/TestSupport/Bare/Emit.lean`),
to `DIR/sha.c`.  `clightn/check.sh` runs it with `lake env lean --run`.
-/

open LeanExe.Native LClight

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  let some t := translate nativeCap Library.Hashing.Sha256.compiled.module
    | IO.eprintln "clightn: the module of sha256 does not translate"; return 1
  match t.inText nativeCap 11 (.words 4) with
  | .error e => IO.eprintln s!"clightn: {e}"; return 1
  | .ok text => IO.FS.writeFile s!"{dir}/sha.c" text
  return 0
