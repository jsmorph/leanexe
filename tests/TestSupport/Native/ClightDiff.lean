import TestSupport.Native.ClightGen

/-!
The executable `clight-diff SEED COUNT ARCHI DIR` writes `COUNT` random programs of
`ClightGen` from the seed `SEED` as `DIR/tI.c`, with the output that `LClight.run` gives for each
under the NaN parameters of `ARCHI`, `x86_64` or `aarch64`, as `DIR/tI.expected`, and the
programs of `nanPrograms` as `DIR/nanI.c` and `DIR/nanI.expected`, and `COUNT` trace programs
as `DIR/vI.c`, with the lines of `expectedTrace` as `DIR/vI.expected`.  It prints the number of
programs of each kind whose output differs between the two targets, which measures how often the
NaN parameters come into play.  `tests/native/clight.sh` runs CompCert's reference interpreter
on the C files and compares.
-/

open LClight TestSupport.Native.ClightGen

def fuel : Nat := 1000000

def main (args : List String) : IO UInt32 := do
  match args with
  | [seedText, countText, archiText, dir] =>
      let some seed := seedText.toNat?
        | throw <| IO.userError s!"clight-diff: the seed {seedText} is not a number"
      let some count := countText.toNat?
        | throw <| IO.userError s!"clight-diff: the count {countText} is not a number"
      let onX86 ← match archiText with
        | "x86_64" => pure true
        | "aarch64" => pure false
        | _ => throw <| IO.userError s!"clight-diff: the architecture {archiText} is not x86_64 or aarch64"
      IO.FS.createDirAll dir
      let write (file : String) (p : program function) : IO Bool := do
        match cText p with
        | .error e => throw <| IO.userError s!"clight-diff: {file}: {e}"
        | .ok text =>
            let x86 := expected Archi.x86_64 p fuel
            let arm := expected Archi.aarch64 p fuel
            IO.FS.writeFile s!"{dir}/{file}.c" text
            IO.FS.writeFile s!"{dir}/{file}.expected" (if onX86 then x86 else arm)
            pure (x86 != arm)
      let mut gen := mkStdGen seed
      let mut dependent := 0
      for i in [0:count] do
        let (p, gen') := Id.run (genProgram.run gen)
        gen := gen'
        if (← write s!"t{i}" p) then
          dependent := dependent + 1
      IO.println s!"clight-diff: {dependent} of {count} random programs differ between x86_64 and aarch64"
      let mut nanDependent := 0
      for (p, i) in nanPrograms.zipIdx do
        if (← write s!"nan{i}" p) then
          nanDependent := nanDependent + 1
      IO.println s!"clight-diff: {nanDependent} of {nanPrograms.length} NaN programs differ between x86_64 and aarch64"
      let mut traceDependent := 0
      for i in [0:count] do
        let (p, gen') := Id.run (genTraceProgram.run gen)
        gen := gen'
        match traceText p with
        | .error e => throw <| IO.userError s!"clight-diff: v{i}: {e}"
        | .ok text =>
            let x86 := expectedTrace Archi.x86_64 p fuel
            let arm := expectedTrace Archi.aarch64 p fuel
            IO.FS.writeFile s!"{dir}/v{i}.c" text
            IO.FS.writeFile s!"{dir}/v{i}.expected" (if onX86 then x86 else arm)
            if x86 != arm then traceDependent := traceDependent + 1
      IO.println s!"clight-diff: {traceDependent} of {count} trace programs differ between x86_64 and aarch64"
      pure 0
  | _ => throw <| IO.userError "usage: clight-diff SEED COUNT x86_64|aarch64 DIR"
