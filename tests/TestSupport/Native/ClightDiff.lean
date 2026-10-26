import TestSupport.Native.ClightGen

/-!
The executable `clight-diff SEED COUNT ARCHI DIR` writes `COUNT` random programs of
`ClightGen` from the seed `SEED` as `DIR/tI.c`, with the output that `LClight.run` gives for each
under the NaN parameters of `ARCHI`, `x86_64` or `aarch64`, as `DIR/tI.expected`.
`tests/native/clight.sh` runs CompCert's reference interpreter on the C files and compares.
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
      let archi ← match archiText with
        | "x86_64" => pure Archi.x86_64
        | "aarch64" => pure Archi.aarch64
        | _ => throw <| IO.userError s!"clight-diff: the architecture {archiText} is not x86_64 or aarch64"
      IO.FS.createDirAll dir
      let mut gen := mkStdGen seed
      for i in [0:count] do
        let (p, gen') := Id.run (genProgram.run gen)
        gen := gen'
        match cText p with
        | .error e => throw <| IO.userError s!"clight-diff: program {i}: {e}"
        | .ok text =>
            IO.FS.writeFile s!"{dir}/t{i}.c" text
            IO.FS.writeFile s!"{dir}/t{i}.expected" (expected archi p fuel)
      pure 0
  | _ => throw <| IO.userError "usage: clight-diff SEED COUNT x86_64|aarch64 DIR"
