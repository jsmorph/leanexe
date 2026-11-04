import TestSupport.Native.ClightGen

/-!
The executable `clight-diff SEED COUNT ARCHI DIR` writes `COUNT` random programs of
`ClightGen` from the seed `SEED` as `DIR/tI.c`, with the output that `LClight.run` gives for each
under the instance of `Archi` that `ARCHI` names, `x86_64`, `aarch64`, or `arm`, as
`DIR/tI.expected`, and the programs of `nanPrograms` as `DIR/nanI.c` and `DIR/nanI.expected`, and
`COUNT` trace programs as `DIR/vI.c`, with the lines of `expectedTrace` as `DIR/vI.expected`, and
`COUNT` input programs as `DIR/wI.c` and `DIR/wI.expected`.  It runs each program under all three
instances and prints, for each kind of program, the number whose output differs between `x86_64`
and `aarch64`, which differ only in the NaN rules, and the number whose output differs between
`aarch64` and `arm`, which differ only in the width of pointers.  `tests/native/clight.sh` runs
CompCert's reference interpreter on the C files and compares.
-/

open LClight TestSupport.Native.ClightGen

def fuel : Nat := 1000000

/-- The output of a program under `Archi.x86_64`, `Archi.aarch64`, and `Archi.arm`. -/
structure Outputs where
  x86_64 : String
  aarch64 : String
  arm : String

def outputs (f : Archi → String) : Outputs :=
  { x86_64 := f Archi.x86_64, aarch64 := f Archi.aarch64, arm := f Archi.arm }

def report (kind : String) (os : Array Outputs) : IO Unit := do
  let nan := (os.filter fun o => o.x86_64 != o.aarch64).size
  let width := (os.filter fun o => o.aarch64 != o.arm).size
  IO.println (s!"clight-diff: {nan} of {os.size} {kind} differ between x86_64 and aarch64, " ++
    s!"{width} between aarch64 and arm")

def main (args : List String) : IO UInt32 := do
  match args with
  | [seedText, countText, archiText, dir] =>
      let some seed := seedText.toNat?
        | throw <| IO.userError s!"clight-diff: the seed {seedText} is not a number"
      let some count := countText.toNat?
        | throw <| IO.userError s!"clight-diff: the count {countText} is not a number"
      let select ← match archiText with
        | "x86_64" => pure Outputs.x86_64
        | "aarch64" => pure Outputs.aarch64
        | "arm" => pure Outputs.arm
        | _ => throw (IO.userError
            s!"clight-diff: the architecture {archiText} is not x86_64, aarch64, or arm")
      IO.FS.createDirAll dir
      let write (file : String) (text : Except String String) (out : Archi → String) :
          IO Outputs := do
        match text with
        | .error e => throw <| IO.userError s!"clight-diff: {file}: {e}"
        | .ok c =>
            let o := outputs out
            IO.FS.writeFile s!"{dir}/{file}.c" c
            IO.FS.writeFile s!"{dir}/{file}.expected" (select o)
            pure o
      let mut gen := mkStdGen seed
      let mut random : Array Outputs := #[]
      for i in [0:count] do
        let (p, gen') := Id.run (genProgram.run gen)
        gen := gen'
        random := random.push (← write s!"t{i}" (cText p) (expected · p fuel))
      report "random programs" random
      let mut nan : Array Outputs := #[]
      for (p, i) in nanPrograms.zipIdx do
        nan := nan.push (← write s!"nan{i}" (cText p) (expected · p fuel))
      report "NaN programs" nan
      let mut traces : Array Outputs := #[]
      for i in [0:count] do
        let (p, gen') := Id.run (genTraceProgram.run gen)
        gen := gen'
        traces := traces.push (← write s!"v{i}" (traceText p) (expectedTrace · p fuel))
      report "trace programs" traces
      let mut inputs : Array Outputs := #[]
      for i in [0:count] do
        let (p, gen') := Id.run (genInputProgram.run gen)
        gen := gen'
        inputs := inputs.push (← write s!"w{i}" (traceText p) (expectedTrace · p fuel))
      report "input programs" inputs
      pure 0
  | _ => throw <| IO.userError "usage: clight-diff SEED COUNT x86_64|aarch64|arm DIR"
