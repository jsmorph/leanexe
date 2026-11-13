import Demos.Conjunction.Adaptive

/-! `conjunction-evaluate FILE` evaluates `Demos.Conjunction.pc` and
`Demos.Conjunction.Adaptive.pcAdaptive` in native Lean on the inputs of `FILE`, for
`tests/conjunction/benchmark.sh`.  Each line of `FILE` holds `pc` or `adaptive`, a name without
spaces, the bit patterns of `m1 m2 c11 c12 c22 r`, and `n`.  The program prints each line followed
by the status and the bit patterns of `lo` and `hi`. -/

open Demos.Conjunction

def evaluate (line : String) : Except String String := do
  let fields := (line.splitOn " ").filter (· ≠ "")
  let some nums := (fields.drop 2).mapM String.toNat?
    | throw s!"malformed line: {line}"
  let [m1, m2, c11, c12, c22, r, n] := nums.map (fun v => v.toUInt64)
    | throw s!"malformed line: {line}"
  let f := Float.ofBits
  let result ← match fields.head? with
    | some "pc" => pure (pc (f m1) (f m2) (f c11) (f c12) (f c22) (f r) n)
    | some "adaptive" => pure (Adaptive.pcAdaptive (f m1) (f m2) (f c11) (f c12) (f c22) (f r) n)
    | _ => throw s!"unknown method: {line}"
  pure s!"{line} {result.status} {result.lo.toBits} {result.hi.toBits}"

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: conjunction-evaluate FILE"; return 2
  for line in (← IO.FS.lines file) do
    if line.trim.isEmpty then continue
    match evaluate line.trim with
    | .ok out => IO.println out
    | .error e => IO.eprintln e; return 1
  return 0
