import Verified.Examples.PtxCases
import Examples.Binary32.VerifiedPtxCases
import Demos.Gpt32.VerifiedCases

/-! Test cases for the PTX kernels, computed by native Lean: the add-one kernel's, then those of
`Verified.Examples.PtxCases`, `Examples.Binary32.VerifiedPtxCases`, and the PTX format of
`Demos.Gpt32.VerifiedCases`.  Each line is
`kernel|blocks|initial output|inputs|expected output`, with buffers in the harness's `u64:`
notation and the expected output as 32-bit words joined by commas, least significant half of each
64-bit word first.  `tests/ptx/run.sh` runs each case with `build/tools/leanexe-cuda-host` and
compares.  Run with `lake env lean --run`. -/

def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

def halves (xs : List UInt64) : String :=
  words (xs.flatMap fun (w : UInt64) => [w &&& 0xffffffff, w >>> 32])

/-- Arbitrary 64-bit words, with the largest word at every 17th place. -/
def arbitrary (n seed : Nat) : List UInt64 :=
  (List.range n).map fun i =>
    if (i + seed) % 17 = 16 then 0xffffffffffffffff
    else UInt64.ofNat ((i + 31 * seed) * 6364136223846793005 + 1442695040888963407)

/-- A case of the add-one kernel: `n` words, launched with `blocks` blocks of 64 threads. -/
def addOneCase (n seed blocks : Nat) : String :=
  let xs := arbitrary n seed
  let len := UInt64.ofNat n
  s!"addOne|{blocks}|u64:{words (len :: List.replicate n 0)}|u64:{words (len :: xs)}|" ++
    halves (len :: xs.map (· + 1))

def main : IO Unit := do
  for (n, seed) in [(0, 1), (1, 2), (63, 3), (64, 4), (65, 5), (200, 6), (1000, 7), (4096, 8)] do
    IO.println (addOneCase n seed (max 1 ((n + 63) / 64)))
  IO.println (addOneCase 100 9 5)
  Verified.Examples.PtxCases.runCases
  Examples.Binary32.VerifiedPtxCases.cases
  Demos.Gpt32.VerifiedCases.runCases .ptx
