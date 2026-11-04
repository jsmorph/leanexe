import Verified.Examples.Ptx

/-!
Test cases of the PTX kernels of the WGSL examples, computed by native Lean, in the format of
`tests/ptx/Cases.lean`: `kernel|blocks|initial output|inputs|expected output`.  Each argument's
buffer is the one that `LeanExe.Source.Arg.ptxBuffer` gives, and each launch has one block of 64
threads more than the count needs.
-/

namespace Verified.Examples.PtxCases

private def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

private def halves (xs : List UInt64) : String :=
  words (xs.flatMap fun (w : UInt64) => [w &&& 0xffffffff, w >>> 32])

private def buffer (arg : LeanExe.Source.Arg) : String := s!"u64:{words arg.ptxBuffer.toList}"

private def caseLine (kernel : String) (n : Nat) (inputs : List LeanExe.Source.Arg)
    (result : Array UInt64) : String :=
  let initial := n.toUInt64 :: List.replicate n 0x7fc000017fc00001
  s!"{kernel}|{(n + 63) / 64 + 1}|u64:{words initial}|{" ".intercalate (inputs.map buffer)}|" ++
    halves (n.toUInt64 :: result.toList)

private def fwords (xs : Array Float32) : Array UInt64 := xs.map fun x => x.toBits.toUInt64

/-- Signed zeros, ones, subnormals, infinities, the canonical NaN, and halves, as in the WGSL
cases. -/
private def floatSpecials : Array Float32 :=
  #[0, 0x80000000, 0x3f800000, 0xc0000000, 1, 0x007fffff, 0x7f800000, 0xff800000, 0x7fc00000,
    0x3f000000, 0xbf000000, 0x3fc00000, 0xbfc00000, 0x40200000, 0xc0200000].map Float32.ofBits

def runCases : IO Unit := do
  for n in [0, 1, 2, 7, 63, 64, 65] do
    let xs := (List.range n).toArray.map fun i => floatSpecials[i % floatSpecials.size]!
    for gain in floatSpecials do
      IO.println (caseLine "verifiedScale" n [.float gain.toBits, .array (fwords xs)]
        (fwords (Wgsl.scale gain xs)))
    IO.println (caseLine "verifiedRoots" n [.array (fwords xs)] (fwords (Wgsl.roundRoot xs)))
  for n in [0, 1, 2, 7, 64, 65] do
    for limit in [0, 1, 3, 8] do
      for size in [0, n / 2, n] do
        let xs := (List.range size).toArray.map fun i => floatSpecials[i % floatSpecials.size]!
        IO.println (caseLine "verifiedBranch" n
          [.array (fwords xs), .word n.toUInt64, .word limit.toUInt64]
          (fwords (Wgsl.branchSum xs n.toUInt64 limit.toUInt64)))
  for n in [0, 1, 2, 7, 63, 64, 65] do
    for invert in [false, true] do
      for size in [n / 2, n] do
        let xs := (List.range size).toArray.map fun i => i % 3 == 0
        IO.println (caseLine "verifiedFlags" n
          [.array (xs.map Verified.boolWord), .word n.toUInt64, .word (Verified.boolWord invert)]
          ((Wgsl.flags xs n.toUInt64 invert).map Verified.boolWord))
  let values : Array UInt64 := #[0, 1, 0xffffffffffffffff, 0x8000000000000000, 0x100000001, 7]
  for n in [0, 1, 2, 7, 63, 64, 65] do
    for size in [0, n / 2, n] do
      let xs := (List.range size).toArray.map fun i => values[i % values.size]!
      IO.println (caseLine "verifiedWords" n [.array xs, .word n.toUInt64]
        (Wgsl.wordScan xs n.toUInt64))

end Verified.Examples.PtxCases
