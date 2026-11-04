import Verified.Examples.Ptx

/-!
Test cases of the PTX kernels of `flags` and `wordScan`, computed by native Lean, in the format of
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

def runCases : IO Unit := do
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
