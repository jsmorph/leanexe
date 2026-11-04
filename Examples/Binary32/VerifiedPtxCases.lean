import Examples.Binary32.Cases
import Examples.Binary32.CompiledPtx

/-! The PTX cases of the verified compiler's kernels of `scale32`, `axpyArray32`, `matVec32`, and
`condMix32`, in the format of `tests/ptx/Cases.lean`: `kernel|blocks|initial output|inputs|expected
output`, with each input the buffer that `LeanExe.Source.Arg.ptxBuffer` gives and the expected
output as 32-bit words.  The inputs are those of the WebAssembly cases. -/

namespace Examples.Binary32.VerifiedPtxCases

private def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

private def floatWords (x : List Float32) : Array UInt64 :=
  (x.map fun v => v.toBits.toUInt64).toArray

private def buffer (arg : LeanExe.Source.Arg) : String := s!"u64:{words arg.ptxBuffer.toList}"

/-- A case line for kernel `name` with `n` output elements, `extra` blocks of 64 threads beyond
those that cover them, and the buffers of `inputs`. -/
private def caseLine (name : String) (n extra : Nat) (inputs : List LeanExe.Source.Arg)
    (result : Array Float32) : String :=
  let blocks := (n + 63) / 64 + extra
  let initial := n.toUInt64 :: List.replicate n 0x7fc000017fc00001
  let out := result.toList.map fun v => v.toBits.toUInt64
  let output := (out.length.toUInt64 :: out).flatMap fun (x : UInt64) =>
    [x &&& 0xffffffff, x >>> 32]
  s!"{name}|{max blocks 1}|u64:{words initial}|{" ".intercalate (inputs.map buffer)}|" ++
    words output

def cases : IO Unit := do
  for ((a, x, y), k) in vectorArgs.zipIdx do
    IO.println (caseLine "verifiedScale32" x.length (k % 2) [.float a.toBits, .array (floatWords x)]
      (Library.Numerics.LinearAlgebra.Binary32.scale32 a x.toArray))
    IO.println (caseLine "verifiedAxpyArray32" x.length (k % 2)
      [.float a.toBits, .array (floatWords x), .array (floatWords y)]
      (Library.Numerics.LinearAlgebra.Binary32.axpyArray32 a x.toArray y.toArray))
  for ((m, v, rows, cols), k) in matVecArgs.zipIdx do
    IO.println (caseLine "verifiedMatVec32" rows.toNat (k % 2)
      [.array (floatWords m), .array (floatWords v), .word rows, .word cols]
      (Library.Numerics.LinearAlgebra.Binary32.matVec32 m.toArray v.toArray rows cols))
  for (args, k) in condMixArgs.zipIdx do
    let (x, lo, hi, n) := args
    IO.println (caseLine "verifiedCondMix32" x.length (k % 2)
      [.array (floatWords x), .float lo.toBits, .float hi.toBits, .word n]
      (condMix32 x.toArray lo hi n))

end Examples.Binary32.VerifiedPtxCases
