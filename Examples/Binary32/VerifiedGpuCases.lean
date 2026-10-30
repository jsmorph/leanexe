import Examples.Binary32.Cases
import LeanExe.WGSL.Build

/-! The GPU cases of the verified compiler's kernels of `scale32`, `axpyArray32`, `matVec32`, and
`condMix32`, in the format of `tests/wgsl/run.sh`: `kernel|workgroups|initial output|inputs|expected
output`, with each input the buffer that the kernel's dispatch theorem names and the expected output
as 32-bit words.  The inputs are those of the WebAssembly cases. -/

namespace Examples.Binary32.VerifiedGpuCases

open LeanExe.WGSL

private def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

private def floatWords (x : List Float32) : Array UInt64 := (x.map fun v => v.toBits.toUInt64).toArray

private def gpuArg (arg : Arg) : String := s!"u32:{",".intercalate (arg.buffer.toList.map toString)}"

/-- A case line for kernel `name` with `n` output elements, `extra` workgroups beyond those that
cover them, and the buffers of `inputs`. -/
private def caseLine (name : String) (n extra : Nat) (inputs : List Arg) (result : Array Float32) :
    String :=
  let groups := max ((n + 63) / 64 + extra) 1
  let initial := n.toUInt64 :: List.replicate n 0x7fc000017fc00001
  let out := result.toList.map fun v => v.toBits.toUInt64
  let output := (out.length.toUInt64 :: out).flatMap fun (x : UInt64) =>
    [x &&& 0xffffffff, x >>> 32]
  s!"{name}|{groups}|u64:{words initial}|{" ".intercalate (inputs.map gpuArg)}|{words output}"

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

end Examples.Binary32.VerifiedGpuCases
