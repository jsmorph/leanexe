import LeanExe.Examples.Binary32

/-! Test cases for the WGSL kernels, computed by native Lean.  Each line is
`kernel|workgroups|initial output|inputs|expected output`, with buffers in the harness's `u64:`
notation and the expected output as 32-bit words joined by commas.  `tests/wgsl/run.sh` runs each
case with `build/tools/leanexe-webgpu-host` and compares.  Run with `lake env lean --run`. -/

open LeanExe.Examples.Binary32

def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

/-- A Wasm array of binary32 values as 64-bit words: the length, then each value's bits. -/
def arrayWords64 (xs : List Float32) : List UInt64 :=
  xs.length.toUInt64 :: xs.map fun x => x.toBits.toUInt64

/-- The same array as 32-bit words, least significant half first. -/
def arrayWords32 (xs : List Float32) : List UInt64 :=
  (arrayWords64 xs).flatMap fun w => [w &&& 0xffffffff, w >>> 32]

def inf32 : Float32 := 1.0 / 0.0
def nan32 : Float32 := 0.0 / 0.0

def specials : List Float32 :=
  [0.0, -0.0, 1.0, -1.0, 0.5, inf32, -inf32, nan32, 3.4028235e38, 1.4e-45, 1.17549435e-38, 3.0,
    7.25, -2.5e-20, 1.0e20]

/-- Arbitrary bit patterns as binary32 values. -/
def arbitrary (i : Nat) : Float32 :=
  Float32.ofBits (UInt32.ofNat ((i * 2654435761 + 12345) % 4294967296))

def main : IO Unit := do
  let sizes := [0, 1, 2, 15, 63, 64, 65, 200]
  for n in sizes do
    for (a, k) in specials.zip (List.range specials.length) do
      let x := (List.range n).map fun i => if i % 3 = 0 then arbitrary (i + 31 * k)
        else specials[(i + k) % specials.length]!
      let r := (scale32 a x.toArray).toList
      let groups := (n + 63) / 64 + (if k % 2 = 0 then 0 else 1)
      let initial := n.toUInt64 :: (List.replicate n 0x7fc000017fc00001)
      IO.println s!"scale|{max groups 1}|u64:{words initial}|u64:{words (arrayWords64 x)} u64:{a.toBits.toUInt64}|{words (arrayWords32 r)}"
