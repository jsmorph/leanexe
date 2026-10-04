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

/-- A binary32 scalar parameter's buffer: its bits and 0. -/
def scalarBuffer (a : Float32) : String := s!"u32:{a.toBits},0"

def main : IO Unit := do
  let sizes := [0, 1, 2, 15, 63, 64, 65, 200]
  for n in sizes do
    for (a, k) in specials.zip (List.range specials.length) do
      let x := (List.range n).map fun i => if i % 3 = 0 then arbitrary (i + 31 * k)
        else specials[(i + k) % specials.length]!
      let y := (List.range (if k % 4 = 1 then n / 2 else n)).map fun i =>
        if i % 2 = 0 then arbitrary (i + 17 * k + 5) else specials[(i + 2 * k) % specials.length]!
      let groups := max ((n + 63) / 64 + (if k % 2 = 0 then 0 else 1)) 1
      let initial := n.toUInt64 :: (List.replicate n 0x7fc000017fc00001)
      let r := (scale32 a x.toArray).toList
      IO.println s!"scale|{groups}|u64:{words initial}|{scalarBuffer a} u64:{words (arrayWords64 x)}|{words (arrayWords32 r)}"
      let r2 := (axpyArray32 a x.toArray y.toArray).toList
      IO.println s!"axpyArray|{groups}|u64:{words initial}|{scalarBuffer a} u64:{words (arrayWords64 x)} u64:{words (arrayWords64 y)}|{words (arrayWords32 r2)}"
  for rows in [0, 1, 2, 5, 64, 65] do
    for cols in [0, 1, 3, 7, 40] do
      for variant in [0, 1] do
        let seed := 7 * rows + 13 * cols + variant
        let mSize := if variant = 1 then rows * cols / 2 else rows * cols
        let vSize := if variant = 1 && cols > 1 then cols - 1 else cols
        let m := (List.range mSize).map fun i => if i % 4 = 0 then arbitrary (i + seed)
          else specials[(i + seed) % specials.length]!
        let v := (List.range vSize).map fun i => if i % 5 = 0 then arbitrary (i + 3 * seed)
          else specials[(2 * i + seed) % specials.length]!
        let groups := max ((rows + 63) / 64 + variant) 1
        let initial := rows.toUInt64 :: (List.replicate rows 0x7fc000017fc00001)
        let r := (matVec32 m.toArray v.toArray rows.toUInt64 cols.toUInt64).toList
        IO.println s!"matVec|{groups}|u64:{words initial}|u64:{words (arrayWords64 m)} u64:{words (arrayWords64 v)} u64:{rows} u64:{cols}|{words (arrayWords32 r)}"
  for n in [0, 1, 3, 4, 7, 64, 65, 130] do
    for (lo, k) in specials.zip (List.range specials.length) do
      let hi := specials[(k * 7 + 3) % specials.length]!
      let x := (List.range n).map fun i => if i % 3 = 0 then arbitrary (i + 11 * k)
        else specials[(i + 5 * k) % specials.length]!
      let bound : UInt64 := if k % 3 = 0 then n.toUInt64 else if k % 3 = 1 then (n / 2).toUInt64
        else 0xffffffff00000000
      let groups := max ((n + 63) / 64 + (if k % 2 = 0 then 0 else 1)) 1
      let initial := n.toUInt64 :: (List.replicate n 0x7fc000017fc00001)
      let r := (condMix32 x.toArray lo hi bound).toList
      IO.println s!"condMix|{groups}|u64:{words initial}|u64:{words (arrayWords64 x)} {scalarBuffer lo} {scalarBuffer hi} u64:{bound}|{words (arrayWords32 r)}"

