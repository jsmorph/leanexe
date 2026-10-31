import Examples.Binary32.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `binary32` and of its WGSL kernels. -/

namespace Examples.Binary32

open TestSupport.Host

def inf32 : Float32 := 1.0 / 0.0
def nan32 : Float32 := 0.0 / 0.0

def specialFloat32s : List Float32 :=
  [0.0, -0.0, 1.0, -1.0, 0.5, inf32, -inf32, nan32, 3.4028235e38, -3.4028235e38, 1.4e-45,
    1.17549435e-38, 1e30, 1e-30, 3.0, 7.25]

/-- Arbitrary bit patterns as binary32 floats. -/
def rf32 (i : Nat) : Float32 := Float32.ofBits (rw i).toUInt32

/-- Values from -10 to 10 in steps of 0.01, in binary32. -/
def small32 (i : Nat) : Float32 := (small i).toFloat32

def float32Triples : List (Float32 × Float32 × Float32) :=
  let sp := specialFloat32s.toArray
  let special := (List.range 30).map fun i =>
    (sp[i % sp.size]!, sp[(i / 3 + 5) % sp.size]!, sp[(7 * i + 1) % sp.size]!)
  let random := (List.range 30).map fun i =>
    (rf32 (3 * i + 500), rf32 (3 * i + 501), rf32 (3 * i + 502))
  let moderate := (List.range 20).map fun i =>
    (small32 (3 * i), small32 (3 * i + 1), small32 (3 * i + 2))
  special ++ random ++ moderate

/-- The arguments `(x, lo, hi)` of `piecewise32`. -/
def piecewiseArgs : List (Float32 × Float32 × Float32) :=
  [(1.0, 1.0, 2.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (1.5, 1.0, 2.0), (2.0, 1.0, 2.0),
    (nan32, 1.0, 2.0), (1.5, nan32, 2.0), (1.5, 1.0, nan32), (-0.0, 0.0, 1.0), (1.5, 2.0, 1.0)] ++
    float32Triples

/-- The arguments `(a, x, y)` of `scale32` and `axpyArray32`, with some second arrays shorter than
the first. -/
def vectorArgs : List (Float32 × List Float32 × List Float32) :=
  [0, 1, 5, 17].flatMap fun n =>
    ((specialFloat32s.take 6).zip (List.range 6)).map fun (a, k) =>
      (a, (List.range n).map (fun i => if i % 2 = 0 then rf32 (i + 7 * k) else small32 (i + k)),
        (List.range (if k % 3 = 1 then n / 2 else n)).map fun i => small32 (3 * i + k))

/-- The arguments `(m, v, rows, cols)` of `matVec32`: matrices stored by rows with the vectors they
multiply, including short matrices and vectors, whose missing elements count as 0. -/
def matVecArgs : List (List Float32 × List Float32 × UInt64 × UInt64) :=
  let vals (n start : Nat) : List Float32 :=
    (List.range n).map fun i => if i % 7 = 3 then rf32 (start + i) else small32 (start + i)
  let shapes : List (Nat × Nat × Nat × Nat) :=
    [(0, 0, 0, 0), (1, 1, 1, 1), (2, 3, 6, 3), (3, 2, 6, 2), (4, 4, 16, 4), (3, 3, 7, 2),
      (5, 1, 5, 1), (1, 5, 5, 5), (2, 2, 4, 0), (6, 4, 24, 4)]
  shapes.map fun (rows, cols, mLen, vLen) =>
    (vals mLen (rows * 31 + cols), vals vLen (rows * 17 + cols * 5 + 1000), rows.toUInt64,
      cols.toUInt64)

/-- The arguments `(x, lo, hi, n)` of `condMix32`, whose mirror reads stop at `n`: all elements,
half,
or a bound beyond every index. -/
def condMixArgs : List (List Float32 × Float32 × Float32 × UInt64) :=
  let sp := specialFloat32s.toArray
  [0, 1, 3, 4, 7, 64, 65].flatMap fun n =>
    (List.range 8).map fun k =>
      ((List.range n).map (fun i =>
          if i % 3 = 0 then rf32 (i + 11 * k) else sp[(i + 5 * k) % sp.size]!),
        sp[k % sp.size]!, sp[(k * 7 + 3) % sp.size]!,
        if k % 3 = 0 then n.toUInt64 else if k % 3 = 1 then (n / 2).toUInt64 else 0xffffffff00000000)

end Examples.Binary32
