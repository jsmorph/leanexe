import Examples.Binary32.Program
import Examples.Host

/-! The module cases of `binary32`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Binary32

open Examples.Host

def fl32 (x : Float32) : String := s!"f32:{x.toBits}"

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

def binary32Cases : IO Unit := do
  for (a, x, y) in float32Triples do
    line "binary32" "axpy32" "f32" [fl32 a, fl32 x, fl32 y]
      (toString (Examples.Binary32.axpy32 a x y).toBits)
    line "binary32" "hypot32" "f32" [fl32 a, fl32 x]
      (toString (Examples.Binary32.hypot32 a x).toBits)
    line "binary32" "ratio32" "f32" [fl32 a, fl32 x, fl32 y]
      (toString (Examples.Binary32.ratio32 a x y).toBits)
  let bounds : List (Float32 × Float32 × Float32) :=
    [(1.0, 1.0, 2.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (1.5, 1.0, 2.0), (2.0, 1.0, 2.0),
      (nan32, 1.0, 2.0), (1.5, nan32, 2.0), (1.5, 1.0, nan32), (-0.0, 0.0, 1.0), (1.5, 2.0, 1.0)]
  for (x, lo, hi) in bounds ++ float32Triples do
    line "binary32" "piecewise32" "f32" [fl32 x, fl32 lo, fl32 hi]
      (toString (Examples.Binary32.piecewise32 x lo hi).toBits)
  -- Arrays for scale32 and axpyArray32, with some second arrays shorter than the first.
  for n in [0, 1, 5, 17] do
    for (a, k) in (specialFloat32s.take 6).zip (List.range 6) do
      let x := (List.range n).map fun i => if i % 2 = 0 then rf32 (i + 7 * k) else small32 (i + k)
      let y := (List.range (if k % 3 = 1 then n / 2 else n)).map fun i => small32 (3 * i + k)
      let words32 (xs : List Float32) : List UInt64 := xs.map fun x => x.toBits.toUInt64
      line "binary32" "scale32" "array-u64" [fl32 a, arrU (words32 x)]
        (words (words32 (Examples.Binary32.scale32 a x.toArray).toList))
      line "binary32" "axpyArray32" "array-u64" [fl32 a, arrU (words32 x), arrU (words32 y)]
        (words (words32 (Examples.Binary32.axpyArray32 a x.toArray y.toArray).toList))
  -- Matrices stored by rows with the vectors they multiply, including short matrices and vectors,
  -- whose missing elements count as 0.
  let words32 (xs : List Float32) : List UInt64 := xs.map fun x => x.toBits.toUInt64
  let vals (n start : Nat) : List Float32 :=
    (List.range n).map fun i => if i % 7 = 3 then rf32 (start + i) else small32 (start + i)
  let shapes : List (Nat × Nat × Nat × Nat) :=
    [(0, 0, 0, 0), (1, 1, 1, 1), (2, 3, 6, 3), (3, 2, 6, 2), (4, 4, 16, 4), (3, 3, 7, 2),
      (5, 1, 5, 1), (1, 5, 5, 5), (2, 2, 4, 0), (6, 4, 24, 4)]
  for (rows, cols, mLen, vLen) in shapes do
    let m := vals mLen (rows * 31 + cols)
    let v := vals vLen (rows * 17 + cols * 5 + 1000)
    let r := Examples.Binary32.matVec32 m.toArray v.toArray rows.toUInt64 cols.toUInt64
    line "binary32" "matVec32" "array-u64"
      [arrU (words32 m), arrU (words32 v), u rows.toUInt64, u cols.toUInt64]
      (words (words32 r.toList))

def cases : IO Unit := do
  binary32Cases

end Examples.Binary32
