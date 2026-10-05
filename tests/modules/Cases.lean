import LeanExe.Examples.Scale
import LeanExe.Examples.Gcd
import LeanExe.Examples.SumArray
import LeanExe.Examples.PairSum
import LeanExe.Examples.SumCount
import LeanExe.Examples.Axpy
import LeanExe.Examples.Binary32
import LeanExe.Examples.ScaledHypot
import LeanExe.Examples.Piecewise
import LeanExe.Examples.SumSquares
import LeanExe.Examples.Mean
import LeanExe.Examples.Bucket
import LeanExe.Examples.Clob
import LeanExe.Examples.Calc
import LeanExe.Examples.Shape
import LeanExe.Examples.Lists
import LeanExe.Examples.Words
import LeanExe.Examples.Trees
import LeanExe.Examples.Updates
import LeanExe.Examples.Bools
import LeanExe.Examples.Grids

/-! Test cases for the modules other than `gpt.wasm` and `prng.wasm`, computed by native
Lean.  Each line is `module|export|result kind|host arguments|expected result`, with
floats given as bit patterns and a pair of arrays as the two arrays' words joined by a
comma; `tests/modules/run.sh` passes the arguments to the Wasmtime host running
`build/MODULE/MODULE.wasm` and compares its output.  Run with `lake env lean --run`. -/

def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)
def arrU (xs : List UInt64) : String := s!"array-u64:{words xs}"
def arrF (xs : List Float) : String := arrU (xs.map Float.toBits)
def chain (xs : List UInt64) : String := s!"chain-u64:{words xs}"
def u (n : UInt64) : String := s!"i64:{n}"
def fl (x : Float) : String := s!"f64:{x.toBits}"

def line (m name kind : String) (args : List String) (expected : String) : IO Unit :=
  IO.println s!"{m}|{name}|{kind}|{" ".intercalate args}|{expected}"

def pair (r : Array UInt64 × Array UInt64) : String := s!"{words r.1.toList},{words r.2.toList}"
def pairKind : String := "list:array-u64,array-u64"
def triple (r : Array UInt64 × Array UInt64 × Array UInt64) : String :=
  s!"{words r.1.toList},{words r.2.1.toList},{words r.2.2.toList}"
def tripleKind : String := "list:array-u64,array-u64,array-u64"

def inf : Float := 1.0 / 0.0
def nan : Float := 0.0 / 0.0
def maxU : UInt64 := 18446744073709551615

/-- Arbitrary words. -/
def rw (i : Nat) : UInt64 := UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64)
/-- Arbitrary bit patterns as floats. -/
def rf (i : Nat) : Float := Float.ofBits (rw i)
/-- Values from -10 to 10 in steps of 0.01. -/
def small (i : Nat) : Float := (UInt64.ofNat ((i * 2654435761) % 2001)).toFloat / 100.0 - 10.0
/-- Words below `n`. -/
def below (n i : Nat) : UInt64 := UInt64.ofNat ((i * 2654435761 + 7) % n)

def specialFloats : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, inf, -inf, nan, 1e308, -1e308, 5e-324, 2.2250738585072014e-308,
    1e200, 1e-200, 3.0, 7.25]

def scaleCases : IO Unit := do
  let chosen : List (UInt64 × UInt64 × UInt64) :=
    [(6, 7, 5), (6, 7, 0), (maxU, 2, 3), (0, 0, 1), (1, 1, 1), (4294967296, 4294967296, 1),
     (9223372036854775808, 2, 1), (maxU, maxU, maxU), (5, 0, 0)]
  let random := (List.range 40).map fun i => (rw (3 * i), rw (3 * i + 1), if i % 5 = 0 then 0 else rw (3 * i + 2) % 1000)
  for (a, b, c) in chosen ++ random do
    line "scale" "scale" "i64" [u a, u b, u c] (toString (LeanExe.Examples.Scale.scale a b c))

def gcdCases : IO Unit := do
  let chosen : List (UInt64 × UInt64) :=
    [(48, 18), (0, 0), (0, 5), (5, 0), (1, maxU), (maxU, maxU - 1), (9223372036854775808, 3),
     (12157665459056928801, 7540113804746346429), (1071, 462)]
  let random := (List.range 40).map fun i => (rw (2 * i + 100), if i % 7 = 0 then 0 else rw (2 * i + 101) % 100000)
  for (a, b) in chosen ++ random do
    line "gcd" "gcd" "i64" [u a, u b] (toString (LeanExe.Examples.Gcd.gcd a b))

def wordArrays : List (List UInt64) :=
  [[], [0], [1, 2, 3], [maxU, 2], [maxU, maxU, maxU]] ++
    (List.range 30).map fun i => (List.range (i % 12)).map fun k => rw (17 * i + k)

def sumArrayCases : IO Unit := do
  for xs in wordArrays do
    line "sumArray" "sumArray" "i64" [arrU xs] (toString (LeanExe.Examples.SumArray.sumArray xs.toArray))

def pairSumCases : IO Unit := do
  let chosen : List (UInt64 × UInt64) := [(3, 4), (maxU, 2), (0, 0), (maxU, maxU)]
  let random := (List.range 30).map fun i => (rw (2 * i + 300), rw (2 * i + 301))
  for (a, b) in chosen ++ random do
    line "pairSum" "pairSum" "i64" [u a, u b] (toString (LeanExe.Examples.PairSum.pairSum a b))

def sumCountCases : IO Unit := do
  for xs in wordArrays do
    line "sumCount" "sumCount" "array-u64" [arrU xs]
      (words (LeanExe.Examples.SumCount.sumCount xs.toArray).toList)

/-- Triples of special values, arbitrary bit patterns, and moderate values. -/
def floatTriples : List (Float × Float × Float) :=
  let sp := specialFloats.toArray
  let special := (List.range 30).map fun i =>
    (sp[i % sp.size]!, sp[(i / 3 + 5) % sp.size]!, sp[(7 * i + 1) % sp.size]!)
  let random := (List.range 30).map fun i => (rf (3 * i + 500), rf (3 * i + 501), rf (3 * i + 502))
  let moderate := (List.range 20).map fun i => (small (3 * i), small (3 * i + 1), small (3 * i + 2))
  special ++ random ++ moderate

def axpyCases : IO Unit := do
  for (a, x, y) in floatTriples do
    line "axpy" "axpy" "f64" [fl a, fl x, fl y] (toString (LeanExe.Examples.Axpy.axpy a x y).toBits)

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
      (toString (LeanExe.Examples.Binary32.axpy32 a x y).toBits)
    line "binary32" "hypot32" "f32" [fl32 a, fl32 x]
      (toString (LeanExe.Examples.Binary32.hypot32 a x).toBits)
    line "binary32" "ratio32" "f32" [fl32 a, fl32 x, fl32 y]
      (toString (LeanExe.Examples.Binary32.ratio32 a x y).toBits)
  let bounds : List (Float32 × Float32 × Float32) :=
    [(1.0, 1.0, 2.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (1.5, 1.0, 2.0), (2.0, 1.0, 2.0),
      (nan32, 1.0, 2.0), (1.5, nan32, 2.0), (1.5, 1.0, nan32), (-0.0, 0.0, 1.0), (1.5, 2.0, 1.0)]
  for (x, lo, hi) in bounds ++ float32Triples do
    line "binary32" "piecewise32" "f32" [fl32 x, fl32 lo, fl32 hi]
      (toString (LeanExe.Examples.Binary32.piecewise32 x lo hi).toBits)
  -- Arrays for scale32 and axpyArray32, with some second arrays shorter than the first.
  for n in [0, 1, 5, 17] do
    for (a, k) in (specialFloat32s.take 6).zip (List.range 6) do
      let x := (List.range n).map fun i => if i % 2 = 0 then rf32 (i + 7 * k) else small32 (i + k)
      let y := (List.range (if k % 3 = 1 then n / 2 else n)).map fun i => small32 (3 * i + k)
      let words32 (xs : List Float32) : List UInt64 := xs.map fun x => x.toBits.toUInt64
      line "binary32" "scale32" "array-u64" [fl32 a, arrU (words32 x)]
        (words (words32 (LeanExe.Examples.Binary32.scale32 a x.toArray).toList))
      line "binary32" "axpyArray32" "array-u64" [fl32 a, arrU (words32 x), arrU (words32 y)]
        (words (words32 (LeanExe.Examples.Binary32.axpyArray32 a x.toArray y.toArray).toList))
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
    let r := LeanExe.Examples.Binary32.matVec32 m.toArray v.toArray rows.toUInt64 cols.toUInt64
    line "binary32" "matVec32" "array-u64"
      [arrU (words32 m), arrU (words32 v), u rows.toUInt64, u cols.toUInt64]
      (words (words32 r.toList))

def scaledHypotCases : IO Unit := do
  for (x, y, s) in [(3.0, 4.0, 1.0), (3.0, 4.0, 0.0), (0.0, 0.0, 0.0)] ++ floatTriples do
    line "scaledHypot" "scaledHypot" "f64" [fl x, fl y, fl s]
      (toString (LeanExe.Examples.ScaledHypot.scaledHypot x y s).toBits)

def piecewiseCases : IO Unit := do
  let chosen : List (Float × Float × Float) :=
    [(1.0, 1.0, 2.0), (0.0, -0.0, 1.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (2.0, 1.0, 2.0),
     (1.5, 1.0, 2.0), (1.5, 2.0, 1.0), (nan, 1.0, 2.0), (1.0, nan, 2.0), (1.5, 1.0, nan)]
  for (x, lo, hi) in chosen ++ floatTriples do
    line "piecewise" "piecewise" "f64" [fl x, fl lo, fl hi]
      (toString (LeanExe.Examples.Piecewise.piecewise x lo hi).toBits)

def floatArrays : List (List Float) :=
  [[], [0.0], [-0.0], [1.0, 2.0, 3.0], [inf], [inf, -inf], [nan, 1.0], [1e200, 1e200], [5e-324, 5e-324],
    [1.0, 1e-16, 1e-16], [1e-16, 1e-16, 1.0], [1.7976931348623157e308, 1.0]] ++
    ((List.range 20).map fun i => (List.range (i % 9)).map fun k => rf (13 * i + k + 700)) ++
    ((List.range 20).map fun i => (List.range (i % 9 + 1)).map fun k => small (11 * i + k))

def sumSquaresCases : IO Unit := do
  for xs in floatArrays do
    line "sumSquares" "sumSquares" "f64" [arrF xs]
      (toString (LeanExe.Examples.SumSquares.sumSquares xs.toArray).toBits)

def meanCases : IO Unit := do
  for xs in floatArrays do
    line "mean" "mean" "f64" [arrF xs] (toString (LeanExe.Examples.Mean.mean xs.toArray).toBits)

def bucketCases : IO Unit := do
  let chosen : List (Float × Float × Float) :=
    [(5.0, 0.0, 1.0), (5.5, 0.0, 2.0), (-1.0, 0.0, 1.0), (1.0, 0.0, 0.0), (0.0, 0.0, 0.0),
     (1e300, 0.0, 1e-300), (nan, 0.0, 1.0), (1.8446744073709552e19, 0.0, 1.0), (3.0, 1.0, -1.0)]
  for (x, lo, width) in chosen ++ floatTriples do
    line "bucket" "bucket" "i64" [fl x, fl lo, fl width]
      (toString (LeanExe.Examples.Bucket.bucket x lo width))

/-- A book of `n` levels with descending prices from `top`, and sizes. -/
def book (n top seed : Nat) : List UInt64 × List UInt64 :=
  ((List.range n).map fun k => UInt64.ofNat (top - 3 * k - (seed + k) % 3),
    (List.range n).map fun k => 1 + below 20 (seed + 5 * k))

def books : List (List UInt64 × List UInt64) :=
  [([], []), ([100], [5]), ([105, 102, 101, 100, 98], [4, 4, 6, 7, 10]), ([100, 98], [5]),
   ([100], [5, 6]), ([100, 99], [maxU, 2])] ++
    (List.range 30).map fun i => book (i % 9) (200 + 7 * i) i

/-- An output array of up to two words, to which `stepCommand` and `runOut` append. -/
def outputs (i : Nat) : List UInt64 := (List.range (i % 3)).map fun k => UInt64.ofNat (7 + k)

def clobCases : IO Unit := do
  for (i, (ps, ss)) in (List.range books.length).zip books do
    let p := ps.toArray
    let s := ss.toArray
    let n := ps.length
    let ks : List UInt64 := [0, UInt64.ofNat (n / 2), UInt64.ofNat n, UInt64.ofNat (n + 2)]
    let prices : List UInt64 :=
      [0, 99, 100, 150, maxU] ++ (if n > 0 then [ps[0]!, ps[n - 1]!, ps[0]! + 1] else [])
    line "clob" "marketBuy" "array-u64" [arrU ps, arrU ss, u (below 60 i)]
      (words (LeanExe.Examples.Clob.marketBuy p s (below 60 i)).toList)
    for k in ks do
      line "clob" "fillLevel" "array-u64" [arrU ss, u k, u (below 8 (i + k.toNat))]
        (words (LeanExe.Examples.Clob.fillLevel s k (below 8 (i + k.toNat))).toList)
      line "clob" "fillTwice" "array-u64" [arrU ss, u k, u (below 8 (i + k.toNat)), u 1]
        (words (LeanExe.Examples.Clob.fillTwice s k (below 8 (i + k.toNat)) 1).toList)
      let fk := LeanExe.Examples.Clob.fillKeep s k (below 8 (i + k.toNat))
      line "clob" "fillKeep" "list:array-u64,array-u64" [arrU ss, u k, u (below 8 (i + k.toNat))]
        s!"{words fk.1.toList},{words fk.2.toList}"
      line "clob" "insertLevel" pairKind [arrU ps, arrU ss, u k, u 97, u 3]
        (pair (LeanExe.Examples.Clob.insertLevel p s k 97 3))
      line "clob" "setLevel" pairKind [arrU ps, arrU ss, u k, u 9]
        (pair (LeanExe.Examples.Clob.setLevel p s k 9))
      line "clob" "removeLevel" pairKind [arrU ps, arrU ss, u k]
        (pair (LeanExe.Examples.Clob.removeLevel p s k))
    for price in prices do
      line "clob" "findLevel" "i64" [arrU ps, u price] (toString (LeanExe.Examples.Clob.findLevel p price))
      line "clob" "depth" "i64" [arrU ps, arrU ss, u price]
        (toString (LeanExe.Examples.Clob.depth p s price))
      line "clob" "addBid" pairKind [arrU ps, arrU ss, u price, u 4]
        (pair (LeanExe.Examples.Clob.addBid p s price 4))
      line "clob" "cancelBid" pairKind [arrU ps, arrU ss, u price, u (below 12 (i + price.toNat))]
        (pair (LeanExe.Examples.Clob.cancelBid p s price (below 12 (i + price.toNat))))
      for kind in [0, 1, 2] do
        line "clob" "applyCommand" pairKind [arrU ps, arrU ss, u kind, u price, u 5]
          (pair (LeanExe.Examples.Clob.applyCommand p s kind price 5))
        line "clob" "stepCommand" tripleKind [arrU ps, arrU ss, arrU (outputs i), u kind, u price, u 5]
          (triple (LeanExe.Examples.Clob.stepCommand p s (outputs i).toArray kind price 5))

/-- Commands of the three kinds against prices near the book `ps`, three words each. -/
def commandList (ps : List UInt64) (count seed : Nat) : List UInt64 :=
  (List.range count).flatMap fun j =>
    let kind := below 3 (seed + 7 * j)
    let near := if ps.isEmpty then 100 else ps[(seed + j) % ps.length]!
    let price := if (seed + j) % 4 = 0 then near + 1 else near
    [kind, price, 1 + below 9 (seed + 3 * j)]

def runCases : IO Unit := do
  for (i, (ps, ss)) in (List.range books.length).zip books do
    for count in [0, 1, 4, 13] do
      let cs := commandList ps count i
      line "clob" "runCommands" pairKind [arrU ps, arrU ss, arrU cs]
        (pair (LeanExe.Examples.Clob.runCommands ps.toArray ss.toArray cs.toArray))
      line "clob" "runOut" tripleKind [arrU ps, arrU ss, arrU (outputs i), arrU cs]
        (triple (LeanExe.Examples.Clob.runOut ps.toArray ss.toArray (outputs i).toArray cs.toArray))
    -- A trailing partial command is ignored.
    let cs := commandList ps 2 i ++ [0, 5]
    line "clob" "runCommands" pairKind [arrU ps, arrU ss, arrU cs]
      (pair (LeanExe.Examples.Clob.runCommands ps.toArray ss.toArray cs.toArray))
    line "clob" "runOut" tripleKind [arrU ps, arrU ss, arrU (outputs i), arrU cs]
      (triple (LeanExe.Examples.Clob.runOut ps.toArray ss.toArray (outputs i).toArray cs.toArray))

open LeanExe.Examples.Calc in
/-- A calculator state as the host's three result words. -/
def calcWords (c : Calc) : String := s!"{c.value},{c.steps},{c.last.ctorIdx}"

open LeanExe.Examples.Calc in
/-- A calculator state as the host's three argument words. -/
def calcArgs (c : Calc) : List String := [u c.value, u c.steps, u c.last.ctorIdx.toUInt64]

open LeanExe.Examples.Calc in
def calculatorCases : IO Unit := do
  let ops := [Op.add, .sub, .mul, .div]
  let operands : List (UInt64 × UInt64) :=
    [(0, 0), (7, 0), (0, 7), (17, 5), (5, 17), (maxU, 2), (maxU, maxU), (2 ^ 32, 2 ^ 32)] ++
      (List.range 8).map fun i => (rw i, rw (i + 50) % 1000)
  for op in ops do
    line "calculator" "inverse" "i64" [u op.ctorIdx.toUInt64] (toString op.inverse.ctorIdx)
    for (a, b) in operands do
      line "calculator" "apply" "i64" [u op.ctorIdx.toUInt64, u a, u b] (toString (op.apply a b))
  for w in [0, 1, 2, 3, 4, 7, maxU] do
    line "calculator" "ofWord" "i64" [u w] (toString (Op.ofWord w).ctorIdx)
  let states : List Calc :=
    ops.flatMap fun op => [⟨0, 0, op⟩, ⟨17, 3, op⟩, ⟨maxU, maxU, op⟩, ⟨rw 3, rw 4, op⟩]
  for c in states do
    for x in [0, 1, 5, maxU, rw 9] do
      line "calculator" "undo" "list:i64,i64,i64" (calcArgs c ++ [u x]) (calcWords (c.undo x))
      for op in ops do
        line "calculator" "step" "list:i64,i64,i64" (calcArgs c ++ [u op.ctorIdx.toUInt64, u x])
          (calcWords (c.step op x))
  for count in [0, 1, 2, 5, 17] do
    for seed in [0, 1, 2] do
      let ws := (List.range (2 * count + seed % 2)).map fun k =>
        if k % 2 = 0 then UInt64.ofNat ((seed + k) % 5) else rw (seed * 31 + k) % 100
      line "calculator" "calcRun" "list:i64,i64,i64" [arrU ws] (calcWords (calcRun ws.toArray))

open LeanExe.Examples.Shape in
/-- A shape as the host's four slots: the constructor index, the circle's radius as its bit
pattern, and the rectangle's sides, with zeros in the slots of the other constructors. -/
def shapeWords : Shape → List UInt64
  | .circle r => [0, r.toBits, 0, 0]
  | .rect w h => [1, 0, w, h]
  | .point => [2, 0, 0, 0]

open LeanExe.Examples.Shape in
/-- A shape as the host's four arguments. -/
def shapeArgs : Shape → List String
  | .circle r => [u 0, fl r, u 0, u 0]
  | .rect w h => [u 1, fl 0, u w, u h]
  | .point => [u 2, fl 0, u 0, u 0]

def shapeKind : String := "list:i64,f64,i64,i64"

open LeanExe.Examples.Shape in
def shapeCases : IO Unit := do
  let dims : List UInt64 := [0, 1, 7, 2 ^ 32, maxU, rw 1, rw 2]
  let radii : List Float := [0.0, -0.0, 1.5, 1e300, inf, nan, 3.0e-310]
  let shapes : List Shape :=
    .point :: radii.map .circle ++ dims.flatMap fun w => [0, 3, maxU].map (Shape.rect w)
  for s in shapes do
    line "shapes" "area" "f64" (shapeArgs s) (toString s.area.toBits)
    line "shapes" "width" "i64" (shapeArgs s) (toString s.width)
    line "shapes" "grow" shapeKind (shapeArgs s) (words (shapeWords s.grow))
    for f in [0, 2, maxU] do
      line "shapes" "scale" shapeKind (shapeArgs s ++ [u f]) (words (shapeWords (s.scale f)))
  for k in [0, 1, 2, 3, maxU] do
    for (a, b) in [(0, 0), (5, 9), (maxU, 2), (2 ^ 53 + 1, 1)] do
      line "shapes" "ofWords" shapeKind [u k, u a, u b] (words (shapeWords (Shape.ofWords k a b)))
      line "shapes" "normalize" shapeKind [u k, u a, u b]
        (words (shapeWords (Shape.normalize k a b)))
  for count in [0, 1, 4, 13] do
    for seed in [0, 1, 2] do
      let ws := (List.range (3 * count + seed % 3)).map fun k =>
        if k % 3 = 0 then UInt64.ofNat ((seed + k) % 4) else rw (seed * 17 + k) % 1000
      line "shapes" "totalArea" "f64" [arrU ws] (toString (totalArea ws.toArray).toBits)

def listCases : IO Unit := do
  let chosen : List (List UInt64) :=
    [[], [0], [maxU], [maxU, 1], [1, 2, 3], [maxU, maxU, maxU], (List.range 200).map rw]
  let random := (List.range 30).map fun i => (List.range (i % 13)).map fun k => rw (13 * i + k)
  for xs in chosen ++ random do
    line "lists" "listSum" "i64" [chain xs] (toString (LeanExe.Examples.Lists.listSum xs))
  for n in [0, 1, 2, 3, 7, 64, 65, 300, 1000] do
    line "lists" "listRange" "chain-u64" [u n] (words (LeanExe.Examples.Lists.listRange n))
    line "lists" "sumRange" "i64" [u n] (toString (LeanExe.Examples.Lists.sumRange n))

open LeanExe.Examples.Words in
def Words.ofList : List UInt64 → Words
  | [] => .nil
  | x :: xs => .cons x (Words.ofList xs)

open LeanExe.Examples.Words in
def Words.toList : Words → List UInt64
  | .nil => []
  | .cons x w => x :: Words.toList w

open LeanExe.Examples.Words in
def wordsCases : IO Unit := do
  let lists : List (List UInt64) := [[], [0], [maxU], [7, 8, 9], (List.range 50).map rw]
  for xs in lists do
    line "words" "first" "i64" [chain xs] (toString (Words.ofList xs).first)
    for acc in [0, 5, maxU] do
      line "words" "sumAcc" "i64" [u acc, chain xs] (toString (Words.sumAcc acc (Words.ofList xs)))
  for n in [0, 1, 2, 7, 64, 300] do
    line "words" "range" "chain-u64" [u n] (words (Words.toList (Words.range n)))

open LeanExe.Examples.Trees in
/-- The host's preorder description of a tree: `.` for a leaf, and a node's key followed by
its subtrees. -/
def KeyTree.describe : KeyTree → String
  | .leaf => "."
  | .node l k r => s!"{k},{KeyTree.describe l},{KeyTree.describe r}"

open LeanExe.Examples.Trees in
/-- A tree of `n` nodes whose shape and keys follow the arbitrary words from `seed`. -/
def KeyTree.arbitrary : Nat → Nat → KeyTree
  | 0, _ => .leaf
  | n + 1, seed =>
    let left := (rw seed).toNat % (n + 1)
    .node (KeyTree.arbitrary left (2 * seed + 1)) (rw (seed + 7)) (KeyTree.arbitrary (n - left) (2 * seed + 2))
termination_by n => n
decreasing_by
  all_goals
    have := Nat.mod_lt (rw seed).toNat (Nat.succ_pos n)
    omega

open LeanExe.Examples.Trees in
/-- A chain of `n` nodes, each with a leaf on the left. -/
def KeyTree.chain : Nat → KeyTree
  | 0 => .leaf
  | n + 1 => .node .leaf (UInt64.ofNat n) (KeyTree.chain n)

open LeanExe.Examples.Trees in
def treeCases : IO Unit := do
  let trees : List KeyTree := [.leaf, .node .leaf 5 .leaf, .node (.node .leaf 1 .leaf) maxU .leaf,
    KeyTree.chain 999] ++ (List.range 20).map fun i => KeyTree.arbitrary (i * 3) i
  for t in trees do
    line "trees" "size" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.size)
    line "trees" "sum" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.sum)
    line "trees" "height" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.height)
    line "trees" "sizeSum" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.sizeSum)
    line "trees" "leftSizes" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.leftSizes)
    line "trees" "leftHeavy" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.leftHeavy)
    let kp := t.keyPair
    line "trees" "keyPair" "list:i64,i64" [s!"tree-u64:{KeyTree.describe t}"] s!"{kp.1},{kp.2}"
    for n in ([0, 1, 3, 10] : List UInt64) do
      line "trees" "sumSizes" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sumSizes n))
    for xs in ([[], [7], [1, 2, 3]] : List (List UInt64)) do
      let r := t.pushSum xs.toArray
      line "trees" "pushSum" "list:array-u64,i64" [arrU xs, s!"tree-u64:{KeyTree.describe t}"]
        s!"{words r.1.toList},{r.2}"
    for n in [0, 1, 3, 10, maxU] do
      line "trees" "dropSmall" "tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.dropSmall n))
      let r := t.sizeDrop n
      line "trees" "sizeDrop" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r.1},{KeyTree.describe r.2}"
      let r2 := t.sizeDropNext n
      line "trees" "sizeDropNext" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r2.1},{KeyTree.describe r2.2}"
      line "trees" "sizeAfterDrop" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sizeAfterDrop n))
      line "trees" "sizeDropSmall" "tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.sizeDropSmall n))
      line "trees" "sizeFirst" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sizeFirst n))
      line "trees" "droppedSize" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.droppedSize n))
      let r3 := t.dropWithSize n
      line "trees" "dropWithSize" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r3.1},{KeyTree.describe r3.2}"
  for t in trees.take 10 do
    line "treeFrame" "wide" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.wide)
  for t in trees do
    for k in [0, 7, maxU] do
      line "treeMoves" "setKey" "tree-u64" [u k, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.setKey k))
    line "treeMoves" "incr" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.incr)
    for x in [0, 1, 7, 500, maxU] do
      line "treeMoves" "insert" "tree-u64" [u x, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.insert x))
    line "treeMoves" "dropRight" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.dropRight)
    line "treeMoves" "addLeft" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.addLeft)
    let sr := t.splitRoot
    line "treeMoves" "splitRoot" "list:tree-u64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{KeyTree.describe sr.1},{KeyTree.describe sr.2}"
    let rr := t.rootAndRest
    line "treeMoves" "rootAndRest" "list:i64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{rr.1},{KeyTree.describe rr.2}"
    let ko := t.keepOld
    line "treeMoves" "keepOld" "list:tree-u64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{KeyTree.describe ko.1},{KeyTree.describe ko.2}"
    line "treeMoves" "addSelf" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.addSelf)
    line "treeMoves" "leftChild" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.leftChild)
    for (a, b) in ([(0, 1), (7, 7), (500, maxU)] : List (UInt64 × UInt64)) do
      line "treeMoves" "insertTwo" "tree-u64" [u a, u b, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.insertTwo a b))
    for a in trees.take 4 do
      line "treeMoves" "addRoot" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.addRoot t))
      line "treeMoves" "addAll" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.addAll t))
      line "treeMoves" "leftSpine" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.leftSpine t))
      let so := KeyTree.splitOr t a
      line "treeMoves" "splitOr" "list:tree-u64,tree-u64"
        [s!"tree-u64:{KeyTree.describe t}", s!"tree-u64:{KeyTree.describe a}"]
        s!"{KeyTree.describe so.1},{KeyTree.describe so.2}"
      for c in [0, 1] do
        let r := KeyTree.pickPair c a t
        line "treeMoves" "pickPair" "list:tree-u64,tree-u64"
          [u c, s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
          s!"{KeyTree.describe r.1},{KeyTree.describe r.2}"
  -- Trees whose root's key is 0, for `trim`'s other path.
  let zeroRoots : List KeyTree := [.node .leaf 0 .leaf, .node (.node .leaf 1 .leaf) 0 (.node .leaf 2 .leaf),
    .node (KeyTree.arbitrary 5 1) 0 (KeyTree.arbitrary 6 2)]
  for t in trees ++ zeroRoots do
    for c in [0, 1, maxU] do
      line "treeMoves" "keepIf" "tree-u64" [u c, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.keepIf c))
    line "treeMoves" "trim" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.trim)

/-- Chains of updates and a borrowed `push`, at positions inside and past the end of each array. -/
def updatesCases : IO Unit := do
  for xs in wordArrays do
    for i in ([0, 1, 2, 5] : List UInt64) do
      let a := rw (xs.length + i.toNat)
      line "updates" "pushTwo" "array-u64" [arrU xs, u a, u (a + 1)]
        (words (LeanExe.Examples.Updates.pushTwo xs.toArray a (a + 1)).toList)
      line "updates" "pushCopy" pairKind [arrU xs, u a]
        (pair (LeanExe.Examples.Updates.pushCopy xs.toArray a))
      for j in ([0, 1, 3, 7] : List UInt64) do
        line "updates" "setTwice" "array-u64" [arrU xs, u i, u j, u a]
          (words (LeanExe.Examples.Updates.setTwice xs.toArray i j a).toList)
        line "updates" "insertErase" "array-u64" [arrU xs, u i, u j, u a]
          (words (LeanExe.Examples.Updates.insertErase xs.toArray i j a).toList)

open LeanExe.Examples.Bools in
def boolsCases : IO Unit := do
  let b (x : Bool) : String := s!"i64:{if x then 1 else 0}"
  let r (x : Bool) : String := toString (if x then 1 else 0)
  let ws : List UInt64 := [0, 1, 2, 3, 7, maxU - 1, maxU]
  let bs := [false, true]
  for x in ws do
    line "bools" "isPositive" "i64" [u x] (r (isPositive x))
    line "bools" "mark" "list:i64,i64" [u x] s!"{r (mark x).flag},{(mark x).value}"
    for y in ws do
      line "bools" "same" "i64" [u x, u y] (r (same x y))
      line "bools" "differ" "i64" [u x, u y] (r (differ x y))
  for a in bs do
    line "bools" "negate" "i64" [b a] (r (negate a))
    for c in bs do
      line "bools" "both" "i64" [b a, b c] (r (both a c))
      line "bools" "either" "i64" [b a, b c] (r (either a c))
      line "bools" "agree" "i64" [b a, b c] (r (agree a c))
    for x in [0, 5, maxU] do
      line "bools" "flagOf" "i64" [b a, u x] (r (flagOf ⟨a, x⟩))
      for y in [0, 9, maxU] do
        line "bools" "pick" "i64" [b a, u x, u y] (toString (pick a x y))
  let fs := specialFloats ++ [1.5, -2.25, 3.0]
  for x in fs do
    for y in fs do
      line "bools" "floatSame" "i64" [fl x, fl y] (r (floatSame x y))
  for lo in [-1.0, 0.0, nan] do
    for hi in [1.0, -0.0, inf] do
      for x in fs do
        line "bools" "inRange" "i64" [fl lo, fl hi, fl x] (r (inRange lo hi x))
  for n in [0, 1, 3, 10] do
    for k in [0, 2, 9, maxU] do
      line "bools" "anyEqual" "i64" [u n, u k] (r (anyEqual n k))

open LeanExe.Examples.Grids in
def gridsCases : IO Unit := do
  let b (x : Bool) : String := toString (if x then 1 else 0)
  let phaseWord : Phase → UInt64
    | .solid => 0 | .liquid => 1 | .gas => 2
  let cellWords (c : Cell) : List UInt64 :=
    [c.index, c.state.density.toBits, c.state.mx.toBits, c.state.my.toBits, c.state.energy.toBits,
     c.pressure.toBits, c.status, if c.ok then 1 else 0, phaseWord c.phase]
  let cell (i : Nat) : Cell :=
    let f (k : Nat) : Float := if (i + k) % 5 = 0 then specialFloats[(i + k) % specialFloats.length]!
      else small (7 * i + k)
    { index := rw i, state := ⟨f 1, f 2, f 3, f 4⟩, pressure := f 5, status := below 4 i,
      ok := i % 2 = 0, phase := match i % 3 with | 0 => .solid | 1 => .liquid | _ => .gas }
  for size in [0, 1, 3, 7] do
    let grid : Array Cell := (List.range size).toArray.map cell
    let arg := arrU (grid.toList.flatMap cellWords)
    let flagsList : List Bool := (List.range size).map fun i => i % 3 == 1
    let flags : Array Bool := flagsList.toArray
    let flagArg := arrU (flagsList.map fun x => if x then 1 else 0)
    let masses : Array Mass := grid.map fun c => ⟨c.pressure⟩
    let massArg := arrU (masses.toList.map (·.value.toBits))
    line "grids" "count" "i64" [arg] (toString (count grid))
    line "grids" "flagCount" "i64" [flagArg] (toString (flagCount flags))
    let indices : List UInt64 :=
      (List.range (size + 1)).map UInt64.ofNat ++ [536870911, 536870912, 9223372036854775808, maxU]
    for i in indices do
      line "grids" "density" "f64" [arg, u i] (toString (density grid i).toBits)
      line "grids" "pressure" "f64" [arg, u i] (toString (pressure grid i).toBits)
      line "grids" "indexAt" "i64" [arg, u i] (toString (indexAt grid i))
      line "grids" "okAt" "i64" [arg, u i] (b (okAt grid i))
      line "grids" "isGas" "i64" [arg, u i] (b (isGas grid i))
      line "grids" "flagAt" "i64" [flagArg, u i] (b (flagAt flags i))
      line "grids" "massAt" "f64" [massArg, u i] (toString (massAt masses i).toBits)
      for j in [0, 2, maxU] do
        line "grids" "energySum" "f64" [arg, u i, u j] (toString (energySum grid i j).toBits)
    let stateWords (s : Conserved) : List UInt64 :=
      [s.density.toBits, s.mx.toBits, s.my.toBits, s.energy.toBits]
    let states : Array Conserved := grid.map (·.state)
    for a in [1.5, -0.0, inf, 0.0 / 0.0] do
      line "grids" "scaled" "array-u64" [arrU (states.toList.flatMap stateWords), fl a]
        (words ((scaled states a).toList.flatMap stateWords))
    line "grids" "totalDensity" "f64" [arrU (states.toList.flatMap stateWords)]
      (toString (totalDensity states).toBits)
    line "grids" "ramp" "array-u64" [u (UInt64.ofNat size)]
      (words ((ramp (UInt64.ofNat size)).toList.flatMap stateWords))
    line "grids" "flags" "array-u64" [u (UInt64.ofNat size)]
      (words ((LeanExe.Examples.Grids.flags (UInt64.ofNat size)).toList.map fun x => if x then 1 else 0))

def main : IO Unit := do
  scaleCases; gcdCases; sumArrayCases; pairSumCases; sumCountCases; axpyCases; scaledHypotCases
  binary32Cases
  piecewiseCases; sumSquaresCases; meanCases; bucketCases; clobCases; runCases
  calculatorCases; shapeCases; listCases; wordsCases; treeCases; updatesCases
  boolsCases; gridsCases
