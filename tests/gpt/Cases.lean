import LeanExe.Examples.Gpt

/-! Test cases for `gpt.wasm`, computed by native Lean.  Each line is
`export|result type|host arguments|expected result`, with arrays and floats given as
bit patterns; `tests/gpt/run.sh` passes the arguments to the Wasmtime host and compares
its output with the expected result.  Run with `lake env lean --run`. -/

open LeanExe.Examples.Gpt

def bitsOf (xs : List Float) : String := ",".intercalate (xs.map fun x => toString x.toBits)
def arr (xs : List Float) : String := s!"array-u64:{bitsOf xs}"
def arrA (xs : Array Float) : String := arr xs.toList
def arrU (xs : List UInt64) : String := s!"array-u64:{",".intercalate (xs.map toString)}"
def u (n : Nat) : String := s!"i64:{n}"
def fl (x : Float) : String := s!"f64:{x.toBits}"

def emit (name : String) (args : List String) (out : Array Float) : IO Unit :=
  IO.println s!"{name}|array-u64|{" ".intercalate args}|{bitsOf out.toList}"

def emitF (name : String) (args : List String) (out : Float) : IO Unit :=
  IO.println s!"{name}|f64|{" ".intercalate args}|{out.toBits}"

def inf : Float := 1.0 / 0.0
def nan : Float := 0.0 / 0.0

/-- Arbitrary bit patterns. -/
def rnd (i : Nat) : Float := Float.ofBits (UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64))

/-- Values from -10 to 10 in steps of 0.01. -/
def small (i : Nat) : Float := (UInt64.ofNat ((i * 2654435761) % 2001)).toFloat / 100.0 - 10.0

/-- Values from -1 to 1 in steps of 0.001. -/
def unit (i : Nat) : Float := (UInt64.ofNat ((i * 2654435761) % 2001)).toFloat / 1000.0 - 1.0

def smalls (n seed : Nat) : List Float := (List.range n).map fun j => small (seed + j)
def units (n seed : Nat) : List Float := (List.range n).map fun j => unit (seed + j)

def dotCases : IO Unit := do
  let chosen : List (List Float × List Float) :=
    [([], []), ([], [1.0]), ([1.0], []), ([1.0, 2.0, 3.0], [4.0, 5.0, 6.0]), ([0.1, 0.2], [0.3, 0.4]),
     ([-0.0], [0.0]), ([-0.0], [-0.0]), ([0.0], [-1.0]), ([inf], [0.0]), ([inf], [2.0]),
     ([inf, -inf], [1.0, 1.0]), ([nan], [1.0]), ([1e200, 1e200], [1e200, -1e200]), ([5e-324], [0.5]),
     ([5e-324, 5e-324], [1.0, 1.0]), ([1.0, 1e-16, 1e-16], [1.0, 1.0, 1.0]),
     ([1e-16, 1e-16, 1.0], [1.0, 1.0, 1.0]), ([1.0, 2.0, 3.0], [4.0]), ([1.0], [4.0, 5.0, 6.0]),
     ([1.7976931348623157e308], [2.0])]
  let random := (List.range 20).map fun i =>
    ((List.range (i % 7)).map fun k => rnd (11 * i + k), (List.range ((i + 3) % 7)).map fun k => rnd (13 * i + k))
  let moderate := (List.range 20).map fun i => (smalls (i % 9) (7 * i), smalls (i % 9) (5 * i + 3))
  for (xs, ys) in chosen ++ random ++ moderate do
    emitF "dot" [arr xs, arr ys] (dot xs.toArray ys.toArray)

def matVecCases : IO Unit := do
  let chosen : List (List Float × List Float × Nat × Nat) :=
    [([], [], 0, 0), ([], [], 2, 3), ([1.0, 2.0, 3.0, 4.0], [1.0, 1.0], 2, 2),
     ([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], [1.0, 0.5, 0.25], 2, 3), ([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], [1.0, 0.5], 3, 2),
     ([1.0, 2.0, 3.0], [1.0, 1.0], 2, 2), ([1.0, 2.0, 3.0, 4.0], [1.0], 2, 2), ([inf, 1.0], [0.0, 1.0], 1, 2),
     ([nan, 1.0], [1.0, 1.0], 1, 2), ([-0.0, -0.0], [1.0, 1.0], 1, 2), ([1e200, 1e200], [1e200, -1e200], 1, 2),
     ([5e-324, 5e-324], [0.5, 0.5], 1, 2), ([1.0, 2.0], [3.0, 4.0], 0, 2), ([1.0, 2.0], [3.0, 4.0], 2, 0),
     ([0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9], [0.9, 0.8, 0.7], 3, 3)]
  let random := (List.range 30).map fun i =>
    let rows := i % 5
    let cols := (i * 7 + 1) % 6
    (smalls (rows * cols + i % 3) (13 * i), smalls (cols + i % 2) (5 * i + 1), rows, cols)
  for (m, v, r, c) in chosen ++ random do
    emit "matVec" [arr m, arr v, u r, u c] (matVec m.toArray v.toArray r.toUInt64 c.toUInt64)

def layerNormCases : IO Unit := do
  let chosen : List (List Float × List Float × List Float × Float) :=
    [([], [], [], 1e-5), ([1.0], [1.0], [0.0], 1e-5), ([1.0, 2.0, 3.0], [1.0, 1.0, 1.0], [0.0, 0.0, 0.0], 1e-5),
     ([1.0, 2.0, 3.0], [2.0, 0.5, -1.0], [0.1, 0.2, 0.3], 0.0),
     ([1.0, 1.0, 1.0], [1.0, 1.0, 1.0], [0.0, 0.0, 0.0], 0.0), ([1.0, 2.0, 3.0, 4.0], [1.0], [], 1e-5),
     ([1.0, 2.0], [1.0, 1.0, 1.0], [5.0, 5.0, 5.0], 1e-5), ([inf, 1.0], [1.0, 1.0], [0.0, 0.0], 1e-5),
     ([nan, 1.0], [1.0, 1.0], [0.0, 0.0], 1e-5), ([-0.0, 0.0], [1.0, 1.0], [-0.0, 0.0], 0.0),
     ([1e300, -1e300], [1.0, 1.0], [0.0, 0.0], 1e-5), ([5e-324, 0.0], [1.0, 1.0], [0.0, 0.0], 0.0),
     ([0.1, 0.2, 0.3], [1.0, 1.0, 1.0], [0.0, 0.0, 0.0], -1.0)]
  let random := (List.range 30).map fun i =>
    let n := i % 9
    (smalls n (13 * i), smalls (n + i % 3 - 1) (5 * i + 1), smalls n (7 * i + 2), (small i).abs / 1000.0)
  for (xs, g, b, eps) in chosen ++ random do
    emit "layerNorm" [arr xs, arr g, arr b, fl eps] (layerNorm xs.toArray g.toArray b.toArray eps)

def expCases : IO Unit := do
  let special : List Float := [0.0, -0.0, 1.0, -1.0, 0.5, 709.78, 709.7827128933840, 709.79, 709.8,
    709.80000000000001, 710.0, -708.39, -708.4, -744.44, -745.13, -745.14, -745.2, -745.20000000000001,
    -746.0, 1e-300, -1e-300, 5e-324, inf, -inf, nan, 1e308, -1e308, 0.34657359027997264,
    -0.34657359027997264, 0.6931471805599453, 88.72283905206835, -87.33654475055310]
  let grid := (List.range 400).map fun i => -745.0 + 1455.0 * (i.toFloat / 400.0)
  for x in special ++ grid ++ (List.range 200).map rnd do
    emitF "exp" [fl x] (exp x)

def softmaxCases : IO Unit := do
  let chosen : List (List Float) :=
    [[], [0.0], [1.0, 2.0, 3.0], [1.0, 1.0, 1.0, 1.0], [-1000.0, 0.0, 1000.0], [inf, 1.0], [-inf, 1.0],
     [nan, 1.0], [-0.0, 0.0], [700.0, 710.0], [-745.0, 0.0], [1e-300, -1e-300], [3.0, 2.0, 1.0, 0.5, 0.25]]
  for xs in chosen ++ (List.range 40).map fun i => smalls (i % 12) (17 * i) do
    emit "softmax" [arr xs] (softmax xs.toArray)

def matVec2Cases : IO Unit := do
  for i in List.range 30 do
    let hidden := i % 5
    let d := (i * 3 + 1) % 5
    let w1 := smalls (hidden * d + i % 2) (13 * i)
    let w2 := smalls (d * hidden) (7 * i + 3)
    let x := smalls (d + i % 3) (5 * i + 1)
    emit "matVec2" [arr w1, arr w2, arr x, u hidden, u d]
      (matVec2 w1.toArray w2.toArray x.toArray hidden.toUInt64 d.toUInt64)

def matMulCases : IO Unit := do
  for i in List.range 40 do
    let n := i % 4
    let k := (i * 3 + 1) % 5
    let m := (i * 7 + 2) % 4
    let a := smalls (n * k + i % 2) (13 * i)
    let b := smalls (k * m - i % 2) (7 * i + 3)
    emit "matMul" [arr a, arr b, u n, u k, u m] (matMul a.toArray b.toArray n.toUInt64 k.toUInt64 m.toUInt64)

/-- Values from -2.5 to 2.5, where `gelu` and `tanh` bend. -/
def mid (i : Nat) : Float := (UInt64.ofNat ((i * 2654435761) % 2001)).toFloat / 400.0 - 2.5

def geluCases : IO Unit := do
  let special : List Float :=
    [0.0, -0.0, 1.0, -1.0, 3.0, -3.0, 10.0, -10.0, 1e-8, -1e-8, 100.0, -100.0, inf, -inf, nan]
  for x in special ++ (List.range 60).map mid do
    emitF "gelu" [fl x] (gelu x)
  for x in special ++ (List.range 30).map mid do
    emitF "tanh" [fl x] (tanh x)
  for i in List.range 25 do
    let t := i % 3 + 1
    let d := (i * 5 + 1) % 4 + 1
    let f := (i * 7 + 2) % 5 + 1
    let x := (List.range (t * d)).map fun j => mid (13 * i + j)
    let y := (List.range (d * f)).map fun j => mid (7 * i + j + 3)
    emit "add" [arr x, arr y] (add x.toArray y.toArray)

def layerNormRowsCases : IO Unit := do
  for i in List.range 30 do
    let t := i % 4
    let d := (i * 3 + 1) % 5
    let l := i % 3
    let x := smalls (t * d + i % 2) (13 * i)
    let g := smalls ((l + 1) * d + i % 3) (7 * i + 3)
    let b := smalls ((l + i % 2) * d) (11 * i + 5)
    let eps : Float := if i % 5 = 0 then 0.0 else 1e-5
    let means := rowMeans x.toArray t.toUInt64 d.toUInt64
    let inv := rowInvStd x.toArray means t.toUInt64 d.toUInt64 eps
    emit "rowMeans" [arr x, u t, u d] means
    emit "rowInvStd" [arr x, arrA means, u t, u d, fl eps] inv
    emit "normalizeRows" [arr x, arrA means, arrA inv, arr g, arr b, u l, u t, u d]
      (normalizeRows x.toArray means inv g.toArray b.toArray l.toUInt64 t.toUInt64 d.toUInt64)
    emit "layerNormRows" [arr x, arr g, arr b, u l, u t, u d, fl eps]
      (layerNormRows x.toArray g.toArray b.toArray l.toUInt64 t.toUInt64 d.toUInt64 eps)

/-- Attention kernels: scores with one head, and softmax rows of one to three heads with
special values in `x`. -/
def softmaxRowsCases : IO Unit := do
  for i in List.range 40 do
    let t := i % 4
    let d := (i * 3 + 1) % 5
    let nh := 1 + i % 3
    let extra := i % 2
    let special : List Float := [nan, inf, -inf, -0.0, 1e308]
    let x := (smalls (t * nh * t + extra) (13 * i)).mapIdx fun j v =>
      if i % 10 = 9 ∧ j = 1 then special[(i / 10) % 5]! else v
    let q := smalls (t * d) (17 * i + 1)
    let k := smalls (t * d + extra) (19 * i + 2)
    let scale : Float := if i % 5 = 0 then 1.0 else 1.0 / d.toFloat.sqrt
    let s := maskedScores q.toArray k.toArray t.toUInt64 1 d.toUInt64 scale
    emit "maskedScores" [arr q, arr k, u t, u 1, u d, fl scale] s
    let mx := rowMax x.toArray t.toUInt64 nh.toUInt64
    let sums := rowSumExp x.toArray mx t.toUInt64 nh.toUInt64
    emit "rowMax" [arr x, u t, u nh] mx
    emit "rowSumExp" [arr x, arrA mx, u t, u nh] sums
    emit "softmaxApply" [arr x, arrA mx, arrA sums, u (t * nh), u t]
      (softmaxApply x.toArray mx sums (t * nh).toUInt64 t.toUInt64)
    emit "softmaxRows" [arrA s, u t, u 1] (softmaxRows s t.toUInt64 1)
    emit "softmaxRows" [arr x, u t, u nh] (softmaxRows x.toArray t.toUInt64 nh.toUInt64)
    let p := softmaxRows s t.toUInt64 1
    let v := smalls (t * d + extra) (41 * i + 7)
    emit "causalMatMul" [arrA p, arr v, u t, u 1, u d] (causalMatMul p v.toArray t.toUInt64 1 d.toUInt64)

/-- Attention kernels with two or three heads. -/
def headCases : IO Unit := do
  for i in List.range 40 do
    let t := i % 4
    let nh := 2 + i % 2
    let dh := (i / 4) % 3
    let d := nh * dh
    let extra := i % 2
    let q := units (t * d) (17 * i + 1)
    let k := units (t * d + extra) (19 * i + 2)
    let scale : Float := 1.0 / dh.toFloat.sqrt
    let s := maskedScores q.toArray k.toArray t.toUInt64 nh.toUInt64 dh.toUInt64 scale
    emit "maskedScores" [arr q, arr k, u t, u nh, u dh, fl scale] s
    let p := softmaxRows s t.toUInt64 nh.toUInt64
    let v := units (t * d + extra) (41 * i + 7)
    emit "causalMatMul" [arrA p, arr v, u t, u nh, u dh]
      (causalMatMul p v.toArray t.toUInt64 nh.toUInt64 dh.toUInt64)

def embedCases : IO Unit := do
  for i in List.range 40 do
    let t := i % 4
    let d := (i * 3 + 1) % 5
    let vocab := (i / 4) % 5
    let extra := i % 2
    let tokens : List UInt64 := (List.range (t + extra)).map fun j =>
      if i % 10 = 9 ∧ j = 0 then 18446744073709551615 else UInt64.ofNat ((i * 7 + j * 3) % (vocab + 2))
    let wte := units (vocab * d + extra) (3 * i)
    let wpe := units (t * d) (5 * i + 1)
    let q := units (t * d + extra) (23 * i + 7)
    let k := units (vocab * d) (29 * i + 8)
    emit "embed" [arrU tokens, arr wte, arr wpe, u t, u d]
      (embed tokens.toArray wte.toArray wpe.toArray t.toUInt64 d.toUInt64)
    emit "matMulT" [arr q, arr k, u t, u d, u vocab]
      (matMulT q.toArray k.toArray t.toUInt64 d.toUInt64 vocab.toUInt64)

/-- The functions with linear layers: `linear`, `mlp`, `attention`, `block`, and
`forward`, with one to three heads, and weights for one or two layers of which `linear`,
`mlp`, `attention`, and `block` use layer `l`. -/
def linearCases : IO Unit := do
  let one := [1.0]
  let zero := [0.0]
  for x in [[1e150], [1e150, 1e200], [1.0, inf], [1.0, 2.0]] do
    let t := x.length
    emit "attention" [arr x, arr one, arr zero, arr one, arr zero, arr one, arr zero, arr one, arr zero,
      u 0, u t, u 1, u 1]
      (attention x.toArray #[1.0] #[0.0] #[1.0] #[0.0] #[1.0] #[0.0] #[1.0] #[0.0] 0 t.toUInt64 1 1)
  for i in List.range 40 do
    let t := i % 4
    let nh := 1 + i % 3
    let dh := (i / 4) % 3
    let d := nh * dh
    let f := (i * 7 + 2) % 6
    let vocab := (i / 2) % 5
    let extra := i % 2
    let eps : Float := if i % 5 = 0 then 0.0 else 1e-5
    let l := i % 2
    let L := l + 1
    let n := i % 4
    let k := (i * 3 + 1) % 5
    let m := (i / 4) % 5
    let lx := units (n * k + extra) (3 * i)
    let lw := units (L * k * m + 1 - extra) (5 * i + 1)
    let lb := units (L * m + extra) (7 * i + 2)
    emit "linear" [arr lx, arr lw, arr lb, u l, u n, u k, u m]
      (linear lx.toArray lw.toArray lb.toArray l.toUInt64 n.toUInt64 k.toUInt64 m.toUInt64)
    let x := units (t * d + extra) (13 * i)
    let wq := units (L * d * d) (17 * i + 1)
    let bq := units (L * d) (19 * i + 2)
    let wk := units (L * d * d + extra) (23 * i + 3)
    let bk := units (L * d) (29 * i + 4)
    let wv := units (L * d * d) (31 * i + 5)
    let bv := units (L * d + extra) (37 * i + 6)
    let wo := units (L * d * d + 1 - extra) (41 * i + 7)
    let bo := units (L * d) (43 * i + 8)
    let g := units (L * d) (47 * i + 9)
    let b := units (L * d) (53 * i + 10)
    let wfc := units (L * d * f) (59 * i + 11)
    let bfc := units (L * f) (61 * i + 12)
    let wproj := units (L * f * d) (67 * i + 13)
    let bproj := units (L * d) (71 * i + 14)
    let A (xs : List Float) : Array Float := xs.toArray
    emit "mlp" [arr x, arr wfc, arr bfc, arr wproj, arr bproj, u l, u t, u d, u f]
      (mlp (A x) (A wfc) (A bfc) (A wproj) (A bproj) l.toUInt64 t.toUInt64 d.toUInt64 f.toUInt64)
    emit "attention"
      [arr x, arr wq, arr bq, arr wk, arr bk, arr wv, arr bv, arr wo, arr bo, u l, u t, u nh, u dh]
      (attention (A x) (A wq) (A bq) (A wk) (A bk) (A wv) (A bv) (A wo) (A bo) l.toUInt64 t.toUInt64
        nh.toUInt64 dh.toUInt64)
    let layerA := [g, b, wq, bq, wk, bk, wv, bv, wo, bo, g, b, wfc, bfc, wproj, bproj]
    emit "block" ([arr x] ++ layerA.map arr ++ [u l, u t, u nh, u dh, u f, fl eps])
      (block (A x) (A g) (A b) (A wq) (A bq) (A wk) (A bk) (A wv) (A bv) (A wo) (A bo) (A g) (A b)
        (A wfc) (A bfc) (A wproj) (A bproj) l.toUInt64 t.toUInt64 nh.toUInt64 dh.toUInt64 f.toUInt64
        eps)
    let tokens : List UInt64 := (List.range (t + extra)).map fun j =>
      if i % 10 = 9 ∧ j = 0 then 18446744073709551615 else UInt64.ofNat ((i * 7 + j * 3) % (vocab + 2))
    let wte := units (vocab * d + extra) (73 * i + 15)
    let wpe := units (t * d) (79 * i + 16)
    let layers := (i / 2 + 1) % 4
    let sizes := [d, d, d * d, d, d * d, d, d * d, d, d * d, d, d, d, d * f, f, f * d, d]
    let ws := sizes.zipIdx.map fun (n, j) => units (layers * n) (83 * i + 31 * j)
    let W (j : Nat) : Array Float := (ws[j]!).toArray
    emit "forward" ([arrU tokens, arr wte, arr wpe] ++ ws.map arr ++
        [arr g, arr b, u layers, u t, u nh, u dh, u f, u vocab, fl eps])
      (forward tokens.toArray (A wte) (A wpe) (W 0) (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) (W 7)
        (W 8) (W 9) (W 10) (W 11) (W 12) (W 13) (W 14) (W 15) (A g) (A b) layers.toUInt64
        t.toUInt64 nh.toUInt64 dh.toUInt64 f.toUInt64 vocab.toUInt64 eps)

/-- `block` on weights stacked over one to three layers; `l` equal to the number of
layers reads past the arrays. -/
def stackedBlockCases : IO Unit := do
  for i in List.range 30 do
    let layers := 1 + i % 3
    let l := i % (layers + 1)
    let t := i % 4
    let nh := 1 + i % 2
    let dh := (i / 4) % 3
    let d := nh * dh
    let f := (i * 7 + 2) % 5
    let eps : Float := if i % 5 = 0 then 0.0 else 1e-5
    let x := units (t * d + i % 2) (13 * i)
    let sizes := [d, d, d * d, d, d * d, d, d * d, d, d * d, d, d, d, d * f, f, f * d, d]
    let ws := sizes.zipIdx.map fun (n, j) => units (layers * n) (97 * i + 31 * j)
    let A (j : Nat) : Array Float := (ws[j]!).toArray
    emit "block" ([arr x] ++ ws.map arr ++ [u l, u t, u nh, u dh, u f, fl eps])
      (block x.toArray (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) (A 6) (A 7) (A 8) (A 9) (A 10) (A 11)
        (A 12) (A 13) (A 14) (A 15) l.toUInt64 t.toUInt64 nh.toUInt64 dh.toUInt64 f.toUInt64 eps)

def main : IO Unit := do
  dotCases
  matVecCases
  layerNormCases
  expCases
  softmaxCases
  matVec2Cases
  matMulCases
  geluCases
  layerNormRowsCases
  softmaxRowsCases
  headCases
  embedCases
  linearCases
  stackedBlockCases
