import LeanExe.Examples.Binary32
import LeanExe.Examples.Gpt32

/-! Test cases for the WGSL kernels, computed by native Lean.  Each line is
`kernel|workgroups|initial output|inputs|expected output`, with buffers in the harness's `u64:`
notation and the expected output as 32-bit words joined by commas.  `tests/wgsl/run.sh` runs each
case with `build/tools/leanexe-webgpu-host` and compares.  Run with `lake env lean --run`. -/

open LeanExe.Examples.Binary32 LeanExe.Examples.Gpt32

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

/-- Moderate values in `[-2, 2]`, with a special value at every 37th place. -/
def moderate (i : Nat) : Float32 :=
  if i % 37 = 36 then specials[i / 37 % specials.length]!
  else (((i * 2654435761 + 7) % 2001).toFloat / 500.0 - 2.0).toFloat32

def floats (n seed : Nat) : List Float32 := (List.range n).map fun i => moderate (i + 131 * seed)

/-- A case line for kernel `name` with `n` output elements. -/
def caseLine (name : String) (n : Nat) (extra : Nat) (inputs : List String) (r : Array Float32) :
    String :=
  let groups := max ((n + 63) / 64 + extra) 1
  let initial := n.toUInt64 :: (List.replicate n 0x7fc000017fc00001)
  s!"{name}|{groups}|u64:{words initial}|{" ".intercalate inputs}|{words (arrayWords32 r.toList)}"

def arr (x : List Float32) : String := s!"u64:{words (arrayWords64 x)}"

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
  -- `exp32` over a grid of [-120, 120], special values, and arbitrary bit patterns.
  for (n, k) in [(0, 0), (1, 1), (64, 2), (65, 3), (1000, 4), (4096, 5)] do
    let x := (List.range n).map fun i =>
      if i % 7 = 0 then specials[(i + k) % specials.length]!
      else if i % 7 = 1 then arbitrary (i + 101 * k)
      else (-120.0 + 240.0 * (i.toFloat + 0.5) / (max n 1).toFloat).toFloat32
    let groups := max ((n + 63) / 64 + (if k % 2 = 0 then 0 else 1)) 1
    let initial := n.toUInt64 :: (List.replicate n 0x7fc000017fc00001)
    let r := (expArray32 x.toArray).toList
    IO.println s!"exp|{groups}|u64:{words initial}|u64:{words (arrayWords64 x)}|{words (arrayWords32 r)}"
  -- The GPT-2 kernels on small configurations.
  for seed in [0, 1, 2] do
    let d := [8, 16, 64][seed]!
    let rows := 5
    let wte := floats (rows * d) seed
    let wpe := floats (4 * d) (seed + 10)
    for (row, p) in [(0, 0), (3, 2), (rows + 1, 1)] do
      IO.println (caseLine "embed" d seed [arr wte, arr wpe, s!"u64:{row}", s!"u64:{p}", s!"u64:{d}"]
        (embed32 wte.toArray wpe.toArray row.toUInt64 p.toUInt64 d.toUInt64))
    let x := floats d (seed + 20)
    let g := floats d (seed + 21)
    let b := floats d (seed + 22)
    IO.println (caseLine "layerNorm" d seed [arr x, arr g, arr b, s!"u64:{d}",
      scalarBuffer d.toFloat.toFloat32]
      (layerNorm32 x.toArray g.toArray b.toArray d.toUInt64 d.toFloat.toFloat32))
    for (k, m) in [(d, 5), (d, 2 * d + 1), (2 * d + 3, d / 2 + 1)] do
      let xs := floats k (seed + 30)
      let w := floats (k * m) (seed + 31)
      let bs := floats m (seed + 32)
      IO.println (caseLine "linear" m seed [arr xs, arr w, arr bs, s!"u64:{k}", s!"u64:{m}"]
        (linear32 xs.toArray w.toArray bs.toArray k.toUInt64 m.toUInt64))
    let base := d * (seed + 1)
    let cache := floats base (seed + 40)
    let rowv := floats d (seed + 41)
    IO.println (caseLine "append" (base + d) seed [arr cache, arr rowv, s!"u64:{base}",
      s!"u64:{base + d}"] (append32 cache.toArray rowv.toArray base.toUInt64 (base + d).toUInt64))
    IO.println (caseLine "add" d seed [arr x, arr g] (add32 x.toArray g.toArray))
    IO.println (caseLine "gelu" (3 * d) seed [arr (floats (3 * d) (seed + 50) ++ [])]
      (geluArray32 (floats (3 * d) (seed + 50)).toArray))
    let vocab := 7
    let wv := floats (vocab * d) (seed + 60)
    IO.println (caseLine "logits" vocab seed [arr x, arr wv, s!"u64:{vocab}", s!"u64:{d}"]
      (logits32 x.toArray wv.toArray vocab.toUInt64 d.toUInt64))
  -- Attention with two heads of 64 (rows of 128) at several positions.
  for p in [0, 2, 9] do
    let d := 128
    let n := 2 * 1024
    let q := floats d (p + 70)
    let kc := floats ((p + 1) * d) (p + 71)
    let vc := floats ((p + 1) * d) (p + 72)
    let sc := scores32 q.toArray kc.toArray p.toUInt64 d.toUInt64 n.toUInt64
    IO.println (caseLine "scores" n 0 [arr q, arr kc, s!"u64:{p}", s!"u64:{d}", s!"u64:{n}"] sc)
    let mx := headMax32 sc p.toUInt64 2
    IO.println (caseLine "headMax" 2 1 [arr sc.toList, s!"u64:{p}", "u64:2"] mx)
    let sm := headSum32 sc mx p.toUInt64 2
    IO.println (caseLine "headSum" 2 0 [arr sc.toList, arr mx.toList, s!"u64:{p}", "u64:2"] sm)
    let pw := probs32 sc mx sm p.toUInt64 n.toUInt64
    IO.println (caseLine "probs" n 1 [arr sc.toList, arr mx.toList, arr sm.toList, s!"u64:{p}",
      s!"u64:{n}"] pw)
    IO.println (caseLine "mix" d 0 [arr pw.toList, arr vc, s!"u64:{p}", s!"u64:{d}"]
      (mix32 pw vc.toArray p.toUInt64 d.toUInt64))

