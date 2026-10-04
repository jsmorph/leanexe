import Project.Gpt32.Driver

/-!
`lean --run tests/gpt32/Native.lean HOST DIR` runs small random models through
`Project.Gpt32.generate`, the driver of `Project/Gpt32/Generate.lean`, on the device the Vulkan
loader chooses, and compares every step's scores with native Lean's `step32` bit for bit.  The
models keep heads of 64 elements and the scores' stride of 1,024 positions, which the kernels
fix, and vary the heads, the MLP width, the layers, and the chunks of the vocabulary.  `DIR`
receives the weight files and the kernels.
-/

open Project.Gpt32 LeanExe.Examples.Gpt32

/-- A value in `[center - scale, center + scale)` from a hash of `seed` and `i`. -/
def randomValue (seed : UInt64) (i : Nat) (center scale : Float) : Float32 :=
  let a := (seed + UInt64.ofNat i * 0x9E3779B97F4A7C15) * 6364136223846793005 + 1442695040888963407
  let b := (a ^^^ (a >>> 29)) * 0xBF58476D1CE4E5B9
  let u := (b >>> 11).toFloat / 9007199254740992.0
  (center + scale * (2.0 * u - 1.0)).toFloat32

def randomArray (seed : UInt64) (n : Nat) (center scale : Float) : Array Float32 :=
  Array.ofFn (n := n) fun i => randomValue seed i.val center scale

def pushWord (b : ByteArray) (w : UInt32) : ByteArray :=
  (((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- The bytes of a Wasm array of binary32 values, as `tests/gpt32/generate.py` writes them. -/
def arrayBytes (xs : Array Float32) : ByteArray :=
  xs.foldl (fun b x => pushWord (pushWord b x.toBits) 0)
    (pushWord (pushWord ByteArray.empty (UInt32.ofNat xs.size)) 0)

def randomLayer (seed : UInt64) (d f : Nat) : Layer32 :=
  let r (k : UInt64) (n : Nat) (center scale : Float) := randomArray (seed * 32 + k) n center scale
  { g1 := r 0 d 1.0 0.2, b1 := r 1 d 0.0 0.1, wq := r 2 (d * d) 0.0 0.15,
    bq := r 3 d 0.0 0.05, wk := r 4 (d * d) 0.0 0.15, bk := r 5 d 0.0 0.05,
    wv := r 6 (d * d) 0.0 0.15, bv := r 7 d 0.0 0.05, wo := r 8 (d * d) 0.0 0.15,
    bo := r 9 d 0.0 0.05, g2 := r 10 d 1.0 0.2, b2 := r 11 d 0.0 0.1,
    wfc := r 12 (d * f) 0.0 0.15, bfc := r 13 f 0.0 0.05, wproj := r 14 (f * d) 0.0 0.1,
    bproj := r 15 d 0.0 0.05 }

def randomWeights (s : Shape32) (vocab positions : Nat) : Weights32 :=
  let d := (64 * s.nh).toNat
  let wte := randomArray 1 (vocab * d) 0.0 0.5
  { wte := (List.range s.rows.length).map fun c =>
      wte.extract (c * s.chunk.toNat * d) ((c * s.chunk.toNat + s.rows[c]!.toNat) * d),
    wpe := randomArray 2 (positions * d) 0.0 0.2,
    layers := (List.range s.layers).map fun l => randomLayer (UInt64.ofNat (l + 3)) d s.f.toNat,
    gf := randomArray 4 d 1.0 0.2, bf := randomArray 5 d 0.0 0.1 }

def writeWeights (dir : String) (W : Weights32) : IO Unit := do
  IO.FS.createDirAll dir
  for (wte, c) in W.wte.zipIdx do
    IO.FS.writeBinFile (weightPath dir s!"wte{c}") (arrayBytes wte)
  IO.FS.writeBinFile (weightPath dir "wpe") (arrayBytes W.wpe)
  IO.FS.writeBinFile (weightPath dir "gf") (arrayBytes W.gf)
  IO.FS.writeBinFile (weightPath dir "bf") (arrayBytes W.bf)
  for (w, l) in W.layers.zipIdx do
    for f in Field.all do
      IO.FS.writeBinFile (weightPath dir s!"l{l}_{f.name}") (arrayBytes (f.get w))

/-- The first element where two lists of score chunks differ in their bits. -/
def firstDifference (a b : List (Array Float32)) : Option String :=
  if a.length != b.length then some s!"{a.length} chunks against {b.length}"
  else
    (a.zip b).zipIdx.findSome? fun ((x, y), c) =>
      if x.size != y.size then some s!"chunk {c}: {x.size} scores against {y.size}"
      else (List.range x.size).findSome? fun i =>
        if x[i]!.toBits != y[i]!.toBits then
          some s!"chunk {c}, score {i}: {x[i]!} ({x[i]!.toBits}) against {y[i]!} ({y[i]!.toBits})"
        else none

/-- Runs one model on the device and natively, and returns the number of steps compared. -/
def check (host dir : String) (nh f chunk vocab layers : Nat) (prompt : List Nat) (n : Nat) :
    IO Nat := do
  let s := shapeOf nh f chunk vocab layers
  let W := randomWeights s vocab (prompt.length + n)
  let tag := s!"nh{nh}-f{f}-c{chunk}-v{vocab}-l{layers}"
  writeWeights s!"{dir}/{tag}" W
  let seen ← IO.mkRef (#[] : Array (List (Array Float32)))
  let ids ← generate host s!"{dir}/{tag}" s!"{dir}/wgsl" s!"{dir}/read.bin" s prompt n
    fun zs => seen.modify (·.push zs)
  let device ← seen.get
  let mut caches := List.replicate s.layers ((#[] : Array Float32), (#[] : Array Float32))
  let mut k := 0
  for p in [0:ids.length - 1] do
    let (cs, zs) := step32 s W (UInt64.ofNat ids[p]!) (UInt64.ofNat p) caches
    caches := cs
    if p + 1 ≥ prompt.length then
      match firstDifference device[k]! zs with
      | some d => throw <| IO.userError s!"{tag}, position {p}: {d}"
      | none => pure ()
      if greedy32 zs != ids[p + 1]! then
        throw <| IO.userError s!"{tag}, position {p}: native token {greedy32 zs}, device {ids[p + 1]!}"
      k := k + 1
  IO.println s!"{tag}: {k} steps, scores equal bit for bit, tokens {ids}"
  return k

def main : List String → IO Unit
  | [host, dir] => do
    let a ← check host dir 1 96 64 200 2 [5, 17, 3] 4
    let b ← check host dir 2 256 200 500 3 [7, 400, 12, 99] 5
    let c ← check host dir 3 192 128 300 1 [250] 6
    IO.println s!"native: {a + b + c} steps compared, 0 failed"
  | _ => throw <| IO.userError "usage: Native.lean HOST DIR"
