import Project.WGSL.PrecisionModel

/-! A word-level algorithm specification, independent of the implementation's
Row/Context structures, packed weight offsets, Wasm code and real-valued models.
All arithmetic below denotes the pure IEEE word operations. No reassociation or
multiply-add fusion is implicit. This specifies the current algorithm, v1. -/
namespace Project.TinyGpt2.FloatSpec

abbrev Vec (n : Nat) := Fin n → UInt64
abbrev Matrix (m n : Nat) := Fin m → Vec n
abbrev Tokens := Fin 4 → Fin 256
abbrev Logits := Vec 256

def vector4 (a b c d : UInt64) : Vec 4 := fun i =>
  match i.val with | 0 => a | 1 => b | 2 => c | _ => d

structure Normalization where
  scale : Vec 4
  shift : Vec 4

structure Parameters where
  token : Matrix 256 4
  position : Matrix 4 4
  query : Matrix 4 4
  key : Matrix 4 4
  value : Matrix 4 4
  attention : Matrix 4 4
  attentionBias : Vec 4
  expand : Matrix 4 8
  expandBias : Vec 8
  contract : Matrix 8 4
  contractBias : Vec 4
  head : Matrix 4 256
  headBias : Vec 256
  norm1 : Normalization
  norm2 : Normalization
  normFinal : Normalization

def add (x y : Vec n) : Vec n := fun i => Wasm.IEEE64.add (x i) (y i)
def sum4 (x : Vec 4) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add (x 0) (x 1)) (Wasm.IEEE64.add (x 2) (x 3))
def sum8 (x : Vec 8) : UInt64 :=
  Wasm.IEEE64.add (sum4 (fun i => x ⟨i.val, by omega⟩))
    (sum4 (fun i => x ⟨4+i.val, by omega⟩))
def dot4 (x y : Vec 4) : UInt64 := sum4 (fun i => Wasm.IEEE64.mul (x i) (y i))
def dot8 (x y : Vec 8) : UInt64 := sum8 (fun i => Wasm.IEEE64.mul (x i) (y i))
def apply4 (m : Matrix 4 n) (x : Vec 4) : Vec n := fun j => dot4 x (fun i => m i j)
def apply8 (m : Matrix 8 n) (x : Vec 8) : Vec n := fun j => dot8 x (fun i => m i j)

def normalize (p : Normalization) (x : Vec 4) : Vec 4 :=
  let mean := Wasm.IEEE64.div (sum4 x) 0x4010000000000000
  let centered := fun i => Wasm.IEEE64.sub (x i) mean
  let variance := Wasm.IEEE64.div (sum4 (fun i => Wasm.IEEE64.mul (centered i) (centered i)))
    0x4010000000000000
  let divisor := Wasm.IEEE64.sqrt (Wasm.IEEE64.add variance 0x3EE4F8B588E368F1)
  fun i => Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.div (centered i) divisor) (p.scale i)) (p.shift i)

/-- Coefficient words in Horner order, with separate multiply and add. -/
def expPolynomial (x : UInt64) : UInt64 :=
  ([0x3CE952C77030AD4A,0x3D2AE7F3E733B81F,0x3D6AE7F3E733B81F,
    0x3DA93974A8C07C9D,0x3DE6124613A86D09,0x3E21EED8EFF8D898,
    0x3E5AE64567F544E4,0x3E927E4FB7789F5C,0x3EC71DE3A556C734,
    0x3EFA01A01A01A01A,0x3F2A01A01A01A01A,0x3F56C16C16C16C17,
    0x3F81111111111111,0x3FA5555555555555,0x3FC5555555555555,
    0x3FE0000000000000,0x3FF0000000000000,0x3FF0000000000000] : List UInt64).foldl
      (fun acc coefficient => Wasm.IEEE64.add (Wasm.IEEE64.mul acc x) coefficient)
      0x3CA6827863B97D97

def reduceExp : Nat → UInt64 → Nat → UInt64 × Nat
  | 0, x, count => (x, count)
  | fuel+1, x, count =>
      if x ≤ 0xBFF0000000000000 then (x, count)
      else reduceExp fuel (Wasm.IEEE64.mul x 0x3FE0000000000000) (count+1)

def squareRepeated : Nat → UInt64 → UInt64
  | 0, x => x
  | n+1, x => squareRepeated n (Wasm.IEEE64.mul x x)

/-- Defined branch behavior for the negative-exponential primitive. Callers in
its advertised finite domain provide nonpositive arguments; the cutoff is -64. -/
def expNegative (x : UInt64) : UInt64 :=
  if 0xC050000000000000 < x then 0
  else let reduced := reduceExp 6 x 0
       squareRepeated reduced.2 (expPolynomial reduced.1)

/-- The model's signed-word maximum, including its signed-zero choice. -/
def maximum (a b : UInt64) : UInt64 :=
  if a < 0x8000000000000000 then
    if b < 0x8000000000000000 then (if a ≤ b then b else a) else a
  else if b < 0x8000000000000000 then b else (if a ≤ b then a else b)

def softmax (last : Fin 4) (scores : Vec 4) : Vec 4 :=
  let active := fun i : Fin 4 => if i.val ≤ last.val then scores i else scores 0
  let m := maximum (maximum (active 0) (active 1)) (maximum (active 2) (active 3))
  let weights := fun i : Fin 4 => if i.val ≤ last.val then
    expNegative (Wasm.IEEE64.sub (scores i) m) else 0
  let total := sum4 weights
  fun i => if i.val ≤ last.val then Wasm.IEEE64.div (weights i) total else 0

def gelu (x : UInt64) : UInt64 :=
  let magnitude := x &&& 0x7FFFFFFFFFFFFFFF
  if magnitude ≤ 0x4020000000000000 then
    let square := Wasm.IEEE64.mul magnitude magnitude
    let factor := Wasm.IEEE64.add (Wasm.IEEE64.mul square 0x3FA6E4E26D4801F7) 0x3FF0000000000000
    let argument := Wasm.IEEE64.mul (Wasm.IEEE64.mul factor magnitude) 0x3FF9884533D43651
    let e := expNegative ((argument &&& 0x7FFFFFFFFFFFFFFF) ||| 0x8000000000000000)
    let divisor := Wasm.IEEE64.add 0x3FF0000000000000 e
    if x < 0x8000000000000000 then Wasm.IEEE64.div magnitude divisor
    else Wasm.IEEE64.div (Wasm.IEEE64.mul (magnitude ||| 0x8000000000000000) e) divisor
  else if x < 0x8000000000000000 then x else 0

def embedding (p : Parameters) (tokens : Tokens) : Matrix 4 4 :=
  fun position => add (p.token (tokens position)) (p.position position)

def attended (last : Fin 4) (query : Vec 4) (keys values : Matrix 4 4) : Vec 4 :=
  let probabilities := fun head : Fin 2 => softmax last (fun position =>
    Wasm.IEEE64.div
      (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (query ⟨2*head.val, by omega⟩) (keys position ⟨2*head.val, by omega⟩))
        (Wasm.IEEE64.mul (query ⟨2*head.val+1, by omega⟩) (keys position ⟨2*head.val+1, by omega⟩)))
      0x3FF6A09E667F3BCD)
  fun j => dot4 (probabilities ⟨j.val/2, by omega⟩) (fun position => values position j)

def hidden (p : Parameters) (tokens : Tokens) (last : Fin 4) : Vec 4 :=
  let embedded := embedding p tokens
  let normalized := fun position => normalize p.norm1 (embedded position)
  let query := apply4 p.query (normalized last)
  let keys := fun position => apply4 p.key (normalized position)
  let values := fun position => apply4 p.value (normalized position)
  let attention := add (apply4 p.attention (attended last query keys values)) p.attentionBias
  let residual1 := add (embedded last) attention
  let expanded := add (apply4 p.expand (normalize p.norm2 residual1)) p.expandBias
  let activated := fun i => gelu (expanded i)
  let residual2 := add residual1 (add (apply8 p.contract activated) p.contractBias)
  normalize p.normFinal residual2

/-- Four sequential additions beginning at positive zero; each product is
rounded separately. This deliberately differs from the balanced binary64 dots. -/
def dot32 (x y : Fin 4 → UInt32) : UInt32 :=
  (List.finRange 4).foldl (fun acc i => Wasm.IEEE32.add acc (Wasm.IEEE32.mul (x i) (y i))) 0

def headWord (p : Parameters) (hidden : Vec 4) (j : Fin 256) : UInt32 :=
  dot32 (fun i => Project.WGSL.Precision.demote (hidden i))
    (fun i => Project.WGSL.Precision.demote (p.head i j))

def finish (word : UInt32) (bias : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Project.WGSL.Precision.promote word) bias

def logits (p : Parameters) (tokens : Tokens) (last : Fin 4) : Logits :=
  let h := hidden p tokens last
  fun j => finish (headWord p h j) (p.headBias j)

end Project.TinyGpt2.FloatSpec
