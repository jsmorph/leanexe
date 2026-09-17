import Project.SequenceSoftmax.Model
import Project.GeluWide.Model

/-! Executable GPT-2 non-matrix stages. All arguments and results use binary64
words. Matrix products are supplied by the generated binary32 WGSL GEMMs.
This demo module does not yet carry an artifact correctness theorem. -/
namespace Project.Gpt2

def add (a b : UInt64) := Wasm.IEEE64.add a b
def sub (a b : UInt64) := Wasm.IEEE64.sub a b
def mul (a b : UInt64) := Wasm.IEEE64.mul a b
def div (a b : UInt64) := Wasm.IEEE64.div a b

def greater (a b : UInt64) : Bool := a != b && Softmax.maximum a b == a

def embedding (x p : Array UInt64) : Array UInt64 := Id.run do
  let mut out := #[]
  for i in [:768] do out := out.push (add x[i]! p[i]!)
  return out

def norm (x p : Array UInt64) : Array UInt64 := Id.run do
  let mut sum := 0
  for i in [:768] do sum := add sum x[i]!
  let mean := div sum 0x4088000000000000 -- 768
  let mut variance := 0
  for i in [:768] do
    let d := sub x[i]! mean
    variance := add variance (mul d d)
  let scale := Wasm.IEEE64.sqrt (add (div variance 0x4088000000000000) 0x3EE4F8B588E368F1)
  let mut out := #[]
  for i in [:768] do out := out.push (add (mul (div (sub x[i]! mean) scale) p[i]!) p[768+i]!)
  return out

-- Cache layout: 128 rows of K, followed by 128 rows of V. Only prior rows are
-- read. Return this position's K, V, then the attended vector (3 * 768 words).
def attention (x cache bias : Array UInt64) (position : Nat) : Array UInt64 := Id.run do
  let mut qkv := #[]
  for i in [:2304] do qkv := qkv.push (add x[i]! bias[i]!)
  let mut out := #[]
  for i in [768:2304] do out := out.push qkv[i]!
  for head in [:12] do
    let mut scores := #[]
    for t in [:position+1] do
      let mut score := 0
      for j in [:64] do
        let k := if t == position then qkv[768+head*64+j]! else cache[t*768+head*64+j]!
        score := add score (mul qkv[head*64+j]! k)
      scores := scores.push (mul score 0x3FC0000000000000) -- 1/sqrt(64)
    let probabilities := SequenceSoftmax.compute scores
    for j in [:64] do
      let mut value := 0
      for t in [:position+1] do
        let v := if t == position then qkv[1536+head*64+j]! else cache[128*768+t*768+head*64+j]!
        value := add value (mul probabilities[t]! v)
      out := out.push value
  return out

def residual (x y bias : Array UInt64) : Array UInt64 := Id.run do
  let mut out := #[]
  for i in [:768] do out := out.push (add x[i]! (add y[i]! bias[i]!))
  return out

def gelu (x bias : Array UInt64) : Array UInt64 := Id.run do
  let mut out := #[]
  for i in [:3072] do out := out.push (GeluWide.evaluateAll (add x[i]! bias[i]!))
  return out

def rng (seed : UInt64) : UInt64 :=
  let s := seed ^^^ (seed >>> 12)
  let s := s ^^^ (s <<< 25)
  s ^^^ (s >>> 27)

def minimumIndex (x : Array UInt64) : Nat := Id.run do
  let mut m := 0
  for i in [1:x.size] do
    if greater x[m]! x[i]! then m := i
  return m

-- params: temperature bits, top-k (1..100), nonzero random state.
def sample (logits params : Array UInt64) : Array UInt64 := Id.run do
  let temperature := params[0]!
  let k := if temperature == 0 then 1 else params[1]!.toNat
  let mut values := #[]
  let mut indices := #[]
  for i in [:k] do
    values := values.push logits[i]!
    indices := indices.push i.toUInt64
  let mut m := minimumIndex values
  for i in [k:logits.size] do
    if greater logits[i]! values[m]! then
      values := values.set! m logits[i]!
      indices := indices.set! m i.toUInt64
      m := minimumIndex values
  if k == 1 then return #[indices[0]!, params[2]!]
  let maximum := SequenceSoftmax.maximum values
  let weights := values.map fun v => ExpNeg.evaluate (div (sub v maximum) temperature)
  let total := SequenceSoftmax.total weights
  let seed := rng params[2]!
  -- xorshift64*: scramble the output so small initial seeds do not all select
  -- the first top-k slot on their first draw. The unmultiplied state is kept.
  let random := seed * 0x2545F4914F6CDD1D
  let uniform := sub ((0x3FF0000000000000 : UInt64) ||| (random >>> 12)) 0x3FF0000000000000
  let target := mul uniform total
  let mut sum := 0
  let mut picked := indices[k-1]!
  let mut found := false
  for i in [:k] do
    sum := add sum weights[i]!
    if !found && greater sum target then
      picked := indices[i]!
      found := true
  return #[picked, seed]

def compute (op : UInt64) (x aux params : Array UInt64) (position : UInt64) : Array UInt64 :=
  if op == 0 && x.size == 768 && aux.size == 768 then embedding x aux
  else if op == 1 && x.size == 768 && params.size == 1536 then norm x params
  else if op == 2 && x.size == 2304 && aux.size == 196608 && params.size == 2304 && position < 128 then
    attention x aux params position.toNat
  else if op == 3 && x.size == 768 && aux.size == 768 && params.size == 768 then residual x aux params
  else if op == 4 && x.size == 3072 && params.size == 3072 then gelu x params
  else if op == 5 && x.size == 50257 && params.size == 3 && params[1]! > 0 && params[1]! ≤ 100 &&
      params[2]! != 0 && params[0]! ≤ 0x4000000000000000 then sample x params
  else #[]

end Project.Gpt2
