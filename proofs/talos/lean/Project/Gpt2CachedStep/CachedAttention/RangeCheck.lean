import Project.Gpt2CachedStep.CachedAttention.Compute
import Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCheck
import Project.ProofKit.F32DotRangeCheck

namespace Project.Gpt2CachedStep.CachedAttention.RangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

structure Parameters where
  scoreMul : Nat
  scoreAdd : Nat
  scoreScale : Nat
  softmax : SoftmaxRangeCertificate.Parameters
  valueMul : Nat
  valueAdd : Nat
  valueMagnitude : Nat

def scoreCheck (cache qkv : ByteArray) (layer position source head : Nat) (p : Parameters) : Bool :=
  let checked := F32DotRangeCertificate.checkedPrefix (fun c => word qkv (head * 64 + c))
    (fun c => cachedKv cache qkv layer position source (head * 64 + c)) p.scoreMul p.scoreAdd 64
  checked.2 && F32RangeCertificate.multiplication checked.1 0x3E000000 p.scoreScale

def probabilityValues (cache qkv : ByteArray) (layer position : Nat) : ByteArray :=
  let ss := scores cache qkv layer position
  let es := exponentials ss (maxima ss (position + 1)) (position + 1)
  probabilities es (sums es (position + 1)) (position + 1)

def check (cache qkv : ByteArray) (layer position : Nat) (p : Parameters) : Bool :=
  let ss := scores cache qkv layer position
  let es := exponentials ss (maxima ss (position + 1)) (position + 1)
  let ps := probabilities es (sums es (position + 1)) (position + 1)
  (List.range 12).all (fun head =>
    (List.range (position + 1)).all (fun source => scoreCheck cache qkv layer position source head p) &&
    SoftmaxRangeCertificate.check (fun j => word ss (head * (position + 1) + j))
      (cachedRowMaximum ss head (position + 1)) (position + 1) p.softmax) &&
  (List.range 768).all (fun i =>
    (F32DotRangeCertificate.checkedPrefix (fun j => word ps (i / 64 * (position + 1) + j))
      (fun j => cachedKv cache qkv layer position j (768 + i)) p.valueMul p.valueAdd (position + 1)).2 &&
    (List.range (position + 1)).all (fun j =>
      decide (Wasm.IEEE32.scaledMagnitude (cachedKv cache qkv layer position j (768 + i)) ≤ p.valueMagnitude)))

def profile (cache qkv : ByteArray) (layer position : Nat) : Parameters := Id.run do
  let ss := scores cache qkv layer position
  let es := exponentials ss (maxima ss (position + 1)) (position + 1)
  let ps := probabilities es (sums es (position + 1)) (position + 1)
  let mut scoreMul := 173
  let mut scoreAdd := 1
  let mut scoreScale := 173
  let mut subBound := 1
  let mut sumBound := 1
  let mut divBound := 24
  let mut valueMul := 173
  let mut valueAdd := 1
  let mut valueMagnitude := 0
  for head in [:12] do
    let maximum := cachedRowMaximum ss head (position + 1)
    let es := SoftmaxError.exponential (fun j => word ss (head * (position + 1) + j)) maximum
    let total := SoftmaxError.denominator (fun j => word ss (head * (position + 1) + j)) maximum (position + 1)
    sumBound := max sumBound (F32SumRangeCertificate.bound es (position + 1))
    for source in [:position + 1] do
      let query := fun c => word qkv (head * 64 + c)
      let key := fun c => cachedKv cache qkv layer position source (head * 64 + c)
      let dot := F32DotRangeCertificate.profile query key 64
      scoreMul := max scoreMul dot.multiplication
      scoreAdd := max scoreAdd dot.addition
      scoreScale := max scoreScale ((Wasm.IEEE32.scaledMagnitude dot.value * Wasm.IEEE32.scaledMagnitude 0x3E000000).log2 + 1)
      subBound := max subBound ((Wasm.IEEE32.scaledValue (word ss (head * (position + 1) + source)) - Wasm.IEEE32.scaledValue maximum).natAbs.log2 + 1)
      divBound := max divBound ((Wasm.IEEE32.scaledMagnitude (es source) * 2 ^ 149 / Wasm.IEEE32.scaledMagnitude total).log2 + 2)
  for i in [:768] do
    let values := fun j => cachedKv cache qkv layer position j (768 + i)
    let dot := F32DotRangeCertificate.profile (fun j => word ps (i / 64 * (position + 1) + j)) values (position + 1)
    valueMul := max valueMul dot.multiplication
    valueAdd := max valueAdd dot.addition
    for j in [:position + 1] do
      valueMagnitude := max valueMagnitude (Wasm.IEEE32.scaledMagnitude (values j))
  return ⟨scoreMul, scoreAdd, scoreScale, ⟨subBound, sumBound, divBound, {}⟩, valueMul, valueAdd, valueMagnitude⟩

end Project.Gpt2CachedStep.CachedAttention.RangeCertificate
