import Project.Gpt2CachedStep.LayerNorm.RangeCheck

namespace Project.Gpt2CachedStep.LayerNorm.RangeCertificate
open LeanExe.Models.Gpt2

def maximum (f : Nat → Nat) : Nat := (List.range 768).foldl (fun m i => max m (f i)) 0

def productBound (a b : UInt32) : Nat :=
  max 173 ((Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b).log2 + 1)

def divisionBound (a b : UInt32) : Nat :=
  max 24 ((Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 / Wasm.IEEE32.scaledMagnitude b).log2 + 2)

def profile (weights input : ByteArray) (scaleOffset biasOffset : Nat) : Parameters := Id.run do
  let totalMean := meanSum input
  let mean := LeanExe.Float32.divBits totalMean 0x44400000
  let total := varianceSum input mean
  let variance := LeanExe.Float32.divBits total 0x44400000
  let shifted := LeanExe.Float32.addBits variance 0x3727C5AC
  let denominator := LeanExe.Float32.sqrtBits shifted
  let inverse := LeanExe.Float32.divBits 0x3F800000 denominator
  let inputMagnitude := maximum fun i => Wasm.IEEE32.scaledMagnitude (word input i)
  let varianceMul := maximum fun i => productBound (centered input mean i) (centered input mean i)
  return {
    inputMagnitude
    meanAdd := Project.ProofKit.F32SumRangeCertificate.bound (fun i => word input i) 768
    meanDiv := divisionBound totalMean 0x44400000
    centerSub := maximum fun i => (Wasm.IEEE32.scaledValue (word input i) - Wasm.IEEE32.scaledValue mean).natAbs.log2 + 1
    varianceMul
    varianceAdd := Project.ProofKit.F32SumRangeCertificate.bound (fun i => LeanExe.Float32.mulBits
      (centered input mean i) (centered input mean i)) 768
    varianceDiv := divisionBound total 0x44400000
    epsilonAdd := (Wasm.IEEE32.scaledValue variance + Wasm.IEEE32.scaledValue 0x3727C5AC).natAbs.log2 + 1
    squareRoot := max 24 ((Wasm.IEEE32.scaledMagnitude shifted * 2 ^ 149).log2 / 2 + 1)
    reciprocal := divisionBound 0x3F800000 denominator
    normalizedMul := maximum fun i => productBound (centered input mean i) inverse
    scaleMul := maximum fun i => productBound (LeanExe.Float32.mulBits (centered input mean i) inverse) (word weights (scaleOffset + i))
    biasAdd := maximum fun i =>
      (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (LeanExe.Float32.mulBits (centered input mean i) inverse)
        (word weights (scaleOffset + i))) + Wasm.IEEE32.scaledValue (word weights (biasOffset + i))).natAbs.log2 + 1 }

end Project.Gpt2CachedStep.LayerNorm.RangeCertificate
