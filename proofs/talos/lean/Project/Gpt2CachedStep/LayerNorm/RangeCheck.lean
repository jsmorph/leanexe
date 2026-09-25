import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32RangeCheck
import Project.ProofKit.F32SumRangeCheck

namespace Project.Gpt2CachedStep.LayerNorm.RangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

structure Parameters where
  inputMagnitude : Nat
  meanAdd : Nat
  meanDiv : Nat
  centerSub : Nat
  varianceMul : Nat
  varianceAdd : Nat
  varianceDiv : Nat
  epsilonAdd : Nat
  squareRoot : Nat
  reciprocal : Nat
  normalizedMul : Nat
  scaleMul : Nat
  biasAdd : Nat

def meanSum (input : ByteArray) : UInt32 :=
  (List.range 768).foldl (fun total i => LeanExe.Float32.addBits total (word input i)) 0

def centered (input : ByteArray) (mean : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.subBits (word input i) mean

def varianceSum (input : ByteArray) (mean : UInt32) : UInt32 :=
  (List.range 768).foldl (fun total i => LeanExe.Float32.addBits total
    (LeanExe.Float32.mulBits (centered input mean i) (centered input mean i))) 0

def denominator (input : ByteArray) : UInt32 :=
  LeanExe.Float32.sqrtBits (LeanExe.Float32.addBits (LeanExe.Float32.divBits
    (varianceSum input (LeanExe.Float32.divBits (meanSum input) 0x44400000)) 0x44400000) 0x3727C5AC)

def check (weights input : ByteArray) (scaleOffset biasOffset : Nat) (p : Parameters) : Bool :=
  let totalMean := meanSum input
  let mean := LeanExe.Float32.divBits totalMean 0x44400000
  let total := varianceSum input mean
  let variance := LeanExe.Float32.divBits total 0x44400000
  let shifted := LeanExe.Float32.addBits variance 0x3727C5AC
  let denominator := LeanExe.Float32.sqrtBits shifted
  let inverse := LeanExe.Float32.divBits 0x3F800000 denominator
  p.meanAdd ≤ 276 &&
    (F32SumRangeCertificate.checkedPrefix (fun i => word input i) p.meanAdd 768).2 &&
    p.varianceAdd ≤ 276 &&
    (F32SumRangeCertificate.checkedPrefix (fun i => LeanExe.Float32.mulBits
      (centered input mean i) (centered input mean i)) p.varianceAdd 768).2 &&
    F32RangeCertificate.division totalMean 0x44400000 p.meanDiv &&
    F32RangeCertificate.division total 0x44400000 p.varianceDiv &&
    F32RangeCertificate.addition variance 0x3727C5AC p.epsilonAdd &&
    F32RangeCertificate.squareRoot shifted p.squareRoot &&
    F32RangeCertificate.division 0x3F800000 denominator p.reciprocal &&
    (List.range 768).all (fun i =>
      let delta := centered input mean i
      let normalized := LeanExe.Float32.mulBits delta inverse
      let scaled := LeanExe.Float32.mulBits normalized (word weights (scaleOffset + i))
      Wasm.IEEE32.isFinite (word input i) && Wasm.IEEE32.isFinite (word weights (scaleOffset + i)) &&
      Wasm.IEEE32.isFinite (word weights (biasOffset + i)) &&
      decide (Wasm.IEEE32.scaledMagnitude (word input i) ≤ p.inputMagnitude) &&
      F32RangeCertificate.subtraction (word input i) mean p.centerSub &&
      F32RangeCertificate.multiplication delta delta p.varianceMul &&
      F32RangeCertificate.multiplication delta inverse p.normalizedMul &&
      F32RangeCertificate.multiplication normalized (word weights (scaleOffset + i)) p.scaleMul &&
      F32RangeCertificate.addition scaled (word weights (biasOffset + i)) p.biasAdd)

end Project.Gpt2CachedStep.LayerNorm.RangeCertificate
