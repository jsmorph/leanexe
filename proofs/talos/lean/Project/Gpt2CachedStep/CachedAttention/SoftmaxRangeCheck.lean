import Project.Gpt2CachedStep.CachedAttention.SoftmaxCompute
import Project.Gpt2CachedStep.ExpNeg.RangeCheck
import Project.ProofKit.F32SumRangeCheck

namespace Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCertificate
open Project.ProofKit SoftmaxError

structure Parameters where
  subtraction : Nat
  summation : Nat
  division : Nat
  exponential : ExpNeg.RangeCertificate.Parameters := {}

def check (scores : Nat → UInt32) (maximum : UInt32) (n : Nat) (p : Parameters) : Bool :=
  let total := denominator scores maximum n
  Wasm.IEEE32.isFinite maximum &&
    p.summation ≤ 276 &&
    (F32SumRangeCertificate.checkedPrefix (SoftmaxError.exponential scores maximum) p.summation n).2 &&
    F32RangeCertificate.lowerAbsolute total 1 1 &&
    Wasm.IEEE32.scaledMagnitude total != 0 &&
    (List.range n).all (fun i =>
      Wasm.IEEE32.isFinite (scores i) &&
      decide (Wasm.IEEE32.scaledValue (scores i) ≤ Wasm.IEEE32.scaledValue maximum) &&
      F32RangeCertificate.subtraction (scores i) maximum p.subtraction &&
      decide (Wasm.IEEE32.scaledValue (shifted scores maximum i) ≤ 0) &&
      ExpNeg.RangeCertificate.check (shifted scores maximum i) p.exponential &&
      F32RangeCertificate.division (SoftmaxError.exponential scores maximum i) total p.division)

end Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCertificate
