import Project.Gpt2CachedStep.ExpNeg.Compute
import Project.ProofKit.F32RangeCheck
import Project.ProofKit.F32HornerRangeCheck

namespace Project.Gpt2CachedStep.ExpNeg.RangeCertificate
open Project.ProofKit LeanExe.Models.Gpt2

structure Parameters where
  multiplication : Nat := 299
  addition : Nat := 151
  squaring : Nat := 299

def check (input : UInt32) (p : Parameters) : Bool :=
  if input > 0xC2800000 then
    decide (Wasm.IEEE32.scaledValue input ≤ -64 * (2 ^ 149 : Int))
  else
    let reduced := reducePrefix input 6
    Wasm.IEEE32.isFinite reduced.1 &&
      decide (Wasm.IEEE32.scaledMagnitude reduced.1 ≤ 2 ^ 149) &&
      F32RangeCertificate.rescaling input reduced.1 reduced.2 &&
      (F32HornerRangeCertificate.checkedPrefix reduced.1 0x253413C3 PolynomialError.coefficient
        p.multiplication p.addition 18).2 &&
      (List.range reduced.2).all (fun i =>
        let current := squarePrefix (expPolynomial reduced.1) i
        F32RangeCertificate.multiplication current current p.squaring)

end Project.Gpt2CachedStep.ExpNeg.RangeCertificate
