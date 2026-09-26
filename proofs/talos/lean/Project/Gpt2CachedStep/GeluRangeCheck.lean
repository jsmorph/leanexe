import Project.Gpt2CachedStep.GeluCompute
import Project.Gpt2CachedStep.ExpNeg.RangeCheck

namespace Project.Gpt2CachedStep.GeluRangeCertificate
open Project.ProofKit

structure Parameters where
  square : Nat := 305
  weighted : Nat := 300
  factor : Nat := 152
  product : Nat := 303
  magnitude : Nat := 304
  exponential : ExpNeg.RangeCertificate.Parameters := {}
  denominatorAdd : Nat := 151
  numeratorMul : Nat := 302
  positiveDiv : Nat := 153
  negativeDiv : Nat := 153

def checkInner (a : UInt32) (p : Parameters) : Bool :=
  let exponential := GeluError.exponential a
  let denominator := LeanExe.Float32.addBits 0x3F800000 exponential
  let numerator := LeanExe.Float32.mulBits (a ||| 0x80000000) exponential
  F32RangeCertificate.multiplication a a p.square &&
  F32RangeCertificate.multiplication (GeluArgumentError.square a) 0x3D372713 p.weighted &&
  F32RangeCertificate.addition (GeluArgumentError.weighted a) 0x3F800000 p.factor &&
  F32RangeCertificate.multiplication (GeluArgumentError.factor a) a p.product &&
  F32RangeCertificate.multiplication (GeluArgumentError.product a) 0x3FCC422A p.magnitude &&
  ExpNeg.RangeCertificate.check (GeluError.argument a) p.exponential &&
  F32RangeCertificate.addition 0x3F800000 exponential p.denominatorAdd &&
  F32RangeCertificate.lowerAbsolute denominator 1 1 &&
  F32RangeCertificate.multiplication (a ||| 0x80000000) exponential p.numeratorMul &&
  F32RangeCertificate.division a denominator p.positiveDiv &&
  F32RangeCertificate.division numerator denominator p.negativeDiv

def check (input : UInt32) (p : Parameters) : Bool :=
  Wasm.IEEE32.isFinite input &&
    (if input &&& 0x7FFFFFFF > 0x41000000 then true else checkInner (input &&& 0x7FFFFFFF) p)

end Project.Gpt2CachedStep.GeluRangeCertificate
