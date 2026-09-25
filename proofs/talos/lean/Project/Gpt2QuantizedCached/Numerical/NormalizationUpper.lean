import Project.Gpt2CachedStep.LayerNorm.RangeCheck
import Project.ProofKit.DyadicUpper

namespace Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
open Project.ProofKit.DyadicUpper

abbrev Parameters := Project.Gpt2CachedStep.LayerNorm.RangeCertificate.Parameters

def mean (p : Parameters) (inputError : Nat) : Nat :=
  add (roundoff p.meanDiv 24 149) (add inputError (roundoff p.meanAdd 25 149))

def center (p : Parameters) (inputError : Nat) : Nat :=
  add (roundoff p.centerSub 25 149) (add inputError (mean p inputError))

def squares (p : Parameters) (inputError actualCenter referenceCenter : Nat) : Nat :=
  768 * add (roundoff p.varianceMul 25 298)
    (add (mul (add actualCenter referenceCenter) (center p inputError)) (roundoff p.varianceAdd 25 149))

def rootFromSquares (p : Parameters) (totalError : Nat) : Nat :=
  add (roundoff p.squareRoot 23 149)
    (1000 * add (roundoff p.epsilonAdd 25 149)
      (add (roundoff p.varianceDiv 24 149) (divNat totalError 768)))

def root (p : Parameters) (inputError actualCenter referenceCenter : Nat) : Nat :=
  rootFromSquares p (squares p inputError actualCenter referenceCenter)

def inverse (p : Parameters) (inputError actualCenter referenceCenter : Nat) : Nat :=
  add (roundoff p.reciprocal 24 149) (1000000 * root p inputError actualCenter referenceCenter)

def component (p : Parameters) (inputError actualCenter referenceCenter gain : Nat) : Nat :=
  add (roundoff p.biasAdd 25 149) (add (roundoff p.scaleMul 25 298)
    (mul (add (roundoff p.normalizedMul 25 298)
      (add (mul actualCenter (inverse p inputError actualCenter referenceCenter)) (1000 * center p inputError))) gain))

structure PairData where
  quantized : Parameters
  reference : Parameters
  quantizedCenter : Nat
  referenceCenter : Nat
  realCenter : Nat
  gain : Nat

def pair (d : PairData) (E : Nat) : Nat :=
  add (component d.quantized E d.quantizedCenter d.realCenter d.gain)
    (component d.reference 0 d.referenceCenter d.realCenter d.gain)

end Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
