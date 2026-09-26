import Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCheck
import Project.Gpt2CachedStep.CachedAttention.RangeCheck
import Project.ProofKit.DyadicUpper

namespace Project.Gpt2QuantizedCached.Numerical.OperationUpper
open Project.ProofKit.DyadicUpper

def addError (bound : Nat) : Nat := roundoff bound 25 149
def mulError (bound : Nat) : Nat := roundoff bound 25 298
def divError (bound : Nat) : Nat := roundoff bound 24 149

def projection (width : Nat) (bias : Bool) (X W E A D : Nat)
    (p : ProjectionRangeCertificate.Parameters) : Nat :=
  let ex := add A E
  let term := add (add (mul W ex) (mul X D)) (mul ex D)
  let group := add (add (mulError p.quantizedOutput) (1032256 * mulError p.quantizedScale)) (64 * term)
  add (add ((width / 64) * add group (addError p.quantizedAdd)) (if bias then addError p.quantizedBias else 0))
    (add (if bias then addError p.referenceBias else 0) (width * add (mulError p.referenceMul) (addError p.referenceAdd)))

structure ProjectionData where
  bounds : ProjectionRangeCertificate.Parameters
  inputMagnitude : Nat
  weightMagnitude : Nat
  activationError : Nat
  weightError : Nat

def project (width : Nat) (bias : Bool) (d : ProjectionData) (E : Nat) : Nat :=
  projection width bias d.inputMagnitude d.weightMagnitude E d.activationError d.weightError d.bounds

def embedding (D : Nat) (m a r : Nat) : Nat := add (add (addError a) (add (mulError m) D)) (addError r)
def residual (L R : Nat) (q r : Nat) : Nat := add (add (addError q) (add L R)) (addError r)
def gelu (E : Nat) : Nat := add (fraction 1 8) (4 * E)

def score (Q K E C : Nat) (m a s : Nat) : Nat :=
  add (mulError s) (8 * add (add (mulError m) (add (mul Q C) (mul E K))) (addError a))

def softmax (n s a d : Nat) : Nat :=
  add (add (divError d) ((n + 1) * add (fraction 1 300) (addError s))) (n * addError a)

def attentionRound (n V s a d m b : Nat) : Nat :=
  n * add (add (mulError m) (mul (softmax n s a d) V)) (addError b)

def attention (position Q K E C : Nat)
    (q r : Project.Gpt2CachedStep.CachedAttention.RangeCertificate.Parameters) : Nat :=
  let history := max E C
  let scores := add (score Q K E history q.scoreMul q.scoreAdd q.scoreScale)
    (score 0 0 0 0 r.scoreMul r.scoreAdd r.scoreScale)
  let qv := fp32Magnitude q.valueMagnitude
  let rv := fp32Magnitude r.valueMagnitude
  add (add (attentionRound (position + 1) qv q.softmax.subtraction q.softmax.summation q.softmax.division q.valueMul q.valueAdd)
    (add (2 * mul qv scores) history))
    (attentionRound (position + 1) rv r.softmax.subtraction r.softmax.summation r.softmax.division r.valueMul r.valueAdd)

end Project.Gpt2QuantizedCached.Numerical.OperationUpper
