import Project.Gpt2QuantizedCached.Numerical.OperationUpper
import Project.Gpt2QuantizedCached.Numerical.NormalizationUpper

namespace Project.Gpt2QuantizedCached.Numerical.ForwardUpper
open OperationUpper

structure BlockData where
  normalized : NormalizationUpper.PairData
  qkv : ProjectionData
  queryMagnitude : Nat
  keyMagnitude : Nat
  quantizedAttention : Project.Gpt2CachedStep.CachedAttention.RangeCertificate.Parameters
  referenceAttention : Project.Gpt2CachedStep.CachedAttention.RangeCertificate.Parameters
  projected : ProjectionData
  residualQuantized : Nat
  residualReference : Nat
  normalized2 : NormalizationUpper.PairData
  expanded : ProjectionData
  projected2 : ProjectionData
  hiddenQuantized : Nat
  hiddenReference : Nat

structure Errors where
  normalized : Nat
  qkv : Nat
  mixed : Nat
  projected : Nat
  residual : Nat
  normalized2 : Nat
  expanded : Nat
  activated : Nat
  projected2 : Nat
  hidden : Nat

def block (d : BlockData) (position E C : Nat) : Errors :=
  let n := NormalizationUpper.pair d.normalized E
  let q := project 768 true d.qkv n
  let m := attention position d.queryMagnitude d.keyMagnitude q C d.quantizedAttention d.referenceAttention
  let p := project 768 true d.projected m
  let r := residual E p d.residualQuantized d.residualReference
  let n2 := NormalizationUpper.pair d.normalized2 r
  let e := project 768 true d.expanded n2
  let a := gelu e
  let p2 := project 3072 true d.projected2 a
  ⟨n, q, m, p, r, n2, e, a, p2, residual r p2 d.hiddenQuantized d.hiddenReference⟩

structure StepData where
  embeddingWeightError : Nat
  embeddingMul : Nat
  embeddingAdd : Nat
  referenceEmbeddingAdd : Nat
  blocks : Nat → BlockData
  normalized : NormalizationUpper.PairData
  vocabulary : ProjectionData

def layerErrors (d : StepData) (position C : Nat) : Nat → Nat × Nat
  | 0 => (embedding d.embeddingWeightError d.embeddingMul d.embeddingAdd d.referenceEmbeddingAdd, 0)
  | n + 1 =>
    let previous := layerErrors d position C n
    let next := block (d.blocks n) position previous.1 C
    (next.hidden, max previous.2 next.qkv)

def step (d : StepData) (position C : Nat) : Nat × Nat :=
  let h := layerErrors d position C 12
  (project 768 false d.vocabulary (NormalizationUpper.pair d.normalized h.1), max C h.2)

def trace : List StepData → Nat → Nat → List Nat
  | [], _, _ => []
  | d :: ds, position, C =>
    let next := step d position C
    next.1 :: trace ds (position + 1) next.2

end Project.Gpt2QuantizedCached.Numerical.ForwardUpper
