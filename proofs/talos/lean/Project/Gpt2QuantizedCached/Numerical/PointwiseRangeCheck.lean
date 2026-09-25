import Project.Gpt2QuantizedCached.Embedding.Compute
import Project.ProofKit.F32RangeCheck

namespace Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

structure EmbeddingParameters where
  multiplication : Nat
  quantizedAdd : Nat
  referenceAdd : Nat
  deriving Inhabited

def addBound (a b : UInt32) : Nat :=
  (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs.log2 + 1

def profileEmbedding (qw rw : ByteArray) (token : UInt32) (position : Nat) : EmbeddingParameters := Id.run do
  let mut p : EmbeddingParameters := ⟨173, 0, 0⟩
  for i in [:768] do
    let code := LeanExe.Float32.ofInt32Bits (Embedding.Error.coefficient qw token i)
    let scale := Embedding.Error.scale qw token
    p := ⟨max p.multiplication ((Wasm.IEEE32.scaledMagnitude code * Wasm.IEEE32.scaledMagnitude scale).log2 + 1),
      max p.quantizedAdd (addBound (Embedding.Error.reconstructed qw token i) (Embedding.Error.positionWord qw position i)),
      max p.referenceAdd (addBound (word rw (token.toNat * 768 + i)) (word rw (positionOffset + position * 768 + i)))⟩
  return p

def checkEmbedding (qw rw : ByteArray) (token : UInt32) (position : Nat) (p : EmbeddingParameters) : Bool :=
  (List.range 768).all fun i =>
    qw[Quantized.tokenWeightOffset + token.toNat * 768 + i]! != 128 &&
    F32RangeCertificate.multiplication (LeanExe.Float32.ofInt32Bits (Embedding.Error.coefficient qw token i))
      (Embedding.Error.scale qw token) p.multiplication &&
    F32RangeCertificate.addition (Embedding.Error.reconstructed qw token i)
      (Embedding.Error.positionWord qw position i) p.quantizedAdd &&
    F32RangeCertificate.addition (word rw (token.toNat * 768 + i))
      (word rw (positionOffset + position * 768 + i)) p.referenceAdd &&
    Embedding.Error.positionWord qw position i == word rw (positionOffset + position * 768 + i)

def profileAdd (left right : ByteArray) : Nat :=
  (List.range 768).foldl (fun bound i => max bound (addBound (word left i) (word right i))) 0

def checkAdd (left right : ByteArray) (bound : Nat) : Bool :=
  (List.range 768).all fun i => F32RangeCertificate.addition (word left i) (word right i) bound

end Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCertificate
