import Project.Gpt2QuantizedCached.Embedding.Error
import Project.Gpt2QuantizedCached.Numerical.TensorBounds
import Project.Gpt2CachedStep.CachedHidden.Source

namespace Project.Gpt2QuantizedCached.Numerical.EmbeddingPair
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open Gpt2CachedStep.LayerNorm.Numerical (word_generate)

structure Parameters where
  qMul : Nat → Nat
  qAdd : Nat → Nat
  rAdd : Nat → Nat
  weightError : Nat → ℝ

structure Ranges (qw rw : ByteArray) (token : UInt32) (position : Nat) (p : Parameters) : Prop where
  quantized : ∀ i < 768, Embedding.Error.Ranges qw token position i (p.qMul i) (p.qAdd i)
  weightError : ∀ i < 768,
    |value (Embedding.Error.scale qw token) * (LeanExe.Signed32.decode (Embedding.Error.coefficient qw token i) : ℝ) -
      value (word rw (token.toNat * 768 + i))| ≤ p.weightError i
  positionEqual : ∀ i < 768, Embedding.Error.positionWord qw position i = word rw (positionOffset + position * 768 + i)
  tokenFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word rw (token.toNat * 768 + i))
  positionFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word rw (positionOffset + position * 768 + i))
  addUpper : ∀ i < 768, p.rAdd i ≤ 276
  addRange : ∀ i < 768, (Wasm.IEEE32.scaledValue (word rw (token.toNat * 768 + i)) +
    Wasm.IEEE32.scaledValue (word rw (positionOffset + position * 768 + i))).natAbs < 2 ^ p.rAdd i

noncomputable def componentError (p : Parameters) (i : Nat) : ℝ :=
  F32AdditionBounds.epsilon (p.qAdd i) + (F32MultiplicationBounds.epsilon (p.qMul i) + p.weightError i) +
    F32AdditionBounds.epsilon (p.rAdd i)

noncomputable def error (p : Parameters) : ℝ := FiniteErrorBound.upper (componentError p) 768

theorem component_error (qw rw : ByteArray) (token : UInt32) (position : Nat) (p : Parameters)
    (h : Ranges qw rw token position p) (i : Nat) (hi : i < 768) :
    |value (word (Quantized.embedding qw token position) i) -
      value (word (Gpt2CachedStep.CachedHidden.embedding rw token position) i)| ≤ componentError p i := by
  have hq := Embedding.Error.component_error qw token position i (p.qMul i) (p.qAdd i) hi
    (value (word rw (token.toNat * 768 + i))) (p.weightError i) (h.quantized i hi) (h.weightError i hi)
  rw [h.positionEqual i hi] at hq
  have hr := F32AdditionBounds.add_real_error _ _ (p.rAdd i) (h.addUpper i hi)
    (h.tokenFinite i hi) (h.positionFinite i hi) (h.addRange i hi)
  rw [← F32Add.add_eq] at hr
  rw [Gpt2CachedStep.CachedHidden.embedding, word_generate _ _ i hi]
  exact F32ErrorPropagation.compare _ _ _ _ _ hq.2 hr.2

theorem close (qw rw : ByteArray) (token : UInt32) (position : Nat) (p : Parameters) (h : Ranges qw rw token position p) :
    Close (Quantized.embedding qw token position) (Gpt2CachedStep.CachedHidden.embedding rw token position) 768 (error p) := by
  intro i hi
  exact (component_error qw rw token position p h i hi).trans (FiniteErrorBound.component_le _ _ i hi)

#print axioms close
end Project.Gpt2QuantizedCached.Numerical.EmbeddingPair
