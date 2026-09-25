import Project.ProofKit.PackedLogitCertificate
import LeanExe.Models.Gpt2.Quantized.Cached

namespace Project.Gpt2QuantizedCached.LogitCertificates
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models

def checkStep (fp32Weights quantizedWeights fp32Cache quantizedCache : ByteArray)
    (token : UInt32) (position : Nat) (errors : Array Nat) (shift : Int) (winner : Nat) : Bool :=
  let fp32 := Gpt2.cachedStep fp32Weights fp32Cache token position
  let quantized := Gpt2.Quantized.cachedStep quantizedWeights quantizedCache token position
  quantized.status == 0 &&
    PackedLogitCertificate.check fp32.logits quantized.logits 50257 errors shift winner

theorem step_sound (fp32Weights quantizedWeights fp32Cache quantizedCache : ByteArray)
    (token : UInt32) (position : Nat) (errors : Array Nat) (shift : Int) (winner : Nat)
    (h : checkStep fp32Weights quantizedWeights fp32Cache quantizedCache token position errors shift winner = true) :
    let fp32 := Gpt2.cachedStep fp32Weights fp32Cache token position
    let quantized := Gpt2.Quantized.cachedStep quantizedWeights quantizedCache token position
    quantized.status = 0 ∧ fp32.logits.size = 201028 ∧ quantized.logits.size = 201028 ∧
      winner < 50257 ∧
      (∀ i < 50257, |value (Gpt2.word quantized.logits i) - (shift : ℝ) / 2 ^ 149 -
        value (Gpt2.word fp32.logits i)| ≤ F32LogitCertificate.realError errors[i]!) ∧
      (∀ i < 50257, i ≠ winner → value (Gpt2.word quantized.logits winner) > value (Gpt2.word quantized.logits i)) := by
  simp only [checkStep, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, PackedLogitCertificate.sound _ _ 50257 errors shift winner h.2⟩

#print axioms step_sound
end Project.Gpt2QuantizedCached.LogitCertificates
