import LeanExe.Models.Gpt2.Quantized.Cached
import Project.Gpt2CachedStep.LayerNorm.Numerical
import Project.ProofKit.F32IntegerExact

namespace Project.Gpt2QuantizedCached.Embedding.Error
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit CodeLib.IEEE32
open Gpt2CachedStep.LayerNorm.Numerical (word_generate)

def coefficient (weights : ByteArray) (token : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Signed32.extend8Bits weights[tokenWeightOffset + token.toNat * 768 + i]!.toUInt32

def scale (weights : ByteArray) (token : UInt32) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token.toNat * 4)

def positionWord (weights : ByteArray) (position i : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (Quantized.positionOffset + (position * 768 + i) * 4)

def reconstructed (weights : ByteArray) (token : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.mulBits (LeanExe.Float32.ofInt32Bits (coefficient weights token i)) (scale weights token)

structure Ranges (weights : ByteArray) (token : UInt32) (position i mulBound addBound : Nat) : Prop where
  coefficientValid : weights[tokenWeightOffset + token.toNat * 768 + i]! ≠ 128
  scaleFinite : CodeLib.IEEE32.Finite (scale weights token)
  positionFinite : CodeLib.IEEE32.Finite (positionWord weights position i)
  mulLower : 173 ≤ mulBound
  mulUpper : mulBound ≤ 425
  mulRange : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits (coefficient weights token i)) *
    Wasm.IEEE32.scaledMagnitude (scale weights token) < 2 ^ mulBound
  addUpper : addBound ≤ 276
  addRange : (Wasm.IEEE32.scaledValue (reconstructed weights token i) +
    Wasm.IEEE32.scaledValue (positionWord weights position i)).natAbs < 2 ^ addBound

theorem component_source (weights : ByteArray) (token : UInt32) (position i : Nat) (hi : i < 768) :
    word (embedding weights token position) i =
      LeanExe.Float32.addBits (reconstructed weights token i) (positionWord weights position i) := by
  unfold embedding
  rw [word_generate _ _ i hi]
  rfl

theorem component_error (weights : ByteArray) (token : UInt32) (position i mulBound addBound : Nat)
    (hi : i < 768) (W weightError : ℝ) (h : Ranges weights token position i mulBound addBound)
    (hw : |value (scale weights token) * (LeanExe.Signed32.decode (coefficient weights token i) : ℝ) - W| ≤ weightError) :
    CodeLib.IEEE32.Finite (word (embedding weights token position) i) ∧
      |value (word (embedding weights token position) i) - (W + value (positionWord weights position i))| ≤
        F32AdditionBounds.epsilon addBound + (F32MultiplicationBounds.epsilon mulBound + weightError) := by
  have hr := QuantizedInt32.byte_range _ h.coefficientValid
  change |LeanExe.Signed32.decode (coefficient weights token i)| ≤ 127 at hr
  rw [← Int.natCast_natAbs] at hr
  have habs : (LeanExe.Signed32.decode (coefficient weights token i)).natAbs < 2 ^ 24 := by
    have : (LeanExe.Signed32.decode (coefficient weights token i)).natAbs ≤ 127 := by
      exact_mod_cast hr
    omega
  have hc := F32IntegerExact.conversion_exact (coefficient weights token i) habs
  have hm := F32MultiplicationBounds.mul_real_error _ _ mulBound h.mulLower h.mulUpper hc.1 h.scaleFinite h.mulRange
  rw [← F32Mul.mul_eq, hc.2, mul_comm (LeanExe.Signed32.decode (coefficient weights token i) : ℝ)] at hm
  have he : |value (reconstructed weights token i) - W| ≤ F32MultiplicationBounds.epsilon mulBound + weightError :=
    (abs_sub_le _ _ _).trans (add_le_add hm.2 hw)
  have ha := F32ErrorPropagation.add (reconstructed weights token i) (positionWord weights position i)
    W (value (positionWord weights position i)) _ 0 addBound hm.1 h.positionFinite h.addUpper h.addRange he (by simp)
  rw [component_source weights token position i hi]
  simpa only [add_zero] using ha

#print axioms component_error
end Project.Gpt2QuantizedCached.Embedding.Error
