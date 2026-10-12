import Verified.Examples.Fourier
import Verified.Examples.TrigNear
import Verified.Examples.LogCoreBits
import LeanExe.ProofKit.F64ExactProduct
import LeanExe.ProofKit.F64NegateOps
import Mathlib.Analysis.Real.Pi.Bounds

namespace Verified.Examples.FourierTwiddle

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx

set_option exponentiation.threshold 1200

local notation "𝐮" => unitRoundoff64

def angle (n m : UInt64) : Float :=
  6.283185307179586 * (m.toFloat / n.toFloat)

theorem twoPi_bits : (6.283185307179586 : Float).toBits = 0x401921FB54442D18 := by
  decide +kernel

theorem twoPi_value : value (6.283185307179586 : Float).toBits =
    7074237752028440 / 2 ^ 50 := by
  rw [twoPi_bits, TrigReduce.value_word _ 7074237752028440 50 (by norm_num)
    (by decide +kernel)]
  norm_num

theorem twoPi_near : FApprox (6.283185307179586 : Float) (2 * Real.pi) (3 * 𝐮) := by
  refine ⟨?_, ?_⟩
  · rw [twoPi_bits]
    unfold CodeLib.IEEE64.Finite
    decide
  · rw [twoPi_value, abs_le]
    have hlo := Real.pi_gt_d20
    have hhi := Real.pi_lt_d20
    norm_num [unitRoundoff64] at hlo hhi ⊢
    constructor <;> linarith

theorem convert_near (n : UInt64) (hn : n.toNat ≤ 2 ^ 53) :
    FApprox n.toFloat (n.toNat : ℝ) 0 := by
  obtain ⟨hf, hv⟩ := LogCoreBits.convert_exact n hn
  unfold FApprox Approx
  rw [F64Convert.toBits_toFloat, hv]
  exact ⟨hf, by simp⟩

theorem ratio_near (n m : UInt64) (hn : 0 < n.toNat) (hm : m.toNat < n.toNat)
    (hn53 : n.toNat ≤ 2 ^ 53) :
    FApprox (m.toFloat / n.toFloat) ((m.toNat : ℝ) / n.toNat) (2 * 𝐮) := by
  have hnp : (0 : ℝ) < n.toNat := by exact_mod_cast hn
  have hmn : (m.toNat : ℝ) ≤ n.toNat := by exact_mod_cast hm.le
  have h := fapprox_div (convert_near m (hm.le.trans hn53)) (convert_near n hn53)
    (m.toNat : ℝ) (n.toNat : ℝ) (by rw [abs_of_nonneg (Nat.cast_nonneg _)])
    (by rw [abs_of_nonneg (Nat.cast_nonneg _)]) hnp 1
    (by simpa only [add_zero, sub_zero] using (div_le_one hnp).mpr hmn) (by norm_num)
  simp only [mul_zero, zero_div, zero_add, sub_zero] at h
  exact h.mono (by norm_num [unitRoundoff64])

theorem angle_near (n m : UInt64) (hn : 0 < n.toNat) (hm : m.toNat < n.toNat)
    (hn53 : n.toNat ≤ 2 ^ 53) :
    FApprox (angle n m) (2 * Real.pi * m.toNat / n.toNat) (26 * 𝐮) := by
  have hnp : (0 : ℝ) < n.toNat := by exact_mod_cast hn
  have hmn : (m.toNat : ℝ) ≤ n.toNat := by exact_mod_cast hm.le
  have hq : |(m.toNat : ℝ) / n.toNat| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnp.le)]
    exact (div_le_one hnp).mpr hmn
  have hp : |2 * Real.pi| ≤ 7 := by
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    linarith [Real.pi_lt_d4]
  have h := fapprox_mul twoPi_near (ratio_near n m hn hm hn53) 7 1 hp hq 8
    (by norm_num [unitRoundoff64]) (by norm_num)
  exact (h.mono (by norm_num [unitRoundoff64])).congr (by ring)

theorem twiddle_near (n m : UInt64) (hn : 0 < n.toNat) (hm : m.toNat < n.toNat)
    (hn53 : n.toNat ≤ 2 ^ 53) :
    FApprox (Fourier.twiddle n m).1 (Real.cos (2 * Real.pi * m.toNat / n.toNat)) (32 * 𝐮) ∧
      FApprox (Fourier.twiddle n m).2 (Real.sin (2 * Real.pi * m.toNat / n.toNat))
        (32 * 𝐮) := by
  have ha := angle_near n m hn hm hn53
  have hc := TrigNear.cos_near (angle n m) ha.1
  have hs := TrigNear.sin_near (angle n m) ha.1
  change FApprox (Trig.cos (angle n m)) _ _ ∧ FApprox (Trig.sin (angle n m)) _ _
  constructor
  · refine ⟨hc.1, ?_⟩
    calc |value (Trig.cos (angle n m)).toBits - Real.cos (2 * Real.pi * m.toNat / n.toNat)|
        ≤ |value (Trig.cos (angle n m)).toBits - Real.cos (value (angle n m).toBits)| +
          |Real.cos (value (angle n m).toBits) - Real.cos (2 * Real.pi * m.toNat / n.toNat)| :=
            abs_sub_le _ _ _
      _ ≤ TrigNear.trigErr + 26 * 𝐮 := add_le_add hc.2
        ((Real.abs_cos_sub_cos_le _ _).trans ha.2)
      _ ≤ 32 * 𝐮 := by norm_num [TrigNear.trigErr, unitRoundoff64]
  · refine ⟨hs.1, ?_⟩
    calc |value (Trig.sin (angle n m)).toBits - Real.sin (2 * Real.pi * m.toNat / n.toNat)|
        ≤ |value (Trig.sin (angle n m)).toBits - Real.sin (value (angle n m).toBits)| +
          |Real.sin (value (angle n m).toBits) - Real.sin (2 * Real.pi * m.toNat / n.toNat)| :=
            abs_sub_le _ _ _
      _ ≤ TrigNear.trigErr + 26 * 𝐮 := add_le_add hs.2
        ((Real.abs_sin_sub_sin_le _ _).trans ha.2)
      _ ≤ 32 * 𝐮 := by norm_num [TrigNear.trigErr, unitRoundoff64]

theorem one_mul_exact (w : UInt64) (hw : Finite w) :
    Finite (Wasm.IEEE64.mul 0x3FF0000000000000 w) ∧
      value (Wasm.IEEE64.mul 0x3FF0000000000000 w) = value w := by
  have h1f : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  by_cases he : Wasm.IEEE64.exponent w = 0
  · have h := F64ExactProduct.int_mul_exact 0x3FF0000000000000 w h1f hw
      1 (Wasm.IEEE64.fraction w) 0 (by decide +kernel)
      (by simp [Wasm.IEEE64.scaledMagnitude, he])
      (by have := Nat.mod_lt w.toNat (by norm_num : 0 < 2 ^ 52)
          simpa only [Wasm.IEEE64.fraction, one_mul] using
            this.trans (by norm_num : 2 ^ 52 < 2 ^ 53))
      (by norm_num)
    refine ⟨h.1, ?_⟩
    have h1v : value (0x3FF0000000000000 : UInt64) = 1 := TrigKernelWords.value_one
    rw [h.2.1, h1v]
    ring
  · have he2 : Wasm.IEEE64.exponent w < 2047 := by
      have hb := Nat.mod_lt (w.toNat / 2 ^ 52) (by norm_num : 0 < 2 ^ 11)
      have hf := hw
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
      change Wasm.IEEE64.exponent w < 2048 at hb
      omega
    have h := F64PowerScale.mul_power_finite 1023 w (by norm_num) (by norm_num) hw
      (by omega) (by omega) (by omega)
    rw [show Wasm.IEEE64.encodeFinite false 1023 0 = (0x3FF0000000000000 : UInt64)
      by decide +kernel] at h
    norm_num at h
    exact h

theorem negOne_mul_exact (s : Float) (hs : Finite s.toBits) :
    Finite ((-1.0 : Float) * s).toBits ∧
      value ((-1.0 : Float) * s).toBits = -value s.toBits := by
  have h := one_mul_exact s.toBits hs
  have h1f : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  rw [F64Bits.toBits_mul,
    show (-1.0 : Float).toBits = Wasm.IEEE64.negate 0x3FF0000000000000 by decide +kernel,
    F64NegateOps.mul_negate_left _ _ h1f hs]
  have hn := F64Magnitude.negate_value _ h.1
  exact ⟨hn.1, by rw [hn.2, h.2]⟩

#print axioms twoPi_bits
#print axioms twoPi_value
#print axioms twoPi_near
#print axioms convert_near
#print axioms ratio_near
#print axioms angle_near
#print axioms twiddle_near
#print axioms one_mul_exact
#print axioms negOne_mul_exact

end Verified.Examples.FourierTwiddle
