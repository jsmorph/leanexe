import Verified.Examples.SinpiProduct

/-!
`Sinpi.piTiny` on words, with its exact steps.  The head `hi` is the truncation of `x` to its high
32 bits scaled by `2 ^ 53`, `x 2 ^ 53` is exact, and the tail `lo = x 2 ^ 53 - hi` is exact, for
normal and subnormal `x` below 1 in magnitude.  The product `pi_hi hi` is exact.  The final
scaling by `2 ^ -53` is exact when its result is normal and within `2 ^ -1075` otherwise.
-/

namespace Verified.Examples.SinpiTinyWords

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanBigWords SinpiProduct

set_option exponentiation.threshold 1200

def P53 : UInt64 := 0x4340000000000000
def Pm53 : UInt64 := 0x3CA0000000000000

/-- `Sinpi.piTiny` on words. -/
def tinyW (b : UInt64) : UInt64 :=
  let h := Wasm.IEEE64.mul (b &&& mask) P53
  let l := Wasm.IEEE64.sub (Wasm.IEEE64.mul b P53) h
  let s := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.add piLo piHi) l)
    (Wasm.IEEE64.mul piLo h)) (Wasm.IEEE64.mul piHi h)
  Wasm.IEEE64.mul s Pm53

theorem shift_mask (b : UInt64) : b >>> 32 <<< 32 = b &&& mask := by
  apply UInt64.toNat_inj.mp
  rw [mask_toNat, TrigWords.shl_toNat, TrigWords.shr_toNat]
  show b.toNat / 2 ^ 32 * 2 ^ 32 % 2 ^ 64 = b.toNat / 2 ^ 32 * 2 ^ 32
  have := b.toNat_lt
  omega

theorem trunc_finite (b : UInt64) (hbf : Finite b) : Finite (b &&& mask) := by
  obtain ⟨he, -, -⟩ := trunc_fields b
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hbf ⊢
  rw [he]
  exact hbf

theorem trunc_canon (b : UInt64) (hbf : Finite b) : canon (b &&& mask) = b &&& mask := by
  have hfin := trunc_finite b hbf
  unfold canon
  have : Wasm.IEEE64.isNaN (b &&& mask) = false := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hfin
    unfold Wasm.IEEE64.isNaN
    simp only [bne_iff_ne, ne_eq] at hfin
    simp [hfin]
  rw [this]
  rfl

theorem tiny_bits (x : Float) (hxf : Finite x.toBits) :
    (Sinpi.piTiny x (x.toBits >>> 32)).toBits = tinyW x.toBits := by
  have h1 : (Float.ofBits 0x400921FB58000000).toBits = piHi := by
    rw [F64Bits.toBits_ofBits]; decide
  have h2 : (Float.ofBits 0xBE5DDE973DCB3B3A).toBits = piLo := by
    rw [F64Bits.toBits_ofBits]; decide
  have h3 : (Float.ofBits 0x4340000000000000).toBits = P53 := by
    rw [F64Bits.toBits_ofBits]; decide
  have h4 : (Float.ofBits 0x3CA0000000000000).toBits = Pm53 := by
    rw [F64Bits.toBits_ofBits]; decide
  have h5 : (Float.ofBits (x.toBits >>> 32 <<< 32)).toBits = x.toBits &&& mask := by
    rw [F64Bits.toBits_ofBits, shift_mask]
    exact trunc_canon _ hxf
  unfold Sinpi.piTiny tinyW
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, h1, h2, h3, h4, h5]

/-- The scaled magnitudes of a word and of its truncation. -/
theorem trunc_mag (b : UInt64) : ∃ m : Nat, m < 2 ^ 53 ∧
    Wasm.IEEE64.scaledMagnitude b = m * 2 ^ (Wasm.IEEE64.exponent b - 1) ∧
    Wasm.IEEE64.scaledMagnitude (b &&& mask) =
      m / 2 ^ 32 * 2 ^ 32 * 2 ^ (Wasm.IEEE64.exponent b - 1) ∧
    (Wasm.IEEE64.exponent b ≠ 0 → 2 ^ 52 ≤ m) := by
  obtain ⟨he, -, hf⟩ := trunc_fields b
  have hfl : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  by_cases h0 : Wasm.IEEE64.exponent b = 0
  · refine ⟨Wasm.IEEE64.fraction b, by omega, ?_, ?_, fun h => absurd h0 h⟩
    · simp only [Wasm.IEEE64.scaledMagnitude, h0, beq_self_eq_true, ite_true, Nat.zero_sub,
        pow_zero, mul_one]
    · simp only [Wasm.IEEE64.scaledMagnitude, he, hf, h0, beq_self_eq_true, ite_true,
        Nat.zero_sub, pow_zero, mul_one]
  · have hne : (Wasm.IEEE64.exponent b == 0) = false := by simpa using h0
    refine ⟨2 ^ 52 + Wasm.IEEE64.fraction b, by omega, ?_, ?_, fun _ => by omega⟩
    · simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false]
    · simp only [Wasm.IEEE64.scaledMagnitude, he, hf, hne, Bool.false_eq_true, ite_false]
      congr 1
      omega

/-- A word below 1 in magnitude has exponent field at most 1022. -/
theorem exp_small (b : UInt64) (h : |value b| < 1) : Wasm.IEEE64.exponent b ≤ 1022 := by
  by_contra hc
  have h1 := TrigNearest.grid_lower b (by omega)
  have : (1 : ℝ) ≤ 2 ^ (52 + (Wasm.IEEE64.exponent b - 1)) / 2 ^ 1074 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem consts53 : Finite P53 ∧ Wasm.IEEE64.sign P53 = false ∧
    Wasm.IEEE64.scaledMagnitude P53 = 1 * 2 ^ 1127 ∧ value P53 = 2 ^ 53 ∧
    Finite Pm53 ∧ Wasm.IEEE64.scaledMagnitude Pm53 = 1 * 2 ^ 1021 ∧ value Pm53 = 1 / 2 ^ 53 := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by decide, by decide +kernel, ?_,
    by unfold CodeLib.IEEE64.Finite; decide, by decide +kernel, ?_⟩
  · rw [TrigSmall.value_of_scaled,
      show Wasm.IEEE64.scaledValue P53 = 2 ^ 1127 by decide +kernel]
    norm_num
  · rw [TrigSmall.value_of_scaled,
      show Wasm.IEEE64.scaledValue Pm53 = 2 ^ 1021 by decide +kernel]
    norm_num

/-- Multiplication by `2 ^ 53` of a word with scaled magnitude `m 2 ^ k` is exact. -/
theorem mul_up (w : UInt64) (hwf : Finite w) (m k : Nat)
    (hm : Wasm.IEEE64.scaledMagnitude w = m * 2 ^ k) (hm53 : m < 2 ^ 53) (hk : k ≤ 1990) :
    Finite (Wasm.IEEE64.mul w P53) ∧ value (Wasm.IEEE64.mul w P53) = value w * 2 ^ 53 ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul w P53) = m * 2 ^ (k + 53) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul w P53) = Wasm.IEEE64.sign w := by
  obtain ⟨f53, s53, m53, v53, -, -, -⟩ := consts53
  obtain ⟨hf, hv, hmag, hs⟩ := F64ExactProduct.mul_exact_scaled w P53 hwf f53 m 1 k 1127 hm m53
    (by omega) (by omega) (by omega)
  refine ⟨hf, by rw [hv, v53], by rw [hmag, mul_one, show k + 1127 - 1074 = k + 53 by omega], ?_⟩
  rw [hs, s53]
  cases Wasm.IEEE64.sign w <;> rfl

/-- Multiplication by `2 ^ -53` of a word below `2 ^ 30`: exact when the result is normal, and
within `2 ^ -1075` otherwise. -/
theorem mul_down (s : UInt64) (hsf : Finite s) (hs1 : |value s| < 2 ^ 30) :
    Finite (Wasm.IEEE64.mul s Pm53) ∧
      (1 / 2 ^ 1022 ≤ |value s / 2 ^ 53| →
        value (Wasm.IEEE64.mul s Pm53) = value s / 2 ^ 53) ∧
      (|value s / 2 ^ 53| < 1 / 2 ^ 1022 →
        |value (Wasm.IEEE64.mul s Pm53) - value s / 2 ^ 53| ≤ 1 / 2 ^ 1075) := by
  obtain ⟨-, -, -, -, fm, mm, vm⟩ := consts53
  have hprod : value s * value Pm53 = value s / 2 ^ 53 := by rw [vm]; ring
  have hb : |value s * value Pm53| < 2 ^ 1022 := by
    rw [hprod, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    have : (2 : ℝ) ^ 30 / 2 ^ 53 < 2 ^ 1022 := by norm_num
    have h2 : |value s| / 2 ^ 53 < 2 ^ 30 / 2 ^ 53 := div_lt_div_of_pos_right hs1 (by positivity)
    linarith
  obtain ⟨hf, herr⟩ := F64MulBounds.mul_real_adaptive s Pm53 hsf fm hb
  rw [hprod] at herr
  refine ⟨hf, fun hn => ?_, fun hn => ?_⟩
  · have he : 54 ≤ Wasm.IEEE64.exponent s := by
      by_contra hc
      have h1 := TrigNearest.grid_bound s
      have h2 : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent s - 1)) / 2 ^ 1074 ≤ 2 ^ 105 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), le_div_iff₀ (by positivity)] at hn
      have h3 : (2 : ℝ) ^ 105 / 2 ^ 1074 = 1 / 2 ^ 1022 * 2 ^ 53 := by norm_num
      linarith
    obtain ⟨m, hm, hm53⟩ := mag_split s
    obtain ⟨-, hv, -, -⟩ := F64ExactProduct.mul_exact_scaled s Pm53 hsf fm m 1
      (Wasm.IEEE64.exponent s - 1) 1021 hm mm (by omega) (by omega) (by
        have : Wasm.IEEE64.exponent s < 2048 := Nat.mod_lt _ (by norm_num)
        omega)
    rw [hv, hprod]
  · dsimp only at herr
    have hm : (if Wasm.IEEE64.scaledMagnitude s * Wasm.IEEE64.scaledMagnitude Pm53 = 0 then 0
        else max |value s / 2 ^ 53| minNormal64) ≤ 1 / 2 ^ 1022 := by
      split
      · positivity
      · exact max_le hn.le (le_of_eq rfl)
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have h2 := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ unitRoundoff64 by rw [hu]; positivity)
    rw [hu] at h2 herr
    have h3 : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 1022) = 1 / 2 ^ 1075 := by norm_num
    linarith

#print axioms tiny_bits
#print axioms trunc_mag
#print axioms mul_up
#print axioms mul_down

end Verified.Examples.SinpiTinyWords
