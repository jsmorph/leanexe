import Verified.Examples.TgammaRefl5

/-!
The results of the path of `tgammaWith` below `-3`.  The code computes `ub = rh + (rl + eps)`
with `rh + rl` near `G 2 ^ E` for `G = Γ x`.  For a normal result it subtracts `E` from the exponent
field of `ub`, which `normal_branch` shows to be within one step when `|G| ≥ 2 ^ -1022 (1 + 2 ^ -50)`:
the exponent field of `ub` then exceeds `E` (`mag_upper`).  For a subnormal result it adds
`th = ±2 ^ (E - 1022)` to `rh` first and clears the exponent field of `ub`, which gives
`(ub - th)/2 ^ E` while `ub` stays in the binade of `th`; `sub_branch` shows that this holds when
`|G| ≤ 2 ^ -1022 (1 - 2 ^ -48)`, with the nearest rounding of `ub` for the lower end
(`mag_lower`), and that the result is within one step.
-/

namespace Verified.Examples.TgammaRefl6
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaBits TgammaRefl3

set_option exponentiation.threshold 4096

/-- A word with exponent field at most `F ≥ 1` is below `2 ^ (F - 1022) (1 - 2 ^ -53)`. -/
theorem mag_upper (w : UInt64) (F : ℕ) (hf : Wasm.IEEE64.exponent w ≤ F) (hF : 1 ≤ F) :
    |value w| ≤ 2 ^ F / 2 ^ 1022 * (1 - 1 / 2 ^ 53) := by
  have hm := F64Sterbenz.magnitude_lt w
  obtain ⟨q, hq⟩ := F64Sterbenz.magnitude_dvd w
  have hq53 : q < 2 ^ 53 := by
    rw [hq, mul_comm] at hm
    exact Nat.lt_of_mul_lt_mul_right hm
  have hmag : Wasm.IEEE64.scaledMagnitude w ≤ 2 ^ (F - 1) * (2 ^ 53 - 1) := by
    rw [hq]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
  have hmr : (Wasm.IEEE64.scaledMagnitude w : ℝ) ≤ 2 ^ (F - 1) * (2 ^ 53 - 1) := by
    have : ((2 ^ (F - 1) * (2 ^ 53 - 1) : ℕ) : ℝ) = 2 ^ (F - 1) * (2 ^ 53 - 1) := by
      push_cast [Nat.one_le_two_pow]
      ring
    rw [← this]
    exact_mod_cast hmag
  rw [F64RoundNearest.abs_value]
  have hF2 : (2 : ℝ) ^ F = 2 ^ (F - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [hF2]
  have : (2 : ℝ) ^ (F - 1) * 2 / 2 ^ 1022 * (1 - 1 / 2 ^ 53) =
      2 ^ (F - 1) * (2 ^ 53 - 1) / 2 ^ 1074 := by
    field_simp
  rw [this]
  exact div_le_div_of_nonneg_right hmr (by positivity)

/-- A normal word is at least `2 ^ (F - 1023)` for its exponent field `F`. -/
theorem mag_lower (w : UInt64) (h1 : 1 ≤ Wasm.IEEE64.exponent w) :
    2 ^ Wasm.IEEE64.exponent w / 2 ^ 1023 ≤ |value w| := by
  rw [F64RoundNearest.abs_value]
  have hm : 2 ^ 52 * 2 ^ (Wasm.IEEE64.exponent w - 1) ≤ Wasm.IEEE64.scaledMagnitude w := by
    have h2 : (Wasm.IEEE64.exponent w == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [Wasm.IEEE64.scaledMagnitude]
    rw [h2]
    simp only [Bool.false_eq_true, ite_false]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hmr : (2 : ℝ) ^ 52 * 2 ^ (Wasm.IEEE64.exponent w - 1) ≤ Wasm.IEEE64.scaledMagnitude w := by
    exact_mod_cast hm
  have hF2 : (2 : ℝ) ^ Wasm.IEEE64.exponent w = 2 ^ (Wasm.IEEE64.exponent w - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [hF2, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hmr (by positivity : (0 : ℝ) ≤ 2 ^ 1023)
  have h3 : (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1023 / 2 := by norm_num
  rw [h3]
  linarith

/-- **A normal result** of the path below `-3`. -/
theorem normal_branch (rh rl eps acc : Float) (E : ℕ) (G : ℝ) (hrhf : Finite rh.toBits)
    (hrlf : Finite rl.toBits) (hepsf : Finite eps.toBits) (hE1 : 1 ≤ E)
    (hG0 : G ≠ 0) (hGt : |G| < 2 ^ 1021) (hrhb : |value rh.toBits| ≤ 2 ^ 60)
    (hR : |value rh.toBits + value rl.toBits - G * 2 ^ E| ≤ 11 * |G * 2 ^ E| / 2 ^ 60)
    (hrl : |value rl.toBits| ≤ |value rh.toBits| / 2 ^ 32)
    (heps : |value eps.toBits| ≤ |value rh.toBits| / 2 ^ 63)
    (hbig : 2 ^ E / 2 ^ 1022 * (1 + 1 / 2 ^ 50) ≤ |G * 2 ^ E|)
    (hacc : F64SignedRounding.WithinSteps 1 G acc.toBits) :
    F64SignedRounding.WithinSteps 1 G
      (if (rh + (rl + eps) != rh + (rl - eps)) = true then acc
        else Float.ofBits ((rh + (rl + eps)).toBits - (UInt64.ofNat E <<< 52))).toBits := by
  by_cases hc : (rh + (rl + eps) != rh + (rl - eps)) = true
  · rw [ite_eq_left hc]; exact hacc
  rw [ite_eq_right hc]
  have hP : (0 : ℝ) < 2 ^ E := by positivity
  obtain ⟨Gs, hGs⟩ : ∃ Gs, Gs = G * 2 ^ E := ⟨_, rfl⟩
  rw [← hGs] at hR hbig
  have hGsa : |Gs| = |G| * 2 ^ E := by rw [hGs, abs_mul, abs_of_pos hP]
  -- `|rh| ≤ |Gs| (1 + 2 ^ -31)`
  have hrhG : |value rh.toBits| ≤ |Gs| * (1 + 1 / 2 ^ 31) := by
    have h1 := abs_sub_abs_le_abs_sub (value rh.toBits + value rl.toBits) Gs
    have h2 := abs_add_le (value rh.toBits + value rl.toBits) (-value rl.toBits)
    rw [add_neg_cancel_right, abs_neg] at h2
    linarith
  -- `t = rl + eps` and `ub = rh + t`
  have ht := fapprox_add (fapprox_self rl hrlf) (fapprox_self eps hepsf)
    (|value rl.toBits| + |value eps.toBits|)
    (by linarith [abs_add_le (value rl.toBits) (value eps.toBits)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 60 < 2 ^ 1022)])
  have hte := ht.2
  simp only [zero_add] at hte
  have htm : |value (rl + eps).toBits| ≤ 2 * |value rh.toBits| := by
    have := abs_sub_abs_le_abs_sub (value (rl + eps).toBits) (value rl.toBits + value eps.toBits)
    have := abs_add_le (value rl.toBits) (value eps.toBits)
    have : (|value rl.toBits| + |value eps.toBits|) / 2 ^ 53 ≤ |value rh.toBits| := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg (value rh.toBits)]
    linarith
  have hu := fapprox_add (fapprox_self rh hrhf) (fapprox_self (rl + eps) ht.1)
    |value rh.toBits + value (rl + eps).toBits| (by simp)
    (by linarith [abs_add_le (value rh.toBits) (value (rl + eps).toBits),
      (by norm_num : (3 : ℝ) * 2 ^ 60 < 2 ^ 1023)])
  have hue := hu.2
  simp only [zero_add] at hue
  generalize rl + eps = t at hte htm hu hue
  generalize rh + t = ub at hu hue ⊢
  -- `S = rh + t` against `Gs`
  have hS : |value rh.toBits + value t.toBits - Gs| ≤ 12 * |Gs| / 2 ^ 60 := by
    have hsplit : value rh.toBits + value t.toBits - Gs = (value rh.toBits + value rl.toBits - Gs) +
        value eps.toBits + (value t.toBits - (value rl.toBits + value eps.toBits)) := by ring
    rw [hsplit]
    have a1 := abs_add_le (value rh.toBits + value rl.toBits - Gs + value eps.toBits)
      (value t.toBits - (value rl.toBits + value eps.toBits))
    have a2 := abs_add_le (value rh.toBits + value rl.toBits - Gs) (value eps.toBits)
    linarith
  have hub : |value ub.toBits - Gs| ≤ 9 / 8 / 2 ^ 53 * |Gs| := by
    have h1 := abs_sub_abs_le_abs_sub (value rh.toBits + value t.toBits) Gs
    have h2 := abs_sub_le (value ub.toBits) (value rh.toBits + value t.toBits) Gs
    linarith
  -- the exponent field of `ub` exceeds `E`
  have hfe : E + 1 ≤ Wasm.IEEE64.exponent ub.toBits := by
    by_contra hcon
    have h1 := mag_upper ub.toBits E (by omega) hE1
    have h2 := abs_sub_abs_le_abs_sub Gs (value ub.toBits)
    rw [abs_sub_comm] at hub
    have hq : (0 : ℝ) < 2 ^ E / 2 ^ 1022 := by positivity
    nlinarith
  obtain ⟨hWf, hWv⟩ := scale_down ub.toBits E hu.1 hfe
  rw [TgammaWords.ofBits_bits _ hWf]
  apply within_one_abs G _ hWf hG0 hGt
  have hval : value (ub.toBits - (UInt64.ofNat E <<< 52)) - G = (value ub.toBits - Gs) / 2 ^ E := by
    rw [hGs, ← hWv]; field_simp
  rw [hval, abs_div, abs_of_pos hP, div_le_iff₀ hP]
  rw [hGsa] at hub
  linarith

/-- The sign bit of a nonzero word is the sign of its value. -/
theorem sign_iff (w : UInt64) (h : value w ≠ 0) : Wasm.IEEE64.sign w = decide (value w < 0) := by
  have hv := TgammaTop.value_sign w
  have hm : (0 : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := Nat.cast_nonneg _
  cases hs : Wasm.IEEE64.sign w
  · rw [hs] at hv
    simp only [Bool.false_eq_true, ite_false] at hv
    have : 0 ≤ value w := by rw [hv]; positivity
    exact (decide_eq_false (not_lt.mpr this)).symm
  · rw [hs] at hv
    simp only [ite_true] at hv
    have : value w ≤ 0 := by rw [hv]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact (decide_eq_true (lt_of_le_of_ne this h)).symm

/-- The value of `th`: `±2 ^ (E - 1022)` with the sign of `w`. -/
theorem th_value (w : UInt64) (E : ℕ) (hre : Wasm.IEEE64.exponent w ≤ E) (hE : E ≤ 2045) :
    CodeLib.IEEE64.Finite ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<<
        52)) &&& 0xFFF0000000000000) ∧
      value ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
        0xFFF0000000000000) = (if Wasm.IEEE64.sign w then -1 else 1) * (2 ^ E / 2 ^ 1022) := by
  obtain ⟨hs, he, hf⟩ := th_fields w E hre hE
  generalize (w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
    0xFFF0000000000000 = T at hs he hf ⊢
  refine ⟨?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [he]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [value_normal T (by omega), hs, he, hf, Nat.add_sub_cancel]
    push_cast
    rw [add_zero, show (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 by norm_num]
    field_simp

/-- The value of `ub` with its exponent field `E + 1` cleared, against `th`. -/
theorem mask_value (u w : UInt64) (E : ℕ) (hue : Wasm.IEEE64.exponent u = E + 1)
    (hs : Wasm.IEEE64.sign u = Wasm.IEEE64.sign w) :
    CodeLib.IEEE64.Finite (u &&& 0x800FFFFFFFFFFFFF) ∧ Wasm.IEEE64.sign (u &&& 0x800FFFFFFFFFFFFF) = Wasm.IEEE64.sign w ∧
      value (u &&& 0x800FFFFFFFFFFFFF) * 2 ^ E =
        value u - (if Wasm.IEEE64.sign w then -1 else 1) * (2 ^ E / 2 ^ 1022) := by
  obtain ⟨ms, me, mf⟩ := mask_fields u
  refine ⟨?_, by rw [ms, hs], ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [me]
    decide
  · rw [value_sub _ me, value_normal u (by omega), ms, mf, hue, Nat.add_sub_cancel, hs]
    rw [show (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 by norm_num]
    split_ifs <;> field_simp <;> ring

end Verified.Examples.TgammaRefl6
