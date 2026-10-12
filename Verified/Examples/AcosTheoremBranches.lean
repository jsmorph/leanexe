import Verified.Examples.AsinTheorem

/-!
The branches of `Asin.acos` as equations, the exact arguments `z = (1 + x)/2` and
`z = (1 - x)/2` of the two half-angle branches, and the identities
`arccos x = π - 2 arcsin √((1 + x)/2)` and `arccos x = 2 arcsin √((1 - x)/2)`.
-/

namespace Verified.Examples.AcosTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx AsinTheoremBranches

set_option exponentiation.threshold 4096

def piF : Float := Float.ofBits 0x400921FB54442D18

def negTail (z : Float) : Float :=
  piF - 2.0 * (z.sqrt + (Asin.asinRatio z * z.sqrt - pio2LoF))

def posTail (z : Float) : Float :=
  2.0 * (wOf z.sqrt + (Asin.asinRatio z * z.sqrt +
    (z - wOf z.sqrt * wOf z.sqrt) / (z.sqrt + wOf z.sqrt)))

theorem acos_one_eq (x : Float) (h1 : ixA x ≥ 0x3ff00000)
    (h2 : (((ixA x - 0x3ff00000) ||| lxA x) == 0) = true) :
    Asin.acos x = if x.toBits >>> 32 >>> 31 == 0 then 0.0 else piF + 2.0 * pio2LoF := by
  unfold ixA lxA at *
  simp only [Asin.acos, h1, h2, ite_true]
  rfl

theorem acos_out_eq (x : Float) (h1 : ixA x ≥ 0x3ff00000)
    (h2 : (((ixA x - 0x3ff00000) ||| lxA x) == 0) = false) :
    Asin.acos x = (x - x) / (x - x) := by
  unfold ixA lxA at *
  simp only [Asin.acos, h1, h2, ite_true, Bool.false_eq_true, ite_false]

theorem acos_tiny_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ixA x < 0x3fe00000)
    (h3 : ixA x ≤ 0x3c600000) : Asin.acos x = pio2HiF + pio2LoF := by
  unfold ixA at *
  simp only [Asin.acos, h1, h2, h3, ite_false, ite_true]
  rfl

theorem acos_small_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ixA x < 0x3fe00000)
    (h3 : ¬ ixA x ≤ 0x3c600000) :
    Asin.acos x = pio2HiF - (x - (pio2LoF - x * Asin.asinRatio (x * x))) := by
  unfold ixA at *
  simp only [Asin.acos, h1, h2, h3, ite_false, ite_true]
  rfl

theorem acos_neg_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ¬ ixA x < 0x3fe00000)
    (h3 : (x.toBits >>> 32 >>> 31 == 1) = true) : Asin.acos x = negTail ((1.0 + x) * 0.5) := by
  unfold ixA at *
  simp only [Asin.acos, h1, h2, h3, ite_false, ite_true]
  rfl

theorem acos_pos_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ¬ ixA x < 0x3fe00000)
    (h3 : (x.toBits >>> 32 >>> 31 == 1) = false) : Asin.acos x = posTail ((1.0 - x) * 0.5) := by
  unfold ixA at *
  simp only [Asin.acos, h1, h2, h3, ite_false, Bool.false_eq_true]
  rfl

/-- `u * 0.5` is exact for `2 ^ -53 ≤ u ≤ 1`. -/
theorem half_exact (u : Float) (hu : Finite u.toBits) (h1 : 1 / 2 ^ 53 ≤ value u.toBits)
    (h2 : value u.toBits ≤ 1) :
    Finite (u * 0.5).toBits ∧ value (u * 0.5).toBits = value u.toBits / 2 := by
  have hde : 2 ≤ Wasm.IEEE64.exponent u.toBits :=
    F64Exact.exponent_two_of_value _ (by
      rw [abs_of_pos (by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 53)])]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 53)])
  obtain ⟨M, hM, hMd⟩ := F64Exact.magnitude_grid u.toBits
  have hhalf : Wasm.IEEE64.scaledMagnitude (0x3FE0000000000000 : UInt64) = 1 * 2 ^ 1073 := by
    decide +kernel
  have hm := F64ExactProduct.mul_exact_scaled u.toBits 0x3FE0000000000000 hu
    (by unfold CodeLib.IEEE64.Finite; decide +kernel) M 1 (Wasm.IEEE64.exponent u.toBits - 1)
    1073 hMd hhalf (by omega) (by omega) (by
      have := F64Exact.exponent_le_of_value u.toBits (by
        rw [abs_of_pos (by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 53)])]
        linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
      omega)
  rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  refine ⟨hm.1, ?_⟩
  rw [hm.2.1, AsinTheoremHalf.half_word_value]
  ring

/-- `z = (1 - x) * 0.5` is exact for `1/2 ≤ x < 1`. -/
theorem pos_z_exact (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ≤ value x.toBits)
    (h2 : value x.toBits < 1) :
    Finite ((1.0 - x) * 0.5).toBits ∧
      value ((1.0 - x) * 0.5).toBits = (1 - value x.toBits) / 2 ∧
      1 / 2 ^ 54 ≤ (1 - value x.toBits) / 2 := by
  obtain ⟨h1f, h1v⟩ := Log1pTheoremReduce.one_float
  have hab : |value x.toBits| = value x.toBits := abs_of_pos (by linarith)
  have hge := AsinTheoremHalf.one_sub_ge x hx (by rw [hab]; exact h1) (by rw [hab]; exact h2)
  rw [hab] at hge
  have hd := F64Exact.sub_exact (1.0 : Float).toBits x.toBits h1f hx (by rw [h1v]; norm_num)
    (by linarith) (by rw [h1v]; linarith) (by rw [h1v]; linarith) (by rw [h1v]; norm_num)
    (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
  rw [h1v, ← F64Bits.toBits_sub] at hd
  have h := half_exact (1.0 - x) hd.1 (by rw [hd.2]; exact hge) (by rw [hd.2]; linarith)
  rw [hd.2] at h
  refine ⟨h.1, h.2, ?_⟩
  have : (1 : ℝ) / 2 ^ 54 = 1 / 2 ^ 53 / 2 := by norm_num
  linarith

/-- `z = (1 + x) * 0.5` is exact for `-1 < x ≤ -1/2`. -/
theorem neg_z_exact (x : Float) (hx : Finite x.toBits) (h1 : -1 < value x.toBits)
    (h2 : value x.toBits ≤ -1 / 2) :
    Finite ((1.0 + x) * 0.5).toBits ∧
      value ((1.0 + x) * 0.5).toBits = (1 + value x.toBits) / 2 ∧
      1 / 2 ^ 54 ≤ (1 + value x.toBits) / 2 := by
  obtain ⟨huf, huv, hug, -⟩ := Log1pTheoremCorr.corr_low x hx h1 h2
  have h := half_exact (1.0 + x) huf hug (by rw [huv]; linarith)
  rw [huv] at h
  refine ⟨h.1, h.2, ?_⟩
  rw [huv] at hug
  have : (1 : ℝ) / 2 ^ 54 = 1 / 2 ^ 53 / 2 := by norm_num
  linarith

theorem arccos_neg_half (a : ℝ) (h0 : -1 ≤ a) (h1 : a ≤ 1) :
    Real.arccos a = Real.pi - 2 * Real.arcsin (Real.sqrt ((1 + a) / 2)) := by
  have h := AsinTheoremHalf.arccos_half (-a) (by linarith) (by linarith)
  rw [Real.arccos_neg, sub_neg_eq_add] at h
  linarith

/-- `|arcsin a| ≤ 2 |a|`, from `sin θ ≥ 2 θ / π` on `[0, π/2]`. -/
theorem abs_arcsin_le (a : ℝ) (h : |a| ≤ 1) : |Real.arcsin a| ≤ 2 * |a| := by
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → Real.arcsin b ≤ 2 * b := by
    intro b h0 h1
    have hθ0 : 0 ≤ Real.arcsin b := Real.arcsin_nonneg.mpr h0
    have hj := Real.mul_le_sin hθ0 (Real.arcsin_le_pi_div_two b)
    rw [Real.sin_arcsin (by linarith) h1, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at hj
    have hp4 := Real.pi_lt_four
    nlinarith
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha, abs_of_nonneg (Real.arcsin_nonneg.mpr ha)]
    exact key a ha (by rw [abs_of_nonneg ha] at h; exact h)
  · have hn := key (-a) (by linarith) (by rw [abs_of_neg ha] at h; exact h)
    rw [Real.arcsin_neg] at hn
    rw [abs_of_neg ha, abs_of_nonpos (Real.arcsin_nonpos.mpr ha.le)]
    linarith

#print axioms half_exact
#print axioms pos_z_exact
#print axioms neg_z_exact
#print axioms abs_arcsin_le

end Verified.Examples.AcosTheoremBranches
