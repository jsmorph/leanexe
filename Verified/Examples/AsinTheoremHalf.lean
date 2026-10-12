import Verified.Examples.AsinTheoremSmall
import Verified.Examples.Log1pTheoremCorr
import Verified.Examples.AtanTheoremReduce
import Verified.Examples.AtanTheoremConst

/-!
The half-angle forms for `1/2 ≤ |x| ≤ 1`: `arccos a = 2 arcsin √((1 - a)/2)` for `-1 ≤ a ≤ 1`, so
`arcsin a = π/2 - 2 arcsin √((1 - a)/2)`.  The argument `t = (1 - |x|) * 0.5` of `asin` is exact:
`1 - |x|` by Sterbenz's lemma and the halving because `1 - |x|` is a multiple of `2 ^ -53`.
-/

namespace Verified.Examples.AsinTheoremHalf
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx AsinTheoremBranches

set_option exponentiation.threshold 4096

theorem arccos_half (a : ℝ) (h0 : -1 ≤ a) (h1 : a ≤ 1) :
    Real.arccos a = 2 * Real.arcsin (Real.sqrt ((1 - a) / 2)) := by
  set θ := Real.arcsin (Real.sqrt ((1 - a) / 2)) with hθ
  have hs0 : 0 ≤ Real.sqrt ((1 - a) / 2) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt ((1 - a) / 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  have hsin : Real.sin θ = Real.sqrt ((1 - a) / 2) := Real.sin_arcsin (by linarith) hs1
  have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hs0
  have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hcos : Real.cos (2 * θ) = a := by
    rw [Real.cos_two_mul, Real.cos_sq', hsin, Real.sq_sqrt (by linarith)]
    ring
  rw [← hcos, Real.arccos_cos (by linarith) (by linarith)]

theorem arcsin_half (a : ℝ) (h0 : -1 ≤ a) (h1 : a ≤ 1) :
    Real.arcsin a = Real.pi / 2 - 2 * Real.arcsin (Real.sqrt ((1 - a) / 2)) := by
  rw [Real.arcsin_eq_pi_div_two_sub_arccos, arccos_half a h0 h1]

/-- A word of magnitude in `[1/2, 1)` is a multiple of `2 ^ -53`, so `1 - |x| ≥ 2 ^ -53`. -/
theorem one_sub_ge (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1) : 1 / 2 ^ 53 ≤ 1 - |value x.toBits| := by
  have hdx : (2 : ℤ) ^ 1021 ∣ Wasm.IEEE64.scaledValue x.toBits := by
    apply Log1pTheoremCorr.scaled_dvd
    have := Log1pTheoremCorr.exponent_ge x.toBits 1022 (-1) (by norm_num) (by norm_num)
      (by norm_num; linarith)
    omega
  obtain ⟨q, hq⟩ := hdx
  have hsx := Log1pTheoremCorr.scaled_of_value x.toBits (value x.toBits) rfl
  have h3 : value x.toBits * 2 ^ 1074 = 2 ^ 1021 * (q : ℝ) := by
    rw [← hsx]
    exact_mod_cast hq
  have h4 : |(q : ℝ)| < 2 ^ 53 := by
    have h5 : |value x.toBits| * 2 ^ 1074 = 2 ^ 1021 * |(q : ℝ)| := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← abs_mul, h3, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1021)]
    nlinarith
  have h5 : |q| < (2 ^ 53 : ℤ) := by
    have : ((|q| : ℤ) : ℝ) < ((2 ^ 53 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h6 : |q| ≤ (2 ^ 53 - 1 : ℤ) := by omega
  have h7 : |(q : ℝ)| ≤ 2 ^ 53 - 1 := by
    have : ((|q| : ℤ) : ℝ) ≤ ((2 ^ 53 - 1 : ℤ) : ℝ) := by exact_mod_cast h6
    push_cast at this
    linarith
  have h8 : |value x.toBits| * 2 ^ 1074 = 2 ^ 1021 * |(q : ℝ)| := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← abs_mul, h3, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1021)]
  have h9 : |value x.toBits| ≤ (2 ^ 53 - 1) / 2 ^ 53 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : (2 ^ 53 - 1 : ℝ) / 2 ^ 53 = 1 - 1 / 2 ^ 53 := by field_simp
  linarith

theorem half_word_value : value (0x3FE0000000000000 : UInt64) = 1 / 2 := by
  rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FE0000000000000 = 1 / 2 by
    decide +kernel]
  norm_num

/-- `t = (1 - |x|) * 0.5` is exact. -/
theorem t_exact (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1) :
    Finite (tOf x).toBits ∧ value (tOf x).toBits = (1 - |value x.toBits|) / 2 := by
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  obtain ⟨h1f, h1v⟩ := Log1pTheoremReduce.one_float
  have hge := one_sub_ge x hx h1 h2
  have hd := F64Exact.sub_exact (1.0 : Float).toBits x.abs.toBits h1f haf (by rw [h1v]; norm_num)
    (by rw [hav]; linarith) (by rw [h1v, hav]; linarith) (by rw [h1v, hav]; linarith)
    (by rw [h1v]; norm_num) (by rw [hav]; linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
  rw [h1v, hav] at hd
  rw [← F64Bits.toBits_sub] at hd
  set d := (1.0 : Float) - x.abs with hdd
  -- the exponent field of `d` is at least 2
  have hde : 2 ≤ Wasm.IEEE64.exponent d.toBits :=
    F64Exact.exponent_two_of_value _ (by
      rw [hd.2, abs_of_pos (by linarith)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 53)])
  obtain ⟨M, hM, hMd⟩ := F64Exact.magnitude_grid d.toBits
  have hhalf : Wasm.IEEE64.scaledMagnitude (0x3FE0000000000000 : UInt64) = 1 * 2 ^ 1073 := by
    decide +kernel
  have hm := F64ExactProduct.mul_exact_scaled d.toBits 0x3FE0000000000000 hd.1
    (by unfold CodeLib.IEEE64.Finite; decide +kernel) M 1 (Wasm.IEEE64.exponent d.toBits - 1) 1073
    hMd hhalf (by omega) (by omega) (by
      have := F64Exact.exponent_le_of_value d.toBits (by
        rw [hd.2, abs_of_pos (by linarith)]
        linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
      omega)
  unfold tOf
  rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl, ← hdd]
  refine ⟨hm.1, ?_⟩
  rw [hm.2.1, hd.2, half_word_value]
  ring

#print axioms arcsin_half
#print axioms t_exact

end Verified.Examples.AsinTheoremHalf
