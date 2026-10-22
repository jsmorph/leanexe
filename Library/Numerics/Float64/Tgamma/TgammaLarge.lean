import Library.Numerics.Float64.Tgamma.TgammaAsym6
import Library.Numerics.Float64.Tgamma.TgammaExpdSpec
import Library.Numerics.Float64.Tgamma.TgammaBranches
import LeanExe.ProofKit.F64PositiveOrder
import LeanExe.ProofKit.GammaThresholds

/-!
The path of `tgammaWith` from `4` to the overflow threshold `t0 = 0x1.573fae561f648p+7`:
`asLgammaAsym` gives `log Γ x` within `2 ^ -60`, `asExpd` its exponential as `(h + l) 2 ^ E`
within `2 ^ -59`, and the code rounds `h + (l + eps)` and adds `E` to the exponent field of the
result.  `scale_word` gives the value of that word, `ub 2 ^ E`, while the exponent field stays
below `2047`, which `field_lower` reduces to `ub 2 ^ E < 2 ^ 1024`.  That bound needs `Γ` below
`2 ^ 1024 (1 - 2 ^ -50)` at the predecessor of `t0`, the hypothesis `GammaBelowT0` that track `erf`
proves.  The result lies within `1.05` units of roundoff of `Γ x` relative, so it is within one
step (`largePath_within`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLarge
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaWords

set_option exponentiation.threshold 4096

/-- `Γ` at the double below `t0`, with the margin that keeps the large path's exponent field
below `2047`. -/
def GammaBelowT0 : Prop :=
  Real.Gamma (PolyBound.ratOfWord 0x406573FAE561F647 : ℝ) ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50)

/-- A positive finite double below `t0` is at most its predecessor. -/
theorem below_t0 (x : Float) (hx : Finite x.toBits) (hpos : 0 < value x.toBits)
    (ht : value x.toBits < (GammaThresholds.t0 : ℝ)) :
    value x.toBits ≤ (PolyBound.ratOfWord 0x406573FAE561F647 : ℝ) := by
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  have hxn : x.toBits.toNat < 2 ^ 63 :=
    (F64PositiveOrder.positive_finite_encoding x.toBits hx hpos).trans hlim
  have h8 : value (0x406573FAE561F648 : UInt64) = (GammaThresholds.t0 : ℝ) := by
    rw [← PolyBound.ratOfWord_cast, GammaThresholds.t0_word]
  rw [PolyBound.ratOfWord_cast, F64PositiveOrder.value_le_iff hxn (by decide)]
  by_contra hc
  have h1 : (0x406573FAE561F648 : UInt64).toNat ≤ x.toBits.toNat := by
    have : (0x406573FAE561F647 : UInt64).toNat + 1 = (0x406573FAE561F648 : UInt64).toNat := by
      decide
    omega
  have h2 := (F64PositiveOrder.value_le_iff (by decide) hxn).mpr h1
  rw [h8] at h2
  linarith

/-- Adding `E` to the exponent field of a positive normal word multiplies its value by `2 ^ E`. -/
theorem scale_word (w : UInt64) (E : ℕ) (hw : w.toNat < 2 ^ 63) (he1 : 2 ^ 52 ≤ w.toNat)
    (hE : w.toNat / 2 ^ 52 + E ≤ 2046) :
    Finite (w + (UInt64.ofNat E <<< 52)) ∧
      value (w + (UInt64.ofNat E <<< 52)) = value w * 2 ^ E := by
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hshift : (UInt64.ofNat E <<< 52).toNat = E * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (by omega)]
    have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [h52, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (w + (UInt64.ofNat E <<< 52)).toNat = w.toNat + E * 2 ^ 52 := by
    rw [UInt64.toNat_add, hshift]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : Wasm.IEEE64.exponent (w + (UInt64.ofNat E <<< 52)) = w.toNat / 2 ^ 52 + E := by
    unfold Wasm.IEEE64.exponent
    rw [hsum]
    omega
  have hex0 : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent
    omega
  have hfr : Wasm.IEEE64.fraction (w + (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.fraction w := by
    unfold Wasm.IEEE64.fraction
    rw [hsum]
    omega
  have hsg : Wasm.IEEE64.sign (w + (UInt64.ofNat E <<< 52)) = false := by
    unfold Wasm.IEEE64.sign
    rw [hsum]
    simp only [decide_eq_false_iff_not, not_le]
    omega
  have hsg0 : Wasm.IEEE64.sign w = false := by
    unfold Wasm.IEEE64.sign
    simp only [decide_eq_false_iff_not, not_le]
    omega
  refine ⟨?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hex]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [TgammaTop.value_sign, TgammaTop.value_sign, hsg, hsg0]
    simp only [Bool.false_eq_true, ite_false, Wasm.IEEE64.scaledMagnitude, hex, hex0, hfr]
    have h1 : (w.toNat / 2 ^ 52 + E == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    have h2 : (w.toNat / 2 ^ 52 == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    rw [h1, h2]
    simp only [Bool.false_eq_true, ite_false]
    rw [show w.toNat / 2 ^ 52 + E - 1 = (w.toNat / 2 ^ 52 - 1) + E by omega, pow_add]
    push_cast
    ring

/-- A positive normal word is at least `2 ^ (f - 1023)` for its exponent field `f`. -/
theorem field_lower (w : UInt64) (hw : w.toNat < 2 ^ 63) (he1 : 2 ^ 52 ≤ w.toNat) :
    (2 : ℝ) ^ (w.toNat / 2 ^ 52) ≤ value w * 2 ^ 1023 := by
  have hex0 : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent
    omega
  have hsg0 : Wasm.IEEE64.sign w = false := by
    unfold Wasm.IEEE64.sign
    simp only [decide_eq_false_iff_not, not_le]
    omega
  rw [TgammaTop.value_sign, hsg0]
  simp only [Bool.false_eq_true, ite_false, Wasm.IEEE64.scaledMagnitude, hex0]
  have h2 : (w.toNat / 2 ^ 52 == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  rw [h2]
  simp only [Bool.false_eq_true, ite_false]
  obtain ⟨k, hk⟩ : ∃ k, w.toNat / 2 ^ 52 = k + 1 := ⟨w.toNat / 2 ^ 52 - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  push_cast
  have hf : (0 : ℝ) ≤ (Wasm.IEEE64.fraction w : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [pow_succ (2 : ℝ) k, div_mul_eq_mul_div, mul_div_assoc,
    show (2 : ℝ) ^ 1023 / 2 ^ 1074 = 1 / 2 ^ 51 by norm_num]
  nlinarith

/-- The magnitude of a rounded product. -/
theorem mag_mul (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℝ)
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A * B ≤ 1) :
    Finite (a * b).toBits ∧ |value (a * b).toBits| ≤ A * B * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have h := fapprox_mul (fapprox_self a ha) (fapprox_self b hb) A B hA hB (A * B)
    (by simp) (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1022)])
  refine ⟨h.1, ?_⟩
  have hm := Approx.mag h
  rw [abs_mul] at hm
  have : |value a.toBits| * |value b.toBits| ≤ A * B := mul_le_mul hA hB (abs_nonneg _) hA0
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hm
  linarith

/-- The magnitude of a rounded sum. -/
theorem mag_add (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℝ)
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A + B ≤ 1) :
    Finite (a + b).toBits ∧ |value (a + b).toBits| ≤ (A + B) * (1 + 1 / 2 ^ 53) := by
  have hs := (abs_add_le (value a.toBits) (value b.toBits)).trans (add_le_add hA hB)
  have h := fapprox_add (fapprox_self a ha) (fapprox_self b hb) (A + B) (by linarith)
    (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)])
  refine ⟨h.1, ?_⟩
  have hm := Approx.mag h
  linarith

/-- `eps = h (c1 + x c2)` of the large path is below `2 ^ -62`. -/
theorem eps_bound (h x : Float) (hh : Finite h.toBits) (hx : Finite x.toBits)
    (hha : |value h.toBits| ≤ 5 / 2) (hxa : |value x.toBits| ≤ 172) :
    Finite (h * (Float.ofBits 0x3BA2E3B40A0E9B4F + x * Float.ofBits 0x3B6BCE27BCE24D11)).toBits ∧
      |value (h * (Float.ofBits 0x3BA2E3B40A0E9B4F +
        x * Float.ofBits 0x3B6BCE27BCE24D11)).toBits| ≤ 1 / 2 ^ 62 := by
  have hw1 : Wasm.IEEE64.isFinite 0x3BA2E3B40A0E9B4F = true := by decide
  have hw2 : Wasm.IEEE64.isFinite 0x3B6BCE27BCE24D11 = true := by decide
  have hc1v : |value (Float.ofBits 0x3BA2E3B40A0E9B4F).toBits| ≤ 1 / 2 ^ 68 := by
    rw [ofBits_bits _ hw1]
    have := abs_value_le 0x3BA2E3B40A0E9B4F (1 / 2 ^ 68) (by decide +kernel)
    push_cast at this
    exact this
  have hc2v : |value (Float.ofBits 0x3B6BCE27BCE24D11).toBits| ≤ 1 / 2 ^ 72 := by
    rw [ofBits_bits _ hw2]
    have := abs_value_le 0x3B6BCE27BCE24D11 (1 / 2 ^ 72) (by decide +kernel)
    push_cast at this
    exact this
  obtain ⟨hm1f, hm1⟩ := mag_mul x _ hx (ofBits_finite _ hw2) 172 (1 / 2 ^ 72) hxa hc2v
    (by norm_num)
  obtain ⟨hs1f, hs1⟩ := mag_add _ _ (ofBits_finite _ hw1) hm1f (1 / 2 ^ 68) (1 / 2 ^ 64) hc1v
    (by linarith [(by norm_num : (172 : ℝ) * (1 / 2 ^ 72) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 64)]) (by norm_num)
  obtain ⟨hepsf, heps⟩ := mag_mul h _ hh hs1f (5 / 2)
    ((1 / 2 ^ 68 + 1 / 2 ^ 64) * (1 + 1 / 2 ^ 53)) hha hs1 (by norm_num)
  refine ⟨hepsf, ?_⟩
  linarith [(by norm_num : (5 / 2 : ℝ) * ((1 / 2 ^ 68 + 1 / 2 ^ 64) * (1 + 1 / 2 ^ 53)) *
    (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 62)]

/-- The real error analysis of the large path: `Γ x = G`, `log Γ x ≈ Y`, `exp Y ≈ (h + l) P` with
`P = 2 ^ E`, the sum `t ≈ l + eps`, and the rounded `U ≈ h + t`. -/
theorem large_bound (G Y P vh vl veps vt U : ℝ) (hGpos : 0 < G)
    (hGtop : G ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50)) (hP0 : 0 < P) (hLe : |Y - Real.log G| ≤ 1 / 2 ^ 60)
    (hex : |(vh + vl) * P - Real.exp Y| ≤ Real.exp Y / 2 ^ 59) (hh1 : 1 / 2 ≤ vh)
    (hl2 : |vl| ≤ 1 / 2 ^ 45) (heps : |veps| ≤ 1 / 2 ^ 62)
    (hte : |vt - (vl + veps)| ≤ 1 / 2 ^ 44 / 2 ^ 53) (hube : |U - (vh + vt)| ≤ |vh + vt| / 2 ^ 53) :
    |U * P - G| ≤ 21 / 20 / 2 ^ 53 * G ∧ U * P < 2 ^ 1024 ∧ 2 / 5 ≤ U := by
  have hEG : |Real.exp Y - G| ≤ G / 2 ^ 59 := by
    have hd : |Y - Real.log G| ≤ 1 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]
    have h1 := Real.abs_exp_sub_one_le hd
    have hEY : Real.exp Y = G * Real.exp (Y - Real.log G) := by
      rw [Real.exp_sub, Real.exp_log hGpos]
      field_simp
    rw [hEY, show G * Real.exp (Y - Real.log G) - G = G * (Real.exp (Y - Real.log G) - 1) by ring,
      abs_mul, abs_of_pos hGpos]
    calc G * |Real.exp (Y - Real.log G) - 1| ≤ G * (2 * (1 / 2 ^ 60)) := by
          gcongr
          linarith
      _ = G / 2 ^ 59 := by ring
  obtain ⟨A, hA⟩ : ∃ A, A = (vh + vl) * P := ⟨_, rfl⟩
  rw [← hA] at hex
  have hAG : |A - G| ≤ 5 * G / 2 ^ 60 := by
    have h1 := abs_sub_le A (Real.exp Y) G
    have h2 : Real.exp Y ≤ G + G / 2 ^ 59 := by linarith [(abs_le.mp hEG).2]
    linarith
  have hPG : P ≤ 3 * G := by
    have h1 : (1 / 2 - 1 / 2 ^ 45) * P ≤ A := by
      rw [hA]
      exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hl2).1]) hP0.le
    linarith [(abs_le.mp hAG).2]
  obtain ⟨S, hSd⟩ : ∃ S, S = vh + vt := ⟨_, rfl⟩
  rw [← hSd] at hube
  have hS1 : |S - (vh + vl)| ≤ 1 / 2 ^ 62 + 1 / 2 ^ 97 := by
    rw [hSd, show vh + vt - (vh + vl) = (vt - (vl + veps)) + veps by ring]
    have := abs_add_le (vt - (vl + veps)) veps
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 / 2 ^ 53 = 1 / 2 ^ 97)]
  have hSA : |S * P - A| ≤ (1 / 2 ^ 62 + 1 / 2 ^ 97) * P := by
    rw [hA, ← sub_mul, abs_mul, abs_of_pos hP0]
    exact mul_le_mul_of_nonneg_right hS1 hP0.le
  have hSP : |S| * P ≤ G * (1 + 1 / 2 ^ 56) := by
    have h1 : |S| * P = |S * P| := by rw [abs_mul, abs_of_pos hP0]
    have h2 := abs_sub_abs_le_abs_sub (S * P) A
    have h3 : |A| ≤ G + 5 * G / 2 ^ 60 := by
      have := abs_sub_abs_le_abs_sub A G
      rw [abs_of_pos hGpos] at this
      linarith
    have h4 : (1 / 2 ^ 62 + 1 / 2 ^ 97) * P ≤ (1 / 2 ^ 62 + 1 / 2 ^ 97) * (3 * G) :=
      mul_le_mul_of_nonneg_left hPG (by norm_num)
    linarith
  have hUS : |U * P - S * P| ≤ |S| * P / 2 ^ 53 := by
    rw [← sub_mul, abs_mul, abs_of_pos hP0]
    calc |U - S| * P ≤ |S| / 2 ^ 53 * P := mul_le_mul_of_nonneg_right hube hP0.le
      _ = |S| * P / 2 ^ 53 := by ring
  have hUG : |U * P - G| ≤ 21 / 20 / 2 ^ 53 * G := by
    have h1 := abs_sub_le (U * P) (S * P) A
    have h2 := abs_sub_le (U * P) A G
    have h3 : (1 / 2 ^ 62 + 1 / 2 ^ 97) * P ≤ (1 / 2 ^ 62 + 1 / 2 ^ 97) * (3 * G) :=
      mul_le_mul_of_nonneg_left hPG (by norm_num)
    have h4 : |S| * P / 2 ^ 53 ≤ G * (1 + 1 / 2 ^ 56) / 2 ^ 53 :=
      div_le_div_of_nonneg_right hSP (by norm_num)
    linarith
  refine ⟨hUG, ?_, ?_⟩
  · have := (abs_le.mp hUG).2
    linarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 - 1 / 2 ^ 50) * (1 + 21 / 20 / 2 ^ 53) < 2 ^ 1024)]
  · have hS0 : 49 / 100 ≤ S := by
      have := (abs_le.mp hS1).1
      linarith [(abs_le.mp hl2).1]
    have := (abs_le.mp hube).1
    rw [abs_of_pos (show 0 < S by linarith)] at this
    linarith

/-- The word of the large path's result: `ub` with `E` added to its exponent field. -/
theorem scale_result (ub : Float) (E : ℕ) (hubf : Finite ub.toBits)
    (hub0 : 2 / 5 ≤ value ub.toBits) (hUP : value ub.toBits * 2 ^ E < 2 ^ 1024) :
    Finite (ub.toBits + (UInt64.ofNat E <<< 52)) ∧
      value (ub.toBits + (UInt64.ofNat E <<< 52)) = value ub.toBits * 2 ^ E := by
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  have hw : ub.toBits.toNat < 2 ^ 63 :=
    (F64PositiveOrder.positive_finite_encoding ub.toBits hubf (by linarith)).trans hlim
  have he1 : 2 ^ 52 ≤ ub.toBits.toNat := by
    have hv : value (0x0010000000000000 : UInt64) = 1 / 2 ^ 1022 := by
      rw [TgammaSpecial.lit_value _ (1 / 2 ^ 1022) (by decide +kernel)]
      norm_num
    have := (F64PositiveOrder.value_le_iff (left := (0x0010000000000000 : UInt64))
      (by decide) hw).mp (by rw [hv]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1022 ≤ 2 / 5)])
    exact le_trans (by decide) this
  have hfe : ub.toBits.toNat / 2 ^ 52 + E ≤ 2046 := by
    by_contra hc'
    have h1 := field_lower ub.toBits hw he1
    have h2 : (2 : ℝ) ^ 2047 ≤ 2 ^ (ub.toBits.toNat / 2 ^ 52 + E) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at h2
    have hP0 : (0 : ℝ) < 2 ^ E := by positivity
    have h3 : (2 : ℝ) ^ (ub.toBits.toNat / 2 ^ 52) * 2 ^ E ≤ value ub.toBits * 2 ^ 1023 * 2 ^ E :=
      mul_le_mul_of_nonneg_right h1 hP0.le
    have h4 : value ub.toBits * 2 ^ 1023 * 2 ^ E < 2 ^ 1024 * 2 ^ 1023 := by
      rw [show value ub.toBits * 2 ^ 1023 * 2 ^ E = value ub.toBits * 2 ^ E * 2 ^ 1023 by ring]
      exact mul_lt_mul_of_pos_right hUP (by positivity)
    linarith [(by norm_num : (2 : ℝ) ^ 1024 * 2 ^ 1023 = 2 ^ 2047)]
  exact scale_word ub.toBits E hw he1 hfe

/-- **The path from `4` to `t0`** within one step of `Γ x`. -/
theorem largePath_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLog : TgammaAsym1.LogdSpec)
    (hS : TgammaApprox.StirlingFact) (hE : TgammaApprox.ExpFact) (hT : GammaBelowT0)
    (dbTab accTab : Array UInt64) (x : Float) (hx : Finite x.toBits) (h4 : 4 < value x.toBits)
    (ht : value x.toBits < (GammaThresholds.t0 : ℝ))
    (hacc : F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accTab dbTab x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.largePath dbTab accTab logdTable expdTable asymTable x).toBits := by
  have ht172 : (GammaThresholds.t0 : ℝ) < 172 := by
    have : GammaThresholds.t0 < 172 := by unfold GammaThresholds.t0; norm_num
    exact_mod_cast this
  -- `Γ x` from `1` to the bound below `t0`
  obtain ⟨G, hG⟩ : ∃ G, G = Real.Gamma (value x.toBits) := ⟨_, rfl⟩
  rw [← hG] at hacc ⊢
  have hGpos : 0 < G := hG ▸ Real.Gamma_pos_of_pos (by linarith)
  have hGtop : G ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50) := by
    have hp := below_t0 x hx (by linarith) ht
    rw [hG]
    exact le_trans (Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hp) hT
  have hG1 : 1 < G := by
    have := TgammaAsym6.lgamma_gt (value x.toBits) h4.le
    rw [← hG] at this
    by_contra hc
    have := Real.log_nonpos hGpos.le (not_lt.mp hc)
    linarith
  unfold TgammaBranches.largePath
  dsimp only
  -- `log Γ x`
  obtain ⟨hLf1, hLf2, hLe, hLl, hL1, hL2⟩ := TgammaAsym6.asLgammaAsym_spec hF hLog hS x 0.0 hx
    TgammaMainRed.zero_finite h4.le (by linarith) (by rw [TgammaMainRed.zero_value]; linarith)
    (by rw [TgammaMainRed.zero_value]; linarith) (by rw [TgammaMainRed.zero_value]; norm_num)
  rw [TgammaMainRed.zero_value, add_zero, ← hG] at hLe
  generalize asLgammaAsym logdTable asymTable x 0.0 = L at hLf1 hLf2 hLe hLl hL1 hL2 ⊢
  obtain ⟨lh, ll⟩ := L
  dsimp only at hLf1 hLf2 hLe hLl hL1 hL2 ⊢
  -- its exponential
  obtain ⟨E, -, he, hf1, hf2, hex, hl2, hh1, hh2⟩ :=
    TgammaExpdSpec.asExpd_spec hF hE lh ll hLf1 hLf2 hL1 hL2 hLl
  generalize asExpd expdTable lh ll = R at he hf1 hf2 hex hl2 hh1 hh2 ⊢
  obtain ⟨h, l, e⟩ := R
  dsimp only at he hf1 hf2 hex hl2 hh1 hh2 ⊢
  subst he
  -- `eps`
  obtain ⟨hepsf, heps⟩ := eps_bound h x hf1 hx (abs_le.mpr ⟨by linarith, hh2⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  generalize h * (Float.ofBits 0x3BA2E3B40A0E9B4F + x * Float.ofBits 0x3B6BCE27BCE24D11) = eps
    at hepsf heps ⊢
  -- the rounding test
  by_cases hc : (h + (l + eps) != h + (l - eps)) = true
  · rw [ite_eq_left hc]
    exact hacc
  rw [ite_eq_right hc]
  -- `t = l + eps` and `ub = h + t`
  have ht' := fapprox_add (fapprox_self l hf2) (fapprox_self eps hepsf) (1 / 2 ^ 44)
    (by linarith [abs_add_le (value l.toBits) (value eps.toBits),
      (by norm_num : (1 : ℝ) / 2 ^ 45 + 1 / 2 ^ 62 ≤ 1 / 2 ^ 44)]) (by norm_num)
  have htm : |value (l + eps).toBits| ≤ 1 := by
    have := Approx.mag ht'
    linarith [abs_add_le (value l.toBits) (value eps.toBits),
      (by norm_num : (1 : ℝ) / 2 ^ 45 + 1 / 2 ^ 62 + (0 + 0 + 1 / 2 ^ 44 / 2 ^ 53) ≤ 1)]
  have hha : |value h.toBits| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, hh2⟩
  have hub := fapprox_add (fapprox_self h hf1) (fapprox_self (l + eps) ht'.1)
    |value h.toBits + value (l + eps).toBits| (by linarith)
    (by linarith [abs_add_le (value h.toBits) (value (l + eps).toBits),
      (by norm_num : (5 / 2 : ℝ) + 1 < 2 ^ 1023)])
  have hte := ht'.2
  have hube := hub.2
  have hubf := hub.1
  simp only [zero_add, add_zero] at hte hube
  generalize l + eps = t at hte hube hubf ⊢
  generalize h + t = ub at hube hubf ⊢
  obtain ⟨hUG, hUP, hU0⟩ := large_bound G _ (2 ^ E) _ _ _ _ _ hGpos hGtop (by positivity) hLe
    hex hh1 hl2 heps hte hube
  obtain ⟨hWf, hWv⟩ := scale_result ub E hubf hU0 hUP
  rw [ofBits_bits _ hWf]
  apply F64RelativeStep.within_one_relative G _ hWf
    (by rw [abs_of_pos hGpos]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1)])
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hWv, hu, abs_of_pos hGpos]
  linarith

#print axioms below_t0
#print axioms scale_word
#print axioms field_lower
#print axioms large_bound
#print axioms scale_result
#print axioms largePath_within

end Library.Numerics.Float64.Tgamma.TgammaLarge
