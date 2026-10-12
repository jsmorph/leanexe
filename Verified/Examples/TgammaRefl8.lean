import Verified.Examples.TgammaRefl7

/-!
The tail of the path of `tgammaWith` below `-3`, after the quotient `rh + rl` with the sign of
`Γ x`: `eps`, the choice between the normal and the subnormal result, and the result word.
`reflTail` writes the code with the branches as `TgammaRefl7.normPart` and `subPart`.
`tail_within` takes `rh + rl` within `11 · 2 ^ -60` of `G 2 ^ E` relative and `rh` within
`24 · 2 ^ -53`, with `|G| ≥ 2 ^ -1019` from `-170` on and the gap of `|G|` around `2 ^ -1022`
below, and shows one step in each branch.
-/

namespace Verified.Examples.TgammaRefl8
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaBits TgammaRefl3 TgammaRefl6
  TgammaRefl7 TgammaFloor

set_option exponentiation.threshold 4096

/-- The tail of `reflPath` after the sign. -/
def reflTail (dbTab accTab : Array UInt64) (x fx rh rl : Float) (e : UInt64) : Float :=
  let eps := rh * (Float.ofBits 0x3BC48AD3CAEFE280 - x * Float.ofBits 0x3B661019F74442B7)
  if fx ≥ -170.0 then normPart (accurate accTab dbTab x) rh rl eps e
  else if nonPositive (((rh.toBits >>> 52) &&& 0x7ff) - e) then
    subPart (accurate accTab dbTab x) rh rl eps e
  else normPart (accurate accTab dbTab x) rh rl eps e

theorem refl_gen (dbTab accTab logTab sinTab expTab asymTab : Array UInt64) (x : Float) :
    TgammaBranches.reflPath dbTab accTab logTab sinTab expTab asymTab x =
      (let fx := floorF x
       let (lh, ll) := fastTwoSum (-x) 1.0
       let (lh, ll) := asLgammaAsym logTab asymTab lh ll
       let (lh, ll, e) := asExpd expTab lh ll
       let dx := x - fx
       let (sh, sl) := asSinpid sinTab dx
       let (lh, ll) := mulDD sh sl lh ll
       let pih := Float.ofBits 0x400921FB54442D18
       let pil := Float.ofBits 0x3CA1A62633145C07
       let rcp := 1.0 / lh
       let rh := rcp * pih
       let rl := rcp * (pil - ll * rh - Fma.fma rh lh (-pih))
       let odd := (-fx).toUInt64 &&& 1 == 1
       reflTail dbTab accTab x fx (if odd then -rh else rh) (if odd then -rl else rl) e) := rfl

theorem float_le_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a ≤ b ↔ value a.toBits ≤ value b.toBits := by
  rw [F64Bits.le_iff]
  unfold Wasm.IEEE64.le
  rw [not_nan_of_finite ha, not_nan_of_finite hb, Bool.false_or, ite_eq_right Bool.false_ne_true,
    decide_eq_true_iff]
  unfold value
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem m170 : Finite (-170.0 : Float).toBits ∧ value (-170.0 : Float).toBits = -170 := by
  have hb : (170.0 : Float).toBits = 0x4065400000000000 := rfl
  have hf : Finite (170.0 : Float).toBits := by rw [hb]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value (170.0 : Float).toBits = 170 := by
    rw [hb, TgammaSpecial.lit_value _ 170 (by decide +kernel)]
    norm_num
  obtain ⟨h1, h2⟩ := neg_float _ hf
  exact ⟨h1, by rw [h2, hv]⟩

/-- The magnitude of a rounded difference. -/
theorem mag_sub (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℝ)
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A + B ≤ 1) :
    Finite (a - b).toBits ∧ |value (a - b).toBits| ≤ (A + B) * (1 + 1 / 2 ^ 53) := by
  have hs := (abs_sub (value a.toBits) (value b.toBits)).trans (add_le_add hA hB)
  have h := fapprox_sub (fapprox_self a ha) (fapprox_self b hb) (A + B) (by linarith)
    (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)])
  refine ⟨h.1, ?_⟩
  have hm := Approx.mag h
  linarith

/-- `eps = rh (c3 - x c4)` of the path below `-3` is below `|rh|/2 ^ 63`. -/
theorem eps_refl (rh x : Float) (hrh : Finite rh.toBits) (hx : Finite x.toBits)
    (hr1 : 1 ≤ |value rh.toBits|) (hr2 : |value rh.toBits| ≤ 2 ^ 60)
    (hxa : |value x.toBits| ≤ 184) :
    Finite (rh * (Float.ofBits 0x3BC48AD3CAEFE280 - x * Float.ofBits 0x3B661019F74442B7)).toBits ∧
      |value (rh * (Float.ofBits 0x3BC48AD3CAEFE280 -
        x * Float.ofBits 0x3B661019F74442B7)).toBits| ≤ |value rh.toBits| / 2 ^ 63 := by
  have hw1 : Wasm.IEEE64.isFinite 0x3BC48AD3CAEFE280 = true := by decide
  have hw2 : Wasm.IEEE64.isFinite 0x3B661019F74442B7 = true := by decide
  have hc1v : |value (Float.ofBits 0x3BC48AD3CAEFE280).toBits| ≤ 9 / 10 ^ 21 := by
    rw [TgammaWords.ofBits_bits _ hw1]
    have := abs_value_le 0x3BC48AD3CAEFE280 (9 / 10 ^ 21) (by decide +kernel)
    push_cast at this
    exact this
  have hc2v : |value (Float.ofBits 0x3B661019F74442B7).toBits| ≤ 15 / 10 ^ 23 := by
    rw [TgammaWords.ofBits_bits _ hw2]
    have := abs_value_le 0x3B661019F74442B7 (15 / 10 ^ 23) (by decide +kernel)
    push_cast at this
    exact this
  obtain ⟨hm1f, hm1⟩ := TgammaLarge.mag_mul x _ hx (TgammaWords.ofBits_finite _ hw2) 184
    (15 / 10 ^ 23) hxa hc2v (by norm_num)
  obtain ⟨hs1f, hs1⟩ := mag_sub _ _ (TgammaWords.ofBits_finite _ hw1) hm1f (9 / 10 ^ 21)
    (28 / 10 ^ 21) hc1v
    (by linarith [(by norm_num : (184 : ℝ) * (15 / 10 ^ 23) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      28 / 10 ^ 21)]) (by norm_num)
  obtain ⟨hepsf, heps⟩ := TgammaLarge.mag_mul rh _ hrh hs1f |value rh.toBits| (1 / 2 ^ 64) le_rfl
    (by linarith [(by norm_num : (9 / 10 ^ 21 + 28 / 10 ^ 21 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 1 / 2 ^ 64)])
    (by linarith)
  refine ⟨hepsf, ?_⟩
  have : (1 : ℝ) / 2 ^ 1075 ≤ |value rh.toBits| * (1 / 2 ^ 63 - (1 / 2 ^ 64) * (1 + 1 / 2 ^ 53)) := by
    have h3 : (1 : ℝ) / 2 ^ 1075 ≤ 1 * (1 / 2 ^ 63 - (1 / 2 ^ 64) * (1 + 1 / 2 ^ 53)) := by norm_num
    have h4 : (0 : ℝ) ≤ 1 / 2 ^ 63 - (1 / 2 ^ 64) * (1 + 1 / 2 ^ 53) := by norm_num
    have := mul_le_mul_of_nonneg_right hr1 h4
    linarith
  linarith

/-- **The tail** of the path below `-3`: one step in each branch. -/
theorem tail_within (dbTab accTab : Array UInt64) (x fx rh rl : Float) (E : ℕ) (G : ℝ)
    (hx : Finite x.toBits) (hxa : |value x.toBits| ≤ 184)
    (hff : Finite fx.toBits) (hrhf : Finite rh.toBits) (hrlf : Finite rl.toBits)
    (hE1 : 1 ≤ E) (hE : E ≤ 1500) (hG0 : G ≠ 0) (hGt : |G| < 2 ^ 1021)
    (hr1 : 1 ≤ |value rh.toBits|) (hr2 : |value rh.toBits| ≤ 2 ^ 60)
    (hR : |value rh.toBits + value rl.toBits - G * 2 ^ E| ≤ 11 * |G * 2 ^ E| / 2 ^ 60)
    (hrhT : |value rh.toBits - G * 2 ^ E| ≤ 24 * |G * 2 ^ E| / 2 ^ 53)
    (hrl : |value rl.toBits| ≤ |value rh.toBits| / 2 ^ 32)
    (hbig : -170 ≤ value fx.toBits → 1 / 2 ^ 1019 ≤ |G|)
    (hgap : value fx.toBits < -170 →
      |G| ≤ 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) ∨ 1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ |G|)
    (hacc : F64SignedRounding.WithinSteps 1 G (accurate accTab dbTab x).toBits) :
    F64SignedRounding.WithinSteps 1 G (reflTail dbTab accTab x fx rh rl (UInt64.ofNat E)).toBits := by
  unfold reflTail
  dsimp only
  obtain ⟨hepsf, heps⟩ := eps_refl rh x hrhf hx hr1 hr2 hxa
  generalize rh * (Float.ofBits 0x3BC48AD3CAEFE280 - x * Float.ofBits 0x3B661019F74442B7) = eps
    at hepsf heps ⊢
  have hP : (0 : ℝ) < 2 ^ E := by positivity
  have hGPa : |G * 2 ^ E| = |G| * 2 ^ E := by rw [abs_mul, abs_of_pos hP]
  rw [hGPa] at hR hrhT
  have hrup : |value rh.toBits| ≤ |G| * 2 ^ E * (1 + 24 / 2 ^ 53) := by
    have := abs_sub_abs_le_abs_sub (value rh.toBits) (G * 2 ^ E)
    rw [hGPa] at this
    linarith
  have hrlo : |G| * 2 ^ E * (1 - 24 / 2 ^ 53) ≤ |value rh.toBits| := by
    have := abs_sub_abs_le_abs_sub (G * 2 ^ E) (value rh.toBits)
    rw [hGPa, abs_sub_comm] at this
    linarith
  obtain ⟨h170f, h170v⟩ := m170
  by_cases hf : fx ≥ -170.0
  · rw [ite_eq_left hf]
    have hfv : -170 ≤ value fx.toBits := by
      have := (float_le_iff _ _ h170f hff).mp hf
      rw [h170v] at this
      exact this
    apply normal_branch rh rl eps _ E G hrhf hrlf hepsf hE1 hG0 hGt hr2 (by rw [hGPa]; exact hR)
      hrl heps _ hacc
    rw [hGPa]
    have := mul_le_mul_of_nonneg_right (hbig hfv) hP.le
    have h2 : (2 : ℝ) ^ E / 2 ^ 1022 * (1 + 1 / 2 ^ 50) ≤ 1 / 2 ^ 1019 * 2 ^ E := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ 2 ^ E := hP.le
      nlinarith
    linarith
  · rw [ite_eq_right hf]
    have hfv : value fx.toBits < -170 := by
      by_contra hc
      rw [not_lt] at hc
      exact hf ((float_le_iff _ _ h170f hff).mpr (by rw [h170v]; exact hc))
    have hg := hgap hfv
    have hexp : Wasm.IEEE64.exponent rh.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    rw [field_eq, nonPositive_sub _ _ (by omega) (by omega)]
    by_cases hre : Wasm.IEEE64.exponent rh.toBits ≤ E
    · rw [decide_eq_true hre, ite_eq_left rfl]
      apply sub_branch rh rl eps _ E G hrhf hrlf hepsf hE1 hE hG0 (by rw [hGPa]; exact hR) hrl heps
        hre _ hacc
      rw [hGPa]
      have hmu := mag_upper rh.toBits E hre hE1
      rcases hg with hs | hb
      · have := mul_le_mul_of_nonneg_right hs hP.le
        have h2 : 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) * 2 ^ E = (2 : ℝ) ^ E / 2 ^ 1022 * (1 - 1 / 2 ^ 48) := by
          ring
        linarith
      · exfalso
        have := mul_le_mul_of_nonneg_right hb hP.le
        have h2 : 1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) * 2 ^ E = (2 : ℝ) ^ E / 2 ^ 1022 * (1 + 1 / 2 ^ 48) := by
          ring
        have hq : (0 : ℝ) < 2 ^ E / 2 ^ 1022 := by positivity
        nlinarith
    · rw [decide_eq_false hre, ite_eq_right (by simp)]
      apply normal_branch rh rl eps _ E G hrhf hrlf hepsf hE1 hG0 hGt hr2 (by rw [hGPa]; exact hR)
        hrl heps _ hacc
      rw [hGPa]
      have hml := mag_lower rh.toBits (by omega)
      have h2 : (2 : ℝ) ^ (E + 1) ≤ 2 ^ Wasm.IEEE64.exponent rh.toBits :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ (E + 1) / 2 ^ 1023 = 2 ^ E / 2 ^ 1022 := by
        rw [pow_succ]; field_simp
      have h4 : (2 : ℝ) ^ (E + 1) / 2 ^ 1023 ≤ 2 ^ Wasm.IEEE64.exponent rh.toBits / 2 ^ 1023 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
      have hq : (0 : ℝ) < 2 ^ E / 2 ^ 1022 := by positivity
      rcases hg with hs | hb
      · exfalso
        have := mul_le_mul_of_nonneg_right hs hP.le
        have h5 : 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) * 2 ^ E = (2 : ℝ) ^ E / 2 ^ 1022 * (1 - 1 / 2 ^ 48) := by
          ring
        nlinarith
      · have := mul_le_mul_of_nonneg_right hb hP.le
        have h5 : 1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) * 2 ^ E = (2 : ℝ) ^ E / 2 ^ 1022 * (1 + 1 / 2 ^ 48) := by
          ring
        nlinarith

#print axioms tail_within
#print axioms m170
#print axioms eps_refl

end Verified.Examples.TgammaRefl8
