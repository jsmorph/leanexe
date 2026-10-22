import Library.Numerics.Float64.Lgamma.LgammaBranches
import Library.Numerics.Float64.Tgamma.TgammaFloor
import Library.Numerics.Float64.Tgamma.TgammaSpecial
import LeanExe.ProofKit.F64Exact
import LeanExe.ProofKit.F64PositiveSpacing
import LeanExe.ProofKit.F64PositiveOrder
import LeanExe.ProofKit.GammaThresholds
import LeanExe.ProofKit.F64WithinSelf

/-!
The exceptional values of `Lgamma.lgammaWith`, for any tables.  NaN gives the canonical NaN, and
both infinities give `+∞`, all with the sign `+1`.  The poles give `+∞`, with the sign `-1` for
`-0` and the negative integers below `0x1.754d9278b51a6p+1014` in magnitude and `+1` for `+0`, and
the negative integers from that magnitude on give `+∞` with the sign `+1`.  1 and 2 give `+0` with
the sign `+1`.  From `0x1.754d9278b51a8p+1014` on the result is `+∞`, and at the two doubles below
it the code returns the two largest finite doubles.  Each proof selects the branch with
`LgammaBranches` and evaluates the last operation on its words.  `lgamma_*_within` compare these
results with the nearest-even reference of `log |Γ x|`: exactly at 1, 2, and from the overflow
threshold on (`GammaThresholds.lgamma_overflow`), and within one step at the two largest finite
results (`GammaThresholds.lgamma_x1`, `lgamma_x2`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSpecial
open CodeLib.IEEE64 LeanExe.ProofKit Lgamma LgammaBranches Library.Numerics.Float64.Tgamma.TgammaFloor
open Library.Numerics.Float64.Tgamma (floorF roundEven)

set_option exponentiation.threshold 4096

theorem big_test (w : UInt64) :
    w <<< 1 ≥ 0xFEAEA9B24F16A34C ↔ 0x7F5754D9278B51A6 ≤ w.toNat % 2 ^ 63 := by
  rw [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
  have := w.toNat_lt
  omega

theorem inf_test (w : UInt64) :
    w <<< 1 ≥ 0xFFE0000000000000 ↔ Wasm.IEEE64.exponent w = 0x7FF := by
  rw [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft]
  simp only [Wasm.IEEE64.exponent, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
    Nat.reducePow]
  have := w.toNat_lt
  omega

theorem inf_eq_test (w : UInt64) :
    (w <<< 1 == 0xFFE0000000000000) = true ↔ w.toNat % 2 ^ 63 = 0x7FF0000000000000 := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
  have := w.toNat_lt
  omega

theorem sign_test (w : UInt64) : (w >>> 63 == 1) = true ↔ 2 ^ 63 ≤ w.toNat := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := w.toNat_lt
  omega

theorem word_ne (w c : UInt64) (h : w.toNat ≠ c.toNat) : ¬ (w == c) = true := by
  rw [beq_iff_eq]
  intro h'
  exact h (by rw [h'])

theorem float_le_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a ≤ b ↔ value a.toBits ≤ value b.toBits := by
  rw [F64Bits.le_iff]
  unfold Wasm.IEEE64.le
  rw [not_nan_of_finite ha, not_nan_of_finite hb, Bool.false_or, ite_eq_right Bool.false_ne_true,
    decide_eq_true_iff]
  unfold value
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem zero_finite : Finite (0.0 : Float).toBits := by
  rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.zero_bits]; unfold CodeLib.IEEE64.Finite; decide

/-- `floorF` of an integer-valued finite double is the double. -/
theorem floorF_int (x : Float) (hx : Finite x.toBits) (n : ℤ) (hn : value x.toBits = n) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = value x.toBits := by
  obtain ⟨hrf, ⟨R, hR⟩, hrd, -⟩ := roundEven_spec x hx
  have hRn : R = n := by
    rw [hR, hn] at hrd
    have h1 : |((R - n : ℤ) : ℝ)| ≤ 1 / 2 := by push_cast; exact hrd
    have h2 : |R - n| < 1 := by
      have : |((R - n : ℤ) : ℝ)| < 1 := lt_of_le_of_lt h1 (by norm_num)
      exact_mod_cast this
    have := abs_lt.mp h2
    omega
  have hval : value (roundEven x).toBits = value x.toBits := by rw [hR, hn, hRn]
  unfold floorF
  dsimp only
  rw [ite_eq_right (fun h => by
    have h' : x < roundEven x := h
    rw [F64UpperWord.float_lt_iff _ _ hx hrf, hval] at h'
    exact lt_irrefl _ h')]
  exact ⟨hrf, hval⟩

section
variable (logTab hTab sinTab asymTab accTab dbTab tab : Array UInt64) (x : Float)

/-- **NaN gives the canonical NaN, with the sign `+1`.** -/
theorem lgamma_nan (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits =
      Wasm.IEEE64.canonicalNaN ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  have he : Wasm.IEEE64.exponent x.toBits = 0x7FF := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have hf : Wasm.IEEE64.fraction x.toBits ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, bne_iff_ne] at h
    exact h.2
  have hx := x.toBits.toNat_lt
  have hm : 0x7FF0000000000001 ≤ x.toBits.toNat % 2 ^ 63 := by
    unfold Wasm.IEEE64.exponent at he
    unfold Wasm.IEEE64.fraction at hf
    simp only [Nat.reducePow] at *
    omega
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by omega))]
  unfold bigPath
  have hA6 : ¬ (x.toBits == 0x7F5754D9278B51A6) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have hA7 : ¬ (x.toBits == 0x7F5754D9278B51A7) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have hne : ¬ (x.toBits <<< 1 == 0xFFE0000000000000) = true := by
    rw [inf_eq_test]; omega
  rw [ite_eq_right hA6, ite_eq_right hA7, ite_eq_left ((inf_test _).mpr he), ite_eq_right hne]
  exact ⟨by rw [F64Bits.toBits_add]; exact F64Saturate.add_nan_left _ _ h, rfl⟩

theorem lgamma_inf (h : x.toBits.toNat % 2 ^ 63 = 0x7FF0000000000000) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FF0000000000000 ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  have hx := x.toBits.toNat_lt
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by omega))]
  unfold bigPath
  have hA6 : ¬ (x.toBits == 0x7F5754D9278B51A6) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have hA7 : ¬ (x.toBits == 0x7F5754D9278B51A7) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have he : Wasm.IEEE64.exponent x.toBits = 0x7FF := by
    unfold Wasm.IEEE64.exponent
    simp only [Nat.reducePow] at *
    omega
  rw [ite_eq_right hA6, ite_eq_right hA7, ite_eq_left ((inf_test _).mpr he),
    ite_eq_left ((inf_eq_test _).mpr h)]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_abs]
  apply UInt64.toNat_inj.mp
  rw [F64UpperWord.abs_toNat, h]
  rfl

/-- **The negative integers from `0x1.754d9278b51a6p+1014` in magnitude give `+∞`, with the
sign `+1`.** -/
theorem lgamma_huge_neg (hf : Finite x.toBits) (h : 0xFF5754D9278B51A6 ≤ x.toBits.toNat) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FF0000000000000 ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  have hx := x.toBits.toNat_lt
  have he : Wasm.IEEE64.exponent x.toBits ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hf
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by
    simp only [Nat.reducePow] at *; omega))]
  unfold bigPath
  have hA6 : ¬ (x.toBits == 0x7F5754D9278B51A6) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have hA7 : ¬ (x.toBits == 0x7F5754D9278B51A7) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  rw [ite_eq_right hA6, ite_eq_right hA7, ite_eq_right (fun h' => he ((inf_test _).mp h')),
    ite_eq_left ((sign_test _).mpr (by simp only [Nat.reducePow] at *; omega))]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_div]
  decide +kernel

/-- **From `0x1.754d9278b51a8p+1014` on, the result is `+∞`, with the sign `+1`.** -/
theorem lgamma_overflow (hf : Finite x.toBits) (h : 0x7F5754D9278B51A8 ≤ x.toBits.toNat)
    (hs : x.toBits.toNat < 2 ^ 63) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FF0000000000000 ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  have he : Wasm.IEEE64.exponent x.toBits ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hf
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by
    simp only [Nat.reducePow] at *; omega))]
  unfold bigPath
  have hA6 : ¬ (x.toBits == 0x7F5754D9278B51A6) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  have hA7 : ¬ (x.toBits == 0x7F5754D9278B51A7) = true := word_ne _ _ (by
    simp only [UInt64.reduceToNat, Nat.reducePow] at *; omega)
  rw [ite_eq_right hA6, ite_eq_right hA7, ite_eq_right (fun h' => he ((inf_test _).mp h')),
    ite_eq_right (fun h' => by
      have := (sign_test _).mp h'
      simp only [Nat.reducePow] at *; omega)]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_mul]
  decide +kernel

/-- **At `0x1.754d9278b51a6p+1014` the code returns `0x1.ffffffffffffep+1023`.** -/
theorem lgamma_x1 (h : x.toBits = 0x7F5754D9278B51A6) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FEFFFFFFFFFFFFE ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by rw [h]; decide))]
  unfold bigPath
  rw [ite_eq_left (by rw [h]; rfl)]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_sub]
  decide +kernel

/-- **At `0x1.754d9278b51a7p+1014` the code returns `0x1.fffffffffffffp+1023`.** -/
theorem lgamma_x2 (h : x.toBits = 0x7F5754D9278B51A7) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FEFFFFFFFFFFFFF ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  rw [lgamma_big _ _ _ _ _ _ _ x ((big_test _).mpr (by rw [h]; decide))]
  unfold bigPath
  rw [ite_eq_right (by rw [h]; decide), ite_eq_left (by rw [h]; rfl)]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_sub]
  decide +kernel

/-- **The poles below `0x1.754d9278b51a6p+1014` in magnitude give `+∞`, with the sign `-1` for
`-0` and the negative integers and `+1` for `+0`.** -/
theorem lgamma_pole_value (hf : Finite x.toBits) (hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6)
    (h0 : value x.toBits ≤ 0) (n : ℤ) (hn : value x.toBits = n) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0x7FF0000000000000 ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 =
      if x.toBits >>> 63 == 1 then -1.0 else 1.0 := by
  obtain ⟨hff, hfv⟩ := floorF_int x hf n hn
  have h2 : (floorF x == x && x ≤ 0.0) = true := by
    rw [Bool.and_eq_true, F64UpperWord.float_beq_iff _ _ hff hf, decide_eq_true_iff,
      float_le_iff _ _ hf zero_finite, Library.Numerics.Float64.Tgamma.TgammaSpecial.zero_bits, F64Magnitude.value_zero]
    exact ⟨hfv, h0⟩
  rw [lgamma_pole _ _ _ _ _ _ _ x (fun h' => by have := (big_test _).mp h'; omega) h2]
  refine ⟨?_, rfl⟩
  rw [F64Bits.toBits_div]
  decide +kernel

theorem one_value : value (1.0 : Float).toBits = 1 := by
  rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.one_bits, Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ 1 (by decide +kernel)]
  norm_num

theorem one_finite : Finite (1.0 : Float).toBits := by
  rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.one_bits]; unfold CodeLib.IEEE64.Finite; decide

theorem two_bits : (2.0 : Float).toBits = 0x4000000000000000 := rfl

theorem two_value : value (2.0 : Float).toBits = 2 := by
  rw [two_bits, Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ 2 (by decide +kernel)]
  norm_num

theorem two_finite : Finite (2.0 : Float).toBits := by
  rw [two_bits]; unfold CodeLib.IEEE64.Finite; decide

/-- **1 and 2 give `+0`, with the sign `+1`.** -/
theorem lgamma_unit_value (hf : Finite x.toBits) (h12 : value x.toBits = 1 ∨ value x.toBits = 2) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits = 0 ∧
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 = 1.0 := by
  have hint : value x.toBits = ((if value x.toBits = 1 then 1 else 2 : ℤ) : ℝ) := by
    rcases h12 with h | h <;> simp [h]
  obtain ⟨hff, hfv⟩ := floorF_int x hf _ hint
  have hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6 := by
    have hb := F64PositiveSpacing.boundary_value 1025 (by norm_num) (by norm_num)
    have hm : |value x.toBits| < |value (F64ExponentBounds.boundary 1025)| := by
      rw [show F64ExponentBounds.boundary 1025 = UInt64.ofNat (1025 * 2 ^ 52) from rfl, hb,
        abs_of_pos (show (0 : ℝ) < 2 ^ (1025 + 51) / 2 ^ 1074 by positivity)]
      rcases h12 with h | h <;> rw [h] <;> norm_num
    have he := F64ExponentBounds.exponent_lt_of_magnitude_lt x.toBits 1025 (by norm_num) hm
    unfold Wasm.IEEE64.exponent at he
    have := x.toBits.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have h2 : ¬ (floorF x == x && x ≤ 0.0) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, float_le_iff _ _ hf zero_finite,
      Library.Numerics.Float64.Tgamma.TgammaSpecial.zero_bits, F64Magnitude.value_zero]
    rintro ⟨-, h⟩
    rcases h12 with h' | h' <;> rw [h'] at h <;> norm_num at h
  have h3 : (floorF x == x && (x == 1.0 || x == 2.0)) = true := by
    rw [Bool.and_eq_true, Bool.or_eq_true, F64UpperWord.float_beq_iff _ _ hff hf,
      F64UpperWord.float_beq_iff _ _ hf one_finite, F64UpperWord.float_beq_iff _ _ hf two_finite,
      one_value, two_value]
    exact ⟨hfv, h12⟩
  rw [lgamma_unit _ _ _ _ _ _ _ x (fun h' => by have := (big_test _).mp h'; omega) h2 h3]
  exact ⟨rfl, rfl⟩

end

/-! ### The comparison with the reference -/

theorem log_abs_gamma (v : ℝ) : Real.log |Real.Gamma v| = GammaBasic.lgamma v := by
  rw [Real.log_abs]; rfl

/-- The reference of 0 is `+0`. -/
theorem within_zero_at_zero (n : ℕ) : F64SignedRounding.WithinSteps n 0 0 := by
  refine ⟨by decide, ?_⟩
  have hr : F64SignedRounding.roundNearestEven 0 = 0 := by
    simp only [F64SignedRounding.roundNearestEven, le_refl, ite_true,
      F64SignedRounding.positive_reference_zero]
  rw [hr]
  simp

/-- `log |Γ|` vanishes at 1 and 2, whose result `+0` is the reference. -/
theorem lgamma_unit_within (v : ℝ) (h12 : v = 1 ∨ v = 2) :
    F64SignedRounding.WithinSteps 0 (Real.log |Real.Gamma v|) 0 := by
  rw [log_abs_gamma]
  rcases h12 with h | h <;> rw [h]
  · rw [GammaBasic.lgamma_one]; exact within_zero_at_zero 0
  · rw [GammaBasic.lgamma_two]; exact within_zero_at_zero 0

/-- From the overflow threshold on, the result `+∞` is the reference. -/
theorem lgamma_overflow_within (v : ℝ) (hv : (GammaThresholds.x3 : ℝ) ≤ v) :
    F64SignedRounding.WithinSteps 0 (Real.log |Real.Gamma v|) 0x7FF0000000000000 := by
  rw [log_abs_gamma]
  have hy := GammaThresholds.lgamma_overflow hv
  have hth : F64PositiveRounding.overflowThreshold ≤ GammaBasic.lgamma v := by
    have : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 := rfl
    rw [this]; exact hy
  have hpos : 0 ≤ GammaBasic.lgamma v := le_trans (by norm_num [F64PositiveRounding.overflowThreshold]) hth
  have hr : F64SignedRounding.roundNearestEven (GammaBasic.lgamma v) = 0x7FF0000000000000 := by
    simp only [F64SignedRounding.roundNearestEven, hpos, ite_true]
    exact F64PositiveRounding.reference_overflow _ hth
  refine ⟨by decide, ?_⟩
  rw [hr]
  simp

/-- At `0x1.754d9278b51a6p+1014` the result is within one step of the reference. -/
theorem lgamma_x1_within :
    F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (GammaThresholds.x1 : ℝ)|)
      0x7FEFFFFFFFFFFFFE := by
  rw [log_abs_gamma]
  have h := GammaThresholds.lgamma_x1
  have hw : value 0x7FEFFFFFFFFFFFFE = 2 ^ 1024 - 2 ^ 972 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ (2 ^ 1024 - 2 ^ 972) (by decide +kernel)]
    push_cast; ring
  apply F64WithinSelf.within_one_of_self _ (by unfold CodeLib.IEEE64.Finite; decide) _
    (1 / 2 ^ 53) (by positivity) le_rfl
  rw [hw, abs_sub_comm, abs_of_pos (show (0 : ℝ) < 2 ^ 1024 - 2 ^ 972 by norm_num)]
  calc |GammaBasic.lgamma GammaThresholds.x1 - (2 ^ 1024 - 2 ^ 972)| ≤ 3 / 5 * 2 ^ 971 := h
    _ ≤ 1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 972) := by norm_num

/-- At `0x1.754d9278b51a7p+1014` the result is within one step of the reference. -/
theorem lgamma_x2_within :
    F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (GammaThresholds.x2 : ℝ)|)
      0x7FEFFFFFFFFFFFFF := by
  rw [log_abs_gamma]
  have h := GammaThresholds.lgamma_x2
  have hw : value 0x7FEFFFFFFFFFFFFF = 2 ^ 1024 - 2 ^ 971 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ (2 ^ 1024 - 2 ^ 971) (by decide +kernel)]
    push_cast; ring
  apply F64WithinSelf.within_one_of_self _ (by unfold CodeLib.IEEE64.Finite; decide) _
    (1 / 2 ^ 53) (by positivity) le_rfl
  rw [hw, abs_sub_comm, abs_of_pos (show (0 : ℝ) < 2 ^ 1024 - 2 ^ 971 by norm_num)]
  calc |GammaBasic.lgamma GammaThresholds.x2 - (2 ^ 1024 - 2 ^ 971)| ≤ 1 / 5 * 2 ^ 971 := h
    _ ≤ 1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 971) := by norm_num

section
variable (logTab hTab sinTab asymTab accTab dbTab tab : Array UInt64) (x : Float)

/-- **At 1 and 2 the result is the reference `+0`.** -/
theorem lgamma_unit_steps (hf : Finite x.toBits) (h12 : value x.toBits = 1 ∨ value x.toBits = 2) :
    F64SignedRounding.WithinSteps 0 (Real.log |Real.Gamma (value x.toBits)|)
      (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits := by
  rw [(lgamma_unit_value logTab hTab sinTab asymTab accTab dbTab tab x hf h12).1]
  exact lgamma_unit_within _ h12

/-- **From `0x1.754d9278b51a8p+1014` on, the result `+∞` is the reference.** -/
theorem lgamma_overflow_steps (hf : Finite x.toBits) (h : 0x7F5754D9278B51A8 ≤ x.toBits.toNat)
    (hs : x.toBits.toNat < 2 ^ 63) :
    F64SignedRounding.WithinSteps 0 (Real.log |Real.Gamma (value x.toBits)|)
      (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits := by
  rw [(lgamma_overflow logTab hTab sinTab asymTab accTab dbTab tab x hf h hs).1]
  apply lgamma_overflow_within
  rw [← GammaThresholds.x3_word, PolyBound.ratOfWord_cast]
  exact (F64PositiveOrder.value_le_iff (by decide) hs).mpr (by
    simp only [UInt64.reduceToNat]; exact h)

/-- **At `0x1.754d9278b51a6p+1014` the result is within one step of the reference.** -/
theorem lgamma_x1_steps (h : x.toBits = 0x7F5754D9278B51A6) :
    F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (value x.toBits)|)
      (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits := by
  rw [(lgamma_x1 logTab hTab sinTab asymTab accTab dbTab tab x h).1, h,
    ← PolyBound.ratOfWord_cast, GammaThresholds.x1_word]
  exact lgamma_x1_within

/-- **At `0x1.754d9278b51a7p+1014` the result is within one step of the reference.** -/
theorem lgamma_x2_steps (h : x.toBits = 0x7F5754D9278B51A7) :
    F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (value x.toBits)|)
      (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).1.toBits := by
  rw [(lgamma_x2 logTab hTab sinTab asymTab accTab dbTab tab x h).1, h,
    ← PolyBound.ratOfWord_cast, GammaThresholds.x2_word]
  exact lgamma_x2_within

end

#print axioms lgamma_nan
#print axioms lgamma_inf
#print axioms lgamma_huge_neg
#print axioms lgamma_overflow
#print axioms lgamma_x1
#print axioms lgamma_x2
#print axioms lgamma_pole_value
#print axioms lgamma_unit_value
#print axioms lgamma_unit_within
#print axioms lgamma_overflow_within
#print axioms lgamma_x1_within
#print axioms lgamma_x2_within
#print axioms lgamma_unit_steps
#print axioms lgamma_overflow_steps
#print axioms lgamma_x1_steps
#print axioms lgamma_x2_steps

end Library.Numerics.Float64.Lgamma.LgammaSpecial
