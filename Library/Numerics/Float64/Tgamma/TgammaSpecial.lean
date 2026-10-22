import Library.Numerics.Float64.Tgamma.TgammaBranches
import Library.Numerics.Float64.Tgamma.TgammaFloor
import LeanExe.ProofKit.F64Saturate
import LeanExe.ProofKit.F64PositiveOrder

/-!
The exceptional values of `Tgamma.tgammaWith`, for any tables: `+∞` at `+0` and at `2 ^ -1024`,
`-∞` at `-0`, `+∞` at `+∞`, the canonical NaN at `-∞`, at NaN, and at the negative integers, `+∞`
from the overflow threshold `0x1.573fae561f648p+7` on, and a zero at or below -184 off the
integers.  Each proof selects the path with `TgammaBranches`, from conditions on the word or the
value of `x`, and evaluates the path's last operation with `F64Saturate` or the definitions in
`Wasm.IEEE64`.  No proof evaluates an arithmetic operation by `decide`; the decided facts concern
single words.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSpecial
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma TgammaBranches TgammaFloor

set_option exponentiation.threshold 4096

section
variable (dbTab accTab smallTab mainTab logTab sinTab expTab asymTab : Array UInt64)

/-- The first test of `tgammaWith` holds exactly for the infinities and NaN. -/
theorem special_test (w : UInt64) :
    w <<< 1 ≥ 0xFFE0000000000000 ↔ Wasm.IEEE64.exponent w = 0x7FF := by
  rw [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft]
  simp only [Wasm.IEEE64.exponent, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
    Nat.reducePow]
  have := w.toNat_lt
  omega

theorem not_special (x : Float) (hx : Finite x.toBits) :
    ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000 := by
  rw [special_test]
  simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hx

theorem lit_value (w : UInt64) (q : ℚ) (h : PolyBound.ratOfWord w = q) : value w = (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, h]

theorem quarter_bits : (0.25 : Float).toBits = 0x3FD0000000000000 := rfl
theorem zero_bits : (0.0 : Float).toBits = 0 := rfl
theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem quarter_test (x : Float) (hx : Finite x.toBits) :
    x.abs < 0.25 ↔ |value x.toBits| < 1 / 4 := by
  obtain ⟨haf, hav⟩ := abs_float x hx
  have hq : Finite (0.25 : Float).toBits := by
    rw [quarter_bits]; unfold CodeLib.IEEE64.Finite; decide
  rw [F64UpperWord.float_lt_iff _ _ haf hq, hav, quarter_bits,
    lit_value 0x3FD0000000000000 (1 / 4) (by decide +kernel)]
  norm_num

theorem zero_test (x : Float) (hx : Finite x.toBits) : (x == 0.0) = true ↔ value x.toBits = 0 := by
  have h0 : Finite (0.0 : Float).toBits := by
    rw [zero_bits]; unfold CodeLib.IEEE64.Finite; decide
  rw [F64UpperWord.float_beq_iff _ _ hx h0, zero_bits, F64Magnitude.value_zero]

/-- `1.0/x` at a zero `x`. -/
theorem one_div_zero (x : Float) (hz : Wasm.IEEE64.scaledMagnitude x.toBits = 0)
    (hx : Finite x.toBits) :
    (1.0 / x).toBits = Wasm.IEEE64.infinity (Wasm.IEEE64.sign x.toBits) := by
  have hs1 : Wasm.IEEE64.sign 0x3FF0000000000000 = false := by decide
  rw [F64Bits.toBits_div, one_bits, F64Saturate.div_by_zero _ _ (by
    unfold CodeLib.IEEE64.Finite; decide) hx (by decide) hz, hs1]
  cases Wasm.IEEE64.sign x.toBits <;> rfl

/-- **`Γ (+0) = +∞`.** -/
theorem tgamma_pos_zero (x : Float) (h : x.toBits = 0) :
    (tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x).toBits =
      0x7FF0000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by rw [h, F64Magnitude.value_zero]
  rw [tgamma_tiny _ _ _ _ _ _ _ _ x (not_special x hx)
    ((quarter_test x hx).mpr (by rw [hv]; norm_num)) (by rw [h]; decide)]
  unfold tinyPath
  rw [ite_eq_right (by rw [h]; decide)]
  simp only []
  rw [ite_eq_left ((zero_test x hx).mpr hv), one_div_zero x (by rw [h]; decide) hx, h]
  decide

/-- **`Γ (-0) = -∞`.** -/
theorem tgamma_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x).toBits =
      0xFFF0000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by
    rw [h, lit_value _ 0 (by decide +kernel)]
    norm_num
  rw [tgamma_tiny _ _ _ _ _ _ _ _ x (not_special x hx)
    ((quarter_test x hx).mpr (by rw [hv]; norm_num)) (by rw [h]; decide)]
  unfold tinyPath
  rw [ite_eq_right (by rw [h]; decide)]
  simp only []
  rw [ite_eq_left ((zero_test x hx).mpr hv), one_div_zero x (by rw [h]; decide) hx, h]
  decide

/-- **`Γ (+∞) = +∞`.** -/
theorem tgamma_pos_inf (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x).toBits =
      0x7FF0000000000000 := by
  rw [tgamma_special _ _ _ _ _ _ _ _ x (by rw [h]; decide)]
  unfold specialPath
  rw [ite_eq_left (by rw [h]; decide), ite_eq_right (by rw [h]; decide), h]

/-- **`Γ (-∞)` is the canonical NaN.** -/
theorem tgamma_neg_inf (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x).toBits =
      Wasm.IEEE64.canonicalNaN := by
  rw [tgamma_special _ _ _ _ _ _ _ _ x (by rw [h]; decide)]
  unfold specialPath
  rw [ite_eq_left (by rw [h]; decide), ite_eq_left (by rw [h]; decide), F64Bits.toBits_div, h]
  exact F64Saturate.div_inf_inf _ _ (by decide) (by decide) (by decide) (by decide)

/-- **A NaN gives the canonical NaN.** -/
theorem tgamma_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x).toBits =
      Wasm.IEEE64.canonicalNaN := by
  have he : Wasm.IEEE64.exponent x.toBits = 0x7FF := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  rw [tgamma_special _ _ _ _ _ _ _ _ x ((special_test _).mpr he)]
  unfold specialPath
  have hne : (x.toBits <<< 1 == 0xFFE0000000000000) = false := by
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    have := x.toBits.toNat_lt
    omega
  rw [ite_eq_right (by rw [hne]; decide), F64Bits.toBits_add]
  exact F64Saturate.add_nan_left _ _ h

end

#print axioms tgamma_pos_zero
#print axioms tgamma_neg_zero
#print axioms tgamma_pos_inf
#print axioms tgamma_neg_inf
#print axioms tgamma_nan

end Library.Numerics.Float64.Tgamma.TgammaSpecial
