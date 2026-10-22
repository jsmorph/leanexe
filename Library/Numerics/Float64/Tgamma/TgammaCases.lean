import Library.Numerics.Float64.Tgamma.TgammaReflPath
import Library.Numerics.Float64.Tgamma.TgammaSmallPath
import Library.Numerics.Float64.Tgamma.TgammaMainPath
import Library.Numerics.Float64.Tgamma.TgammaEdge
import Library.Numerics.Float64.Tgamma.TgammaInt
import Library.Numerics.Float64.Tgamma.TgammaBranches

/-!
The tests of `tgammaWith` in terms of the value of a finite `x`: the threshold `2 ^ -112` of the
tiny path (`tiny_test`), the overflow threshold `t0` (`t0_test`), the integer test (`int_true`,
`int_false`), and the comparisons with `-184`, `-3`, and `4` (`m184_test`, `m3_test`, `p4_test`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaCases
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

/-- The test of the tiny path is `|x| < 2 ^ -112`. -/
theorem tiny_test (x : Float) :
    x.toBits <<< 1 < 0x71E0000000000000 ↔ |value x.toBits| < 1 / 2 ^ 112 := by
  have hw := x.toBits.toNat_lt
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hsh : (x.toBits <<< 1).toNat = 2 * (x.toBits.toNat % 2 ^ 63) := by
    rw [UInt64.toNat_shiftLeft]
    have h1 : (1 : UInt64).toNat % 64 = 1 := rfl
    rw [h1, Nat.shiftLeft_eq, pow_one]
    omega
  have habs := F64UpperWord.value_abs x.toBits
  have hat := F64UpperWord.abs_toNat x.toBits
  have hlt : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [hat]; omega
  have hb : value (0x38F0000000000000 : UInt64) = 1 / 2 ^ 112 := by
    rw [TgammaSpecial.lit_value _ (1 / 2 ^ 112) (by decide +kernel)]
    norm_num
  have h71 : (0x71E0000000000000 : UInt64).toNat = 0x71E0000000000000 := rfl
  have h38 : (0x38F0000000000000 : UInt64).toNat = 0x38F0000000000000 := rfl
  rw [UInt64.lt_iff_toNat_lt, hsh, h71, ← habs, ← hb]
  constructor
  · intro h
    exact F64PositiveOrder.value_strict (by rw [h38]; norm_num) (by rw [hat, h38]; omega)
  · intro h
    by_contra hc
    have := (F64PositiveOrder.value_le_iff (left := (0x38F0000000000000 : UInt64))
      (by rw [h38]; norm_num) hlt).mpr (by rw [hat, h38]; omega)
    linarith

/-- The overflow test is `t0 ≤ x`. -/
theorem t0_test (x : Float) (hx : Finite x.toBits) :
    x ≥ Float.ofBits 0x406573FAE561F648 ↔ (GammaThresholds.t0 : ℝ) ≤ value x.toBits := by
  have hw : Wasm.IEEE64.isFinite 0x406573FAE561F648 = true := by decide
  rw [ge_iff_le, TgammaRefl8.float_le_iff _ _ (TgammaWords.ofBits_finite _ hw) hx,
    TgammaWords.ofBits_value _ hw, GammaThresholds.t0_word]

/-- `floorF x = ⌊x⌋` for every finite `x`. -/
theorem floorF_all (x : Float) (hx : Finite x.toBits) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = ⌊value x.toBits⌋ := by
  rcases lt_or_ge |value x.toBits| (2 ^ 52) with hb | hb
  · exact floorF_spec x hx hb
  · obtain ⟨k, hk⟩ := TgammaRefl4.grid x.toBits 52 le_rfl hb
    rw [show 52 - 52 = 0 from rfl, pow_zero, div_one] at hk
    obtain ⟨hrf, ⟨R, hR⟩, hrd, -⟩ := roundEven_spec x hx
    have hRk : R = k := by
      rw [hR, hk] at hrd
      have h3 : ((|R - k| : ℤ) : ℝ) ≤ 1 / 2 := by rw [Int.cast_abs]; push_cast; exact hrd
      have h4 : |R - k| < 1 := by
        have : ((|R - k| : ℤ) : ℝ) < 1 := lt_of_le_of_lt h3 (by norm_num)
        exact_mod_cast this
      rw [abs_lt] at h4
      omega
    unfold floorF
    dsimp only
    have hc : ¬ roundEven x > x := by
      rw [GT.gt, F64UpperWord.float_lt_iff _ _ hx hrf, hR, hk, hRk]
      exact lt_irrefl _
    rw [ite_eq_right hc]
    refine ⟨hrf, ?_⟩
    rw [hR, hk, hRk, Int.floor_intCast]

/-- The integer test of `tgammaWith`. -/
theorem int_test (x : Float) (hx : Finite x.toBits) :
    (floorF x == x) = true ↔ (⌊value x.toBits⌋ : ℝ) = value x.toBits := by
  obtain ⟨hff, hfv⟩ := floorF_all x hx
  rw [F64UpperWord.float_beq_iff _ _ hff hx, hfv]

theorem lit_neg (y : Float) (w : UInt64) (q : ℚ) (hb : y.toBits = w)
    (hw : Wasm.IEEE64.isFinite w = true) (hq : PolyBound.ratOfWord w = q) :
    Finite (-y).toBits ∧ value (-y).toBits = -(q : ℝ) := by
  have hf : Finite y.toBits := by rw [hb]; exact hw
  obtain ⟨h1, h2⟩ := neg_float y hf
  exact ⟨h1, by rw [h2, hb, TgammaSpecial.lit_value _ q hq]⟩

theorem m184_test (x : Float) (hx : Finite x.toBits) : x ≤ -184.0 ↔ value x.toBits ≤ -184 := by
  obtain ⟨hf, hv⟩ := lit_neg (184.0 : Float) 0x4067000000000000 184 rfl (by decide) (by decide +kernel)
  rw [TgammaRefl8.float_le_iff _ _ hx hf, hv]
  norm_num

theorem m3_test (x : Float) (hx : Finite x.toBits) : x < -3.0 ↔ value x.toBits < -3 := by
  obtain ⟨hf, hv⟩ := lit_neg (3.0 : Float) 0x4008000000000000 3 rfl (by decide) (by decide +kernel)
  rw [F64UpperWord.float_lt_iff _ _ hx hf, hv]
  norm_num

theorem p4_test (x : Float) (hx : Finite x.toBits) : x > 4.0 ↔ 4 < value x.toBits := by
  have hb : (4.0 : Float).toBits = 0x4010000000000000 := rfl
  have hf : Finite (4.0 : Float).toBits := by rw [hb]; unfold CodeLib.IEEE64.Finite; decide
  rw [GT.gt, F64UpperWord.float_lt_iff _ _ hf hx, hb,
    TgammaSpecial.lit_value _ 4 (by decide +kernel)]
  norm_num

#print axioms tiny_test
#print axioms t0_test
#print axioms floorF_all
#print axioms int_test
#print axioms m184_test

end Library.Numerics.Float64.Tgamma.TgammaCases
