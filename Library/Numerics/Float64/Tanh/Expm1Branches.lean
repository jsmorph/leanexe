import Library.Numerics.Float64.Tanh.Compiled
import LeanExe.ProofKit.F64NearestSum
import LeanExe.ProofKit.F64StrictOrder

/-!
The branches of fdlibm's `expm1`.  `highWord w` is the high word of the magnitude of `w`, which the
code compares with constants, and `high_le_iff` turns such a comparison into one between `abs x`
and the value of the constant shifted into place.  Each `select_*` theorem states the value of
`Tanh.expm1 x` on one branch.
-/

namespace Library.Numerics.Float64.Tanh.Expm1Branches
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The high word of the magnitude. -/
def highWord (w : UInt64) : UInt64 := w >>> 32 &&& 2147483647

/-- The sign bit. -/
def sgn (w : UInt64) : Bool := w >>> 63 == 1

theorem highWord_toNat (w : UInt64) : (highWord w).toNat = w.toNat % 2 ^ 63 / 2 ^ 32 := by
  simp only [highWord, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.reduceToNat,
    Nat.reduceMod]
  change (w.toNat >>> 32) &&& (2 ^ 31 - 1) = w.toNat % 2 ^ 63 / 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 63 = 2 ^ 32 * 2 ^ 31 by norm_num, Nat.mod_mul_right_div_self]

theorem sgn_iff (w : UInt64) : sgn w = Wasm.IEEE64.sign w := by
  simp only [sgn, Wasm.IEEE64.sign]
  have h := w.toNat_lt
  by_cases hs : 2 ^ 63 ≤ w.toNat
  · have : w >>> 63 = 1 := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod]
      rw [Nat.shiftRight_eq_div_pow]
      change w.toNat / 2 ^ 63 = 1
      omega
    simp [this]
    omega
  · have : w >>> 63 = 0 := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod]
      rw [Nat.shiftRight_eq_div_pow]
      change w.toNat / 2 ^ 63 = 0
      omega
    simp [this]
    omega

/-- A comparison of the high word with `C` is a comparison of the magnitude with the value of
`C` shifted into the high word. -/
theorem high_le_iff (w : UInt64) (C : Nat) (hC : C < 0x7ff00000) :
    (UInt64.ofNat C ≤ highWord w) ↔ value (UInt64.ofNat (C * 2 ^ 32)) ≤ |value w| := by
  have hCw : (UInt64.ofNat C).toNat = C := UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  have hB : (UInt64.ofNat (C * 2 ^ 32)).toNat = C * 2 ^ 32 :=
    UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  have hBabs : F64Order.absBits (UInt64.ofNat (C * 2 ^ 32)) = UInt64.ofNat (C * 2 ^ 32) := by
    apply UInt64.toNat_inj.mp
    rw [F64Order.absBits_toNat, hB]
    omega
  have hBpos : 0 ≤ value (UInt64.ofNat (C * 2 ^ 32)) := by
    rw [F64NearestSum.value_of_lt_limit _ (by rw [hB]; unfold F64NearestNonnegative.limit; omega)]
    positivity
  rw [UInt64.le_iff_toNat_le, hCw, highWord_toNat, Nat.le_div_iff_mul_le (by norm_num)]
  constructor
  · intro h
    have hle : F64Order.absBits (UInt64.ofNat (C * 2 ^ 32)) ≤ F64Order.absBits w := by
      rw [hBabs, UInt64.le_iff_toNat_le, hB, F64Order.absBits_toNat]
      exact h
    have := F64Order.abs_value_mono _ _ hle
    rwa [abs_of_nonneg hBpos] at this
  · intro h
    by_contra hn
    have hlt : F64Order.absBits w < F64Order.absBits (UInt64.ofNat (C * 2 ^ 32)) := by
      rw [hBabs, UInt64.lt_iff_toNat_lt, hB, F64Order.absBits_toNat]
      omega
    have := F64Order.abs_value_lt _ _ hlt
    rw [abs_of_nonneg hBpos] at this
    linarith

/-- A finite word has high word below `0x7ff00000`. -/
theorem high_finite (w : UInt64) (hw : Finite w) : ¬ highWord w ≥ 2146435072 := by
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  rw [highWord_toNat] at hn
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
    ne_eq] at hw
  change 2146435072 ≤ w.toNat % 2 ^ 63 / 2 ^ 32 at hn
  have : w.toNat % 2 ^ 63 / 2 ^ 52 = w.toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [show (2 : Nat) ^ 63 = 2 ^ 52 * 2 ^ 11 by norm_num, Nat.mod_mul_right_div_self]
  omega

/-! ### Selection of the branches -/

theorem select_reduced_one (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0))
    (h4 : highWord x.toBits > 1071001154) (h5 : highWord x.toBits < 1072734898) :
    Tanh.expm1 x =
      if sgn x.toBits = true then
        Tanh.expm1Kernel ((x + Float.ofBits 4604418534311723008) -
            -Float.ofBits 4461442080421002358)
          ((x + Float.ofBits 4604418534311723008) - ((x + Float.ofBits 4604418534311723008) -
            -Float.ofBits 4461442080421002358) - -Float.ofBits 4461442080421002358) true 1
      else
        Tanh.expm1Kernel ((x - Float.ofBits 4604418534311723008) -
            Float.ofBits 4461442080421002358)
          ((x - Float.ofBits 4604418534311723008) - ((x - Float.ofBits 4604418534311723008) -
            Float.ofBits 4461442080421002358) - Float.ofBits 4461442080421002358) (sgn x.toBits) 1 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h4' : x.toBits >>> 32 &&& 2147483647 > 1071001154 := h4
  have h5' : x.toBits >>> 32 &&& 2147483647 < 1072734898 := h5
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1', if_pos h4', if_pos h5']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_reduced_neg (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0))
    (h4 : highWord x.toBits > 1071001154) (h5 : ¬ highWord x.toBits < 1072734898)
    (hn : sgn x.toBits = true) :
    Tanh.expm1 x =
      Tanh.expm1Kernel ((x - -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
          Float.ofBits 4604418534311723008) -
          -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
            Float.ofBits 4461442080421002358)
        ((x - -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
            Float.ofBits 4604418534311723008) -
          ((x - -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
            Float.ofBits 4604418534311723008) -
            -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
              Float.ofBits 4461442080421002358) -
          -(-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64.toFloat *
            Float.ofBits 4461442080421002358)
        true (-(Float.ofBits 4609176140021203710 * x - 0.5)).toUInt64 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h4' : x.toBits >>> 32 &&& 2147483647 > 1071001154 := h4
  have h5' : ¬ (x.toBits >>> 32 &&& 2147483647 < 1072734898) := h5
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1', if_pos h4', if_neg h5']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_reduced_pos (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0))
    (h4 : highWord x.toBits > 1071001154) (h5 : ¬ highWord x.toBits < 1072734898)
    (hn : sgn x.toBits = false) :
    Tanh.expm1 x =
      Tanh.expm1Kernel ((x - (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
          Float.ofBits 4604418534311723008) -
          (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
            Float.ofBits 4461442080421002358)
        ((x - (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
            Float.ofBits 4604418534311723008) -
          ((x - (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
            Float.ofBits 4604418534311723008) -
            (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
              Float.ofBits 4461442080421002358) -
          (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64.toFloat *
            Float.ofBits 4461442080421002358)
        (sgn x.toBits) (Float.ofBits 4609176140021203710 * x + 0.5).toUInt64 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h4' : x.toBits >>> 32 &&& 2147483647 > 1071001154 := h4
  have h5' : ¬ (x.toBits >>> 32 &&& 2147483647 < 1072734898) := h5
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1', if_pos h4', if_neg h5']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_middle (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0))
    (h4 : ¬ highWord x.toBits > 1071001154) (h5 : ¬ highWord x.toBits < 1016070144) :
    Tanh.expm1 x = Tanh.expm1Kernel x 0.0 false 0 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h4' : ¬ (x.toBits >>> 32 &&& 2147483647 > 1071001154) := h4
  have h5' : ¬ (x.toBits >>> 32 &&& 2147483647 < 1016070144) := h5
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1', if_neg h4', if_neg h5']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_tiny (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0))
    (h4 : ¬ highWord x.toBits > 1071001154) (h5 : highWord x.toBits < 1016070144) :
    Tanh.expm1 x = x - (Float.ofBits 9094988921128908188 + x -
      (Float.ofBits 9094988921128908188 + x)) := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  have h4' : ¬ (x.toBits >>> 32 &&& 2147483647 > 1071001154) := h4
  have h5' : x.toBits >>> 32 &&& 2147483647 < 1016070144 := h5
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1', if_neg h4', if_pos h5']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_overflow (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) :
    Tanh.expm1 x = Float.ofBits 9094988921128908188 * Float.ofBits 9094988921128908188 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_saturated (x : Float) (h1 : ¬ highWord x.toBits ≥ 2146435072)
    (h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735))
    (h3 : highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) :
    Tanh.expm1 x = Float.ofBits 118622047889322841 - 1.0 := by
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  unfold Tanh.expm1
  simp only []
  rw [if_neg h1']
  simp only [highWord, sgn] at *
  split_ifs <;> simp_all

theorem select_nonfinite (x : Float) (h1 : highWord x.toBits ≥ 2146435072) :
    Tanh.expm1 x = if (x.toBits &&& 4503599627370495 != 0) = true then x + x
      else if sgn x.toBits = true then -1.0 else x := by
  have h1' : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072 := h1
  unfold Tanh.expm1
  simp only []
  rw [if_pos h1']
  rfl

#print axioms highWord_toNat
#print axioms sgn_iff
#print axioms high_le_iff
#print axioms high_finite
#print axioms select_reduced_one
#print axioms select_reduced_neg
#print axioms select_reduced_pos
#print axioms select_middle
#print axioms select_tiny
#print axioms select_overflow
#print axioms select_saturated
#print axioms select_nonfinite

end Library.Numerics.Float64.Tanh.Expm1Branches
