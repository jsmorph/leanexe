import Library.Numerics.Float64.Erf.ErfBranches
import Library.Numerics.Float64.Erf.ErfTailEval

/-!
The path of `Erf.erfWith` for each range of `|x|`, and the words it computes.  `ix_below` turns
the code's comparison of the high word `ix` with a constant `T` into `|x| < v`, where `v` is the
value of the double whose high word is `T` (`thr_*`).  The `sel_*` lemmas give the expression that
`erfWith` evaluates on each range, and `neg_flag` the sign test `hx >>> 31 == 1`.
-/

namespace Library.Numerics.Float64.Erf.ErfBits
open CodeLib.IEEE64 LeanExe.ProofKit ErfBranches

set_option exponentiation.threshold 4096

theorem thr_inf : value (UInt64.ofNat (0x7ff00000 * 2 ^ 32)) = 2 ^ 1024 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x7ff00000 * 2 ^ 32)) = 2 ^ 2098 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_small : value (UInt64.ofNat (0x3feb0000 * 2 ^ 32)) = 27 / 32 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x3feb0000 * 2 ^ 32)) = 27 * 2 ^ 1069 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_tiny : value (UInt64.ofNat (0x3e300000 * 2 ^ 32)) = 1 / 2 ^ 28 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x3e300000 * 2 ^ 32)) = 2 ^ 1046 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_sub : value (UInt64.ofNat (0x00800000 * 2 ^ 32)) = 1 / 2 ^ 1015 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x00800000 * 2 ^ 32)) = 2 ^ 59 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_mid : value (UInt64.ofNat (0x3ff40000 * 2 ^ 32)) = 5 / 4 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x3ff40000 * 2 ^ 32)) = 5 * 2 ^ 1072 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_six : value (UInt64.ofNat (0x40180000 * 2 ^ 32)) = 6 := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x40180000 * 2 ^ 32)) = 3 * 2 ^ 1075 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem thr_b2 : value (UInt64.ofNat (0x4006DB6E * 2 ^ 32)) = ((ErfTailCoeffs.tailB2 : ℚ) : ℝ) := by
  have h : Wasm.IEEE64.scaledValue (UInt64.ofNat (0x4006DB6E * 2 ^ 32)) = 748983 * 2 ^ 1056 := by
    decide +kernel
  rw [value, h, ErfTailCoeffs.tailB2]
  norm_num

/-- The code's comparison of `ix` with a constant `T`. -/
theorem ix_below (b : UInt64) (T : Nat) (hT : T < 2 ^ 31) (v : ℝ)
    (hv : value (UInt64.ofNat (T * 2 ^ 32)) = v) :
    (b >>> 32 &&& 0x7fffffff) < UInt64.ofNat T ↔ |value b| < v := by
  rw [← hv]
  exact ix_lt_value b T hT

/-- A finite word lies below `2^1024` in magnitude. -/
theorem finite_below (b : UInt64) (hb : Finite b) : |value b| < 2 ^ 1024 := by
  have he : Wasm.IEEE64.exponent b < 2047 := by
    have h := hb
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent b < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have h := F64Magnitude.magnitude_lt b 2047 1024 (by norm_num) (by norm_num) he
  simpa using h

/-- The sign test of the code. -/
theorem neg_flag (b : UInt64) : (b >>> 32 >>> 31 == 1) = Wasm.IEEE64.sign b := by
  have hb := b.toNat_lt
  have h : (b >>> 32 >>> 31).toNat = b.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    omega
  by_cases hs : 2 ^ 63 ≤ b.toNat
  · have h1 : b >>> 32 >>> 31 = 1 := by
      apply UInt64.toNat_inj.mp
      rw [h]
      simp only [UInt64.reduceToNat]
      omega
    rw [h1]
    unfold Wasm.IEEE64.sign
    rw [decide_eq_true hs]
    rfl
  · have h1 : b >>> 32 >>> 31 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [h]
      simp only [UInt64.reduceToNat]
      omega
    rw [h1]
    unfold Wasm.IEEE64.sign
    rw [decide_eq_false hs]
    rfl

/-- The ranges of `|x|` as conditions on `ix`. -/
theorem ix_conds (x : Float) (hf : Finite x.toBits) :
    ¬ ((0x7ff00000 : UInt64) ≤ x.toBits >>> 32 &&& 0x7fffffff) ∧
      ((x.toBits >>> 32 &&& 0x7fffffff) < 0x3feb0000 ↔ |value x.toBits| < 27 / 32) ∧
      ((x.toBits >>> 32 &&& 0x7fffffff) < 0x3e300000 ↔ |value x.toBits| < 1 / 2 ^ 28) ∧
      ((x.toBits >>> 32 &&& 0x7fffffff) < 0x00800000 ↔ |value x.toBits| < 1 / 2 ^ 1015) ∧
      ((x.toBits >>> 32 &&& 0x7fffffff) < 0x3ff40000 ↔ |value x.toBits| < 5 / 4) ∧
      ((0x40180000 : UInt64) ≤ x.toBits >>> 32 &&& 0x7fffffff ↔ 6 ≤ |value x.toBits|) ∧
      ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E ↔
        |value x.toBits| < ((ErfTailCoeffs.tailB2 : ℚ) : ℝ)) := by
  refine ⟨?_, ix_below _ _ (by norm_num) _ thr_small, ix_below _ _ (by norm_num) _ thr_tiny,
    ix_below _ _ (by norm_num) _ thr_sub, ix_below _ _ (by norm_num) _ thr_mid, ?_,
    ix_below _ _ (by norm_num) _ thr_b2⟩
  · intro h
    have h2 := (ix_below _ _ (by norm_num) _ thr_inf).mpr (finite_below _ hf)
    rw [UInt64.le_iff_toNat_le] at h
    rw [UInt64.lt_iff_toNat_lt] at h2
    have hc1 : (UInt64.ofNat 2146435072).toNat = 2146435072 := rfl
    have hc2 : (0x7ff00000 : UInt64).toNat = 2146435072 := rfl
    rw [hc1] at h2
    rw [hc2] at h
    omega
  · have key : ∀ a b : UInt64, a ≤ b ↔ ¬ b < a := fun a b => by
      rw [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      omega
    rw [key, ← not_lt]
    exact not_congr (ix_below _ _ (by norm_num) _ thr_six)

theorem sel_inf_free (tab : Array UInt64) (x : Float) (hf : Finite x.toBits) :
    Erf.erfWith tab x =
      if (x.toBits >>> 32 &&& 0x7fffffff) < 0x3feb0000 then
        if (x.toBits >>> 32 &&& 0x7fffffff) < 0x3e300000 then
          if (x.toBits >>> 32 &&& 0x7fffffff) < 0x00800000 then
            (8.0 * x + Float.ofBits 0x3FF06EBA8214DB69 * x) / 8.0
          else x + Float.ofBits 0x3FC06EBA8214DB69 * x
        else x + x * Erf.erfSmall (x * x)
      else if (x.toBits >>> 32 &&& 0x7fffffff) < 0x3ff40000 then
        (if x.toBits >>> 32 >>> 31 == 1 then
          -Float.ofBits 0x3FEB0AC160000000 - (Erf.erfMiddle (x.abs - 1.0)).1 /
            (Erf.erfMiddle (x.abs - 1.0)).2
        else Float.ofBits 0x3FEB0AC160000000 + (Erf.erfMiddle (x.abs - 1.0)).1 /
            (Erf.erfMiddle (x.abs - 1.0)).2)
      else if (0x40180000 : UInt64) ≤ x.toBits >>> 32 &&& 0x7fffffff then
        (if x.toBits >>> 32 >>> 31 == 1 then Float.ofBits 0x01A56E1FC2F8F359 - 1.0
          else 1.0 - Float.ofBits 0x01A56E1FC2F8F359)
      else
        (if x.toBits >>> 32 >>> 31 == 1 then
          Erf.erfExp tab x.abs
              (Erf.erfTail (1.0 / (x.abs * x.abs)) ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).1
              (Erf.erfTail (1.0 / (x.abs * x.abs))
                ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).2 / x.abs - 1.0
        else 1.0 - Erf.erfExp tab x.abs
              (Erf.erfTail (1.0 / (x.abs * x.abs)) ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).1
              (Erf.erfTail (1.0 / (x.abs * x.abs))
                ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).2 / x.abs) := by
  have h1 := (ix_conds x hf).1
  simp only [Erf.erfWith, ge_iff_le, h1, ↓reduceIte]

#print axioms thr_inf
#print axioms thr_b2
#print axioms neg_flag
#print axioms ix_conds
#print axioms sel_inf_free

end Library.Numerics.Float64.Erf.ErfBits
