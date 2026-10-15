import LeanExe.ProofKit.F64PackingFinite
import LeanExe.ProofKit.F64AddNearest
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64Approx

/-!
Rounding to binary64 up to the overflow threshold `2^1024 - 2^970`.  `F64PackRelative.pack_spec`
stops at `2^1023`, below the top binade.  A magnitude `n` below the scaled threshold
`2^2098 - 2^2044` packs to a finite word (`top_finite`): in the top binade the significand rounds
to `2^53` only when `n` lies at or above the midpoint `2^2098 - 2^2044` between the largest finite
magnitude and `2^2098`, by `F64AddNearest.roundShift_nearest`.  `F64Packing.pack_finite_spec` then
gives the rounded magnitude, so the relative error of `CodeLib.IEEE64.roundedMagnitude` holds up
to the threshold (`signed_pack_relative_top`), and with it the relative error of a sum and of a
difference (`add_real_relative_top`, `sub_real_relative_top`) and their forms in `F64Approx`
(`approx_add_top`, `approx_sub_top`).
-/

namespace LeanExe.ProofKit.F64TopPack
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- **A magnitude below the scaled overflow threshold packs to a finite word.** -/
theorem top_finite (negative : Bool) (n : ℕ) (hmax : n + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative n) := by
  by_cases hsmall : n < 2 ^ 2097
  · exact (F64PackRelative.pack_spec negative n hsmall).1
  push Not at hsmall
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hsmall
    have : 0 < 2 ^ 2097 := by positivity
    omega
  have hlog : Nat.log2 n = 2097 := by
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn0).2 (by omega))
    · exact (Nat.le_log2 hn0).2 hsmall
  have hsub : ¬ n < 4503599627370496 := by
    have : (4503599627370496 : ℕ) ≤ 2 ^ 2097 := by norm_num
    omega
  have hex : ¬ n < 9007199254740992 := by
    have : (9007199254740992 : ℕ) ≤ 2 ^ 2097 := by norm_num
    omega
  set r := Wasm.IEEE32.roundShift n 2045 with hr
  have hb := CodeLib.IEEE32.roundShift_bounds n 2045
  rw [← hr] at hb
  have hq1 : 2 ^ 52 ≤ n / 2 ^ 2045 :=
    (Nat.le_div_iff_mul_le (by positivity)).2 (by rw [← pow_add]; exact hsmall)
  have hq2 : n / 2 ^ 2045 < 2 ^ 53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 (by rw [← pow_add]; omega)
  have hcarry : r ≠ 2 ^ 53 := by
    intro h
    have hnear := F64AddNearest.roundShift_nearest n 2045 (2 ^ 53 - 1) (by norm_num)
    rw [← hr, h] at hnear
    have hn1 : (2 : ℤ) ^ 2097 ≤ n := by exact_mod_cast hsmall
    have hn2 : (n : ℤ) + 2 ^ 2044 < 2 ^ 2098 := by exact_mod_cast hmax
    have e1 : ((2 ^ 53 : ℕ) : ℤ) * 2 ^ 2045 = 2 ^ 2098 := by norm_num
    have e2 : ((2 ^ 53 - 1 : ℕ) : ℤ) * 2 ^ 2045 = 2 ^ 2098 - 2 * 2 ^ 2044 := by norm_num
    rw [e1, e2] at hnear
    set A : ℤ := 2 ^ 2098 - n with hA
    have hP : (0 : ℤ) < 2 ^ 2044 := by positivity
    have hP2 : (2 : ℤ) ^ 2044 * 2 ^ 53 = 2 ^ 2097 := by norm_num
    rw [abs_of_pos (by linarith : (0 : ℤ) < 2 ^ 2098 - n)] at hnear
    rcases abs_cases ((2 : ℤ) ^ 2098 - 2 * 2 ^ 2044 - n) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rw [h1] at hnear <;> linarith
  have hr2 : r < 2 ^ 53 := lt_of_le_of_ne (by omega) hcarry
  have hcarryNum : ¬ r = 9007199254740992 := by
    intro h
    exact hcarry (by rw [h]; norm_num)
  have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
      Wasm.IEEE64.encodeFinite negative (2045 + 1) (r - 2 ^ 52) := by
    simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hex, hlog, ← hr, hcarryNum]
  rw [hactual]
  exact finite_encodeFinite negative _ _ (by norm_num) (by omega)

/-- Packing below the scaled overflow threshold: the word is finite, with the rounded magnitude
and the given sign. -/
theorem pack_top (negative : Bool) (n : ℕ) (hmax : n + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative n) ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative n) =
        roundedMagnitude n ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude negative n) = negative :=
  ⟨top_finite negative n hmax, F64Packing.pack_finite_spec negative n (top_finite negative n hmax)⟩

/-- `F64PackRelative.signed_pack_relative` up to the scaled overflow threshold. -/
theorem signed_pack_relative_top (z : ℤ) (hmax : z.natAbs + 2 ^ 2044 < 2 ^ 2098) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) - z| *
      (2 ^ 53 : ℤ) ≤ z.natAbs := by
  obtain ⟨hf, hm, hs⟩ := pack_top (z < 0) z.natAbs hmax
  have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) =
      if z < 0 then -(roundedMagnitude z.natAbs : ℤ) else roundedMagnitude z.natAbs := by
    simp [Wasm.IEEE64.scaledValue, hm, hs]
  have herr := roundedMagnitude_relative_error z.natAbs
  refine ⟨hf, ?_⟩
  by_cases hz : z < 0
  · have hz' := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hz)
    rw [hv, if_pos hz]
    rw [show -(roundedMagnitude z.natAbs : ℤ) - z =
      -((roundedMagnitude z.natAbs : ℤ) - z.natAbs) by omega, abs_neg]
    exact herr
  · have hz' := Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hz)
    rw [hv, if_neg hz]
    rw [show (roundedMagnitude z.natAbs : ℤ) - z =
      (roundedMagnitude z.natAbs : ℤ) - z.natAbs by omega]
    exact herr

/-- **The relative error of a sum** below the overflow threshold. -/
theorem add_real_relative_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a + value b| < 2 ^ 1024 - 2 ^ 970) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
      unitRoundoff64 * |value a + value b| := by
  by_cases hsmall : |value a + value b| < 2 ^ 1023
  · exact F64AddBounds.add_real_relative a b ha hb hsmall
  push Not at hsmall
  set z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b with hzdef
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hzv : value a + value b = (z : ℝ) / 2 ^ 1074 := by
    simp [value, hzdef]
    ring
  have hz0 : z ≠ 0 := by
    intro h
    rw [hzv, h] at hsmall
    simp at hsmall
    have : (0 : ℝ) < 2 ^ 1023 := by positivity
    linarith
  have hzb : z.natAbs + 2 ^ 2044 < 2 ^ 2098 := by
    rw [hzv, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at hbound
    have h1 : |(z : ℝ)| < 2 ^ 2098 - 2 ^ 2044 := by
      have : (2 ^ 1024 - 2 ^ 970 : ℝ) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2044 := by norm_num
      linarith
    have h2 : (z.natAbs : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    have h3 : ((z.natAbs + 2 ^ 2044 : ℕ) : ℝ) < ((2 ^ 2098 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  have hround := signed_pack_relative_top z hzb
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs := by
    have hne : (z == 0) = false := by simpa using hz0
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hzdef, hne]
  rw [heq]
  refine ⟨hround.1, ?_⟩
  set e := Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) - z
    with he
  have hev : value (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) - (value a + value b) =
      (e : ℝ) / 2 ^ 1074 := by
    rw [hzv, he]
    simp [value]
    ring
  have hscaled : |(e : ℝ)| * 2 ^ 53 ≤ |(z : ℝ)| := by
    have h1 : |e| * (2 ^ 53 : ℤ) ≤ z.natAbs := hround.2
    have h2 : ((|e| * (2 ^ 53 : ℤ) : ℤ) : ℝ) ≤ ((z.natAbs : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [← Int.cast_abs] at h2 ⊢
    have h3 : ((z.natAbs : ℤ) : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
    rw [Int.cast_abs]
    rw [Int.cast_abs] at h2
    linarith [h3]
  rw [hev, hzv, abs_div, abs_div, abs_of_pos hp, unitRoundoff64]
  rw [div_le_iff₀ hp]
  have : |(e : ℝ)| ≤ |(z : ℝ)| / 2 ^ 53 := by
    rw [le_div_iff₀ (by positivity)]
    exact hscaled
  have : 1 / 2 ^ 53 * (|(z : ℝ)| / 2 ^ 1074) * 2 ^ 1074 = |(z : ℝ)| / 2 ^ 53 := by
    field_simp
  linarith

/-- **The relative error of a difference** below the overflow threshold. -/
theorem sub_real_relative_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a - value b| < 2 ^ 1024 - 2 ^ 970) :
    Finite (Wasm.IEEE64.sub a b) ∧
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
      unitRoundoff64 * |value a - value b| := by
  have hn := negate_spec b hb
  have hv : value (Wasm.IEEE64.negate b) = -value b := by
    simp [value, hn.2]
    ring
  have hs := add_real_relative_top a (Wasm.IEEE64.negate b) ha hn.1
    (by simpa only [hv, ← sub_eq_add_neg] using hbound)
  simpa only [Wasm.IEEE64.sub, hv, ← sub_eq_add_neg] using hs

open F64Approx in
/-- `F64Approx.approx_add` up to the overflow threshold. -/
theorem approx_add_top {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea)
    (hb : Approx b vb eb) (B : ℝ) (hB : |va + vb| + (ea + eb) ≤ B)
    (hBmax : B < 2 ^ 1024 - 2 ^ 970) :
    Approx (Wasm.IEEE64.add a b) (va + vb) (ea + eb + B / 2 ^ 53) := by
  have hsum : |(value a + value b) - (va + vb)| ≤ ea + eb := by
    rw [show (value a + value b) - (va + vb) = (value a - va) + (value b - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 hb.2)
  have hm : |value a + value b| ≤ B := by
    have := abs_sub_abs_le_abs_sub (value a + value b) (va + vb)
    linarith
  have hr := add_real_relative_top a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a + value b| ≤ B / 2 ^ 53 := by
    rw [unitRoundoff64, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hm (by positivity)
  calc |value (Wasm.IEEE64.add a b) - (va + vb)|
      ≤ |value (Wasm.IEEE64.add a b) - (value a + value b)| +
          |(value a + value b) - (va + vb)| := abs_sub_le _ _ _
    _ ≤ B / 2 ^ 53 + (ea + eb) := add_le_add (hr.2.trans hu) hsum
    _ = ea + eb + B / 2 ^ 53 := by ring

open F64Approx in
/-- `F64Approx.approx_sub` up to the overflow threshold. -/
theorem approx_sub_top {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea)
    (hb : Approx b vb eb) (B : ℝ) (hB : |va - vb| + (ea + eb) ≤ B)
    (hBmax : B < 2 ^ 1024 - 2 ^ 970) :
    Approx (Wasm.IEEE64.sub a b) (va - vb) (ea + eb + B / 2 ^ 53) := by
  have hdiff : |(value a - value b) - (va - vb)| ≤ ea + eb := by
    rw [show (value a - value b) - (va - vb) = (value a - va) + -(value b - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 (by rw [abs_neg]; exact hb.2))
  have hm : |value a - value b| ≤ B := by
    have := abs_sub_abs_le_abs_sub (value a - value b) (va - vb)
    linarith
  have hr := sub_real_relative_top a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a - value b| ≤ B / 2 ^ 53 := by
    rw [unitRoundoff64, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hm (by positivity)
  calc |value (Wasm.IEEE64.sub a b) - (va - vb)|
      ≤ |value (Wasm.IEEE64.sub a b) - (value a - value b)| +
          |(value a - value b) - (va - vb)| := abs_sub_le _ _ _
    _ ≤ B / 2 ^ 53 + (ea + eb) := add_le_add (hr.2.trans hu) hdiff
    _ = ea + eb + B / 2 ^ 53 := by ring

#print axioms top_finite
#print axioms signed_pack_relative_top
#print axioms add_real_relative_top
#print axioms approx_add_top
#print axioms approx_sub_top

end LeanExe.ProofKit.F64TopPack
