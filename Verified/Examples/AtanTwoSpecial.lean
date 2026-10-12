import Verified.Examples.AtanTwoBits

/-!
The exceptional inputs of `Atan.atan2 y x` as words.  For `y = ±0` and `x` not NaN the result is
`y` when the sign bit of `x` is clear and `±π` rounded otherwise.  For `y = ±∞` and finite `x` it
is `±π/2` rounded.  For `x = ±∞` and finite nonzero `y` it is `±0` or `±π` rounded, and for both
infinite it is `±π/4` or `±3π/4` rounded, by IEEE 754's rules.
-/

namespace Verified.Examples.AtanTwoSpecial
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanTwoBranches AtanTwoBits

set_option exponentiation.threshold 4096

/-- Closes `(e).toBits = w` for a constant expression `e` of words and literals. -/
macro "bits_eval" : tactic => `(tactic| (simp only [F64Bits.toBits_add, F64Bits.toBits_sub,
    F64Bits.toBits_mul, F64Bits.toBits_neg, F64Bits.toBits_ofBits,
    show (3.0 : Float).toBits = 0x4008000000000000 from rfl,
    show (0.0 : Float).toBits = 0 from rfl] <;> decide +kernel))

theorem atan2_yzero_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = true) :
    Atan.atan2 y x = if mOf y x == 0 || mOf y x == 1 then y
      else if mOf y x == 2 then Float.ofBits 0x400921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359
      else -Float.ofBits 0x400921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359 := by
  unfold notNaN mOf ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, Bool.false_eq_true, ite_false, ite_true]
  try rfl

theorem atan2_xinf_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = false)
    (h4 : (ixOf x == 0x7ff00000) = true) :
    Atan.atan2 y x = if ixOf y == 0x7ff00000 then
        (if mOf y x == 0 then Float.ofBits 0x3FE921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359
        else if mOf y x == 1 then
          -Float.ofBits 0x3FE921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359
        else if mOf y x == 2 then
          3.0 * Float.ofBits 0x3FE921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359
        else -3.0 * Float.ofBits 0x3FE921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359)
      else (if mOf y x == 0 then 0.0 else if mOf y x == 1 then -0.0
        else if mOf y x == 2 then
          Float.ofBits 0x400921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359
        else -Float.ofBits 0x400921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359) := by
  unfold notNaN mOf ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, h4, Bool.false_eq_true, ite_false, ite_true]
  try rfl

theorem atan2_yinf_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = false)
    (h4 : (ixOf x == 0x7ff00000) = false) (h5 : (ixOf y == 0x7ff00000) = true) :
    Atan.atan2 y x = if y.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359 := by
  unfold notNaN ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false, ite_true]
  try rfl

/-- The fields of an infinite word. -/
theorem inf_fields (x : Float)
    (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    (ixOf x).toNat = 0x7ff00000 ∧ (lxOf x).toNat = 0 ∧ value x.toBits ≠ 0 ∧
      (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by
  have hv : value x.toBits ≠ 0 := by
    rw [Ne, value_eq_zero_iff]
    rcases hx with h | h <;> rw [h] <;> decide
  have h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by
    unfold lxOf
    rcases hx with h | h <;> rw [h] <;> decide
  refine ⟨?_, ?_, hv, h1⟩
  · rw [ix_toNat]
    rcases hx with h | h <;> rw [h] <;> decide
  · rw [lx_toNat]
    rcases hx with h | h <;> rw [h] <;> decide

theorem not_nan_inf (y x : Float) (hy : Finite y.toBits)
    (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) : notNaN y x := by
  obtain ⟨hix, hlx, -, -⟩ := inf_fields x hx
  unfold notNaN
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
  exact ⟨not_gt_of_le (nan_test_inf x hix hlx), not_gt_of_le (nan_test y hy)⟩

theorem not_nan_inf2 (y x : Float) (hx : Finite x.toBits)
    (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000) : notNaN y x := by
  obtain ⟨hiy, hly, -, -⟩ := inf_fields y hy
  unfold notNaN
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
  exact ⟨not_gt_of_le (nan_test x hx), not_gt_of_le (nan_test_inf y hiy hly)⟩

theorem not_nan_inf3 (y x : Float)
    (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000)
    (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) : notNaN y x := by
  obtain ⟨hiy, hly, -, -⟩ := inf_fields y hy
  obtain ⟨hix, hlx, -, -⟩ := inf_fields x hx
  unfold notNaN
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
  exact ⟨not_gt_of_le (nan_test_inf x hix hlx), not_gt_of_le (nan_test_inf y hiy hly)⟩

theorem m_lit (y x : Float) (a b : Bool) (hy : Wasm.IEEE64.sign y.toBits = a)
    (hx : Wasm.IEEE64.sign x.toBits = b) :
    (mOf y x).toNat = (if a then 1 else 0) + 2 * (if b then 1 else 0) := by
  rw [m_toNat]
  obtain ⟨hyT, hyF⟩ := sign_toNat y.toBits
  obtain ⟨hxT, hxF⟩ := sign_toNat x.toBits
  cases a <;> cases b
  · rw [hyF.mp hy, hxF.mp hx]
    rfl
  · rw [hyF.mp hy, hxT.mp hx]
    rfl
  · rw [hyT.mp hy, hxF.mp hx]
    rfl
  · rw [hyT.mp hy, hxT.mp hx]
    rfl

theorem m00 (y x : Float) (hy : Wasm.IEEE64.sign y.toBits = false)
    (hx : Wasm.IEEE64.sign x.toBits = false) : mOf y x = 0 :=
  UInt64.toNat_inj.mp (by rw [m_lit y x _ _ hy hx]; rfl)

theorem m10 (y x : Float) (hy : Wasm.IEEE64.sign y.toBits = true)
    (hx : Wasm.IEEE64.sign x.toBits = false) : mOf y x = 1 :=
  UInt64.toNat_inj.mp (by rw [m_lit y x _ _ hy hx]; rfl)

theorem m01 (y x : Float) (hy : Wasm.IEEE64.sign y.toBits = false)
    (hx : Wasm.IEEE64.sign x.toBits = true) : mOf y x = 2 :=
  UInt64.toNat_inj.mp (by rw [m_lit y x _ _ hy hx]; rfl)

theorem m11 (y x : Float) (hy : Wasm.IEEE64.sign y.toBits = true)
    (hx : Wasm.IEEE64.sign x.toBits = true) : mOf y x = 3 :=
  UInt64.toNat_inj.mp (by rw [m_lit y x _ _ hy hx]; rfl)

theorem lit_beq : ((0 : UInt64) == 0) = true ∧ ((0 : UInt64) == 1) = false ∧
    ((0 : UInt64) == 2) = false ∧ ((1 : UInt64) == 0) = false ∧ ((1 : UInt64) == 1) = true ∧
    ((1 : UInt64) == 2) = false ∧ ((2 : UInt64) == 0) = false ∧ ((2 : UInt64) == 1) = false ∧
    ((2 : UInt64) == 2) = true ∧ ((3 : UInt64) == 0) = false ∧ ((3 : UInt64) == 1) = false ∧
    ((3 : UInt64) == 2) = false := by decide

theorem inf_ix_test (x : Float) (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    (ixOf x == 0x7ff00000) = true := by
  rcases hx with h | h <;> unfold ixOf <;> rw [h] <;> decide

theorem sign_bits_pos : Wasm.IEEE64.sign 0x7FF0000000000000 = false := by decide

theorem sign_bits_neg : Wasm.IEEE64.sign 0xFFF0000000000000 = true := by decide

/-- `y = ±0` and `x` not NaN. -/
theorem atan2_zero (y x : Float) (hy : y.toBits = 0 ∨ y.toBits = 0x8000000000000000)
    (hxn : Wasm.IEEE64.isNaN x.toBits = false) :
    (Atan.atan2 y x).toBits = if Wasm.IEEE64.sign x.toBits then
      (if Wasm.IEEE64.sign y.toBits then 0xC00921FB54442D18 else 0x400921FB54442D18)
      else y.toBits := by
  have hyf : Finite y.toBits := by
    rcases hy with h | h <;> rw [h] <;> unfold CodeLib.IEEE64.Finite <;> decide
  have hn : notNaN y x := by
    have hN := x.toBits.toNat_lt
    have hix := ix_toNat x
    have hlx := lx_toNat x
    unfold notNaN
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
    refine ⟨not_gt_of_le ?_, not_gt_of_le (nan_test y hyf)⟩
    by_cases hf : Finite x.toBits
    · exact nan_test x hf
    · have he : x.toBits.toNat % 2 ^ 63 / 2 ^ 52 = 2047 ∧ x.toBits.toNat % 2 ^ 52 = 0 := by
        simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
          ne_eq, not_not] at hf
        simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_false_iff,
          beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hxn
        omega
      exact nan_test_inf x (by rw [hix]; omega) (by rw [hlx]; omega)
  have hv : value y.toBits = 0 := by
    rw [value_eq_zero_iff]
    rcases hy with h | h <;> rw [h] <;> decide
  by_cases h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true
  · have hb := one_bits x h1
    rw [atan2_one_eq y x hn h1, hb, show Wasm.IEEE64.sign 0x3FF0000000000000 = false by decide]
    simp only [Bool.false_eq_true, ite_false]
    rcases hy with h | h
    · exact AtanTheoremSpecial.atan_zero y h |>.trans h.symm
    · exact AtanTheoremSpecial.atan_neg_zero y h |>.trans h.symm
  have h1' : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by simpa using h1
  have h2 : (ixOf y ||| lxOf y == 0) = true := by
    rw [zero_test, decide_eq_true_eq]
    exact hv
  rw [atan2_yzero_eq y x hn h1' h2]
  cases hsy : Wasm.IEEE64.sign y.toBits <;> cases hsx : Wasm.IEEE64.sign x.toBits <;>
    (first
      | rw [m00 y x hsy hsx]
      | rw [m10 y x hsy hsx]
      | rw [m01 y x hsy hsx]
      | rw [m11 y x hsy hsx]) <;>
    simp only [lit_beq, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
      Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true] <;> bits_eval

/-- `y = ±∞` and finite `x`: `±π/2` rounded. -/
theorem atan2_inf_y (y x : Float) (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000)
    (hx : Finite x.toBits) :
    (Atan.atan2 y x).toBits =
      if Wasm.IEEE64.sign y.toBits then 0xBFF921FB54442D18 else 0x3FF921FB54442D18 := by
  have hn := not_nan_inf2 y x hx hy
  obtain ⟨hiy, hly, hy0, -⟩ := inf_fields y hy
  have hsy : Wasm.IEEE64.sign y.toBits = (y.toBits >>> 32 >>> 31 == 1) :=
    (F64UpperWord.sign_test y.toBits).symm
  by_cases h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true
  · rw [atan2_one_eq y x hn h1]
    rcases hy with h | h
    · rw [(AtanTheoremSpecial.atan_pos_inf y h).1, h, sign_bits_pos]
      rfl
    · rw [(AtanTheoremSpecial.atan_neg_inf y h).1, h, sign_bits_neg]
      rfl
  have h1' : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by simpa using h1
  have h2 : (ixOf y ||| lxOf y == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hy0
  have hres : (if y.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359).toBits =
      if Wasm.IEEE64.sign y.toBits then 0xBFF921FB54442D18 else 0x3FF921FB54442D18 := by
    rw [hsy]
    cases (y.toBits >>> 32 >>> 31 == 1) <;>
      simp only [Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true] <;> bits_eval
  by_cases hx0 : value x.toBits = 0
  · have h3 : (ixOf x ||| lxOf x == 0) = true := by
      rw [zero_test, decide_eq_true_eq]
      exact hx0
    rw [atan2_xzero_eq y x hn h1' h2 h3]
    exact hres
  have h3 : (ixOf x ||| lxOf x == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hx0
  rw [atan2_yinf_eq y x hn h1' h2 h3 (inf_test x hx) (inf_ix_test y hy)]
  exact hres

/-- `x = ±∞` and finite nonzero `y`: `±0` for `+∞` and `±π` rounded for `-∞`. -/
theorem atan2_inf_x (y x : Float) (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000)
    (hy : Finite y.toBits) (hy0 : value y.toBits ≠ 0) :
    (Atan.atan2 y x).toBits = if Wasm.IEEE64.sign x.toBits then
      (if Wasm.IEEE64.sign y.toBits then 0xC00921FB54442D18 else 0x400921FB54442D18)
      else (if Wasm.IEEE64.sign y.toBits then 0x8000000000000000 else 0) := by
  have hn := not_nan_inf y x hy hx
  obtain ⟨hix, hlx, hx0, h1⟩ := inf_fields x hx
  have h2 : (ixOf y ||| lxOf y == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hy0
  have h3 : (ixOf x ||| lxOf x == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hx0
  rw [atan2_xinf_eq y x hn h1 h2 h3 (inf_ix_test x hx), if_neg (by rw [inf_test y hy]; decide)]
  cases hsx : Wasm.IEEE64.sign x.toBits <;> cases hsy : Wasm.IEEE64.sign y.toBits <;>
    (first
      | rw [m00 y x hsy hsx]
      | rw [m10 y x hsy hsx]
      | rw [m01 y x hsy hsx]
      | rw [m11 y x hsy hsx]) <;>
    simp only [lit_beq, Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true] <;>
    bits_eval

/-- `x` and `y` infinite: `±π/4` or `±3π/4` rounded. -/
theorem atan2_inf_both (y x : Float)
    (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000)
    (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    (Atan.atan2 y x).toBits = if Wasm.IEEE64.sign x.toBits then
      (if Wasm.IEEE64.sign y.toBits then 0xC002D97C7F3321D2 else 0x4002D97C7F3321D2)
      else (if Wasm.IEEE64.sign y.toBits then 0xBFE921FB54442D18 else 0x3FE921FB54442D18) := by
  have hn := not_nan_inf3 y x hy hx
  obtain ⟨-, -, hy0, -⟩ := inf_fields y hy
  obtain ⟨-, -, hx0, h1⟩ := inf_fields x hx
  have h2 : (ixOf y ||| lxOf y == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hy0
  have h3 : (ixOf x ||| lxOf x == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hx0
  rw [atan2_xinf_eq y x hn h1 h2 h3 (inf_ix_test x hx), if_pos (inf_ix_test y hy)]
  cases hsx : Wasm.IEEE64.sign x.toBits <;> cases hsy : Wasm.IEEE64.sign y.toBits <;>
    (first
      | rw [m00 y x hsy hsx]
      | rw [m10 y x hsy hsx]
      | rw [m01 y x hsy hsx]
      | rw [m11 y x hsy hsx]) <;>
    simp only [lit_beq, Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true] <;>
    bits_eval

#print axioms atan2_zero
#print axioms atan2_inf_y
#print axioms atan2_inf_x
#print axioms atan2_inf_both

end Verified.Examples.AtanTwoSpecial
