import Verified.Examples.AtanhTheoremLarge
import Verified.Examples.AsinTheoremSpecial
import Verified.Examples.AsinhTheoremTiny

/-!
**`atanh` within two steps** and its exceptional inputs.  The code's first test,
`(ix ||| ((lx ||| -lx) >>> 31)) > 0x3ff00000`, holds exactly when `|x| > 1` or `x` is not finite:
the shifted low word is 1 when `lx ≠ 0` and 0 otherwise (`low_bit`), and an `or` with a bit below
2 adds at most 1 to an even bound (`or_bit_le`).  Then `|x| = 1` gives `x/0 = ±∞`, `|x| < 2 ^ -28`
gives `x`, and the rest is `±atanhT x`, whose two ranges `AtanhTheoremSmallCases` and
`AtanhTheoremLarge` cover.
-/

namespace Verified.Examples.AtanhTheorem
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanhTheoremBranches

set_option exponentiation.threshold 4096

/-- The shifted low-word test of the code. -/
def lowBit (x : Float) : UInt64 :=
  ((x.toBits &&& 0xFFFFFFFF) ||| ((0 - (x.toBits &&& 0xFFFFFFFF)) &&& 0xFFFFFFFF)) >>> 31

theorem or_bit_le (a t : ℕ) (ht : t < 2) : a ||| t ≤ 2 * (a / 2) + 1 := by
  have h2 : a % 2 ||| t < 2 ^ 1 := Nat.or_lt_two_pow (by omega) (by omega)
  have e1 : 2 ^ 1 * (a / 2) + a % 2 = 2 ^ 1 * (a / 2) ||| a % 2 :=
    Nat.two_pow_add_eq_or_of_lt (by omega) (a / 2)
  have e1' : a = 2 ^ 1 * (a / 2) ||| a % 2 := by rw [← e1]; omega
  have e2 : 2 ^ 1 * (a / 2) + (a % 2 ||| t) = 2 ^ 1 * (a / 2) ||| (a % 2 ||| t) :=
    Nat.two_pow_add_eq_or_of_lt h2 (a / 2)
  have h3 : a % 2 ||| t < 2 := h2
  calc a ||| t = (2 ^ 1 * (a / 2) ||| a % 2) ||| t := by rw [← e1']
    _ = 2 ^ 1 * (a / 2) ||| (a % 2 ||| t) := Nat.or_assoc _ _ _
    _ = 2 ^ 1 * (a / 2) + (a % 2 ||| t) := e2.symm
    _ ≤ 2 * (a / 2) + 1 := by rw [pow_one]; omega

theorem low_bit (x : Float) :
    (lowBit x).toNat = if x.toBits.toNat % 2 ^ 32 = 0 then 0 else 1 := by
  have hl := Log1pTheoremReduce.low_nat x.toBits
  set l := x.toBits &&& 0xFFFFFFFF with hldef
  have hl32 : l.toNat < 2 ^ 32 := by rw [hl]; omega
  have hneg : ((0 - l) &&& 0xFFFFFFFF).toNat = (2 ^ 32 - l.toNat) % 2 ^ 32 := by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_sub, show (0 : UInt64).toNat = 0 from rfl]
    have : (2 ^ 64 - l.toNat + 0) % 2 ^ 64 % 2 ^ 32 = (2 ^ 32 - l.toNat) % 2 ^ 32 := by omega
    exact this
  unfold lowBit
  rw [← hldef, UInt64.toNat_shiftRight, show (31 : UInt64).toNat % 64 = 31 from rfl,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_or, hneg]
  have hor : l.toNat ||| (2 ^ 32 - l.toNat) % 2 ^ 32 < 2 ^ 32 :=
    Nat.or_lt_two_pow hl32 (Nat.mod_lt _ (by norm_num))
  by_cases h0 : l.toNat = 0
  · rw [h0, ite_eq_left (by rw [← hl]; exact h0)]
    simp
  · rw [ite_eq_right (by rw [← hl]; exact h0)]
    have hge : 2 ^ 31 ≤ l.toNat ||| (2 ^ 32 - l.toNat) % 2 ^ 32 := by
      rcases Nat.lt_or_ge l.toNat (2 ^ 31) with h | h
      · have : 2 ^ 31 ≤ (2 ^ 32 - l.toNat) % 2 ^ 32 := by omega
        exact this.trans (by rw [Nat.or_comm]; exact Nat.left_le_or)
      · exact h.trans Nat.left_le_or
    omega

theorem atanh_tiny_eq (x : Float) (h1 : ixOf x < 0x3e300000)
    (hh : Float.ofBits 0x7E37E43C8800759C + x > 0.0) : Asinh.atanh x = x := by
  have h0 : ¬ (ixOf x ||| lowBit x) > 0x3ff00000 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_or]
    have hb := low_bit x
    have hi : (ixOf x).toNat < 0x3e300000 := UInt64.lt_iff_toNat_lt.mp h1
    have hle := or_bit_le (ixOf x).toNat (lowBit x).toNat (by rw [hb]; split <;> omega)
    simp only [UInt64.reduceToNat]
    omega
  have h2 : (ixOf x == 0x3ff00000) = false := by
    have hi : (ixOf x).toNat < 0x3e300000 := UInt64.lt_iff_toNat_lt.mp h1
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    rw [h] at hi
    simp at hi
  unfold lowBit ixOf at h0
  unfold ixOf at h1 h2
  simp only [Asinh.atanh, h0, h2, h1, hh, ite_false, decide_true, Bool.and_true, ite_true,
    Bool.false_eq_true]

theorem artanh_odd (v : ℝ) : Real.artanh (-v) = -Real.artanh v := by
  rw [Real.artanh, Real.artanh, show (1 + -v) / (1 - -v) = ((1 + v) / (1 - v))⁻¹ by
    rw [inv_div]; ring, Real.sqrt_inv, Real.log_inv]

theorem zero_finite : Finite (0.0 : Float).toBits := by
  rw [show (0.0 : Float).toBits = 0 from rfl]
  unfold CodeLib.IEEE64.Finite
  decide

theorem huge_gt_zero (x : Float) (hx : Finite x.toBits) (hs : |value x.toBits| < 1) :
    Float.ofBits 0x7E37E43C8800759C + x > 0.0 := by
  have hh : (10 : ℝ) ^ 299 ≤ value 0x7E37E43C8800759C := by
    rw [AtanTheoremReduce.value_word 0x7E37E43C8800759C (PolyBound.ratOfWord 0x7E37E43C8800759C) rfl]
    have : (10 ^ 299 : ℚ) ≤ PolyBound.ratOfWord 0x7E37E43C8800759C := by decide +kernel
    exact_mod_cast this
  have hh2 : value 0x7E37E43C8800759C ≤ (10 : ℝ) ^ 301 := by
    rw [AtanTheoremReduce.value_word 0x7E37E43C8800759C (PolyBound.ratOfWord 0x7E37E43C8800759C) rfl]
    have : PolyBound.ratOfWord 0x7E37E43C8800759C ≤ (10 ^ 301 : ℚ) := by decide +kernel
    exact_mod_cast this
  have hf : Wasm.IEEE64.isFinite 0x7E37E43C8800759C = true := by decide +kernel
  have hpos : (0 : ℝ) < value 0x7E37E43C8800759C := lt_of_lt_of_le (by positivity) hh
  have hB : |value 0x7E37E43C8800759C + value x.toBits| + (0 + 0) ≤ (10 : ℝ) ^ 302 := by
    have h1 := abs_add_le (value 0x7E37E43C8800759C) (value x.toBits)
    rw [abs_of_pos hpos] at h1
    have h2 : (10 : ℝ) ^ 301 + 1 ≤ 10 ^ 302 := by norm_num
    linarith
  have hx' : F64Approx.FApprox x (value x.toBits) 0 := F64Approx.approx_self _ hx
  have ha := F64Approx.fapprox_add (F64Approx.fapprox_ofBits _ hf) hx' _ hB (by norm_num)
  rw [gt_iff_lt, F64UpperWord.float_lt_iff _ _ zero_finite ha.1, Log1pTheoremTail.zero_bits_value]
  have hl := ha.lower
  have hs' := (abs_lt.mp hs).1
  have h3 : (0 : ℝ) + 0 + 10 ^ 302 / 2 ^ 53 ≤ 10 ^ 298 := by norm_num
  have h4 : (2 : ℝ) ≤ 10 ^ 299 - 10 ^ 298 := by norm_num
  linarith

theorem atanh_out_eq (x : Float) (h0 : (ixOf x ||| lowBit x) > 0x3ff00000) :
    Asinh.atanh x = (x - x) / (x - x) := by
  unfold lowBit ixOf at h0
  simp only [Asinh.atanh, h0, ite_true]

theorem atanh_one_eq (x : Float) (h0 : ¬ (ixOf x ||| lowBit x) > 0x3ff00000)
    (h1 : (ixOf x == 0x3ff00000) = true) : Asinh.atanh x = x / 0.0 := by
  unfold lowBit ixOf at h0
  unfold ixOf at h1
  simp only [Asinh.atanh, h0, h1, ite_false, ite_true]

/-- Below 1 in magnitude the first test fails. -/
theorem in_condition (x : Float) (h : ixOf x < 0x3ff00000) :
    ¬ (ixOf x ||| lowBit x) > 0x3ff00000 := by
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_or]
  have hb := low_bit x
  have hi : (ixOf x).toNat < 0x3ff00000 := UInt64.lt_iff_toNat_lt.mp h
  have hle := or_bit_le (ixOf x).toNat (lowBit x).toNat (by rw [hb]; split <;> omega)
  simp only [UInt64.reduceToNat]
  omega

/-- An input outside `[-1, 1]`, infinite, or NaN passes the first test. -/
theorem out_condition (x : Float) (h : ¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1)) :
    (ixOf x ||| lowBit x) > 0x3ff00000 := by
  obtain ⟨h1, h2⟩ := AsinTheoremSpecial.out_conditions x h
  have hix : (ixOf x).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 32 := F64UpperWord.high_toNat x.toBits
  have h1' : 0x3ff00000 ≤ (ixOf x).toNat := UInt64.le_iff_toNat_le.mp h1
  have hb := low_bit x
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_or]
  simp only [UInt64.reduceToNat]
  rcases Nat.lt_or_ge 0x3ff00000 (ixOf x).toNat with c | c
  · exact lt_of_lt_of_le c Nat.left_le_or
  · have he : (ixOf x).toNat = 0x3ff00000 := le_antisymm c h1'
    have hl : x.toBits.toNat % 2 ^ 32 ≠ 0 := by
      intro hl0
      apply beq_eq_false_iff_ne.mp h2
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_or, UInt64.toNat_sub_of_le _ _ h1, show (0 : UInt64).toNat = 0 from rfl,
        show (AsinTheoremBranches.ixA x).toNat = (ixOf x).toNat from rfl, he,
        show (AsinTheoremBranches.lxA x).toNat = (x.toBits &&& 0xFFFFFFFF).toNat from rfl,
        Log1pTheoremReduce.low_nat, hl0]
      simp
    rw [hb, ite_eq_right hl, he]
    decide

/-- **`atanh` within two steps.**  For every finite `x` with `|x| < 1`, `Asinh.atanh x` lies within
two representable steps of the nearest-even rounding of `artanh x`. -/
theorem atanh_within_two (x : Float) (hx : Finite x.toBits) (hdom : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 2 (Real.artanh (value x.toBits)) (Asinh.atanh x).toBits := by
  have T28 := AtanTheorem.ix_lt x 0x3e300000 (by norm_num) (1 / 2 ^ 28) (by decide +kernel)
  have T1 := AtanTheorem.ix_lt x 0x3ff00000 (by norm_num) 1 (by decide +kernel)
  have T5 := AtanTheorem.ix_lt x 0x3fe00000 (by norm_num) (1 / 2) (by decide +kernel)
  push_cast at T28 T1 T5
  have hi1 : ixOf x < 0x3ff00000 := T1.mpr hdom
  have h0 := in_condition x hi1
  by_cases c1 : ixOf x < 0x3e300000
  · have hs := T28.mp c1
    rw [atanh_tiny_eq x c1 (huge_gt_zero x hx hdom)]
    have h := AsinhTheoremTiny.atanh_tiny_within x hx hs
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  have h28 : 1 / 2 ^ 28 ≤ |value x.toBits| := not_lt.mp (fun h => c1 (T28.mpr h))
  have h1 : (ixOf x == 0x3ff00000) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    rw [h] at hi1
    exact absurd hi1 (by decide)
  rw [atanh_main_eq x h0 h1 c1]
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  have hx0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at h28
    linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 28)]
  refine AsinhTheoremLarge.signed_two x (atanhT x) Real.artanh artanh_odd ?_ hx0
  unfold atanhT
  by_cases c2 : ixOf x < 0x3fe00000
  · rw [ite_eq_left c2]
    have h := AtanhTheoremSmallCases.atanh_small x.abs haf (by rw [hav]; exact h28)
      (by rw [hav]; exact T5.mp c2)
    rwa [hav] at h
  · rw [ite_eq_right c2]
    have h5 : 1 / 2 ≤ |value x.toBits| := not_lt.mp (fun h => c2 (T5.mpr h))
    have h := AtanhTheoremLarge.atanh_large x.abs haf (by rw [hav]; exact h5) (by rw [hav]; exact hdom)
    rwa [hav] at h

/-- NaN, the infinities, and `|x| > 1` give the canonical NaN. -/
theorem atanh_nan (x : Float) (h : ¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1)) :
    (Asinh.atanh x).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [atanh_out_eq x (out_condition x h), F64Bits.toBits_div, F64Bits.toBits_sub]
  exact AsinTheoremSpecial.self_quot_nan x.toBits

/-- A finite nonzero word divided by `+0` is the infinity of its sign. -/
theorem div_zero_word (w : UInt64) (hn : Wasm.IEEE64.isNaN w = false)
    (hi : Wasm.IEEE64.isInfinite w = false) (hm : (Wasm.IEEE64.scaledMagnitude w == 0) = false) :
    Wasm.IEEE64.div w 0 = Wasm.IEEE64.infinity (Wasm.IEEE64.sign w) := by
  have h0n : Wasm.IEEE64.isNaN 0 = false := by decide
  have h0i : Wasm.IEEE64.isInfinite 0 = false := by decide
  have h0s : Wasm.IEEE64.sign 0 = false := by decide
  have h0m : (Wasm.IEEE64.scaledMagnitude 0 == 0) = true := by decide
  simp only [Wasm.IEEE64.div, hn, h0n, hi, h0i, h0s, hm, h0m, Bool.or_self, Bool.false_eq_true,
    ite_false, ite_true, Bool.bne_false]

theorem atanh_one (x : Float) (h : x.toBits = 0x3FF0000000000000) :
    (Asinh.atanh x).toBits = 0x7FF0000000000000 := by
  rw [atanh_one_eq x (by unfold ixOf lowBit; rw [h]; decide) (by unfold ixOf; rw [h]; decide),
    F64Bits.toBits_div, h, show (0.0 : Float).toBits = 0 from rfl,
    div_zero_word _ (by decide) (by decide) (by decide +kernel)]
  decide

theorem atanh_neg_one (x : Float) (h : x.toBits = 0xBFF0000000000000) :
    (Asinh.atanh x).toBits = 0xFFF0000000000000 := by
  rw [atanh_one_eq x (by unfold ixOf lowBit; rw [h]; decide) (by unfold ixOf; rw [h]; decide),
    F64Bits.toBits_div, h, show (0.0 : Float).toBits = 0 from rfl,
    div_zero_word _ (by decide) (by decide) (by decide +kernel)]
  decide

theorem atanh_zero (x : Float) (h : x.toBits = 0) : (Asinh.atanh x).toBits = 0 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by rw [h]; exact F64Magnitude.value_zero
  rw [atanh_tiny_eq x (by unfold ixOf; rw [h]; decide)
    (huge_gt_zero x hx (by rw [hv, abs_zero]; norm_num)), h]

theorem atanh_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (Asinh.atanh x).toBits = 0x8000000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by
    rw [h, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x8000000000000000 = 0 by
      decide +kernel]
    norm_num
  rw [atanh_tiny_eq x (by unfold ixOf; rw [h]; decide)
    (huge_gt_zero x hx (by rw [hv, abs_zero]; norm_num)), h]

#print axioms or_bit_le
#print axioms low_bit
#print axioms artanh_odd
#print axioms atanh_within_two
#print axioms atanh_nan
#print axioms atanh_one
#print axioms atanh_neg_one
#print axioms atanh_zero
#print axioms atanh_neg_zero

end Verified.Examples.AtanhTheorem
