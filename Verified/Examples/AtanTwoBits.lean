import Verified.Examples.AtanTwoAtan
import Verified.Examples.AtanTwoArg

/-!
Word facts for `Atan.atan2`.  The tests of the code on the high words `ix`, `iy` and the low
words `lx`, `ly` become arithmetic on `toNat`: the NaN test fails for finite inputs, the zero test
holds exactly for `±0`, and the shifted difference `k` of the high words is `(iy - ix)/2 ^ 20` for
`iy ≥ ix` and `2 ^ 64` minus the rounded-up quotient otherwise.  `m` is the sign bit of `y` plus
twice that of `x`.  The words of the constant results come from evaluating the operations.
-/

namespace Verified.Examples.AtanTwoBits
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanTwoBranches

set_option exponentiation.threshold 4096

theorem ix_toNat (x : Float) : (ixOf x).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 32 :=
  F64UpperWord.high_toNat x.toBits

theorem ix_lt (x : Float) : (ixOf x).toNat < 2 ^ 31 := by
  rw [ix_toNat]
  omega

theorem lx_toNat (x : Float) : (lxOf x).toNat = x.toBits.toNat % 2 ^ 32 := by
  simp only [lxOf, UInt64.toNat_and]
  rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem exp_ix (x : Float) : Wasm.IEEE64.exponent x.toBits = (ixOf x).toNat / 2 ^ 20 := by
  rw [ix_toNat]
  simp only [Wasm.IEEE64.exponent]
  have := x.toBits.toNat_lt
  omega

theorem shr63 (k : UInt64) : (k >>> 63).toNat = k.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem shr20 (k : UInt64) : (k >>> 20).toNat = k.toNat / 2 ^ 20 := by
  rw [UInt64.toNat_shiftRight, show (20 : UInt64).toNat % 64 = 20 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem sign_toNat (w : UInt64) :
    (Wasm.IEEE64.sign w = true ↔ w.toNat / 2 ^ 63 = 1) ∧
      (Wasm.IEEE64.sign w = false ↔ w.toNat / 2 ^ 63 = 0) := by
  have := w.toNat_lt
  simp only [Wasm.IEEE64.sign, decide_eq_true_eq, decide_eq_false_iff_not, not_le]
  omega

theorem or_small (a s : ℕ) (hs : s < 2 ^ 20) : (a ||| s) / 2 ^ 20 = a / 2 ^ 20 := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib,
    Nat.shiftRight_eq_div_pow s, Nat.div_eq_of_lt hs, Nat.or_zero]

/-- fdlibm's NaN test fails for a finite word. -/
theorem nan_test (x : Float) (hx : Finite x.toBits) :
    (ixOf x ||| ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31)) ≤ 0x7ff00000 := by
  have hf : (ixOf x).toNat < 0x7ff00000 := F64UpperWord.finite_high x.toBits hx
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_or]
  have hs : ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31).toNat < 2 ^ 20 := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_and,
      show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow]
    have h1 : (lxOf x).toNat < 2 ^ 32 := by
      rw [lx_toNat]
      omega
    have h2 : (0 - lxOf x).toNat &&& (0xFFFFFFFF : UInt64).toNat < 2 ^ 32 := by
      rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
    have h3 := Nat.or_lt_two_pow h1 h2
    omega
  have h4 := or_small (ixOf x).toNat _ hs
  rw [show (0x7ff00000 : UInt64).toNat = 0x7ff00000 from rfl]
  omega

/-- fdlibm's NaN test fails for an infinite word, whose low word is 0. -/
theorem nan_test_inf (x : Float) (hx : (ixOf x).toNat = 0x7ff00000) (hl : (lxOf x).toNat = 0) :
    (ixOf x ||| ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31)) ≤ 0x7ff00000 := by
  have hl0 : lxOf x = 0 := UInt64.toNat_inj.mp (by rw [hl]; rfl)
  rw [hl0, UInt64.le_iff_toNat_le, UInt64.toNat_or, hx]
  decide

theorem not_gt_of_le {a b : UInt64} (h : a ≤ b) : ¬ b < a := by
  rw [UInt64.le_iff_toNat_le] at h
  rw [UInt64.lt_iff_toNat_lt]
  omega

theorem not_nan (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits) : notNaN y x := by
  unfold notNaN
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]
  exact ⟨not_gt_of_le (nan_test x hx), not_gt_of_le (nan_test y hy)⟩

theorem value_eq_zero_iff (w : UInt64) : value w = 0 ↔ w.toNat % 2 ^ 63 = 0 := by
  have key : Wasm.IEEE64.scaledMagnitude w = 0 ↔ w.toNat % 2 ^ 63 = 0 := by
    have := w.toNat_lt
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      beq_iff_eq]
    split_ifs with h
    · omega
    · constructor
      · intro h2
        exfalso
        have : 0 < (2 ^ 52 + w.toNat % 2 ^ 52) * 2 ^ (w.toNat / 2 ^ 52 % 2 ^ 11 - 1) := by
          positivity
        omega
      · intro h2
        omega
  have ha := F64RoundNearest.abs_value w
  constructor
  · intro h
    rw [h, abs_zero] at ha
    apply key.mp
    by_contra hne
    have : (0 : ℝ) < (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
      have : (0 : ℝ) < Wasm.IEEE64.scaledMagnitude w := by exact_mod_cast Nat.pos_of_ne_zero hne
      positivity
    linarith
  · intro h
    rw [key.mpr h, Nat.cast_zero, zero_div] at ha
    exact abs_eq_zero.mp ha

/-- fdlibm's zero test `(ix | lx) == 0` holds exactly for `±0`. -/
theorem zero_test (x : Float) :
    (ixOf x ||| lxOf x == 0) = decide (value x.toBits = 0) := by
  have hw := x.toBits.toNat_lt
  have hi := ix_toNat x
  have hl := lx_toNat x
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, value_eq_zero_iff, ← UInt64.toNat_inj,
    UInt64.toNat_or, show (0 : UInt64).toNat = 0 from rfl, Nat.or_eq_zero_iff, hi, hl]
  omega

theorem one_bits (x : Float) (h : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true) :
    x.toBits = 0x3FF0000000000000 := by
  have hw := x.toBits.toNat_lt
  have hl := lx_toNat x
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := congrArg UInt64.toNat h1
  have h2' := congrArg UInt64.toNat h2
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow, show (0x3ff00000 : UInt64).toNat = 0x3ff00000 from rfl] at h1'
  rw [hl, show (0 : UInt64).toNat = 0 from rfl] at h2'
  apply UInt64.toNat_inj.mp
  rw [show (0x3FF0000000000000 : UInt64).toNat = 0x3FF0000000000000 from rfl]
  omega

theorem one_test (x : Float) (h : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true) :
    value x.toBits = 1 := by
  rw [one_bits x h, AtanTheoremCases.word_eq 0x3FF0000000000000 1 (by decide +kernel)]
  norm_num

theorem inf_test (x : Float) (hx : Finite x.toBits) : (ixOf x == 0x7ff00000) = false := by
  have hf : (ixOf x).toNat < 0x7ff00000 := F64UpperWord.finite_high x.toBits hx
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg UInt64.toNat h
  rw [show (0x7ff00000 : UInt64).toNat = 0x7ff00000 from rfl] at this
  omega

theorem k_cases (y x : Float) :
    ((ixOf x).toNat ≤ (ixOf y).toNat →
      (kOf2 y x).toNat = ((ixOf y).toNat - (ixOf x).toNat) / 2 ^ 20) ∧
    ((ixOf y).toNat < (ixOf x).toNat →
      (kOf2 y x).toNat =
        2 ^ 64 - 2 ^ 44 + (2 ^ 64 - ((ixOf x).toNat - (ixOf y).toNat)) / 2 ^ 20) := by
  have hix := ix_lt x
  have hiy := ix_lt y
  have hd : (ixOf y - ixOf x).toNat = (2 ^ 64 - (ixOf x).toNat + (ixOf y).toNat) % 2 ^ 64 :=
    UInt64.toNat_sub _ _
  constructor
  · intro hle
    have hz : ((ixOf y - ixOf x) >>> 63 == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg UInt64.toNat h
      rw [shr63, hd, show (1 : UInt64).toNat = 1 from rfl] at this
      omega
    unfold kOf2
    rw [hz, if_neg (by decide)]
    simp only [UInt64.toNat_or, shr20, hd, show (0 : UInt64).toNat = 0 from rfl, Nat.or_zero]
    omega
  · intro hlt
    have ho : ((ixOf y - ixOf x) >>> 63 == 1) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, shr63, hd, show (1 : UInt64).toNat = 1 from rfl]
      omega
    unfold kOf2
    rw [ho, if_pos rfl]
    simp only [UInt64.toNat_or, shr20, hd]
    rw [show (0xFFFFF00000000000 : UInt64).toNat = 2 ^ 44 * (2 ^ 20 - 1) from rfl]
    have hb : (2 ^ 64 - (ixOf x).toNat + (ixOf y).toNat) % 2 ^ 64 / 2 ^ 20 < 2 ^ 44 := by omega
    rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hb]
    omega

theorem big_cond (y x : Float)
    (h : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = true) :
    (ixOf x).toNat + 61 * 2 ^ 20 ≤ (ixOf y).toNat := by
  obtain ⟨k1, k2⟩ := k_cases y x
  have hix := ix_lt x
  have hiy := ix_lt y
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, gt_iff_lt, ← UInt64.toNat_inj,
    shr63, UInt64.lt_iff_toNat_lt, show (0 : UInt64).toNat = 0 from rfl] at h
  rw [show (60 : UInt64).toNat = 60 from rfl] at h
  rcases Nat.lt_or_ge (ixOf y).toNat (ixOf x).toNat with hlt | hge
  · rw [k2 hlt] at h
    omega
  · rw [k1 hge] at h
    omega

theorem nbig_cond (y x : Float)
    (h : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = false) :
    (ixOf y).toNat < (ixOf x).toNat + 61 * 2 ^ 20 := by
  by_contra hc
  push Not at hc
  have hk := (k_cases y x).1 (by omega)
  have hiy := ix_lt y
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, ne_eq,
    ← UInt64.toNat_inj, shr63, gt_iff_lt, UInt64.lt_iff_toNat_lt,
    show (0 : UInt64).toNat = 0 from rfl, show (60 : UInt64).toNat = 60 from rfl, hk] at h
  omega

theorem tiny_cond (y x : Float)
    (h : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = true) :
    Wasm.IEEE64.sign x.toBits = true ∧ (ixOf y).toNat + 60 * 2 ^ 20 < (ixOf x).toNat := by
  obtain ⟨k1, k2⟩ := k_cases y x
  have hix := ix_lt x
  have hiy := ix_lt y
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, h63⟩, hlt⟩ := h
  rw [F64UpperWord.sign_test] at hs
  refine ⟨hs, ?_⟩
  rw [beq_iff_eq, ← UInt64.toNat_inj, shr63, show (1 : UInt64).toNat = 1 from rfl] at h63
  rw [UInt64.lt_iff_toNat_lt,
    show (0xFFFFFFFFFFFFFFC4 : UInt64).toNat = 2 ^ 64 - 60 from rfl] at hlt
  rcases Nat.lt_or_ge (ixOf y).toNat (ixOf x).toNat with hl | hge
  · rw [k2 hl] at hlt
    omega
  · rw [k1 hge] at h63
    omega

theorem m_toNat (y x : Float) :
    (mOf y x).toNat = y.toBits.toNat / 2 ^ 63 + 2 * (x.toBits.toNat / 2 ^ 63) := by
  have hy := y.toBits.toNat_lt
  have hx := x.toBits.toNat_lt
  unfold mOf
  simp only [UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_shiftRight,
    show (32 : UInt64).toNat % 64 = 32 from rfl, show (31 : UInt64).toNat % 64 = 31 from rfl,
    show (30 : UInt64).toNat % 64 = 30 from rfl, Nat.shiftRight_eq_div_pow,
    show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl]
  have e1 : y.toBits.toNat / 2 ^ 32 / 2 ^ 31 = y.toBits.toNat / 2 ^ 63 := by omega
  have e2 : x.toBits.toNat / 2 ^ 63 = x.toBits.toNat / 2 ^ 32 / 2 ^ 30 / 2 := by omega
  have ha : y.toBits.toNat / 2 ^ 63 < 2 := by omega
  have hb : x.toBits.toNat / 2 ^ 32 / 2 ^ 30 < 4 := by omega
  rw [e1, e2]
  generalize y.toBits.toNat / 2 ^ 63 = a at ha ⊢
  generalize x.toBits.toNat / 2 ^ 32 / 2 ^ 30 = b at hb ⊢
  interval_cases a <;> interval_cases b <;> rfl

theorem m_one_toNat (y x : Float) : (mOf y x &&& 1).toNat = y.toBits.toNat / 2 ^ 63 := by
  have hy := y.toBits.toNat_lt
  rw [UInt64.toNat_and, m_toNat, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem quad_zero (z : Float) : quadTail z 0 = z := rfl

theorem quad_one (z : Float) : quadTail z 1 = -z := rfl

theorem quad_two (z : Float) : quadTail z 2 = piF - (z - piLoF) := rfl

theorem quad_three (z : Float) : quadTail z 3 = (z - piLoF) - piF := rfl

theorem half_bits :
    (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359).toBits =
      0x3FF921FB54442D18 := by
  rw [F64Bits.toBits_add, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  decide +kernel

theorem half_neg_bits :
    (-Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359).toBits =
      Wasm.IEEE64.negate 0x3FF921FB54442D18 := by
  rw [F64Bits.toBits_sub, F64Bits.toBits_neg, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  decide +kernel

theorem big_bits2 : (Float.ofBits 0x3FF921FB54442D18 + 0.5 * piLoF).toBits = 0x3FF921FB54442D18 := by
  rw [piLoF, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
    F64Bits.toBits_ofBits, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  decide +kernel

theorem big_neg_bits2 :
    (-(Float.ofBits 0x3FF921FB54442D18 + 0.5 * piLoF)).toBits =
      Wasm.IEEE64.negate 0x3FF921FB54442D18 := by
  rw [F64Bits.toBits_neg, big_bits2]
  decide +kernel

theorem pi_bits : (piF - (0.0 - piLoF)).toBits = 0x400921FB54442D18 := by
  rw [piF, piLoF, F64Bits.toBits_sub, F64Bits.toBits_sub, F64Bits.toBits_ofBits,
    F64Bits.toBits_ofBits, show (0.0 : Float).toBits = 0 from rfl]
  decide +kernel

theorem pi_neg_bits : ((0.0 - piLoF) - piF).toBits = Wasm.IEEE64.negate 0x400921FB54442D18 := by
  rw [piF, piLoF, F64Bits.toBits_sub, F64Bits.toBits_sub, F64Bits.toBits_ofBits,
    F64Bits.toBits_ofBits, show (0.0 : Float).toBits = 0 from rfl]
  decide +kernel

#print axioms not_nan
#print axioms zero_test
#print axioms k_cases
#print axioms m_toNat
#print axioms pi_neg_bits

end Verified.Examples.AtanTwoBits
