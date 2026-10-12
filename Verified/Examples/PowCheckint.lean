import Verified.Examples.Pow
import Verified.Examples.ExpBranches
import LeanExe.ProofKit.F64Magnitude

/-!
`Pow.checkint` on the bits of a finite nonzero `y`: 0 when `y` is not an integer, 1 when it is an
odd integer, and 2 when it is an even integer.  With exponent field `e` and fraction `f`,
`|y| = (2 ^ 52 + f) 2 ^ (e - 1075)`: below `e = 0x3ff` it lies below 1; above `0x3ff + 52` it is a
multiple of 2; in between it is an integer when the low `1075 - e` bits of `f` vanish, and odd
when bit `1075 - e` of `2 ^ 52 + f` is set.
-/

namespace Verified.Examples.PowCheckint
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem and_pow (x n : Nat) : x &&& 2 ^ n = x / 2 ^ n % 2 * 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : n = j
  · subst hj
    simp only [decide_true, Bool.and_true, le_refl, Nat.sub_self, Bool.true_and]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    simp
  · simp only [hj, decide_false, Bool.and_false]
    by_cases hnj : n ≤ j
    · have hlt : x / 2 ^ n % 2 < 2 ^ (j - n) :=
        lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
          (by
            have : 1 ≤ j - n := by omega
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by norm_num) this)
      rw [Nat.testBit_lt_two_pow hlt]
      simp
    · simp [hnj]

/-- `Pow.checkint` without its `let`, with `0x3ff + 52` written as 1075. -/
theorem checkint_eq (w : UInt64) : Pow.checkint w =
    if (w >>> 52) &&& 0x7ff < (0x3ff : UInt64) then 0
    else if (w >>> 52) &&& 0x7ff > (1075 : UInt64) then 2
    else if w &&& (((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff))) - 1) != 0 then 0
    else if w &&& ((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff))) != 0 then 1
    else 2 := rfl

theorem bne_toNat (x : UInt64) : (x != 0) = decide (x.toNat ≠ 0) := by
  by_cases h : x = 0
  · subst h
    decide
  · have h' : x.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by rw [h']; rfl))
    rw [decide_eq_true h']
    exact bne_iff_ne.mpr h

/-- `checkint` through the divisibility of the scaled magnitude. -/
theorem checkint_magnitude (w : UInt64) (hf : Wasm.IEEE64.exponent w < 2047)
    (h0 : 0 < Wasm.IEEE64.scaledMagnitude w) :
    Pow.checkint w = if ¬ 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w then 0
      else if 2 ^ 1075 ∣ Wasm.IEEE64.scaledMagnitude w then 2 else 1 := by
  have hw := ExpBranches.exponent_word_spec w
  simp only [ExpBranches.exponentWord] at hw
  set e := Wasm.IEEE64.exponent w
  set f := Wasm.IEEE64.fraction w
  have hfl : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hT := w.toNat_lt
  rw [checkint_eq]
  by_cases he1 : e < 1023
  · have hc : (w >>> 52) &&& 0x7ff < (0x3ff : UInt64) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hw]
      exact he1
    have hM : Wasm.IEEE64.scaledMagnitude w < 2 ^ 1074 := by
      have := F64Magnitude.magnitude_lt_of_exponent_lt w 1023 (by norm_num) he1
      calc
        _ < 2 ^ (51 + 1023) := this
        _ = 2 ^ 1074 := by norm_num
    have hnd : ¬ 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w :=
      fun h => absurd (Nat.le_of_dvd h0 h) (by omega)
    rw [ite_eq_left hc, ite_eq_left hnd]
  · have hc : ¬ (w >>> 52) &&& 0x7ff < (0x3ff : UInt64) := by
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [hw] at this
      exact he1 this
    rw [ite_eq_right hc]
    have hmag : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + f) * 2 ^ (e - 1) := by
      have he0 : (Wasm.IEEE64.exponent w == 0) = false := by
        rw [beq_eq_false_iff_ne]
        change e ≠ 0
        omega
      unfold Wasm.IEEE64.scaledMagnitude
      simp only [he0, Bool.false_eq_true, ite_false]
      all_goals rfl
    by_cases he2 : 1075 < e
    · have hc2 : (w >>> 52) &&& 0x7ff > (1075 : UInt64) := by
        apply UInt64.lt_iff_toNat_lt.mpr
        rw [hw]
        exact he2
      have hd : 2 ^ 1075 ∣ Wasm.IEEE64.scaledMagnitude w := by
        rw [hmag]
        exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
      have hd' : 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w :=
        dvd_trans (pow_dvd_pow 2 (by norm_num)) hd
      rw [ite_eq_left hc2, ite_eq_right (not_not.mpr hd'), ite_eq_left hd]
    · have hc2 : ¬ (w >>> 52) &&& 0x7ff > (1075 : UInt64) := by
        intro h
        have := UInt64.lt_iff_toNat_lt.mp h
        rw [hw] at this
        exact he2 this
      rw [ite_eq_right hc2]
      set s := 1075 - e with hs
      have hs52 : s ≤ 52 := by omega
      have hsh : ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff)).toNat = s := by
        rw [UInt64.toNat_sub_of_le (1075 : UInt64) ((w >>> 52) &&& 0x7ff)
          (UInt64.le_iff_toNat_le.mpr (by rw [hw]; change e ≤ 1075; omega)), hw]
        rfl
      have hpow : ((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff))).toNat =
          2 ^ s := by
        rw [UInt64.toNat_shiftLeft, hsh, Nat.mod_eq_of_lt (show s < 64 by omega),
          show (1 : UInt64).toNat = 1 from rfl, Nat.one_shiftLeft]
        have h1 : 2 ^ s ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) hs52
        exact Nat.mod_eq_of_lt (lt_of_le_of_lt h1 (by norm_num))
      have hlow : (w &&& (((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff))) -
          1)).toNat = f % 2 ^ s := by
        rw [UInt64.toNat_and, UInt64.toNat_sub_of_le
          ((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff))) 1
          (UInt64.le_iff_toNat_le.mpr (by rw [hpow]; exact Nat.one_le_two_pow)), hpow]
        rw [show (1 : UInt64).toNat = 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        simp only [f, Wasm.IEEE64.fraction]
        exact (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hs52)).symm
      have hbit : (w &&& ((1 : UInt64) <<< ((1075 : UInt64) - ((w >>> 52) &&& 0x7ff)))).toNat =
          w.toNat / 2 ^ s % 2 * 2 ^ s := by
        rw [UInt64.toNat_and, hpow, and_pow]
      -- divisibility of the magnitude
      have hsd : 2 ^ s ∣ 2 ^ 52 := pow_dvd_pow 2 hs52
      have hdiv1 : 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w ↔ f % 2 ^ s = 0 := by
        rw [hmag, show 1074 = s + (e - 1) by omega, pow_add,
          Nat.mul_dvd_mul_iff_right (by positivity), Nat.dvd_add_right hsd,
          Nat.dvd_iff_mod_eq_zero]
      have hdiv2 : 2 ^ 1075 ∣ Wasm.IEEE64.scaledMagnitude w ↔ 2 ^ (s + 1) ∣ 2 ^ 52 + f := by
        rw [hmag, show 1075 = (s + 1) + (e - 1) by omega, pow_add,
          Nat.mul_dvd_mul_iff_right (by positivity)]
      -- the bit `s` of the word and of `2 ^ 52 + f`
      have hq : w.toNat = w.toNat / 2 ^ 52 * 2 ^ 52 + f := (Nat.div_add_mod' _ _).symm
      have h52 : (2 : Nat) ^ 52 = 2 ^ (52 - s) * 2 ^ s := by
        rw [← pow_add, Nat.sub_add_cancel hs52]
      have hparity : w.toNat / 2 ^ s % 2 = (2 ^ 52 + f) / 2 ^ s % 2 := by
        have h1 : w.toNat / 2 ^ s = w.toNat / 2 ^ 52 * 2 ^ (52 - s) + f / 2 ^ s := by
          have e1 : w.toNat = f + w.toNat / 2 ^ 52 * 2 ^ (52 - s) * 2 ^ s := by
            rw [mul_assoc, ← h52]
            omega
          conv_lhs => rw [e1]
          rw [Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
        have h2 : (2 ^ 52 + f) / 2 ^ s = 2 ^ (52 - s) + f / 2 ^ s := by
          rw [h52, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
        rw [h1, h2]
        rcases Nat.lt_or_ge s 52 with hs' | hs'
        · have h3 : 2 ∣ 2 ^ (52 - s) := dvd_pow_self 2 (by omega)
          have h4 : 2 ∣ w.toNat / 2 ^ 52 * 2 ^ (52 - s) := Dvd.dvd.mul_left h3 _
          omega
        · have hs52' : s = 52 := by omega
          have he' : e = 1023 := by omega
          have hf0 : f / 2 ^ s = 0 := by rw [hs52']; exact Nat.div_eq_of_lt hfl
          rw [hf0, hs52', Nat.sub_self, pow_zero, mul_one]
          have : w.toNat / 2 ^ 52 % 2 ^ 11 = 1023 := he'
          omega
      have hdiv2' : 2 ^ s ∣ 2 ^ 52 + f →
          (2 ^ (s + 1) ∣ 2 ^ 52 + f ↔ (2 ^ 52 + f) / 2 ^ s % 2 = 0) := by
        intro h
        obtain ⟨q, hq'⟩ := h
        rw [hq', pow_succ, Nat.mul_dvd_mul_iff_left (by positivity),
          Nat.mul_div_cancel_left _ (by positivity), Nat.dvd_iff_mod_eq_zero]
      rw [bne_toNat, bne_toNat, hlow, hbit, hparity]
      by_cases hf0 : f % 2 ^ s = 0
      · have hd1 : 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w := hdiv1.mpr hf0
        have hd2 := hdiv2' ((Nat.dvd_add_right hsd).mpr (Nat.dvd_of_mod_eq_zero hf0))
        have c1 : ¬ (decide (f % 2 ^ s ≠ 0) = true) := by
          rw [decide_eq_true_eq]
          exact not_not.mpr hf0
        rw [ite_eq_right c1, ite_eq_right (not_not.mpr hd1)]
        by_cases hb : (2 ^ 52 + f) / 2 ^ s % 2 = 0
        · have c2 : ¬ (decide ((2 ^ 52 + f) / 2 ^ s % 2 * 2 ^ s ≠ 0) = true) := by
            rw [decide_eq_true_eq, hb, zero_mul]
            exact not_not.mpr rfl
          rw [ite_eq_right c2, ite_eq_left ((hdiv2.trans hd2).mpr hb)]
        · have hb1 : (2 ^ 52 + f) / 2 ^ s % 2 = 1 := by omega
          have c2 : decide ((2 ^ 52 + f) / 2 ^ s % 2 * 2 ^ s ≠ 0) = true := by
            rw [decide_eq_true_eq, hb1, one_mul]
            positivity
          rw [ite_eq_left c2, ite_eq_right (fun h => hb ((hdiv2.trans hd2).mp h))]
      · have hd1 : ¬ 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w := fun h => hf0 (hdiv1.mp h)
        have c1 : decide (f % 2 ^ s ≠ 0) = true := by
          rw [decide_eq_true_eq]
          exact hf0
        rw [ite_eq_left c1, ite_eq_left hd1]

theorem checkint_spec (w : UInt64) (hf : Wasm.IEEE64.exponent w < 2047)
    (h0 : 0 < Wasm.IEEE64.scaledMagnitude w) :
    (Pow.checkint w = 0 ↔ ∀ n : Int, value w ≠ n) ∧
      (Pow.checkint w = 1 ↔ ∃ n : Int, value w = n ∧ n % 2 = 1) ∧
      (Pow.checkint w = 2 ↔ ∃ n : Int, value w = n ∧ n % 2 = 0) := by
  have hpos : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hval : ∀ n : Int, value w = n ↔ Wasm.IEEE64.scaledValue w = n * 2 ^ 1074 := by
    intro n
    have hcast : ((n * 2 ^ 1074 : ℤ) : ℝ) = (n : ℝ) * 2 ^ 1074 := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [value, div_eq_iff hpos.ne', ← hcast, Int.cast_inj]
  have hmagn : ∀ n : Int, Wasm.IEEE64.scaledValue w = n * 2 ^ 1074 →
      Wasm.IEEE64.scaledMagnitude w = n.natAbs * 2 ^ 1074 := by
    intro n h
    have h1 := congrArg Int.natAbs h
    rw [natAbs_scaledValue, Int.natAbs_mul, Int.natAbs_pow] at h1
    exact h1
  have hint : (∃ n : Int, value w = n) ↔ 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w := by
    constructor
    · rintro ⟨n, hn⟩
      rw [hmagn n ((hval n).mp hn)]
      exact Dvd.intro_left _ rfl
    · rintro ⟨k, hk⟩
      refine ⟨if Wasm.IEEE64.sign w then -(k : Int) else k, (hval _).mpr ?_⟩
      have hsv : Wasm.IEEE64.scaledValue w = if Wasm.IEEE64.sign w then
          -(Wasm.IEEE64.scaledMagnitude w : Int) else Wasm.IEEE64.scaledMagnitude w := rfl
      rw [hsv, hk]
      split_ifs <;> push_cast <;> ring
  have hpar : ∀ n : Int, value w = n →
      (n % 2 = 0 ↔ 2 ^ 1075 ∣ Wasm.IEEE64.scaledMagnitude w) := by
    intro n hn
    rw [hmagn n ((hval n).mp hn), show 1075 = 1 + 1074 by norm_num, pow_add,
      Nat.mul_dvd_mul_iff_right (by positivity)]
    constructor
    · intro h2
      exact Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero h2)
    · intro h2
      exact Int.emod_eq_zero_of_dvd (Int.natAbs_dvd_natAbs.mp h2)
  rw [checkint_magnitude w hf h0]
  by_cases h1 : 2 ^ 1074 ∣ Wasm.IEEE64.scaledMagnitude w
  · obtain ⟨n, hn⟩ := hint.mpr h1
    have hnint : ¬ ∀ m : Int, value w ≠ m := fun h => h n hn
    rw [ite_eq_right (not_not.mpr h1)]
    by_cases h2 : 2 ^ 1075 ∣ Wasm.IEEE64.scaledMagnitude w
    · have heven : n % 2 = 0 := (hpar n hn).mpr h2
      rw [ite_eq_left h2]
      refine ⟨⟨fun h => absurd h (by decide), fun h => absurd h hnint⟩,
        ⟨fun h => absurd h (by decide), ?_⟩, ⟨fun _ => ⟨n, hn, heven⟩, fun _ => rfl⟩⟩
      rintro ⟨m, hm, hodd⟩
      have : n = m := by exact_mod_cast hn.symm.trans hm
      omega
    · have hodd : n % 2 = 1 := by
        have := (hpar n hn).not.mpr h2
        omega
      rw [ite_eq_right h2]
      refine ⟨⟨fun h => absurd h (by decide), fun h => absurd h hnint⟩,
        ⟨fun _ => ⟨n, hn, hodd⟩, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), ?_⟩⟩
      rintro ⟨m, hm, hev⟩
      have : n = m := by exact_mod_cast hn.symm.trans hm
      omega
  · have hnone : ∀ m : Int, value w ≠ m := fun m hm => h1 (hint.mp ⟨m, hm⟩)
    rw [ite_eq_left h1]
    refine ⟨⟨fun _ => hnone, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), ?_⟩,
      ⟨fun h => absurd h (by decide), ?_⟩⟩
    · rintro ⟨m, hm, -⟩
      exact absurd hm (hnone m)
    · rintro ⟨m, hm, -⟩
      exact absurd hm (hnone m)

#print axioms and_pow
#print axioms checkint_eq
#print axioms bne_toNat
#print axioms checkint_magnitude
#print axioms checkint_spec

end Verified.Examples.PowCheckint
