import Verified.Examples.AcosTheoremPos

/-!
`Asin.acos x` within one step of `arccos x` for every finite `x` with `|x| ≤ 1`.  The proof
follows the code's branches on the high word of `|x|`: `1` gives `+0` and `-1` gives `π` rounded,
below `2 ^ -57` the result is `pio2_hi + pio2_lo`, below `1/2` it is
`pio2_hi - (x - (pio2_lo - x r(x²)))`, and from `1/2` on the half-angle forms of
`AcosTheoremNeg` and `AcosTheoremPos` apply by the sign of `x`.
-/

namespace Verified.Examples.AcosTheorem
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx AsinTheoremBranches AsinTheorem
  AcosTheoremBranches

set_option exponentiation.threshold 4096

theorem ix_tiny (x : Float) : ixA x ≤ 0x3c600000 ↔ |value x.toBits| < 1048577 / 2 ^ 77 := by
  have h := ixA_lt x 0x3c600001 (by norm_num) (1048577 / 2 ^ 77) (by decide +kernel)
  push_cast at h
  rw [← h, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    show (0x3c600000 : UInt64).toNat = 1012924416 from rfl]
  first
    | rw [show (0x3c600001 : UInt64).toNat = 1012924417 from rfl]
    | rw [show (UInt64.ofNat 0x3c600001).toNat = 1012924417 from rfl]
  omega

theorem pi_word_close : |value (0x400921FB54442D18 : UInt64) - Real.pi| ≤ 21 / 10 ^ 17 := by
  have hpi := AtanTheoremConst.atan_inf
  have hlo := AcosTheoremSmall.lo_bound
  rw [AcosTheoremNeg.pi_twice]
  have h3 : 2 * value (0x3FF921FB54442D18 : UInt64) - Real.pi =
      2 * (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) -
        2 * value 0x3C91A62633145C07 := by ring
  rw [h3]
  have h4 := abs_sub (2 * (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2))
    (2 * value 0x3C91A62633145C07)
  rw [abs_mul, abs_mul, abs_two] at h4
  have h5 : (2 : ℝ) / 2 ^ 64 + 2 / 10 ^ 16 ≤ 21 / 10 ^ 17 := by norm_num
  linarith

/-- `±1`: `+0` for `1`, and `π` rounded for `-1`. -/
theorem acos_unit (x : Float) (h : |value x.toBits| = 1) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) (Asin.acos x).toBits := by
  rcases unit_bits x h with hb | hb
  · have hv : value x.toBits = 1 := by
      rw [hb, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by
        decide +kernel]
      norm_num
    have he : (Asin.acos x).toBits = 0 := by
      rw [acos_one_eq x (by unfold ixA; rw [hb]; decide) (by unfold ixA lxA; rw [hb]; decide),
        if_pos (by rw [hb]; decide)]
      rfl
    rw [he, hv, Real.arccos_one]
    exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide)
      (by rw [F64SignedRounding.positive_reference_zero]; decide)
      (by rw [F64SignedRounding.positive_reference_zero]; decide)
  · have hv : value x.toBits = -1 := by
      rw [hb, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0xBFF0000000000000 = -1 by
        decide +kernel]
      norm_num
    have he : (Asin.acos x).toBits = 0x400921FB54442D18 := by
      rw [acos_one_eq x (by unfold ixA; rw [hb]; decide) (by unfold ixA lxA; rw [hb]; decide),
        if_neg (by rw [hb]; decide)]
      unfold piF pio2LoF
      rw [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits,
        show (2.0 : Float).toBits = 0x4000000000000000 from rfl]
      decide +kernel
    rw [he, hv, Real.arccos_neg_one]
    have hc := pi_word_close
    have hp := Real.pi_gt_three
    have hp4 := Real.pi_lt_four
    refine within_zero_one (F64WithinZero.within_zero_of_close _ _ AcosTheoremNeg.pi_finite 1024
      (by norm_num) (by decide) (by decide) (lt_of_le_of_lt hc (by norm_num)) ?_)
    rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (4 : ℝ) < 2 ^ 1023)]

/-- The accuracy of `Asin.acos`: for every finite input with `|x| ≤ 1` the result lies within one
representable step of the nearest-even rounding of `arccos x`. -/
theorem acos_within_one (x : Float) (hx : Finite x.toBits) (hdom : |value x.toBits| ≤ 1) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) (Asin.acos x).toBits := by
  by_cases h1 : ixA x ≥ 0x3ff00000
  · have hge : 1 ≤ |value x.toBits| :=
      not_lt.mp (fun h => AtanTheorem.u_not_lt_of_ge _ _ h1 ((ix_one x).mpr h))
    exact acos_unit x (le_antisymm hdom hge)
  have hlt1 : |value x.toBits| < 1 := (ix_one x).mp (AtanTheorem.u_lt_of_not_ge _ _ h1)
  by_cases h2 : ixA x < 0x3fe00000
  · have hhalf := (ix_half x).mp h2
    by_cases h3 : ixA x ≤ 0x3c600000
    · have hs := (ix_tiny x).mp h3
      rw [acos_tiny_eq x h1 h2 h3]
      exact AcosTheoremSmall.tiny_within x (lt_of_lt_of_le hs (by norm_num))
    · have hge : 1048577 / 2 ^ 77 ≤ |value x.toBits| := not_lt.mp (fun h => h3 ((ix_tiny x).mpr h))
      rw [acos_small_eq x h1 h2 h3]
      exact AcosTheoremSmall.small_within x hx (le_trans (by norm_num) hge) hhalf
  have hge : 1 / 2 ≤ |value x.toBits| := not_lt.mp (fun h => h2 ((ix_half x).mpr h))
  have hv0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at hge
    norm_num at hge
  have hmag := F64Magnitude.scaledMagnitude_pos x.toBits hv0
  have hsgn := F64UpperWord.sign_test x.toBits
  cases hs : (x.toBits >>> 32 >>> 31 == 1)
  · rw [acos_pos_eq x h1 h2 hs]
    have hpos : 0 ≤ value x.toBits := by
      by_contra hn
      have := (F64Magnitude.sign_value x.toBits hmag).mpr (lt_of_not_ge hn)
      rw [← hsgn, hs] at this
      exact Bool.false_ne_true this
    rw [abs_of_nonneg hpos] at hge hlt1
    exact AcosTheoremPos.pos_within x hx hge hlt1
  · rw [acos_neg_eq x h1 h2 hs]
    have hneg : value x.toBits < 0 := (F64Magnitude.sign_value x.toBits hmag).mp (by rw [← hsgn, hs])
    rw [abs_of_neg hneg] at hge hlt1
    exact AcosTheoremNeg.neg_within x hx (by linarith) (by linarith)

#print axioms acos_within_one

end Verified.Examples.AcosTheorem
