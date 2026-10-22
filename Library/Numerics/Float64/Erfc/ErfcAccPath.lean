import Library.Numerics.Float64.Erfc.ErfcFastPath
import Library.Numerics.Float64.Erfc.ErfcAccAll
import Library.Numerics.Float64.Erfc.ErfcAsymAccFin
import Library.Numerics.Float64.Erfc.ErfcHardNeg
import Library.Numerics.Float64.Erfc.ErfcHardPos
import Library.Numerics.Float64.Erfc.ErfcHardAsym
import Library.Numerics.Float64.Erfc.ErfcSpecial

/-!
`cr_erfc_accurate` within one step of `erfc x` for `-47/8 < x < 0` and
`0 < x < 0x1.b39dc41e48bfdp+4`.  For `x < 0` the code adds 1 to `cr_erf_accurate (-x)`
(`neg_fallback`), and for `0 < x ≤ 0x1.b59ffb450828cp+0` it subtracts `cr_erf_accurate x` from 1
(`pos_fallback`); in both, `h + l` lies within `(7/8) u erfc x` of `erfc x` up to one rounding of a
low part, so the rounded sum lies within one step (`ErfcTest.near_within`).  Above, the result of
`erfc_asympt_accurate` is the special input's (`ErfcSpecial`) or the scaled double-double's
(`ErfcAsymAccFin.finA_within`).  The tables of hard cases replace the result on their inputs by a
word within one step (`ErfcHardNeg`, `ErfcHardPos`, `ErfcHardAsym`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccPath

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcOps ErfcTrack ErfcRound ErfcTest ErfcFastPlan
  ErfcFastAll ErfcFastPath ErfcAccAll ErfcAccPlan ErfcAsymAccHL ErfcAsymAccFin Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound
  RealErf

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)

/-- The fallback of `cr_erfc_accurate` for `-47/8 < x < 0`: `1 + erf (-x)`. -/
theorem neg_fallback (hF : FmaNearest) (x : Float) (hx : ff x) (hneg : fv x < 0)
    (hlo : -(47 / 8) < fv x) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x))
      ((Erfc.fastTwoSum 1.0 (Erfc.erfAccurate Erfc.accTable (-x)).1).1 +
        ((Erfc.fastTwoSum 1.0 (Erfc.erfAccurate Erfc.accTable (-x)).1).2 +
          (Erfc.erfAccurate Erfc.accTable (-x)).2)).toBits := by
  obtain ⟨nf, nv⟩ := neg_f x hx
  obtain ⟨c1, c2, cl, ce⟩ := erfAcc_err hF (-x) nf (by rw [nv]; linarith) (by rw [nv]; linarith)
  have hT := aTarget_abs (fv (-x)) (by rw [nv]; linarith) (by rw [nv]; linarith)
  have herf0 := erf_nonneg (fv (-x)) (by rw [nv]; linarith)
  have herf1 := erf_lt_one (fv (-x))
  have hy : RealErf.erfc (fv x) = 1 + RealErf.erf (fv (-x)) := by
    rw [nv, show fv x = -(-fv x) by ring, erfc_neg, RealErf.erfc]; ring
  set hE := (Erfc.erfAccurate Erfc.accTable (-x)).1
  set lE := (Erfc.erfAccurate Erfc.accTable (-x)).2
  have hd := ce.trans hT
  have hhe1 : -1 ≤ fv hE := by
    have := (abs_le.mp hd).1; have := (abs_le.mp cl).2; linarith
  have hhe2 : fv hE < 2 := by
    have := (abs_le.mp hd).2; have := (abs_le.mp cl).1; linarith
  obtain ⟨s1, s2, ssum, st⟩ := fts_unit hE c1 hhe1 hhe2
  set h := (Erfc.fastTwoSum 1.0 hE).1
  set t := (Erfc.fastTwoSum 1.0 hE).2
  obtain ⟨l1, lerr, lmag⟩ := add_bound s2 c2 st cl (by norm_num)
  have hhb : |fv h| ≤ 4 := by
    have : |fv t| ≤ 1 := st.trans (by norm_num)
    have := abs_le.mp this
    rw [abs_le]; constructor <;> linarith
  have hsum : |fv h + fv (t + lE)| ≤ 2 ^ 1022 := by
    refine (abs_add_le _ _).trans ?_
    linarith [show (3 * u + 2 * u) * (1 + u) ≤ 1 by norm_num, show (5 : ℝ) ≤ 2 ^ 1022 by norm_num]
  have sn := add_snear h (t + lE) s1 l1 hsum
  rw [hy]
  refine near_within _ _ _ sn ?_ ?_ ?_
  · linarith [show (1 : ℝ) / 2 ^ 1021 ≤ 1 by norm_num]
  · linarith [show (2 : ℝ) ≤ 2 ^ 1022 by norm_num]
  · have e1 : fv h + fv (t + lE) - (1 + RealErf.erf (fv (-x))) =
        (fv hE + fv lE - RealErf.erf (fv (-x))) + (fv (t + lE) - (fv t + fv lE)) := by linarith
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    nlinarith

/-- `erfc` at `0x1.b59ffb450828cp+0` is above `2^-15`. -/
theorem erfc_xacc (z : ℝ) (hz : z ≤ xAcc) : (1 / 2 ^ 15 : ℝ) ≤ RealErf.erfc z := by
  have hx : (xAcc : ℝ) ≤ xMax := by rw [xAcc_val, xMax_val]; norm_num
  exact erfc_xmax.trans (erfc_strictAnti.antitone (hz.trans hx))

/-- The fallback of `cr_erfc_accurate` for `0 ≤ x ≤ 0x1.b59ffb450828cp+0`: `1 - erf x`. -/
theorem pos_fallback (hF : FmaNearest) (x : Float) (hx : ff x) (hpos : 0 ≤ fv x)
    (hhi : fv x ≤ xAcc) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x))
      ((Erfc.fastTwoSum 1.0 (-(Erfc.erfAccurate Erfc.accTable x).1)).1 +
        ((Erfc.fastTwoSum 1.0 (-(Erfc.erfAccurate Erfc.accTable x).1)).2 -
          (Erfc.erfAccurate Erfc.accTable x).2)).toBits := by
  have hxa : (xAcc : ℝ) < 47 / 8 := by rw [xAcc_val]; norm_num
  obtain ⟨c1, c2, cl, ce⟩ := erfAcc_err hF x hx hpos (by linarith)
  have hT := aTarget_rel (fv x) hpos hhi
  have herf0 := erf_nonneg (fv x) hpos
  have hey : RealErf.erfc (fv x) = 1 - RealErf.erf (fv x) := rfl
  have hy0 := erfc_xacc (fv x) hhi
  have hy1 : RealErf.erfc (fv x) ≤ 1 := by rw [hey]; linarith
  set hE := (Erfc.erfAccurate Erfc.accTable x).1
  set lE := (Erfc.erfAccurate Erfc.accTable x).2
  have hd := ce.trans hT
  have hu : (0 : ℝ) < u := by norm_num
  have hdu : 7 / 8 * u * RealErf.erfc (fv x) ≤ u := by nlinarith
  have hhe1 : -1 ≤ fv hE := by
    have := (abs_le.mp hd).1; have := (abs_le.mp cl).2; linarith
  have hhe2 : fv hE ≤ 1 := by
    have := (abs_le.mp hd).2; have := (abs_le.mp cl).1
    have : RealErf.erf (fv x) ≤ 1 - 1 / 2 ^ 15 := by rw [hey] at hy0; linarith
    linarith [show 2 * u + u < 1 / 2 ^ 15 by norm_num]
  obtain ⟨nf, nv⟩ := neg_f hE c1
  obtain ⟨s1, s2, ssum, st⟩ := fts_unit (-hE) nf (by rw [nv]; linarith) (by rw [nv]; linarith)
  set h := (Erfc.fastTwoSum 1.0 (-hE)).1
  set t := (Erfc.fastTwoSum 1.0 (-hE)).2
  have hsub : |fv t - fv lE| ≤ 2 ^ 1022 :=
    (ErfcEft2.abs_sub_le' _ _).trans (by linarith [show 3 * u + 2 * u ≤ 2 ^ 1022 by norm_num])
  obtain ⟨l1, lerr⟩ := sub_f _ _ s2 c2 hsub
  have hlb : |fv t - fv lE| ≤ 5 * u := (ErfcEft2.abs_sub_le' _ _).trans (by linarith)
  have hlm : |fv (t - lE)| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (fv (t - lE)) (fv t - fv lE)
    have : u * |fv t - fv lE| ≤ u * (5 * u) := by gcongr
    linarith [show u * (5 * u) + 5 * u ≤ 1 by norm_num]
  have hhm : |fv h| ≤ 4 := by
    have : |fv t| ≤ 1 := st.trans (by norm_num)
    have := abs_le.mp this
    rw [nv] at ssum
    rw [abs_le]; constructor <;> linarith
  have hsum : |fv h + fv (t - lE)| ≤ 2 ^ 1022 := by
    refine (abs_add_le _ _).trans ?_
    linarith [show (5 : ℝ) ≤ 2 ^ 1022 by norm_num]
  have sn := add_snear h (t - lE) s1 l1 hsum
  refine near_within _ _ _ sn ?_ ?_ ?_
  · linarith [show (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 15 by norm_num]
  · linarith [show (1 : ℝ) ≤ 2 ^ 1022 by norm_num]
  · rw [hey]
    have e1 : fv h + fv (t - lE) - (1 - RealErf.erf (fv x)) = -(fv hE + fv lE - RealErf.erf (fv x)) +
        (fv (t - lE) - (fv t - fv lE)) := by
      rw [nv] at ssum; linarith
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have : u * |fv t - fv lE| ≤ u * (5 * u) := by gcongr
    have : u * (5 * u) ≤ 1 / 16 * u * (1 / 2 ^ 15) := by norm_num
    rw [hey] at hd hy0
    nlinarith

/-- `erfc_asympt_accurate` for `0x1.b59ffb450828cp+0 < x < 0x1.b39dc41e48bfdp+4`. -/
theorem asym_within (hF : FmaNearest) (x : Float) (hx : ff x)
    (hlo : (ratOfWord 0x3FFB59FFB450828C : ℝ) < fv x)
    (hhi : fv x < ratOfWord 0x403B39DC41E48BFD) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x))
      (Erfc.erfcAsymptAccurate Erfc.expAccTable Erfc.asymAccTable Erfc.excTable x).toBits := by
  unfold Erfc.erfcAsymptAccurate
  split
  · rename_i heq
    exact ErfcSpecial.special_within hF x hx heq
  · refine ErfcHardAsym.table x _ hx ?_
    rw [asymAcc_eq]
    obtain ⟨K, hK1, hK2, ef, ev, hf, lf, herr, hlh, hh1, hh2⟩ := aa_hl hF x hx hlo hhi
    have k1 : (0 : ℚ) < ratOfWord 0x3FFB59FFB450828C := by decide +kernel
    have hx0 : 0 < fv x := lt_trans (by qc k1) hlo
    have hy1 : RealErf.erfc (fv x) ≤ 1 := by
      have := erf_nonneg (fv x) hx0.le
      unfold RealErf.erfc; linarith
    exact finA_within _ _ _ K _ hK1 hK2 ef ev hf lf herr hlh hh1 hh2 (erfc_pos _) hy1

/-- `cr_erfc_accurate` for `-47/8 < x < 0` and `0 < x < 0x1.b39dc41e48bfdp+4`. -/
theorem acc_within (hF : FmaNearest) (x : Float) (hx : ff x) (hlo : -(47 / 8) < fv x)
    (h0 : fv x ≠ 0) (hhi : fv x < ratOfWord 0x403B39DC41E48BFD) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x))
      (Erfc.erfcAccurate Erfc.accTable Erfc.expAccTable Erfc.asymAccTable Erfc.excTable x).toBits := by
  obtain ⟨z0f, z0v⟩ := zero_val
  have fA : Finite (0x3FFB59FFB450828C : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨af, av⟩ := ofBits_ff _ fA
  have hxa : ratOfWord 0x3FFB59FFB450828C = xAcc := by decide +kernel
  unfold Erfc.erfcAccurate
  split
  · rename_i hneg
    have hn : fv x < 0 := by have := (flt_iff _ _ hx z0f).mp hneg; rwa [z0v] at this
    exact ErfcHardNeg.table x _ hx (neg_fallback hF x hx hn hlo)
  · rename_i hneg
    have hn : 0 ≤ fv x := by
      by_contra hc
      exact hneg ((flt_iff _ _ hx z0f).mpr (by rw [z0v]; linarith))
    split
    · rename_i hle
      have hl : fv x ≤ xAcc := by
        have := (fle_iff _ _ hx af).mp hle; rwa [av, hxa] at this
      exact ErfcHardPos.table x _ hx (pos_fallback hF x hx hn hl)
    · rename_i hle
      have hl : (ratOfWord 0x3FFB59FFB450828C : ℝ) < fv x := by
        by_contra hc
        exact hle ((fle_iff _ _ hx af).mpr (by rw [av]; linarith))
      exact asym_within hF x hx hl hhi

#print axioms acc_within

end Library.Numerics.Float64.Erfc.ErfcAccPath
