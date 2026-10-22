import Library.Numerics.Float64.Erfc.ErfcAccRows0
import Library.Numerics.Float64.Erfc.ErfcAccRows1
import Library.Numerics.Float64.Erfc.ErfcAccRows2
import Library.Numerics.Float64.Erfc.ErfcAccRows3
import Library.Numerics.Float64.Erfc.ErfcAccRows4
import Library.Numerics.Float64.Erfc.ErfcAccRows5
import Library.Numerics.Float64.Erfc.ErfcAccTiny
import Library.Numerics.Float64.Erfc.ErfcFastAll
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`cr_erf_accurate` for `0 ≤ z < 47/8`.  `accRows_ok` collects the 47 row checks of `C2`, `tacc_err`
bounds `cr_erf_accurate_tiny` below `1/8` with the series certificate of `ErfcSeries`, and
`erfAcc_err` bounds the distance of the computed double-double from `erf z` by `aTarget z`: the
tiny case's target below `1/8` and the row's target from `1/8` on.  `aTarget_abs` bounds that by
`(7/8) u`, and `aTarget_rel` by `(7/8) u erfc z` for `z ≤ 0x1.b59ffb450828cp+0`.  The low part
stays below `2 u`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccAll

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcAccMain ErfcAccTiny ErfcSeries
  ErfcRound ErfcAccRow ErfcAccPlan ErfcFastAll FmaSpec PolyBound PolyCalc RealErf

set_option exponentiation.threshold 2200

theorem accRows_ok (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 47) : rowOK i := by
  interval_cases i
  exacts [ErfcAccRows0.ok_1, ErfcAccRows0.ok_2, ErfcAccRows0.ok_3, ErfcAccRows0.ok_4,
    ErfcAccRows0.ok_5, ErfcAccRows0.ok_6, ErfcAccRows0.ok_7, ErfcAccRows0.ok_8,
    ErfcAccRows1.ok_9, ErfcAccRows1.ok_10, ErfcAccRows1.ok_11, ErfcAccRows1.ok_12,
    ErfcAccRows1.ok_13, ErfcAccRows1.ok_14, ErfcAccRows1.ok_15, ErfcAccRows1.ok_16,
    ErfcAccRows2.ok_17, ErfcAccRows2.ok_18, ErfcAccRows2.ok_19, ErfcAccRows2.ok_20,
    ErfcAccRows2.ok_21, ErfcAccRows2.ok_22, ErfcAccRows2.ok_23, ErfcAccRows2.ok_24,
    ErfcAccRows3.ok_25, ErfcAccRows3.ok_26, ErfcAccRows3.ok_27, ErfcAccRows3.ok_28,
    ErfcAccRows3.ok_29, ErfcAccRows3.ok_30, ErfcAccRows3.ok_31, ErfcAccRows3.ok_32,
    ErfcAccRows4.ok_33, ErfcAccRows4.ok_34, ErfcAccRows4.ok_35, ErfcAccRows4.ok_36,
    ErfcAccRows4.ok_37, ErfcAccRows4.ok_38, ErfcAccRows4.ok_39, ErfcAccRows4.ok_40,
    ErfcAccRows5.ok_41, ErfcAccRows5.ok_42, ErfcAccRows5.ok_43, ErfcAccRows5.ok_44,
    ErfcAccRows5.ok_45, ErfcAccRows5.ok_46, ErfcAccRows5.ok_47]

/-- The low parts of the rows of `C2`, in groups of at most six rows. -/
theorem accL_1 : ∀ i < 7, 1 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_7 : ∀ i < 13, 7 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_13 : ∀ i < 19, 13 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_19 : ∀ i < 25, 19 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_25 : ∀ i < 31, 25 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_31 : ∀ i < 37, 31 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_37 : ∀ i < 43, 37 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_43 : ∀ i < 48, 43 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem accL_ok : ∀ i < 48, 1 ≤ i →
    (accBR (accRowQ Erfc.accTable i) (1 / 16)).t7L ≤ 2 * (1 / 2 ^ 53) := by
  intro i hi h1
  rcases Nat.lt_or_ge i 7 with h | h
  · exact accL_1 i h (by omega)
  rcases Nat.lt_or_ge i 13 with h | h
  · exact accL_7 i h (by omega)
  rcases Nat.lt_or_ge i 19 with h | h
  · exact accL_13 i h (by omega)
  rcases Nat.lt_or_ge i 25 with h | h
  · exact accL_19 i h (by omega)
  rcases Nat.lt_or_ge i 31 with h | h
  · exact accL_25 i h (by omega)
  rcases Nat.lt_or_ge i 37 with h | h
  · exact accL_31 i h (by omega)
  rcases Nat.lt_or_ge i 43 with h | h
  · exact accL_37 i h (by omega)
  exact accL_43 i hi (by omega)

theorem tacc_ent : TAccEntQ taccQ := by decide +kernel

theorem tacc_hyp : TAccHyp taccQ (1 / 8) (taccB taccQ (1 / 8)) := by decide +kernel

theorem tacc_chk : rowCheck 8 15 0 (1 / 8) (1 / 2 ^ 62) (taccPoly taccQ) 0 = true := by
  decide +kernel

theorem tacc_tot : (taccB taccQ (1 / 8)).fine + rowBound 8 15 0 (1 / 8) (1 / 2 ^ 62) ≤
    7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) := by
  decide +kernel

theorem tacc_low : (taccB taccQ (1 / 8)).finL ≤ 2 * (1 / 2 ^ 53) := by decide +kernel

/-- The positivity of the series in `erfcLo` at the tops of the first 14 rows. -/
theorem ser_pos : ∀ i < 14, 0 ≤ evalQ (ser 80) (min (((i + 1 : ℕ) : ℚ) / 8) xAcc) +
    serRem 80 (min (((i + 1 : ℕ) : ℚ) / 8) xAcc) := by
  decide +kernel

/-- The conditions of `cr_erf_accurate_tiny`, and the positivity of the series in `erfcLo`. -/
theorem tacc_ok : TAccEntQ taccQ ∧ TAccHyp taccQ (1 / 8) (taccB taccQ (1 / 8)) ∧
    rowCheck 8 15 0 (1 / 8) (1 / 2 ^ 62) (taccPoly taccQ) 0 = true ∧
    (taccB taccQ (1 / 8)).fine + rowBound 8 15 0 (1 / 8) (1 / 2 ^ 62) ≤
      7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) ∧
    (taccB taccQ (1 / 8)).finL ≤ 2 * (1 / 2 ^ 53) ∧
    (∀ i < 14, 0 ≤ evalQ (ser 80) (min (((i + 1 : ℕ) : ℚ) / 8) xAcc) +
      serRem 80 (min (((i + 1 : ℕ) : ℚ) / 8) xAcc)) :=
  ⟨tacc_ent, tacc_hyp, tacc_chk, tacc_tot, tacc_low, ser_pos⟩

/-- `Erfc.erfAccurateTiny` within `(7/8) u erfcLo (1/8)` of `erf z` for `|z| ≤ 1/8`. -/
theorem tacc_err (hF : FmaNearest) (z : Float) (hz : ff z) (hzR : |fv z| ≤ 1 / 8) :
    ff (Erfc.erfAccurateTiny z).1 ∧ ff (Erfc.erfAccurateTiny z).2 ∧
      |fv (Erfc.erfAccurateTiny z).1 + fv (Erfc.erfAccurateTiny z).2 - RealErf.erf (fv z)| ≤
        ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) : ℚ) : ℝ) ∧
      |fv (Erfc.erfAccurateTiny z).2| ≤ 2 * (1 / 2 ^ 53) := by
  obtain ⟨hent, hyp, hchk, htot, hL, -⟩ := tacc_ok
  have hz' : |fv z| ≤ ((1 / 8 : ℚ) : ℝ) := by push_cast; exact hzR
  have hp := tacc_core_pr hF Erfc.tinyCoeff z taccQ (1 / 8) _ hyp hz hz' (tEnt_of_q _ hent)
  rw [← erfAccurateTiny_eq] at hp
  have hs := row_sound 8 15 0 (1 / 8) (1 / 2 ^ 62) (taccPoly taccQ) 0 (by norm_num) hchk (fv z) hz'
  rw [Rat.cast_zero, zero_add] at hs
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2.2.trans (by qc hL)⟩
  have htot' : ((taccB taccQ (1 / 8)).fine : ℝ) + (rowBound 8 15 0 (1 / 8) (1 / 2 ^ 62) : ℝ) ≤
      ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) : ℚ) : ℝ) := by qc htot
  have := abs_add_le (fv (Erfc.erfAccurateTiny z).1 + fv (Erfc.erfAccurateTiny z).2 -
    eval (taccPoly taccQ) (fv z)) (eval (taccPoly taccQ) (fv z) - RealErf.erf (fv z))
  rw [sub_add_sub_cancel] at this
  linarith [hp.2.2.1]

/-- The bound of `cr_erf_accurate` at `z`. -/
noncomputable def aTarget (z : ℝ) : ℝ :=
  if z < 1 / 8 then ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) : ℚ) : ℝ)
  else (target ⌊8 * z⌋₊ : ℝ)

/-- `cr_erf_accurate` on `[0, 47/8)` within `aTarget z` of `erf z`. -/
theorem erfAcc_err (hF : FmaNearest) (z : Float) (hz : ff z) (h0 : 0 ≤ fv z)
    (h1 : fv z < 47 / 8) :
    ff (Erfc.erfAccurate Erfc.accTable z).1 ∧ ff (Erfc.erfAccurate Erfc.accTable z).2 ∧
      |fv (Erfc.erfAccurate Erfc.accTable z).2| ≤ 2 * (1 / 2 ^ 53) ∧
      |fv (Erfc.erfAccurate Erfc.accTable z).1 + fv (Erfc.erfAccurate Erfc.accTable z).2 -
        RealErf.erf (fv z)| ≤ aTarget (fv z) := by
  have f125 := lit_vals8.2.2.2.2.1
  have v125 := lit_vals8.2.2.2.2.2
  unfold aTarget
  by_cases hs : fv z < 1 / 8
  · have hlt : z < 0.125 := (flt_iff _ _ hz f125).mpr (by rw [v125]; exact hs)
    rw [if_pos hs]
    unfold Erfc.erfAccurate
    rw [if_pos hlt]
    obtain ⟨c1, c2, ce, cl⟩ := tacc_err hF z hz (by rw [abs_of_nonneg h0]; linarith)
    exact ⟨c1, c2, cl, ce⟩
  · have hlt : ¬ z < 0.125 := fun h => hs (by
      have := (flt_iff _ _ hz f125).mp h; rwa [v125] at this)
    rw [if_neg hs]
    set i := ⌊8 * fv z⌋₊ with hi
    have h8 : 0 ≤ 8 * fv z := by linarith
    have hi1 : 1 ≤ i := Nat.le_floor (by push_cast; linarith)
    have hi2 : i ≤ 46 := Nat.lt_succ_iff.mp ((Nat.floor_lt h8).mpr (by push_cast; linarith))
    have hfl := Nat.floor_le h8
    have hfu := Nat.lt_floor_add_one (8 * fv z)
    obtain ⟨c1, c2, ce, cl⟩ := acc_row_err hF Erfc.accTable i _ _ _ _ _ (accRows_ok i hi1 (by omega))
      z hz (by rw [← hi] at hfl; linarith) (by rw [← hi] at hfu; linarith)
    exact ⟨c1, c2, cl.trans (by qc accL_ok i (by omega) hi1), ce⟩

theorem aTarget_abs (z : ℝ) (h0 : 0 ≤ z) (h1 : z < 47 / 8) : aTarget z ≤ 7 / 8 * (1 / 2 ^ 53) := by
  obtain ⟨-, -, -, -, -, hpos⟩ := tacc_ok
  unfold aTarget
  split
  · have := erfcLo_le_one (1 / 8) (by
      have h := hpos 0 (by norm_num)
      rwa [show min (((0 + 1 : ℕ) : ℚ) / 8) xAcc = 1 / 8 by unfold xAcc; norm_num] at h)
    have : (7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 8) : ℚ) ≤ 7 / 8 * (1 / 2 ^ 53) := by nlinarith
    qc this
  · unfold target
    split
    · rename_i _ hi
      have := erfcLo_le_one _ (hpos ⌊8 * z⌋₊ (by omega))
      have : (7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((⌊8 * z⌋₊ + 1 : ℕ) : ℚ) / 8) xAcc) : ℚ) ≤
          7 / 8 * (1 / 2 ^ 53) := by nlinarith
      qc this
    · norm_num

theorem xAcc_val : (xAcc : ℝ) = 7698779147895436 / 2 ^ 52 := by unfold xAcc; push_cast; ring

theorem aTarget_rel (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ xAcc) :
    aTarget z ≤ 7 / 8 * (1 / 2 ^ 53) * RealErf.erfc z := by
  obtain ⟨-, -, -, -, -, hpos⟩ := tacc_ok
  have hxm : (xAcc : ℝ) < 14 / 8 := by rw [xAcc_val]; norm_num
  unfold aTarget
  split
  · rename_i hs
    have h := hpos 0 (by norm_num)
    rw [show min (((0 + 1 : ℕ) : ℚ) / 8) xAcc = 1 / 8 by unfold xAcc; norm_num] at h
    have hg := erfc_ge 80 (1 / 8) (by norm_num) h
    have hm : RealErf.erfc ((1 / 8 : ℚ) : ℝ) ≤ RealErf.erfc z :=
      erfc_strictAnti.antitone (by push_cast; linarith)
    push_cast at hg hm ⊢
    nlinarith
  · rename_i hs
    have h8 : 0 ≤ 8 * z := by linarith
    have hi13 : ⌊8 * z⌋₊ ≤ 13 :=
      Nat.lt_succ_iff.mp ((Nat.floor_lt h8).mpr (by push_cast; linarith))
    unfold target
    rw [if_pos hi13]
    have h := hpos _ (by omega : ⌊8 * z⌋₊ < 14)
    have hg := erfc_ge 80 _ (le_min (by positivity) (by unfold xAcc; norm_num)) h
    have hfu := Nat.lt_floor_add_one (8 * z)
    have hzm : z ≤ ((min (((⌊8 * z⌋₊ + 1 : ℕ) : ℚ) / 8) xAcc : ℚ) : ℝ) := by
      push_cast
      exact le_min (by linarith) h1
    have hm := erfc_strictAnti.antitone hzm
    have : (((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((⌊8 * z⌋₊ + 1 : ℕ) : ℚ) / 8) xAcc)) :
        ℚ) : ℝ) = 7 / 8 * (1 / 2 ^ 53) *
          ((erfcLo 80 (min (((⌊8 * z⌋₊ + 1 : ℕ) : ℚ) / 8) xAcc) : ℚ) : ℝ) := by push_cast; ring
    rw [this]
    have hu : (0 : ℝ) ≤ 7 / 8 * (1 / 2 ^ 53) := by norm_num
    exact mul_le_mul_of_nonneg_left (hg.trans hm) hu

#print axioms accRows_ok
#print axioms tacc_err
#print axioms erfAcc_err
#print axioms aTarget_abs
#print axioms aTarget_rel

end Library.Numerics.Float64.Erfc.ErfcAccAll
