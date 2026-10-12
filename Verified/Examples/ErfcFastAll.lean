import Verified.Examples.ErfcFastRows0
import Verified.Examples.ErfcFastRows1
import Verified.Examples.ErfcFastRows2
import Verified.Examples.ErfcFastRows3
import Verified.Examples.ErfcFastRows4
import Verified.Examples.ErfcFastRows5
import Verified.Examples.ErfcFastRows6
import Verified.Examples.ErfcFastRows7
import Verified.Examples.ErfcFastRows8
import Verified.Examples.ErfcFastRows9
import Verified.Examples.ErfcFastRows10
import Verified.Examples.ErfcFastRows11
import Verified.Examples.ErfcFastTiny
import Verified.Examples.ErfcCast

/-!
`cr_erf_fast` for `0 ≤ z < 95/16`.  `rows_ok` collects the 94 row checks, and `erfFast_err` bounds
the distance of the computed double-double from `erf z` by the target of the row of `z`, or by the
bound of `ErfcFastTiny` below `1/16`.  `zTarget_abs` bounds that by `(7/8) u`, and `zTarget_rel` by
`(7/8) u erfc z` for `z ≤ 0x1.713786d9c7c09p+1`.  The low part stays below `2 u`.
-/

namespace Verified.Examples.ErfcFastAll

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcFastMain ErfcSeries ErfcRound
  ErfcFastRow ErfcFastPlan ErfcFastTiny FmaSpec PolyBound PolyCalc RealErf

set_option exponentiation.threshold 2200

theorem rows_ok (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 94) : rowOK i := by
  interval_cases i
  exacts [ErfcFastRows0.ok_1, ErfcFastRows0.ok_2, ErfcFastRows0.ok_3, ErfcFastRows0.ok_4,
    ErfcFastRows0.ok_5, ErfcFastRows0.ok_6, ErfcFastRows0.ok_7, ErfcFastRows0.ok_8,
    ErfcFastRows1.ok_9, ErfcFastRows1.ok_10, ErfcFastRows1.ok_11, ErfcFastRows1.ok_12,
    ErfcFastRows1.ok_13, ErfcFastRows1.ok_14, ErfcFastRows1.ok_15, ErfcFastRows1.ok_16,
    ErfcFastRows2.ok_17, ErfcFastRows2.ok_18, ErfcFastRows2.ok_19, ErfcFastRows2.ok_20,
    ErfcFastRows2.ok_21, ErfcFastRows2.ok_22, ErfcFastRows2.ok_23, ErfcFastRows2.ok_24,
    ErfcFastRows3.ok_25, ErfcFastRows3.ok_26, ErfcFastRows3.ok_27, ErfcFastRows3.ok_28,
    ErfcFastRows3.ok_29, ErfcFastRows3.ok_30, ErfcFastRows3.ok_31, ErfcFastRows3.ok_32,
    ErfcFastRows4.ok_33, ErfcFastRows4.ok_34, ErfcFastRows4.ok_35, ErfcFastRows4.ok_36,
    ErfcFastRows4.ok_37, ErfcFastRows4.ok_38, ErfcFastRows4.ok_39, ErfcFastRows4.ok_40,
    ErfcFastRows5.ok_41, ErfcFastRows5.ok_42, ErfcFastRows5.ok_43, ErfcFastRows5.ok_44,
    ErfcFastRows5.ok_45, ErfcFastRows5.ok_46, ErfcFastRows5.ok_47, ErfcFastRows5.ok_48,
    ErfcFastRows6.ok_49, ErfcFastRows6.ok_50, ErfcFastRows6.ok_51, ErfcFastRows6.ok_52,
    ErfcFastRows6.ok_53, ErfcFastRows6.ok_54, ErfcFastRows6.ok_55, ErfcFastRows6.ok_56,
    ErfcFastRows7.ok_57, ErfcFastRows7.ok_58, ErfcFastRows7.ok_59, ErfcFastRows7.ok_60,
    ErfcFastRows7.ok_61, ErfcFastRows7.ok_62, ErfcFastRows7.ok_63, ErfcFastRows7.ok_64,
    ErfcFastRows8.ok_65, ErfcFastRows8.ok_66, ErfcFastRows8.ok_67, ErfcFastRows8.ok_68,
    ErfcFastRows8.ok_69, ErfcFastRows8.ok_70, ErfcFastRows8.ok_71, ErfcFastRows8.ok_72,
    ErfcFastRows9.ok_73, ErfcFastRows9.ok_74, ErfcFastRows9.ok_75, ErfcFastRows9.ok_76,
    ErfcFastRows9.ok_77, ErfcFastRows9.ok_78, ErfcFastRows9.ok_79, ErfcFastRows9.ok_80,
    ErfcFastRows10.ok_81, ErfcFastRows10.ok_82, ErfcFastRows10.ok_83, ErfcFastRows10.ok_84,
    ErfcFastRows10.ok_85, ErfcFastRows10.ok_86, ErfcFastRows10.ok_87, ErfcFastRows10.ok_88,
    ErfcFastRows11.ok_89, ErfcFastRows11.ok_90, ErfcFastRows11.ok_91, ErfcFastRows11.ok_92,
    ErfcFastRows11.ok_93, ErfcFastRows11.ok_94]

/-- The low parts of the rows, eight rows at a time. -/
theorem lowL0 : ∀ i < 9, 1 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL1 : ∀ i < 17, 9 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL2 : ∀ i < 25, 17 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL3 : ∀ i < 33, 25 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL4 : ∀ i < 41, 33 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL5 : ∀ i < 49, 41 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL6 : ∀ i < 57, 49 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL7 : ∀ i < 65, 57 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL8 : ∀ i < 73, 65 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL9 : ∀ i < 81, 73 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL10 : ∀ i < 89, 81 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL11 : ∀ i < 95, 89 ≤ i →
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  decide +kernel

theorem lowL (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 94) :
    (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53) := by
  if h : i < 9 then exact lowL0 i h (by omega)
  else if h : i < 17 then exact lowL1 i h (by omega)
  else if h : i < 25 then exact lowL2 i h (by omega)
  else if h : i < 33 then exact lowL3 i h (by omega)
  else if h : i < 41 then exact lowL4 i h (by omega)
  else if h : i < 49 then exact lowL5 i h (by omega)
  else if h : i < 57 then exact lowL6 i h (by omega)
  else if h : i < 65 then exact lowL7 i h (by omega)
  else if h : i < 73 then exact lowL8 i h (by omega)
  else if h : i < 81 then exact lowL9 i h (by omega)
  else if h : i < 89 then exact lowL10 i h (by omega)
  else exact lowL11 i (by omega) (by omega)

/-- The low part of the tiny case. -/
theorem lowTiny : (tinyB tinyQ (1 / 16)).s3L ≤ 2 * (1 / 2 ^ 53) := by decide +kernel

/-- The positivity of the series in `erfcLo` at the tops of the rows 1 to 46. -/
theorem serPos : ∀ i < 47, 0 ≤ evalQ (ser 80) (min (((i + 1 : ℕ) : ℚ) / 16) xMax) +
    serRem 80 (min (((i + 1 : ℕ) : ℚ) / 16) xMax) := by
  decide +kernel

theorem aux_ok : (∀ i < 95, 1 ≤ i → (mainB (rowQ Erfc.fastTable i) (1 / 32)).s8L ≤ 2 * (1 / 2 ^ 53)) ∧
    (tinyB tinyQ (1 / 16)).s3L ≤ 2 * (1 / 2 ^ 53) ∧
    (∀ i < 47, 0 ≤ evalQ (ser 80) (min (((i + 1 : ℕ) : ℚ) / 16) xMax) +
      serRem 80 (min (((i + 1 : ℕ) : ℚ) / 16) xMax)) :=
  ⟨fun i hi h1 => lowL i h1 (by omega), lowTiny, serPos⟩

/-- The bound of `cr_erf_fast` at `z`: the tiny case's bound below `1/16`, and the target of the
row of `z` from `1/16` on. -/
noncomputable def zTarget (z : ℝ) : ℝ :=
  if z < 1 / 16 then ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 16) : ℚ) : ℝ)
  else (target ⌊16 * z⌋₊ : ℝ)

theorem err_words : ff (Float.ofBits 0x3BA7800000000000) ∧
    |fv (Float.ofBits 0x3BA7800000000000)| ≤ 1 / 2 ^ 60 ∧ ff (Float.ofBits 0x3BA1100000000000) ∧
    |fv (Float.ofBits 0x3BA1100000000000)| ≤ 1 / 2 ^ 60 := by
  have f1 : Finite (0x3BA7800000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f2 : Finite (0x3BA1100000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ f1
  obtain ⟨a2, b2⟩ := ofBits_ff _ f2
  refine ⟨a1, ?_, a2, ?_⟩
  · rw [b1]
    have : |ratOfWord 0x3BA7800000000000| ≤ 1 / 2 ^ 60 := by decide +kernel
    qc this
  · rw [b2]
    have : |ratOfWord 0x3BA1100000000000| ≤ 1 / 2 ^ 60 := by decide +kernel
    qc this

/-- `cr_erf_fast` on `[0, 95/16)` within `zTarget z` of `erf z`. -/
theorem erfFast_err (hF : FmaNearest) (z : Float) (hz : ff z) (h0 : 0 ≤ fv z)
    (h1 : fv z < 95 / 16) :
    ff (Erfc.erfFast Erfc.fastTable z).1 ∧ ff (Erfc.erfFast Erfc.fastTable z).2.1 ∧
      ff (Erfc.erfFast Erfc.fastTable z).2.2 ∧
      |fv (Erfc.erfFast Erfc.fastTable z).2.2| ≤ 1 / 2 ^ 60 ∧
      |fv (Erfc.erfFast Erfc.fastTable z).2.1| ≤ 2 * (1 / 2 ^ 53) ∧
      |fv (Erfc.erfFast Erfc.fastTable z).1 + fv (Erfc.erfFast Erfc.fastTable z).2.1 -
        erf (fv z)| ≤ zTarget (fv z) := by
  obtain ⟨hL, htL, -⟩ := aux_ok
  obtain ⟨e1f, e1v, e2f, e2v⟩ := err_words
  have f0625 := (ErfcFastRow.lit_vals).2.2.2.2.1
  have v0625 := (ErfcFastRow.lit_vals).2.2.2.2.2
  unfold Erfc.erfFast zTarget
  by_cases hs : fv z < 1 / 16
  · have hlt : z < 0.0625 := (flt_iff _ _ hz f0625).mpr (by rw [v0625]; exact hs)
    rw [ite_eq_left hlt, ite_eq_left hs]
    dsimp only
    obtain ⟨c1, c2, ce, cl⟩ := tiny_err hF z hz (by rw [abs_of_nonneg h0]; linarith)
    refine ⟨c1, c2, e1f, e1v, cl.trans (by qc htL), ce⟩
  · have hlt : ¬ z < 0.0625 := fun h => hs (by
      have := (flt_iff _ _ hz f0625).mp h; rwa [v0625] at this)
    rw [ite_eq_right hlt, ite_eq_right hs]
    dsimp only
    set i := ⌊16 * fv z⌋₊ with hi
    have h16 : 0 ≤ 16 * fv z := by linarith
    have hi1 : 1 ≤ i := Nat.le_floor (by push_cast; linarith)
    have hi2 : i ≤ 94 := Nat.lt_succ_iff.mp ((Nat.floor_lt h16).mpr (by push_cast; linarith))
    have hfl := Nat.floor_le h16
    have hfu := Nat.lt_floor_add_one (16 * fv z)
    obtain ⟨c1, c2, ce, cl⟩ := row_err hF Erfc.fastTable i _ _ _ _ _ (rows_ok i hi1 hi2) z hz
      (by rw [← hi] at hfl; linarith) (by rw [← hi] at hfu; linarith)
    refine ⟨c1, c2, e2f, e2v, cl.trans (by qc hL i (by omega) hi1), ce⟩

theorem erfcLo_le_one (y : ℚ) (h : 0 ≤ evalQ (ser 80) y + serRem 80 y) : erfcLo 80 y ≤ 1 := by
  unfold erfcLo
  have : (0 : ℚ) ≤ sHi := by unfold sHi; norm_num
  nlinarith

theorem zTarget_abs (z : ℝ) (h0 : 0 ≤ z) (h1 : z < 95 / 16) : zTarget z ≤ 7 / 8 * (1 / 2 ^ 53) := by
  obtain ⟨-, -, hpos⟩ := aux_ok
  unfold zTarget
  split
  · have := erfcLo_le_one (1 / 16) (by
      have h := hpos 0 (by norm_num)
      rwa [show min (((0 + 1 : ℕ) : ℚ) / 16) xMax = 1 / 16 by unfold xMax; norm_num] at h)
    have : (7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 16) : ℚ) ≤ 7 / 8 * (1 / 2 ^ 53) := by nlinarith
    qc this
  · unfold target
    split
    · rename_i _ hi
      have := erfcLo_le_one _ (hpos ⌊16 * z⌋₊ (by omega))
      have : (7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((⌊16 * z⌋₊ + 1 : ℕ) : ℚ) / 16) xMax) : ℚ) ≤
          7 / 8 * (1 / 2 ^ 53) := by nlinarith
      qc this
    · norm_num

theorem xMax_val : (xMax : ℝ) = 0x1713786d9c7c09 / 2 ^ 51 := by unfold xMax; push_cast; ring

theorem zTarget_rel (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ xMax) :
    zTarget z ≤ 7 / 8 * (1 / 2 ^ 53) * erfc z := by
  obtain ⟨-, -, hpos⟩ := aux_ok
  have hxm : (xMax : ℝ) < 47 / 16 := by rw [xMax_val]; norm_num
  unfold zTarget
  split
  · rename_i hs
    have h := hpos 0 (by norm_num)
    rw [show min (((0 + 1 : ℕ) : ℚ) / 16) xMax = 1 / 16 by unfold xMax; norm_num] at h
    have hg := erfc_ge 80 (1 / 16) (by norm_num) h
    have hm : erfc ((1 / 16 : ℚ) : ℝ) ≤ erfc z :=
      erfc_strictAnti.antitone (by push_cast; linarith)
    push_cast at hg hm ⊢
    nlinarith
  · rename_i hs
    have h16 : 0 ≤ 16 * z := by linarith
    have hi46 : ⌊16 * z⌋₊ ≤ 46 :=
      Nat.lt_succ_iff.mp ((Nat.floor_lt h16).mpr (by push_cast; linarith))
    unfold target
    rw [if_pos hi46]
    have h := hpos _ (by omega : ⌊16 * z⌋₊ < 47)
    have hg := erfc_ge 80 _ (le_min (by positivity) (by unfold xMax; norm_num)) h
    have hfu := Nat.lt_floor_add_one (16 * z)
    have hzm : z ≤ ((min (((⌊16 * z⌋₊ + 1 : ℕ) : ℚ) / 16) xMax : ℚ) : ℝ) := by
      push_cast
      exact le_min (by linarith) h1
    have hm := erfc_strictAnti.antitone hzm
    have : (((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((⌊16 * z⌋₊ + 1 : ℕ) : ℚ) / 16) xMax)) :
        ℚ) : ℝ) = 7 / 8 * (1 / 2 ^ 53) *
          ((erfcLo 80 (min (((⌊16 * z⌋₊ + 1 : ℕ) : ℚ) / 16) xMax) : ℚ) : ℝ) := by push_cast; ring
    rw [this]
    have hu : (0 : ℝ) ≤ 7 / 8 * (1 / 2 ^ 53) := by norm_num
    exact mul_le_mul_of_nonneg_left (hg.trans hm) hu

#print axioms rows_ok
#print axioms erfFast_err
#print axioms zTarget_abs
#print axioms zTarget_rel

end Verified.Examples.ErfcFastAll
