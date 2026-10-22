import Library.Numerics.Float64.Erfc.ErfcFastAll
import Library.Numerics.Float64.Erfc.ErfcTest
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The fast path of `cr_erfc` below `0x1.713786d9c7c09p+1`.  For `x < 0`, `erfc x = 1 + erf (-x)`, and
the code adds 1 to `cr_erf_fast (-x)` by `fast_two_sum`, exact here even when the high part slightly
exceeds 1 (`fts_one`).  For `0 ≤ x`, `erfc x = 1 - erf x`, and the code subtracts.  `erfcFast_neg`
and `erfcFast_pos` bound the distance of `h + l` from `erfc x` by `(15/16) u erfc x`, with the bounds
on `h`, `l`, and `err` that the rounding test needs (`FastOK`), and `fast_within` gives one step
when the test passes.
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastPath

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcTrack ErfcSeries ErfcRound
  ErfcFastPlan ErfcFastAll ErfcTest FmaSpec PolyBound PolyCalc RealErf

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)

/-- `fast_two_sum (1, b)` for `1 < b < 2` is exact. -/
theorem fts_one (b : Float) (hb : ff b) (h1 : 1 < fv b) (h2 : fv b < 2) :
    ff (Erfc.fastTwoSum 1.0 b).1 ∧ ff (Erfc.fastTwoSum 1.0 b).2 ∧
      fv (Erfc.fastTwoSum 1.0 b).1 + fv (Erfc.fastTwoSum 1.0 b).2 = 1 + fv b ∧
      |fv (Erfc.fastTwoSum 1.0 b).2| ≤ 3 * u := by
  obtain ⟨f1, v1⟩ := one_val
  have k : (3 : ℝ) ≤ 2 ^ 1022 := by norm_num
  have hs : |fv 1.0 + fv b| ≤ 2 ^ 1022 := by rw [v1, abs_of_pos (by linarith)]; linarith
  obtain ⟨sf, sn⟩ := add_near (1.0 : Float).toBits b.toBits f1 hb hs
  rw [← F64Bits.toBits_add] at sf sn
  obtain ⟨-, serr⟩ := add_f 1.0 b f1 hb hs
  rw [v1] at serr
  rw [show value (Float.toBits (1.0 : Float)) = fv (1.0 : Float) from rfl, v1] at sn
  have hsn : ∀ v : UInt64, |fv (1.0 + b) - (1 + fv b)| ≤ |value v - (1 + fv b)| := sn
  have he3 : |fv (1.0 + b) - (1 + fv b)| ≤ 3 * u := by
    refine serr.trans ?_
    rw [abs_of_pos (by linarith)]
    have : (0 : ℝ) ≤ u := by norm_num
    nlinarith
  have hs2 : (2 : ℝ) ≤ |fv (1.0 + b)| := by
    have hP : Rep (2 : ℝ) := by
      have := rep_int 2 (by norm_num)
      simpa using this
    exact nearest_ge _ _ _ hsn hP (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith)
  have hspos : 0 < fv (1.0 + b) := by
    have := (abs_le.mp he3).1
    linarith [show (3 : ℝ) * u < 1 by norm_num]
  rw [abs_of_pos hspos] at hs2
  -- `s - 1` is exact
  have hg1 : 1023 ≤ gx (1.0 + b).toBits := gx_ge _ _ (by
    rw [show (2 : ℝ) ^ (52 + 1023) / 2 ^ 1074 = 2 by norm_num]
    show 2 ≤ |fv (1.0 + b)|
    rw [abs_of_pos hspos]; exact hs2)
  have hgrid1 : OnGrid (1 : ℝ) 1023 := ⟨2 ^ 51, by norm_num⟩
  have hr1 : Rep (fv (1.0 + b) - fv (1.0 : Float)) := by
    rw [v1]
    refine rep_of_onGrid (onGrid_sub (onGrid_mono (onGrid_word (1.0 + b).toBits) hg1) hgrid1)
      (by norm_num) ?_
    rw [abs_of_pos (by linarith)]
    have : (fv (1.0 + b) : ℝ) ≤ 3 + 3 * u := by linarith [(abs_le.mp he3).2]
    have : ((2 : ℝ) ^ 53 + 1) * 2 ^ 1023 / 2 ^ 1074 = (2 ^ 53 + 1) / 2 ^ 51 := by
      rw [show (2 : ℝ) ^ 1074 = 2 ^ 1023 * 2 ^ 51 by norm_num]; field_simp
    rw [this]
    show fv (1.0 + b) - 1 < (2 ^ 53 + 1) / 2 ^ 51
    have : (4 : ℝ) ≤ (2 ^ 53 + 1) / 2 ^ 51 := by norm_num
    linarith [show (3 : ℝ) * u < 1 by norm_num]
  obtain ⟨ef, ev⟩ := sub_exact (1.0 + b) 1.0 sf f1
    (by rw [v1, abs_of_pos (by linarith)]; linarith [(abs_le.mp he3).2,
      show (4 : ℝ) ≤ 2 ^ 1022 by norm_num, show (3 : ℝ) * u < 1 by norm_num]) hr1
  rw [v1] at ev
  -- `b - (s - 1)` is exact
  have hgb : 1022 ≤ gx b.toBits := gx_ge _ _ (by
    rw [show (2 : ℝ) ^ (52 + 1022) / 2 ^ 1074 = 1 by norm_num]
    show 1 ≤ |fv b|; rw [abs_of_pos (by linarith)]; linarith)
  have hge : 1022 ≤ gx (1.0 + b - 1.0).toBits ∨ fv (1.0 + b - 1.0) = 0 := by
    left
    refine gx_ge _ _ ?_
    rw [show (2 : ℝ) ^ (52 + 1022) / 2 ^ 1074 = 1 by norm_num]
    show 1 ≤ |fv (1.0 + b - 1.0)|
    rw [ev, abs_of_pos (by linarith)]; linarith
  have hr2 : Rep (fv b - fv (1.0 + b - 1.0)) := by
    rcases hge with hg | hz
    · refine rep_of_onGrid (onGrid_sub (onGrid_mono (onGrid_word b.toBits) hgb)
        (onGrid_mono (onGrid_word (1.0 + b - 1.0).toBits) hg)) (by norm_num) ?_
      rw [ev]
      have : |fv b - (fv (1.0 + b) - 1)| ≤ 3 * u := by
        rw [show fv b - (fv (1.0 + b) - 1) = -(fv (1.0 + b) - (1 + fv b)) by ring, abs_neg]
        exact he3
      calc |fv b - (fv (1.0 + b) - 1)| ≤ 3 * u := this
        _ < ((2 : ℝ) ^ 53 + 1) * 2 ^ 1022 / 2 ^ 1074 := by norm_num
    · rw [hz, sub_zero]; exact rep_word _ hb
  obtain ⟨tf, tv⟩ := sub_exact b (1.0 + b - 1.0) hb ef (by
    rw [ev]
    have : |fv b - (fv (1.0 + b) - 1)| ≤ 3 * u := by
      rw [show fv b - (fv (1.0 + b) - 1) = -(fv (1.0 + b) - (1 + fv b)) by ring, abs_neg]
      exact he3
    linarith [show (3 : ℝ) * u ≤ 2 ^ 1022 by norm_num]) hr2
  have hfst : (Erfc.fastTwoSum 1.0 b).1 = 1.0 + b := rfl
  have hsnd : (Erfc.fastTwoSum 1.0 b).2 = b - (1.0 + b - 1.0) := rfl
  rw [hfst, hsnd]
  refine ⟨sf, tf, by rw [tv, ev]; ring, ?_⟩
  rw [tv, ev, show fv b - (fv (1.0 + b) - 1) = -(fv (1.0 + b) - (1 + fv b)) by ring, abs_neg]
  exact he3

/-- `fast_two_sum (1, b)` for `-1 ≤ b < 2`. -/
theorem fts_unit (b : Float) (hb : ff b) (h1 : -1 ≤ fv b) (h2 : fv b < 2) :
    ff (Erfc.fastTwoSum 1.0 b).1 ∧ ff (Erfc.fastTwoSum 1.0 b).2 ∧
      fv (Erfc.fastTwoSum 1.0 b).1 + fv (Erfc.fastTwoSum 1.0 b).2 = 1 + fv b ∧
      |fv (Erfc.fastTwoSum 1.0 b).2| ≤ 3 * u := by
  obtain ⟨f1, v1⟩ := one_val
  by_cases hc : fv b ≤ 1
  · have hab : |fv b| ≤ |fv (1.0 : Float)| := by
      rw [v1, abs_one, abs_le]; constructor <;> linarith
    obtain ⟨a1, a2, a3, a4⟩ := ErfcTrack.fts_bound f1 hb (le_of_eq (by rw [v1, abs_one]))
      (show |fv b| ≤ 1 by rw [abs_le]; constructor <;> linarith) hab (by norm_num)
    refine ⟨a1, a2, by rw [a3, v1], a4.trans (by norm_num)⟩
  · exact fts_one b hb (lt_of_not_ge hc) h2

/-- The bounds on the fast path's result that the rounding test needs, and the distance of
`h + l` from `y`. -/
def FastOK (y : ℝ) (r : Float × Float × Float) : Prop :=
  ff r.1 ∧ ff r.2.1 ∧ ff r.2.2 ∧ |fv r.1| ≤ 4 ∧ |fv r.2.1| ≤ 1 ∧ |fv r.2.2| ≤ 1 ∧
    |fv r.1 + fv r.2.1 - y| ≤ 15 / 16 * u * y

theorem zero_val : ff (0.0 : Float) ∧ fv (0.0 : Float) = 0 := by
  have h : (0.0 : Float).toBits = 0 := rfl
  unfold ff fv
  rw [h]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, by simp [value, Wasm.IEEE64.scaledValue,
    Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Wasm.IEEE64.sign]⟩

/-- `err h + c` with small `err` and `c` is finite and below 1. -/
theorem err_small (e h c : Float) (he : ff e) (hh : ff h) (hc : ff c) (heb : |fv e| ≤ 1 / 2 ^ 60)
    (hhb : |fv h| ≤ 2) (hcb : |fv c| ≤ 1 / 2 ^ 60) :
    ff (e * h) ∧ |fv (e * h)| ≤ 1 / 2 ^ 50 ∧ ff (e * h + c) ∧ |fv (e * h + c)| ≤ 1 := by
  have hp : |fv e * fv h| ≤ 1 / 2 ^ 59 := by
    rw [abs_mul]
    calc |fv e| * |fv h| ≤ 1 / 2 ^ 60 * 2 := mul_le_mul heb hhb (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 59 := by norm_num
  obtain ⟨m1, merr⟩ := mul_f e h he hh (hp.trans (by norm_num))
  have hm : |fv (e * h)| ≤ 1 / 2 ^ 50 := by
    have := abs_sub_abs_le_abs_sub (fv (e * h)) (fv e * fv h)
    have : (1 / 2 ^ 53 : ℝ) * |fv e * fv h| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 59) := by gcongr
    have : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 59) + 1 / 2 ^ 1075 + 1 / 2 ^ 59 ≤ 1 / 2 ^ 50 := by norm_num
    linarith
  obtain ⟨a1, aerr⟩ := add_f (e * h) c m1 hc ((abs_add_le _ _).trans (by
    linarith [show (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 60 ≤ 2 ^ 1022 by norm_num]))
  refine ⟨m1, hm, a1, ?_⟩
  have := abs_sub_abs_le_abs_sub (fv (e * h + c)) (fv (e * h) + fv c)
  have h3 : |fv (e * h) + fv c| ≤ 1 / 2 ^ 49 := (abs_add_le _ _).trans (by
    linarith [show (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 60 ≤ 1 / 2 ^ 49 by norm_num])
  have : (1 / 2 ^ 53 : ℝ) * |fv (e * h) + fv c| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 49) := by gcongr
  have : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 49) + 1 / 2 ^ 49 ≤ 1 := by norm_num
  linarith

theorem c102 : ff (Float.ofBits 0x3994000000000000) ∧
    |fv (Float.ofBits 0x3994000000000000)| ≤ 1 / 2 ^ 60 ∧ ff (Float.ofBits 0x3974000000000000) ∧
    |fv (Float.ofBits 0x3974000000000000)| ≤ 1 / 2 ^ 60 := by
  have f1 : Finite (0x3994000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f2 : Finite (0x3974000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ f1
  obtain ⟨a2, b2⟩ := ofBits_ff _ f2
  refine ⟨a1, ?_, a2, ?_⟩
  · rw [b1]
    have : |ratOfWord 0x3994000000000000| ≤ 1 / 2 ^ 60 := by decide +kernel
    qc this
  · rw [b2]
    have : |ratOfWord 0x3974000000000000| ≤ 1 / 2 ^ 60 := by decide +kernel
    qc this

theorem erf_nonneg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ RealErf.erf y := by
  have := erf_strictMono.monotone hy
  rwa [erf_zero] at this

/-- The fast path of `cr_erfc` for `-95/16 < x < 0`. -/
theorem erfcFast_neg (hF : FmaNearest) (x : Float) (hx : ff x) (hneg : fv x < 0)
    (hlo : -(95 / 16) < fv x) :
    FastOK (RealErf.erfc (fv x)) (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x) := by
  obtain ⟨z0f, z0v⟩ := zero_val
  obtain ⟨cf, cb, -, -⟩ := c102
  have hxneg : x < 0.0 := (flt_iff _ _ hx z0f).mpr (by rw [z0v]; exact hneg)
  obtain ⟨nf, nv⟩ := neg_f x hx
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := erfFast_err hF (-x) nf (by rw [nv]; linarith)
    (by rw [nv]; linarith)
  have hT := zTarget_abs (fv (-x)) (by rw [nv]; linarith) (by rw [nv]; linarith)
  have herf0 := erf_nonneg (fv (-x)) (by rw [nv]; linarith)
  have herf1 := erf_lt_one (fv (-x))
  have hy : RealErf.erfc (fv x) = 1 + RealErf.erf (fv (-x)) := by
    rw [nv, show fv x = -(-fv x) by ring, erfc_neg, RealErf.erfc]; ring
  unfold Erfc.erfcFast
  rw [ite_eq_left hxneg]
  dsimp only
  set he := (Erfc.erfFast Erfc.fastTable (-x)).1
  set le := (Erfc.erfFast Erfc.fastTable (-x)).2.1
  set ee := (Erfc.erfFast Erfc.fastTable (-x)).2.2
  have hd := c6.trans hT
  have hle := c5
  have hu : (0 : ℝ) < u := by norm_num
  have hhe1 : -1 ≤ fv he := by
    have := (abs_le.mp hd).1; have := (abs_le.mp hle).2; linarith
  have hhe2 : fv he < 2 := by
    have := (abs_le.mp hd).2; have := (abs_le.mp hle).1; linarith
  obtain ⟨s1, s2, ssum, st⟩ := fts_unit he c1 hhe1 hhe2
  obtain ⟨l1, lerr, lmag⟩ := add_bound s2 c2 st hle (by norm_num)
  obtain ⟨m1, -, e1, eb⟩ := err_small ee he _ c3 c1 cf c4
    (by rw [abs_le]; constructor <;> linarith) cb
  refine ⟨s1, l1, e1, ?_, lmag.trans (by norm_num), eb, ?_⟩
  · have := abs_sub_abs_le_abs_sub (fv (Erfc.fastTwoSum 1.0 he).1) (1 + fv he)
    rw [show fv (Erfc.fastTwoSum 1.0 he).1 - (1 + fv he) = -fv (Erfc.fastTwoSum 1.0 he).2 by
      linarith, abs_neg] at this
    have : |1 + fv he| ≤ 3 := by rw [abs_le]; constructor <;> linarith
    linarith [show (3 : ℝ) * u ≤ 1 by norm_num]
  · rw [hy]
    have e1 : fv (Erfc.fastTwoSum 1.0 he).1 + fv ((Erfc.fastTwoSum 1.0 he).2 + le) -
        (1 + RealErf.erf (fv (-x))) = (fv he + fv le - RealErf.erf (fv (-x))) +
          (fv ((Erfc.fastTwoSum 1.0 he).2 + le) - (fv (Erfc.fastTwoSum 1.0 he).2 + fv le)) := by
      linarith
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have : 3 * u + 2 * u ≤ 1 / 2 ^ 50 := by norm_num
    have : u * (3 * u + 2 * u) ≤ 1 / 16 * u := by nlinarith
    nlinarith

/-- The top of the second range of `cr_erfc_fast`, `0x1.713786d9c7c09p+1`. -/
theorem xmax_word : ff (Float.ofBits 0x400713786D9C7C09) ∧
    fv (Float.ofBits 0x400713786D9C7C09) = (xMax : ℝ) := by
  have f1 : Finite (0x400713786D9C7C09 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ f1
  exact ⟨a1, by rw [b1, show ratOfWord 0x400713786D9C7C09 = xMax by decide +kernel]⟩

/-- `erfc` at `0x1.713786d9c7c09p+1` is above `2^-15`. -/
theorem erfc_xmax : (1 / 2 ^ 15 : ℝ) ≤ RealErf.erfc xMax := by
  have h : (0 : ℚ) ≤ evalQ (ser 80) xMax + serRem 80 xMax ∧ 1 / 2 ^ 15 ≤ erfcLo 80 xMax := by
    decide +kernel
  have := erfc_ge 80 xMax (by unfold xMax; norm_num) h.1
  have h2 : ((1 / 2 ^ 15 : ℚ) : ℝ) ≤ (erfcLo 80 xMax : ℝ) := by qc h.2
  push_cast at h2
  linarith

/-- The fast path of `cr_erfc` for `0 ≤ x ≤ 0x1.713786d9c7c09p+1`. -/
theorem erfcFast_pos (hF : FmaNearest) (x : Float) (hx : ff x) (hpos : 0 ≤ fv x)
    (hhi : fv x ≤ xMax) :
    FastOK (RealErf.erfc (fv x)) (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x) := by
  obtain ⟨z0f, z0v⟩ := zero_val
  obtain ⟨cf, cb, cf2, cb2⟩ := c102
  obtain ⟨xf, xv⟩ := xmax_word
  have hxm : (xMax : ℝ) < 95 / 16 := by rw [xMax_val]; norm_num
  have hxnot : ¬ x < 0.0 := fun h => by
    have := (flt_iff _ _ hx z0f).mp h; rw [z0v] at this; linarith
  have hxle : x ≤ Float.ofBits 0x400713786D9C7C09 := (fle_iff _ _ hx xf).mpr (by rw [xv]; exact hhi)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := erfFast_err hF x hx hpos (by linarith)
  have hT := zTarget_rel (fv x) hpos hhi
  have herf0 := erf_nonneg (fv x) hpos
  have herf1 := erf_lt_one (fv x)
  have hey : RealErf.erfc (fv x) = 1 - RealErf.erf (fv x) := rfl
  have hy0 : (1 / 2 ^ 15 : ℝ) ≤ RealErf.erfc (fv x) :=
    erfc_xmax.trans (erfc_strictAnti.antitone hhi)
  have hy1 : RealErf.erfc (fv x) ≤ 1 := by rw [hey]; linarith
  unfold Erfc.erfcFast
  rw [ite_eq_right hxnot, ite_eq_left hxle]
  dsimp only
  set he := (Erfc.erfFast Erfc.fastTable x).1
  set le := (Erfc.erfFast Erfc.fastTable x).2.1
  set ee := (Erfc.erfFast Erfc.fastTable x).2.2
  have hd := c6.trans hT
  have hle := c5
  have hu : (0 : ℝ) < u := by norm_num
  have hdu : 7 / 8 * u * RealErf.erfc (fv x) ≤ u := by nlinarith
  have hhe1 : -1 ≤ fv he := by
    have := (abs_le.mp hd).1; have := (abs_le.mp hle).2; linarith
  have hhe2 : fv he ≤ 1 := by
    have := (abs_le.mp hd).2; have := (abs_le.mp hle).1
    have : RealErf.erf (fv x) ≤ 1 - 1 / 2 ^ 15 := by rw [hey] at hy0; linarith
    linarith [show 2 * u + u < 1 / 2 ^ 15 by norm_num]
  obtain ⟨nf, nv⟩ := neg_f he c1
  obtain ⟨s1, s2, ssum, st⟩ := fts_unit (-he) nf (by rw [nv]; linarith) (by rw [nv]; linarith)
  have hsub : |fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le| ≤ 2 ^ 1022 :=
    (ErfcEft2.abs_sub_le' _ _).trans (by linarith [show 3 * u + 2 * u ≤ 2 ^ 1022 by norm_num])
  obtain ⟨l1, lerr⟩ := sub_f _ _ s2 c2 hsub
  have hlb : |fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le| ≤ 5 * u :=
    (ErfcEft2.abs_sub_le' _ _).trans (by linarith)
  obtain ⟨m1, mb, e1, eb⟩ := err_small ee he _ c3 c1 cf2 c4
    (by rw [abs_le]; constructor <;> linarith) cb2
  have main : |fv (Erfc.fastTwoSum 1.0 (-he)).1 + fv ((Erfc.fastTwoSum 1.0 (-he)).2 - le) -
      RealErf.erfc (fv x)| ≤ 15 / 16 * u * RealErf.erfc (fv x) := by
    rw [hey]
    have e1 : fv (Erfc.fastTwoSum 1.0 (-he)).1 + fv ((Erfc.fastTwoSum 1.0 (-he)).2 - le) -
        (1 - RealErf.erf (fv x)) = -(fv he + fv le - RealErf.erf (fv x)) +
          (fv ((Erfc.fastTwoSum 1.0 (-he)).2 - le) -
            (fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le)) := by
      rw [nv] at ssum; linarith
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have : u * |fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le| ≤ u * (5 * u) := by gcongr
    have : u * (5 * u) ≤ 1 / 16 * u * (1 / 2 ^ 15) := by norm_num
    rw [hey] at hd hy0
    nlinarith
  have hlm : |fv ((Erfc.fastTwoSum 1.0 (-he)).2 - le)| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (fv ((Erfc.fastTwoSum 1.0 (-he)).2 - le))
      (fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le)
    have : u * |fv (Erfc.fastTwoSum 1.0 (-he)).2 - fv le| ≤ u * (5 * u) := by gcongr
    linarith [show u * (5 * u) + 5 * u ≤ 1 by norm_num]
  have hhm : |fv (Erfc.fastTwoSum 1.0 (-he)).1| ≤ 4 := by
    have := abs_sub_abs_le_abs_sub (fv (Erfc.fastTwoSum 1.0 (-he)).1) (1 + fv (-he))
    rw [show fv (Erfc.fastTwoSum 1.0 (-he)).1 - (1 + fv (-he)) = -fv (Erfc.fastTwoSum 1.0 (-he)).2
      by linarith, abs_neg] at this
    have : |1 + fv (-he)| ≤ 2 := by rw [nv, abs_le]; constructor <;> linarith
    linarith [show (3 : ℝ) * u ≤ 1 by norm_num]
  split
  · exact ⟨s1, l1, m1, hhm, hlm, mb.trans (by norm_num), main⟩
  · exact ⟨s1, l1, e1, hhm, hlm, eb, main⟩

/-- When the rounding test passes on the fast path below `0x1.713786d9c7c09p+1`, the result lies
within one step of `erfc x`. -/
theorem fast_within (x : Float) (r : Float × Float × Float) (hr : FastOK (RealErf.erfc (fv x)) r)
    (hy : 1 / 2 ^ 1021 ≤ RealErf.erfc (fv x)) (htest : (r.1 + (r.2.1 - r.2.2) == r.1 + (r.2.1 + r.2.2)) = true) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x)) (r.1 + (r.2.1 - r.2.2)).toBits := by
  obtain ⟨h1, h2, h3, hb1, hb2, hb3, hd⟩ := hr
  have hn := test_near r.1 r.2.1 r.2.2 h1 h2 h3 hb1 hb2 hb3 htest
  have hy0 := erfc_pos (fv x)
  have hy2 := erfc_lt_two (fv x)
  exact near_within _ _ _ hn hy (by linarith [show (2 : ℝ) < 2 ^ 1022 by norm_num]) hd

#print axioms erfcFast_neg
#print axioms erfcFast_pos
#print axioms fast_within

#print axioms fts_one
#print axioms fts_unit

end Library.Numerics.Float64.Erfc.ErfcFastPath
