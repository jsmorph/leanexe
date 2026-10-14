import Verified.Examples.ErfcAccPath
import Verified.Examples.ErfcAsymFast

/-!
The main path of `cr_erfc`, `Erfc.erfcMain`, within one step of `erfc x` for
`-47/8 < x < 0x1.b39dc41e48bfdp+4`, `x ≠ 0`.  When the rounding test of the fast path passes, its
result lies within one step (`ErfcFastPath.fast_within`): the fast path meets `FastOK` below
`0x1.713786d9c7c09p+1` (`ErfcFastPath`) and up to `0x1.9db1bb14e15cap+4` (`fast_ok_asym`, from
`ErfcAsymFast.asym_fast_err`), where `erfc x` stays above `2^-1021` (`erfc_lower`); from there on
the fast path returns `(0, 0, 1)`, whose test fails.  Otherwise the accurate path's result lies
within one step (`ErfcAccPath.acc_within`).
-/

namespace Verified.Examples.ErfcMainPath

open Real CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound ErfcTest ErfcFastPlan ErfcFastAll
  ErfcFastPath ErfcAsymFast ErfcAsymZ ErfcAccPath FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- `erfc z` lies above `2^-1021` for `2 ≤ z < 25.86`. -/
theorem erfc_lower (z : ℝ) (h2 : 2 ≤ z) (hz : z < 2586 / 100) : 1 / 2 ^ 1021 ≤ erfc z := by
  have hG := G_bounds z h2
  have hz0 : 0 < z := by linarith
  have hE := exp_lower2 (-z ^ 2) (by nlinarith)
  have hx : 49 / 100 / (2586 / 100) ≤ erfcx z := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith [hG.1, erfcx_pos z]
  rw [erfc_eq]
  calc (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 967 * (49 / 100 / (2586 / 100)) := by norm_num
    _ ≤ exp (-z ^ 2) * erfcx z := mul_le_mul hE hx (by positivity) (exp_pos _).le

/-- A product of floats of magnitude at most `1/2` rounds to a float of magnitude at most 1. -/
theorem small_mul (a b : Float) (ha : ff a) (hb : ff b) (hab : |fv a * fv b| ≤ 1 / 2) :
    ff (a * b) ∧ |fv (a * b)| ≤ 1 := by
  obtain ⟨f, e⟩ := mul_f a b ha hb (hab.trans (by norm_num))
  refine ⟨f, ?_⟩
  have := abs_sub_abs_le_abs_sub (fv (a * b)) (fv a * fv b)
  have : u * |fv a * fv b| ≤ u * (1 / 2) := by gcongr
  linarith [show u * (1 / 2) + η + 1 / 2 ≤ 1 by norm_num]

/-- The words of the fast path's tests and bounds. -/
theorem fast_words : ff (Float.ofBits 0x4039DB1BB14E15CA) ∧
    fv (Float.ofBits 0x4039DB1BB14E15CA) = ratOfWord 0x4039DB1BB14E15CA ∧
    ff (Float.ofBits 0x3BBD900000000000) ∧ |fv (Float.ofBits 0x3BBD900000000000)| ≤ 1 / 2 ∧
    ff (Float.ofBits 0x0010000000000000) ∧ |fv (Float.ofBits 0x0010000000000000)| ≤ 1 ∧
    (2 : ℝ) ≤ ratOfWord 0x400713786D9C7C09 ∧ (ratOfWord 0x4039DB1BB14E15CA : ℝ) < 2586 / 100 ∧
    ratOfWord 0x400713786D9C7C09 = xMax := by
  have f1 : Finite (0x4039DB1BB14E15CA : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f2 : Finite (0x3BBD900000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f3 : Finite (0x0010000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ f1
  obtain ⟨a2, b2⟩ := ofBits_ff _ f2
  obtain ⟨a3, b3⟩ := ofBits_ff _ f3
  have k : |ratOfWord 0x3BBD900000000000| ≤ 1 / 2 ∧ |ratOfWord 0x0010000000000000| ≤ 1 ∧
      (2 : ℚ) ≤ ratOfWord 0x400713786D9C7C09 ∧ ratOfWord 0x4039DB1BB14E15CA < 2586 / 100 ∧
      ratOfWord 0x400713786D9C7C09 = xMax := by
    decide +kernel
  obtain ⟨k1, k2, k3, k4, k5⟩ := k
  exact ⟨a1, b1, a2, by rw [b2]; qc k1, a3, by rw [b3]; qc k2, by qc k3, by qc k4, k5⟩

/-- The fast path above `0x1.713786d9c7c09p+1`. -/
theorem fast_ok_asym (hF : FmaNearest) (x : Float) (hx : ff x) (hlo : (xMax : ℝ) < fv x)
    (hhi : fv x < ratOfWord 0x4039DB1BB14E15CA) :
    FastOK (erfc (fv x)) (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x) := by
  obtain ⟨z0f, z0v⟩ := zero_val
  obtain ⟨xf, xv⟩ := xmax_word
  obtain ⟨tf, tv, cf2, cb2, cf3, cb3, -, -, k5⟩ := fast_words
  have hxm : (0 : ℝ) < xMax := by rw [xMax_val]; norm_num
  have hxnot : ¬ x < 0.0 := fun h => by
    have := (flt_iff _ _ hx z0f).mp h; rw [z0v] at this; linarith
  have hxgt : ¬ x ≤ Float.ofBits 0x400713786D9C7C09 := fun h => by
    have := (fle_iff _ _ hx xf).mp h; rw [xv] at this; linarith
  have hxlt : ¬ x ≥ Float.ofBits 0x4039DB1BB14E15CA := fun h => by
    have := (fle_iff _ _ tf hx).mp h; rw [tv] at this; linarith
  obtain ⟨f1, f2, herr, hb1, hb2⟩ := asym_fast_err hF x hx (by rw [k5]; exact hlo) hhi
  unfold Erfc.erfcFast
  rw [if_neg hxnot, if_neg hxgt, fast_eq, if_neg hxlt]
  set p := asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x
  have hy := erfc_pos (fv x)
  have hm : |fv (Float.ofBits 0x3BBD900000000000) * fv p.1| ≤ 1 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (fv (Float.ofBits 0x3BBD900000000000)), abs_nonneg (fv p.1)]
  obtain ⟨mf, mb⟩ := small_mul _ _ cf2 f1 hm
  have he : ff (fin (Float.ofBits 0x044151B9A3FDD5C9) (Float.ofBits 0x3BBD900000000000)
      (Float.ofBits 0x0010000000000000) p).2.2 ∧
      |fv (fin (Float.ofBits 0x044151B9A3FDD5C9) (Float.ofBits 0x3BBD900000000000)
        (Float.ofBits 0x0010000000000000) p).2.2| ≤ 1 := by
    rcases fin_err (Float.ofBits 0x044151B9A3FDD5C9) (Float.ofBits 0x3BBD900000000000)
      (Float.ofBits 0x0010000000000000) p with h | h <;> rw [h]
    · exact ⟨mf, mb⟩
    · exact ⟨cf3, cb3⟩
  refine ⟨by rw [fin_fst]; exact f1, by rw [fin_snd]; exact f2, he.1,
    by rw [fin_fst]; linarith, by rw [fin_snd]; exact hb2, he.2, ?_⟩
  rw [fin_fst, fin_snd]
  refine herr.trans ?_
  have : (0 : ℝ) ≤ erfc (fv x) := hy.le
  have : (1 : ℝ) / 2 ^ 57 ≤ 15 / 16 * u := by norm_num
  nlinarith

/-- When the rounding test of the fast path passes, the fast path meets `FastOK` and `erfc x` lies
above `2^-1021`. -/
theorem fast_cases (hF : FmaNearest) (x : Float) (hx : ff x) (hlo : -(47 / 8) < fv x)
    (htest : ((Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).1 +
        ((Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).2.1 -
          (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).2.2) ==
      (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).1 +
        ((Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).2.1 +
          (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x).2.2)) = true) :
    FastOK (erfc (fv x)) (Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x) ∧
      1 / 2 ^ 1021 ≤ erfc (fv x) := by
  obtain ⟨z0f, z0v⟩ := zero_val
  obtain ⟨xf, xv⟩ := xmax_word
  obtain ⟨tf, tv, -, -, -, -, k2, k3, -⟩ := fast_words
  by_cases hneg : fv x < 0
  · refine ⟨erfcFast_neg hF x hx hneg (by linarith), ?_⟩
    have h1 : erf (fv x) ≤ 0 := by
      have := erf_nonneg (-fv x) (by linarith)
      rw [erf_neg] at this; linarith
    unfold erfc; linarith [show (1 : ℝ) / 2 ^ 1021 ≤ 1 by norm_num]
  by_cases hm : fv x ≤ xMax
  · refine ⟨erfcFast_pos hF x hx (by linarith) hm, ?_⟩
    exact (show (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 15 by norm_num).trans
      (erfc_xmax.trans (erfc_strictAnti.antitone hm))
  have hxm : (0 : ℝ) < xMax := by rw [xMax_val]; norm_num
  have hxnot : ¬ x < 0.0 := fun h => by
    have := (flt_iff _ _ hx z0f).mp h; rw [z0v] at this; linarith
  have hxgt : ¬ x ≤ Float.ofBits 0x400713786D9C7C09 := fun h => by
    have := (fle_iff _ _ hx xf).mp h; rw [xv] at this; linarith
  by_cases ht : fv x < ratOfWord 0x4039DB1BB14E15CA
  · refine ⟨fast_ok_asym hF x hx (lt_of_not_ge hm) ht, ?_⟩
    have : (xMax : ℝ) = ratOfWord 0x400713786D9C7C09 := by rw [fast_words.2.2.2.2.2.2.2.2]
    exact erfc_lower (fv x) (by linarith) (by linarith)
  · exfalso
    have hge : x ≥ Float.ofBits 0x4039DB1BB14E15CA :=
      (fle_iff _ _ tf hx).mpr (by rw [tv]; linarith)
    have hfast : Erfc.erfcFast Erfc.fastTable Erfc.expTable Erfc.asymTable x = (0.0, 0.0, 1.0) := by
      unfold Erfc.erfcFast
      rw [if_neg hxnot, if_neg hxgt, fast_eq, if_pos hge]
    rw [hfast] at htest
    simp only [F64Bits.beq_eq, F64Bits.toBits_add, F64Bits.toBits_sub,
      show (0.0 : Float).toBits = 0 from rfl,
      show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl] at htest
    revert htest
    decide +kernel

/-- `Erfc.erfcMain` within one step of `erfc x` for `-47/8 < x < 0x1.b39dc41e48bfdp+4`,
`x ≠ 0`. -/
theorem main_within (hF : FmaNearest) (x : Float) (hx : ff x) (hlo : -(47 / 8) < fv x)
    (h0 : fv x ≠ 0) (hhi : fv x < ratOfWord 0x403B39DC41E48BFD) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.erfcMain Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable Erfc.asymAccTable
        Erfc.expAccTable Erfc.excTable x).toBits := by
  unfold Erfc.erfcMain
  dsimp only
  split
  · rename_i htest
    obtain ⟨hok, hy⟩ := fast_cases hF x hx hlo htest
    exact fast_within x _ hok hy htest
  · exact acc_within hF x hx hlo h0 hhi

#print axioms main_within

end Verified.Examples.ErfcMainPath
