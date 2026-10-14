import Verified.Examples.LgammaLogAccTail
import Verified.Examples.TgammaMainRed
import Verified.Examples.TgammaPolyLip

/-!
**`Lgamma.asLogdAccurate` within `2^-88` of `log y`** for every positive finite double `y`
(`acc_abs`), under `FmaSpec.FmaNearest` and `LgammaApprox.LogAccFact`.  With `y = 2^E t` and
`X = r t - 1` from the reduction (`LgammaLogAccRed.reduce_spec`), `log y = E log 2 - log r1 - log r2 +
log (1 + X)`.  The code computes `E` times the three parts of `ln 2`, the triples `h1 i1 + h2 i2`,
and the kernel `X · logAccPoly X` (`LgammaLogAccKern.kern_spec`).  The sum `E ln2₀ + s₂` of the
high parts is exact on the grid `2^-42`, and it is 0 or at least `6.79 · 10^-4` in magnitude
(`l0_ok`), larger than the rest, so the first renormalization is exact.  The error is
`1074 · 2^-100` from `ln 2`, `2^-80 |X|` from the kernel's polynomial, `2 · 2^-96` from the table,
and smaller roundings.
-/

namespace Verified.Examples.LgammaLogdAcc
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul LgammaLogAccKern
  LgammaLogAccTail

set_option exponentiation.threshold 4096

/-- `fastTwoSum a b` with `a = 0` is exact. -/
theorem fts_zero (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (ha0 : value a.toBits = 0) (hbl : |value b.toBits| < 2 ^ 1000) :
    Finite (fastTwoSum a b).1.toBits ∧ Finite (fastTwoSum a b).2.toBits ∧
      value (fastTwoSum a b).1.toBits = value b.toBits ∧ value (fastTwoSum a b).2.toBits = 0 := by
  have hlim : |value a.toBits + value b.toBits| < 2 ^ 1023 := by
    rw [ha0, zero_add]; linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)]
  obtain ⟨hsf, hsv⟩ := TgammaLogdTab.fadd_exact a b b ha hb hb (by rw [ha0, zero_add]) hlim
  rw [ha0, zero_add] at hsv
  obtain ⟨hzf, hzv⟩ := TgammaLogdTab.fsub_exact (a + b) a b hsf ha hb (by rw [hsv, ha0, sub_zero])
    (by rw [hsv, ha0, sub_zero]; linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)])
  rw [hsv, ha0, sub_zero] at hzv
  obtain ⟨htf, htv⟩ := TgammaLogdTab.fsub_exact b (a + b - a) a hb hzf ha
    (by rw [hzv, ha0, sub_self]) (by rw [hzv, sub_self, abs_zero]; norm_num)
  rw [hzv, sub_self] at htv
  exact ⟨hsf, htf, hsv, htv⟩

/-- The sum of the high parts `E ln2₀ + h₁ + h₂` on the grid `2^-42`: 0 or at least
`2987000000/2^42` in magnitude for `|E| ≤ 1`. -/
def l0Ok : Bool :=
  (List.range 33).all fun i => (List.range 32).all fun j => ([-1, 0, 1] : List ℤ).all fun E =>
    let k := E * 3048493539143 + hiN (3 * i + 2) + hiN (99 + 3 * j + 2)
    k == 0 || decide (2987000000 ≤ |k|)

theorem l0_ok : l0Ok = true := by decide +kernel

theorem l0_bound (i j : ℕ) (hi : i < 33) (hj : j < 32) (E : ℤ) (hE : |E| ≤ 1074) :
    E * 3048493539143 + hiN (3 * i + 2) + hiN (99 + 3 * j + 2) = 0 ∨
      2987000000 ≤ |E * 3048493539143 + hiN (3 * i + 2) + hiN (99 + 3 * j + 2)| := by
  obtain ⟨-, h1, h2, -⟩ := words_ok
  obtain ⟨-, a0, a1⟩ := h1 i hi
  obtain ⟨-, b0, b1⟩ := h2 j hj
  rcases (show E = -1 ∨ E = 0 ∨ E = 1 ∨ 2 ≤ |E| by
    rcases le_or_gt 2 |E| with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · rw [abs_lt] at h; omega) with h | h | h | h
  all_goals try (
    have hc := l0_ok
    unfold l0Ok at hc
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hc
    have := hc i hi j hj E (by rw [h]; simp)
    rw [h] at this ⊢
    exact this)
  right
  rw [abs_le] at hE
  rcases le_or_gt 0 E with hE0 | hE0
  · rw [abs_of_nonneg hE0] at h
    rw [abs_of_pos (by nlinarith)]
    nlinarith
  · rw [abs_of_neg hE0] at h
    rw [abs_of_neg (by nlinarith)]
    nlinarith

theorem r_pos : (∀ i < 33, 0 < LgammaApprox.r1 i) ∧ ∀ i < 32, 0 < LgammaApprox.r2 i := by
  decide +kernel

/-- The bounds of `logAccPoly` and of its Lipschitz constant on `|X| ≤ 1/2399`. -/
theorem poly_lip :
    TgammaPolyLip.bndQ (1 / 2399) (LgammaApprox.ddCoeffs Lgamma.logAccurateTable 198 6 ++
      [LgammaApprox.q Lgamma.logAccurateTable 210, LgammaApprox.q Lgamma.logAccurateTable 212,
        LgammaApprox.q Lgamma.logAccurateTable 214]) ≤ 1001 / 1000 ∧
    TgammaPolyLip.lipQ (1 / 2399) (LgammaApprox.ddCoeffs Lgamma.logAccurateTable 198 6 ++
      [LgammaApprox.q Lgamma.logAccurateTable 210, LgammaApprox.q Lgamma.logAccurateTable 212,
        LgammaApprox.q Lgamma.logAccurateTable 214]) ≤ 1 := by
  decide +kernel

/-- `X logAccPoly X` changes by at most `1.01 |a - b|` on `|X| ≤ 1/2399`. -/
theorem xpoly_lip (a b : ℝ) (ha : |a| ≤ 1 / 2399) (hb : |b| ≤ 1 / 2399) :
    |a * LgammaApprox.logAccPoly a - b * LgammaApprox.logAccPoly b| ≤ 101 / 100 * |a - b| := by
  obtain ⟨hB, hL⟩ := poly_lip
  have hB' := (Rat.cast_le (K := ℝ)).mpr hB
  have hL' := (Rat.cast_le (K := ℝ)).mpr hL
  push_cast at hB' hL'
  have ha' : |a| ≤ ((1 / 2399 : ℚ) : ℝ) := by push_cast; exact ha
  have hb' : |b| ≤ ((1 / 2399 : ℚ) : ℝ) := by push_cast; exact hb
  have h1 := TgammaPolyLip.eval_bound (1 / 2399) (by norm_num) a ha' (LgammaApprox.ddCoeffs
    Lgamma.logAccurateTable 198 6 ++ [LgammaApprox.q Lgamma.logAccurateTable 210,
      LgammaApprox.q Lgamma.logAccurateTable 212, LgammaApprox.q Lgamma.logAccurateTable 214])
  have h2 := TgammaPolyLip.eval_lip (1 / 2399) (by norm_num) a b ha' hb' (LgammaApprox.ddCoeffs
    Lgamma.logAccurateTable 198 6 ++ [LgammaApprox.q Lgamma.logAccurateTable 210,
      LgammaApprox.q Lgamma.logAccurateTable 212, LgammaApprox.q Lgamma.logAccurateTable 214])
  simp only [LgammaApprox.logAccPoly]
  set pa := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.logAccurateTable 198 6 ++
    [LgammaApprox.q Lgamma.logAccurateTable 210, LgammaApprox.q Lgamma.logAccurateTable 212,
      LgammaApprox.q Lgamma.logAccurateTable 214]) a
  set pb := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.logAccurateTable 198 6 ++
    [LgammaApprox.q Lgamma.logAccurateTable 210, LgammaApprox.q Lgamma.logAccurateTable 212,
      LgammaApprox.q Lgamma.logAccurateTable 214]) b
  have key : a * pa - b * pb = (a - b) * pa + b * (pa - pb) := by ring
  rw [key]
  have h3 : |(a - b) * pa| ≤ |a - b| * (1001 / 1000) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by push_cast at h1; linarith) (abs_nonneg _)
  have h4 : |b * (pa - pb)| ≤ 1 / 2399 * |a - b| := by
    rw [abs_mul]
    have : |pa - pb| ≤ |a - b| := by push_cast at h2; nlinarith [abs_nonneg (a - b)]
    exact mul_le_mul hb this (abs_nonneg _) (by norm_num)
  have := abs_add_le ((a - b) * pa) (b * (pa - pb))
  have h0 := abs_nonneg (a - b)
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **`asLogdAccurate` within `2^-88` of `log y`** for a positive finite `y`, with bounds on the
middle and low parts. -/
theorem acc_abs (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (y : Float)
    (hy : Finite y.toBits) (hpos : 0 < value y.toBits) :
    Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits ∧
      Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits ∧
      Finite (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits ∧
      |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits +
          value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits +
          value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits -
          Real.log (value y.toBits)| ≤ 1 / 2 ^ 88 ∧
      |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.1.toBits| ≤
        |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits| / 2 ^ 51 + 1 / 2 ^ 50 ∧
      |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).2.2.toBits| ≤
        |value (Lgamma.asLogdAccurate Tgamma.logdTable H y).1.toBits| / 2 ^ 100 + 1 / 2 ^ 100 := by
  obtain ⟨E, hEb, hRt, hRt1, hRt2, hRr, hRrv, hRrt, hRed, hRedv, hRi1, hRi2, hyv, -⟩ :=
    LgammaLogAccRed.reduce_spec y hy hpos
  obtain ⟨T, hT⟩ : ∃ T, Lgamma.asLogdAccurate Tgamma.logdTable H y = T := ⟨_, rfl⟩
  rw [hT]
  unfold Lgamma.asLogdAccurate at hT
  generalize hR : Lgamma.logReduce Tgamma.logdTable y = R at hT hRt hRt1 hRt2 hRr hRrv hRrt hRed hRedv hRi1 hRi2 hyv
  obtain ⟨t, r, ed, i1, i2⟩ := R
  dsimp only at hT hRt hRt1 hRt2 hRr hRrv hRrt hRed hRedv hRi1 hRi2 hyv
  generalize hD : fastTwoSum (r * t - 1.0) (Fma.fma r t (-(r * t))) = D at hT
  generalize hP : Lgamma.polyDD H 198 6 D.1 D.2
    (D.1 * (entry H 210 + D.1 * (entry H 212 + D.1 * entry H 214))) = P at hT
  generalize hQ : mulDD D.1 D.2 P.1 P.2 = Q at hT
  generalize hS1 : sumDD (Float.ofBits 0x3D2EF35793C76000 * ed) (Float.ofBits 0x3A8CC01F97B57A08 * ed)
    (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)) (entry H (3 * i1) + entry H (99 + 3 * i2)) =
    S1 at hT
  generalize hS2 : sumDD S1.1 S1.2 Q.1 Q.2 = S2 at hT
  generalize hF1 : fastTwoSum (Float.ofBits 0x3FE62E42FEFA3800 * ed +
    (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2))) S2.1 = F1 at hT
  generalize hF2 : fastTwoSum F1.2 S2.2 = F2 at hT
  subst hT
  dsimp only
  -- the reduction's values
  set τ := value t.toBits with hτdef
  set ρ := value r.toBits with hρdef
  set X := ρ * τ - 1 with hXdef
  have hX : |X| ≤ 1 / 2400 := hRrt
  -- the kernel's inputs
  have z0 := TgammaMainRed.zero_finite
  have zv := TgammaMainRed.zero_value
  obtain ⟨-, -, -, hxf, hlf, -, hX104, hxb, hlb, -, -⟩ := TgammaLogdKernel.kernel_spec hF r t 0.0 0.0
    0.0 0.0 hRr hRt z0 z0 z0 z0 hRrt (by rw [zv]; norm_num) (by rw [zv]; norm_num)
    (by rw [zv]; norm_num) (by rw [zv]; norm_num)
  obtain ⟨hD1f, hD2f, hDe, -, hD2b⟩ := TgammaAcc2.fts_approx _ _ hxf hlf (1 / 2400 + 1 / 2 ^ 52)
    (1 / 2 ^ 52) hxb hlb (by norm_num)
  rw [hD] at hD1f hD2f hDe hD2b
  set Xd := value D.1.toBits + value D.2.toBits with hXddef
  have hXd : |Xd - X| ≤ 1 / 2 ^ 103 := by
    have := abs_sub_le Xd (value (r * t - 1.0).toBits + value (Fma.fma r t (-(r * t))).toBits) X
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 / 2 ^ 53 + (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 104 +
      1 / 2 ^ 104 ≤ 1 / 2 ^ 103)]
  have hXdb : |Xd| ≤ 1 / 2400 + 1 / 2 ^ 103 := by
    have := abs_sub_abs_le_abs_sub Xd X; linarith
  have hD1b : |value D.1.toBits| ≤ 1 / 2400 + 1 / 2 ^ 51 := by
    have h1 := abs_sub_abs_le_abs_sub (value D.1.toBits) (-value D.2.toBits)
    rw [sub_neg_eq_add, abs_neg] at h1
    linarith [(by norm_num : (1 : ℝ) / 2400 + 1 / 2 ^ 103 + (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51 ≤
      1 / 2400 + 1 / 2 ^ 51)]
  -- the kernel
  obtain ⟨hQ1f, hQ2f, hQe, hQ2b, hQ1b⟩ := kern_spec hF D.1 D.2 hD1f hD2f
    ((1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51) hD1b hD2b (by norm_num)
  rw [hP, hQ] at hQ1f hQ2f hQe hQ2b hQ1b
  have hlip := xpoly_lip Xd X (by linarith [(by norm_num : (1 : ℝ) / 2400 + 1 / 2 ^ 103 ≤ 1 / 2399)])
    (by linarith [(by norm_num : (1 : ℝ) / 2400 ≤ 1 / 2399)])
  have hfact := hLA.1 X hX
  have hQlog : |value Q.1.toBits + value Q.2.toBits - Real.log (1 + X)| ≤ 1 / 2 ^ 91 := by
    have h1 := abs_sub_le (value Q.1.toBits + value Q.2.toBits) (Xd * LgammaApprox.logAccPoly Xd)
      (X * LgammaApprox.logAccPoly X)
    have h2 := abs_sub_le (value Q.1.toBits + value Q.2.toBits) (X * LgammaApprox.logAccPoly X)
      (Real.log (1 + X))
    rw [abs_sub_comm (X * LgammaApprox.logAccPoly X)] at h2
    have h3 : 1 / 2 ^ 80 * |X| ≤ 1 / 2 ^ 80 * (1 / 2400) := mul_le_mul_of_nonneg_left hX (by norm_num)
    have h4 : |Xd| / 2 ^ 93 ≤ (1 / 2400 + 1 / 2 ^ 103) / 2 ^ 93 :=
      div_le_div_of_nonneg_right hXdb (by norm_num)
    have h5 : 101 / 100 * |Xd - X| ≤ 101 / 100 * (1 / 2 ^ 103) :=
      mul_le_mul_of_nonneg_left hXd (by norm_num)
    linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 103 : ℝ) / 2 ^ 93 +
      (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51 / 2 ^ 40 + 1 / 2 ^ 1060 +
      101 / 100 * (1 / 2 ^ 103) + 1 / 2 ^ 80 * (1 / 2400) ≤ 1 / 2 ^ 91)]
  have hQ2b' : |value Q.2.toBits| ≤ 1 / 2 ^ 54 := by
    have h4 : |Xd| / 2 ^ 44 ≤ (1 / 2400 + 1 / 2 ^ 103) / 2 ^ 44 :=
      div_le_div_of_nonneg_right hXdb (by norm_num)
    linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 103 : ℝ) / 2 ^ 44 +
      2 * ((1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51) + 1 / 2 ^ 1060 ≤ 1 / 2 ^ 54)]
  have hQ1b' : |value Q.1.toBits| ≤ 4185 / 10 ^ 7 := by
    have h4 : (|Xd| + (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51) * (1 + 1 / 2 ^ 8) ≤
        (1 / 2400 + 1 / 2 ^ 103 + (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51) * (1 + 1 / 2 ^ 8) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 103 + (1 / 2400 + 1 / 2 ^ 52 + 1 / 2 ^ 52) / 2 ^ 51 : ℝ) *
      (1 + 1 / 2 ^ 8) + 1 / 2 ^ 1060 ≤ 4185 / 10 ^ 7)]
  -- the words of the table
  obtain ⟨-, hhi1, hhi2, hmid1, hmid2, hlo1, hlo2⟩ := words_ok
  obtain ⟨ia0, ia1, ia2⟩ := ix_a i1 hRi1
  obtain ⟨ib0, ib1, ib2⟩ := ix_b i2 hRi2
  set n1 := i1.toNat with hn1
  set n2 := i2.toNat with hn2
  obtain ⟨hh1, hh1a, hh1b⟩ := hhi1 n1 hRi1
  obtain ⟨hh2, hh2a, hh2b⟩ := hhi2 n2 hRi2
  obtain ⟨hm1, hm1a, hm1b⟩ := hmid1 n1 hRi1
  obtain ⟨hm2, hm2a, hm2b⟩ := hmid2 n2 hRi2
  obtain ⟨hl1a, hl1b⟩ := hlo1 n1 hRi1
  obtain ⟨hl2a, hl2b⟩ := hlo2 n2 hRi2
  obtain ⟨fe1h, ve1h⟩ := entry_val (3 * n1 + 2) (by omega) (3 * i1 + 2) ia2
  obtain ⟨fe2h, ve2h⟩ := entry_val (99 + 3 * n2 + 2) (by omega) (99 + 3 * i2 + 2) ib2
  obtain ⟨fe1m, ve1m⟩ := entry_val (3 * n1 + 1) (by omega) (3 * i1 + 1) ia1
  obtain ⟨fe2m, ve2m⟩ := entry_val (99 + 3 * n2 + 1) (by omega) (99 + 3 * i2 + 1) ib1
  obtain ⟨fe1l, ve1l⟩ := entry_val (3 * n1) (by omega) (3 * i1) ia0
  obtain ⟨fe2l, ve2l⟩ := entry_val (99 + 3 * n2) (by omega) (99 + 3 * i2) ib0
  rw [hh1] at ve1h
  rw [hh2] at ve2h
  rw [hm1] at ve1m
  rw [hm2] at ve2m
  push_cast at ve1h ve2h ve1m ve2m
  have hl1a' := (Rat.cast_le (K := ℝ)).mpr hl1a
  have hl1b' := (Rat.cast_le (K := ℝ)).mpr hl1b
  have hl2a' := (Rat.cast_le (K := ℝ)).mpr hl2a
  have hl2b' := (Rat.cast_le (K := ℝ)).mpr hl2b
  push_cast at hl1a' hl1b' hl2a' hl2b'
  rw [← ve1l] at hl1a' hl1b'
  rw [← ve2l] at hl2a' hl2b'
  -- the words of `ln 2`
  obtain ⟨wc0, wc1, wc2a, wc2b, fc0, fc1, fc2⟩ := ln2_words
  have vc0 : value (Float.ofBits 0x3FE62E42FEFA3800).toBits = 3048493539143 / 2 ^ 42 := by
    rw [TgammaWords.ofBits_value _ fc0, wc0]; push_cast; ring
  have vc1 : value (Float.ofBits 0x3D2EF35793C76000).toBits = 1063452974651 / 2 ^ 84 := by
    rw [TgammaWords.ofBits_value _ fc1, wc1]; push_cast; ring
  have vc2 : value (Float.ofBits 0x3A8CC01F97B57A08).toBits =
      ((PolyBound.ratOfWord 0x3A8CC01F97B57A08 : ℚ) : ℝ) := TgammaWords.ofBits_value _ fc2
  have wc2a' := (Rat.cast_lt (K := ℝ)).mpr wc2a
  have wc2b' := (Rat.cast_le (K := ℝ)).mpr wc2b
  push_cast at wc2a' wc2b'
  have ffc0 := TgammaWords.ofBits_finite _ fc0
  have ffc1 := TgammaWords.ofBits_finite _ fc1
  have ffc2 := TgammaWords.ofBits_finite _ fc2
  have hEr : |(E : ℝ)| ≤ 1074 := by exact_mod_cast hEb
  have hEi := abs_le.mp hEb
  have hEn : E.natAbs ≤ 1074 := by
    have h := Int.natCast_natAbs E
    omega
  -- `s₂`, `l₀`, and `l₀ + s₂`, exact
  obtain ⟨hs2f, hs2v⟩ := TgammaAcc1.grid_add (entry H (3 * i1 + 2)) (entry H (99 + 3 * i2 + 2))
    fe1h fe2h (hiN (3 * n1 + 2) + hiN (99 + 3 * n2 + 2)) 42 (by rw [ve1h, ve2h]; push_cast; ring)
    (by rw [abs_le, show (2 : ℤ) ^ 53 = 9007199254740992 by norm_num]; constructor <;> omega)
    (by norm_num)
  obtain ⟨hl0f, hl0v⟩ := TgammaAcc1.grid_mul (Float.ofBits 0x3FE62E42FEFA3800) ed ffc0 hRed
    3048493539143 E 42 0 (by rw [vc0]; norm_num) (by rw [hRedv]; norm_num)
    (by rw [show (3048493539143 : ℤ).natAbs = 3048493539143 from rfl]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hEn) (by norm_num)) (by norm_num)
  obtain ⟨hl0'f, hl0'v⟩ := TgammaAcc1.grid_add (Float.ofBits 0x3FE62E42FEFA3800 * ed)
    (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2)) hl0f hs2f
    (E * 3048493539143 + hiN (3 * n1 + 2) + hiN (99 + 3 * n2 + 2)) 42
    (by rw [hl0v, hs2v, vc0, ve1h, ve2h, hRedv]; push_cast; ring)
    (by rw [abs_le, show (2 : ℤ) ^ 53 = 9007199254740992 by norm_num]; constructor <;> omega)
    (by norm_num)
  set K := E * 3048493539143 + hiN (3 * n1 + 2) + hiN (99 + 3 * n2 + 2) with hKdef
  set l0' := Float.ofBits 0x3FE62E42FEFA3800 * ed + (entry H (3 * i1 + 2) + entry H (99 + 3 * i2 + 2))
    with hl0'def
  have hl0'K : value l0'.toBits = (K : ℝ) / 2 ^ 42 := by
    rw [hl0'v, hl0v, hs2v, vc0, ve1h, ve2h, hRedv, hKdef]; push_cast; ring
  -- `l₁` and `s₁`, exact, and `l₂` and `s₀`
  obtain ⟨hl1f, hl1v⟩ := TgammaAcc1.grid_mul (Float.ofBits 0x3D2EF35793C76000) ed ffc1 hRed
    1063452974651 E 84 0 (by rw [vc1]; norm_num) (by rw [hRedv]; norm_num)
    (by rw [show (1063452974651 : ℤ).natAbs = 1063452974651 from rfl]
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hEn) (by norm_num)) (by norm_num)
  obtain ⟨hs1f, hs1v⟩ := TgammaAcc1.grid_add (entry H (3 * i1 + 1)) (entry H (99 + 3 * i2 + 1))
    fe1m fe2m (midN (3 * n1 + 1) + midN (99 + 3 * n2 + 1)) 94 (by rw [ve1m, ve2m]; push_cast; ring)
    (by rw [abs_le, show (2 : ℤ) ^ 53 = 9007199254740992 by norm_num]; constructor <;> omega)
    (by norm_num)
  have fl2 := fapprox_mul (fapprox_self _ ffc2) (fapprox_self _ hRed) (1 / 2 ^ 86) 1074
    (by rw [vc2, abs_of_pos wc2a']; exact wc2b') (by rw [hRedv]; exact hEr) (1 / 2 ^ 86 * 1074)
    (by simp) (by norm_num)
  have fs0 := fapprox_add (fapprox_self _ fe1l) (fapprox_self _ fe2l) (2 / 2 ^ 93)
    (by rw [add_zero, abs_of_nonneg (by linarith)]; linarith) (by norm_num)
  have hl2b : |value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits| ≤ 1 / 2 ^ 75 := by
    have h1 := fl2.2
    have h2 : |value (Float.ofBits 0x3A8CC01F97B57A08).toBits * value ed.toBits| ≤ 1 / 2 ^ 86 * 1074 := by
      rw [abs_mul, vc2, abs_of_pos wc2a', hRedv]
      exact mul_le_mul wc2b' hEr (abs_nonneg _) (by norm_num)
    have h3 := abs_sub_abs_le_abs_sub (value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits)
      (value (Float.ofBits 0x3A8CC01F97B57A08).toBits * value ed.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 86 * 1074 + (0 * 1074 + 1 / 2 ^ 86 * 0 + 0 * 0 +
      1 / 2 ^ 86 * 1074 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 1 / 2 ^ 75)]
  have hs0b : |value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits| ≤ 1 / 2 ^ 91 := by
    have h1 := fs0.2
    have h3 := abs_sub_abs_le_abs_sub (value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits)
      (value (entry H (3 * i1)).toBits + value (entry H (99 + 3 * i2)).toBits)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ value (entry H (3 * i1)).toBits +
      value (entry H (99 + 3 * i2)).toBits)] at h3
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 93 + (0 + 0 + 2 / 2 ^ 93 / 2 ^ 53) ≤ 1 / 2 ^ 91)]
  have hl1b : |value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits| ≤ 1 / 2 ^ 33 := by
    rw [hl1v, vc1, hRedv, abs_mul]
    have : |(1063452974651 : ℝ) / 2 ^ 84| * |(E : ℝ)| ≤ 1063452974651 / 2 ^ 84 * 1074 := by
      rw [abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hEr (by norm_num)
    linarith [(by norm_num : (1063452974651 : ℝ) / 2 ^ 84 * 1074 ≤ 1 / 2 ^ 33)]
  have hs1b : |value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits| ≤ 1 / 2 ^ 40 := by
    rw [hs1v, ve1m, ve2m]
    have h1 : ((midN (3 * n1 + 1) : ℤ) : ℝ) ≤ 4312648921537145 := by exact_mod_cast hm1b
    have h2 : ((midN (99 + 3 * n2 + 1) : ℤ) : ℝ) ≤ 4496283226037544 := by exact_mod_cast hm2b
    have h3 : (0 : ℝ) ≤ ((midN (3 * n1 + 1) : ℤ) : ℝ) := by exact_mod_cast hm1a
    have h4 : (0 : ℝ) ≤ ((midN (99 + 3 * n2 + 1) : ℤ) : ℝ) := by exact_mod_cast hm2a
    rw [abs_le]
    constructor <;> linarith [(by norm_num : ((4312648921537145 : ℝ) + 4496283226037544) / 2 ^ 94 ≤
      1 / 2 ^ 40)]
  -- `S₁`
  obtain ⟨hS1f1, hS1f2, hS1e, hS1l, hS1h⟩ := sumDD_spec _ _ _ _ hl1f
    (by exact fl2.1) hs1f (by exact fs0.1)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 33 < 2 ^ 898)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 40 < 2 ^ 898)])
    (1 / 2 ^ 75 + 1 / 2 ^ 91) (by linarith) (by norm_num)
  rw [hS1] at hS1f1 hS1f2 hS1e hS1l hS1h
  have hS1hb : |value S1.1.toBits| ≤ 1 / 2 ^ 32 := by
    have := abs_add_le (value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits)
      (value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits)
    have h2 : |value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits +
        value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits| * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 33 + 1 / 2 ^ 40) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 33 + 1 / 2 ^ 40 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
      1 / 2 ^ 32)]
  have hS1lb : |value S1.2.toBits| ≤ 1 / 2 ^ 74 := by
    have h2 : |value S1.1.toBits| / 2 ^ 51 ≤ 1 / 2 ^ 32 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS1hb (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 75 + 1 / 2 ^ 91 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 32 / 2 ^ 51 +
      1 / 2 ^ 1073 ≤ 1 / 2 ^ 74)]
  have hS1err : |value S1.1.toBits + value S1.2.toBits -
      (value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits +
        value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits +
        (value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits +
          value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits))| ≤ 1 / 2 ^ 120 := by
    have h2 : |value S1.1.toBits| / 2 ^ 52 ≤ 1 / 2 ^ 32 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS1hb (by norm_num)
    linarith [(by norm_num : (3 * (1 / 2 ^ 75 + 1 / 2 ^ 91) + 1 / 2 ^ 32 / 2 ^ 52 + 1 / 2 ^ 1074 : ℝ) /
      2 ^ 53 ≤ 1 / 2 ^ 120)]
  -- `S₂`
  obtain ⟨hS2f1, hS2f2, hS2e, hS2l, hS2h⟩ := sumDD_spec _ _ _ _ hS1f1 hS1f2 hQ1f hQ2f
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 32 < 2 ^ 898)])
    (by linarith [(by norm_num : (4185 : ℝ) / 10 ^ 7 < 2 ^ 898)])
    (1 / 2 ^ 74 + 1 / 2 ^ 54) (by linarith) (by norm_num)
  rw [hS2] at hS2f1 hS2f2 hS2e hS2l hS2h
  have hS2hb : |value S2.1.toBits| ≤ 4186 / 10 ^ 7 := by
    have := abs_add_le (value S1.1.toBits) (value Q.1.toBits)
    have h2 : |value S1.1.toBits + value Q.1.toBits| * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 32 + 4185 / 10 ^ 7) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 32 + 4185 / 10 ^ 7 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
      4186 / 10 ^ 7)]
  have hS2lb : |value S2.2.toBits| ≤ 1 / 2 ^ 53 := by
    have h2 : |value S2.1.toBits| / 2 ^ 51 ≤ 4186 / 10 ^ 7 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS2hb (by norm_num)
    linarith [(by norm_num : (1 / 2 ^ 74 + 1 / 2 ^ 54 : ℝ) * (1 + 1 / 2 ^ 51) + 4186 / 10 ^ 7 / 2 ^ 51 +
      1 / 2 ^ 1073 ≤ 1 / 2 ^ 53)]
  have hS2err : |value S2.1.toBits + value S2.2.toBits -
      (value S1.1.toBits + value S1.2.toBits + (value Q.1.toBits + value Q.2.toBits))| ≤ 1 / 2 ^ 104 := by
    have h2 : |value S2.1.toBits| / 2 ^ 52 ≤ 4186 / 10 ^ 7 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS2hb (by norm_num)
    linarith [(by norm_num : (3 * (1 / 2 ^ 74 + 1 / 2 ^ 54) + 4186 / 10 ^ 7 / 2 ^ 52 + 1 / 2 ^ 1074 : ℝ) /
      2 ^ 53 ≤ 1 / 2 ^ 104)]
  -- `F₁`: exact
  have hF1spec : Finite F1.1.toBits ∧ Finite F1.2.toBits ∧
      value F1.1.toBits + value F1.2.toBits = value l0'.toBits + value S2.1.toBits ∧
      |value F1.2.toBits| ≤ |value F1.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 ∧
      |value F1.1.toBits| ≤ 746 := by
    have hKb : |(K : ℝ)| ≤ 1074 * 3048493539143 + 2 * 3048493539143 := by
      have : |K| ≤ 1074 * 3048493539143 + 2 * 3048493539143 := by rw [abs_le]; constructor <;> omega
      exact_mod_cast this
    have hl0'b : |value l0'.toBits| ≤ (1074 * 3048493539143 + 2 * 3048493539143) / 2 ^ 42 := by
      rw [hl0'K, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 42)]
      exact div_le_div_of_nonneg_right hKb (by norm_num)
    rcases l0_bound n1 n2 hRi1 hRi2 E hEb with hk0 | hk1
    · have hz : value l0'.toBits = 0 := by rw [hl0'K, show K = 0 from hk0]; simp
      obtain ⟨h1, h2, h3, h4⟩ := fts_zero l0' S2.1 hl0'f hS2f1 hz
        (by linarith [(by norm_num : (4186 : ℝ) / 10 ^ 7 < 2 ^ 1000)])
      rw [hF1] at h1 h2 h3 h4
      refine ⟨h1, h2, by rw [h3, h4, hz]; ring, by rw [h4, abs_zero]; positivity, ?_⟩
      rw [h3]; linarith
    · have hKr : (2987000000 : ℝ) ≤ |(K : ℝ)| := by exact_mod_cast hk1
      have hl0'lo : 2987000000 / 2 ^ 42 ≤ |value l0'.toBits| := by
        rw [hl0'K, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 42)]
        exact div_le_div_of_nonneg_right hKr (by norm_num)
      obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec l0' S2.1 hl0'f hS2f1
        (by linarith [(by norm_num : (4186 : ℝ) / 10 ^ 7 ≤ 2987000000 / 2 ^ 42)])
        (by linarith [(by norm_num : ((1074 : ℝ) * 3048493539143 + 2 * 3048493539143) / 2 ^ 42 <
          2 ^ 900)])
      rw [hF1] at h1 h2 h3 h5
      refine ⟨h1, h2, h3, h5, ?_⟩
      have h6 := abs_sub_abs_le_abs_sub (value F1.1.toBits) (-value F1.2.toBits)
      rw [sub_neg_eq_add, abs_neg, h3] at h6
      have h7 := abs_add_le (value l0'.toBits) (value S2.1.toBits)
      have h8 : |value F1.2.toBits| ≤ |value S2.1.toBits| := by
        obtain ⟨-, -, -, h4, -⟩ := fastTwoSum_spec l0' S2.1 hl0'f hS2f1
          (by linarith [(by norm_num : (4186 : ℝ) / 10 ^ 7 ≤ 2987000000 / 2 ^ 42)])
          (by linarith [(by norm_num : ((1074 : ℝ) * 3048493539143 + 2 * 3048493539143) / 2 ^ 42 <
            2 ^ 900)])
        rw [hF1] at h4; exact h4
      linarith [(by norm_num : ((1074 : ℝ) * 3048493539143 + 2 * 3048493539143) / 2 ^ 42 +
        2 * (4186 / 10 ^ 7) ≤ 746)]
  obtain ⟨hF1f1, hF1f2, hF1sum, hF1l, hF1h⟩ := hF1spec
  -- `F₂`
  have hF1lb : |value F1.2.toBits| ≤ 746 / 2 ^ 52 + 1 / 2 ^ 1074 := by
    have : |value F1.1.toBits| / 2 ^ 52 ≤ 746 / 2 ^ 52 := div_le_div_of_nonneg_right hF1h (by norm_num)
    linarith
  have hF1d : |value F1.1.toBits| / 2 ^ 52 ≤ 746 / 2 ^ 52 :=
    div_le_div_of_nonneg_right hF1h (by norm_num)
  obtain ⟨hF2f1, hF2f2, hF2e, hF2h, hF2l⟩ := TgammaAcc2.fts_approx F1.2 S2.2 hF1f2 hS2f2
    (|value F1.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) (1 / 2 ^ 53) hF1l hS2lb
    (by linarith [(by norm_num : (746 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 53 ≤ 2 ^ 1000)])
  rw [hF2] at hF2f1 hF2f2 hF2e hF2h hF2l
  -- the parts as reals
  have q0 : ((PolyBound.ratOfWord 0x3FE62E42FEFA3800 : ℚ) : ℝ) = 3048493539143 / 2 ^ 42 := by
    rw [wc0]; norm_num
  have q1 : ((PolyBound.ratOfWord 0x3D2EF35793C76000 : ℚ) : ℝ) = 1063452974651 / 2 ^ 84 := by
    rw [wc1]; norm_num
  have hi1r : ((PolyBound.ratOfWord Lgamma.logAccurateTable[3 * n1 + 2]! : ℚ) : ℝ) =
      (hiN (3 * n1 + 2) : ℝ) / 2 ^ 42 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hh1; push_cast at this; exact this
  have hi2r : ((PolyBound.ratOfWord Lgamma.logAccurateTable[99 + 3 * n2 + 2]! : ℚ) : ℝ) =
      (hiN (99 + 3 * n2 + 2) : ℝ) / 2 ^ 42 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hh2; push_cast at this; exact this
  have mi1r : ((PolyBound.ratOfWord Lgamma.logAccurateTable[3 * n1 + 1]! : ℚ) : ℝ) =
      (midN (3 * n1 + 1) : ℝ) / 2 ^ 94 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hm1; push_cast at this; exact this
  have mi2r : ((PolyBound.ratOfWord Lgamma.logAccurateTable[99 + 3 * n2 + 1]! : ℚ) : ℝ) =
      (midN (99 + 3 * n2 + 1) : ℝ) / 2 ^ 94 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hm2; push_cast at this; exact this
  have lo1r : value (entry H (3 * i1)).toBits =
      ((PolyBound.ratOfWord Lgamma.logAccurateTable[3 * n1]! : ℚ) : ℝ) := ve1l
  have lo2r : value (entry H (99 + 3 * i2)).toBits =
      ((PolyBound.ratOfWord Lgamma.logAccurateTable[99 + 3 * n2]! : ℚ) : ℝ) := ve2l
  have vl0' : value l0'.toBits = (E : ℝ) * (3048493539143 / 2 ^ 42) +
      (hiN (3 * n1 + 2) : ℝ) / 2 ^ 42 + (hiN (99 + 3 * n2 + 2) : ℝ) / 2 ^ 42 := by
    rw [hl0'K, hKdef]; push_cast; ring
  have vl1 : value (Float.ofBits 0x3D2EF35793C76000 * ed).toBits = (E : ℝ) * (1063452974651 / 2 ^ 84) := by
    rw [hl1v, vc1, hRedv]; ring
  have vs1 : value (entry H (3 * i1 + 1) + entry H (99 + 3 * i2 + 1)).toBits =
      (midN (3 * n1 + 1) : ℝ) / 2 ^ 94 + (midN (99 + 3 * n2 + 1) : ℝ) / 2 ^ 94 := by
    rw [hs1v, ve1m, ve2m]
  have hl2e : |value (Float.ofBits 0x3A8CC01F97B57A08 * ed).toBits -
      (E : ℝ) * ((PolyBound.ratOfWord 0x3A8CC01F97B57A08 : ℚ) : ℝ)| ≤ 1 / 2 ^ 125 := by
    have := fl2.2
    rw [vc2, hRedv] at this
    rw [mul_comm (E : ℝ)]
    linarith [(by norm_num : (0 : ℝ) * 1074 + 1 / 2 ^ 86 * 0 + 0 * 0 + 1 / 2 ^ 86 * 1074 / 2 ^ 53 +
      1 / 2 ^ 1075 ≤ 1 / 2 ^ 125)]
  have hs0e : |value (entry H (3 * i1) + entry H (99 + 3 * i2)).toBits -
      (((PolyBound.ratOfWord Lgamma.logAccurateTable[3 * n1]! : ℚ) : ℝ) +
        ((PolyBound.ratOfWord Lgamma.logAccurateTable[99 + 3 * n2]! : ℚ) : ℝ))| ≤ 1 / 2 ^ 140 := by
    have := fs0.2
    rw [lo1r, lo2r] at this
    linarith [(by norm_num : (0 : ℝ) + 0 + 2 / 2 ^ 93 / 2 ^ 53 ≤ 1 / 2 ^ 140)]
  -- the facts on `ln 2` and the table
  obtain ⟨-, hh1f, hh2f, hln2⟩ := hLA
  have hH1 := hh1f n1 hRi1
  have hH2 := hh2f n2 hRi2
  simp only [LgammaApprox.h1, LgammaApprox.h2, LgammaApprox.ln2Acc, LgammaApprox.q,
    LgammaApprox.r1, LgammaApprox.r2] at hH1 hH2 hln2
  rw [show 100 + 3 * n2 = 99 + 3 * n2 + 1 by omega, show 101 + 3 * n2 = 99 + 3 * n2 + 2 by omega]
    at hH2
  push_cast at hH1 hH2 hln2
  rw [q0, q1] at hln2
  have hEln2 : |(E : ℝ) * (3048493539143 / 2 ^ 42) + (E : ℝ) * (1063452974651 / 2 ^ 84) +
      (E : ℝ) * ((PolyBound.ratOfWord 0x3A8CC01F97B57A08 : ℚ) : ℝ) - E * Real.log 2| ≤
      1074 / 2 ^ 100 := by
    rw [show (E : ℝ) * (3048493539143 / 2 ^ 42) + (E : ℝ) * (1063452974651 / 2 ^ 84) +
      (E : ℝ) * ((PolyBound.ratOfWord 0x3A8CC01F97B57A08 : ℚ) : ℝ) - E * Real.log 2 =
      (E : ℝ) * (3048493539143 / 2 ^ 42 + 1063452974651 / 2 ^ 84 +
        ((PolyBound.ratOfWord 0x3A8CC01F97B57A08 : ℚ) : ℝ) - Real.log 2) by ring, abs_mul]
    have := mul_le_mul hEr hln2 (abs_nonneg _) (by norm_num)
    linarith
  -- the logarithm of `y`
  have hτ0 : 0 < τ := by linarith
  have hr1 := (Rat.cast_lt (K := ℝ)).mpr (r_pos.1 n1 hRi1)
  have hr2 := (Rat.cast_lt (K := ℝ)).mpr (r_pos.2 n2 hRi2)
  push_cast at hr1 hr2
  simp only [LgammaApprox.r1, LgammaApprox.r2, LgammaApprox.q] at hr1 hr2 hRrv
  push_cast at hRrv
  have h1X : 0 < 1 + X := by
    have := abs_le.mp hX; rw [hXdef] at this ⊢; linarith
  have hlogy : Real.log (value y.toBits) =
      E * Real.log 2 - Real.log ((PolyBound.ratOfWord Tgamma.logdTable[64 + n1]! : ℚ) : ℝ) -
        Real.log ((PolyBound.ratOfWord Tgamma.logdTable[97 + n2]! : ℚ) : ℝ) + Real.log (1 + X) := by
    rw [hyv, Real.log_mul (by positivity) hτ0.ne', Real.log_zpow]
    have hρ0 : 0 < ρ := by rw [hRrv]; exact mul_pos hr1 hr2
    have hτe : τ = (1 + X) / (((PolyBound.ratOfWord Tgamma.logdTable[64 + n1]! : ℚ) : ℝ) *
        ((PolyBound.ratOfWord Tgamma.logdTable[97 + n2]! : ℚ) : ℝ)) := by
      rw [hXdef, ← hRrv, eq_div_iff hρ0.ne']; ring
    rw [hτe, Real.log_div h1X.ne' (mul_pos hr1 hr2).ne', Real.log_mul hr1.ne' hr2.ne']
    ring
  -- the low and middle parts of the result
  have hF2e' : |value F2.1.toBits + value F2.2.toBits - (value F1.2.toBits + value S2.2.toBits)| ≤
      1 / 2 ^ 100 := by
    have : (|value F1.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 53) / 2 ^ 104 ≤
        (746 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 53) / 2 ^ 104 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 / 2 ^ 53 + (746 / 2 ^ 52 + 1 / 2 ^ 1074 + 1 / 2 ^ 53) /
      2 ^ 104 ≤ 1 / 2 ^ 100)]
  refine ⟨hF1f1, hF2f1, hF2f2, ?_, ?_, ?_⟩
  · rw [hlogy]
    have e1 := abs_le.mp hF2e'
    have e2 := abs_le.mp hS2err
    have e3 := abs_le.mp hS1err
    have e4 := abs_le.mp hl2e
    have e5 := abs_le.mp hs0e
    have e6 := abs_le.mp hQlog
    have e7 := abs_le.mp hEln2
    have e8 := abs_le.mp hH1
    have e9 := abs_le.mp hH2
    rw [abs_le]
    constructor <;> linarith
  · have h0 : 0 ≤ |value F1.1.toBits| := abs_nonneg _
    linarith [hF2h]
  · have h0 : 0 ≤ |value F1.1.toBits| := abs_nonneg _
    linarith [hF2l]

#print axioms acc_abs

end Verified.Examples.LgammaLogdAcc
