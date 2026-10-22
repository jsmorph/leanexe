import Library.Numerics.Float64.Lgamma.LgammaLogdAcc
import Library.Numerics.Float64.Lgamma.LgammaAsymRecip

/-!
The logarithm of `x = xh + xl` in `Lgamma.asLgammaAsymAccurate`, for `15/4 ≤ xh ≤ 2^120` and
`|xl| ≤ xh/2^51`: `asLogdAccurate xh`, within `2^-88` of `log xh` (`LgammaLogdAcc.acc_abs`), and,
when `xl ≠ 0`, the correction `d - d²/2` for `d = xl (zh + c) ≈ t = xl/xh`, with `zh = 1/xh` and
`c = fma (zh, -xh, 1) zh` (`LgammaRecip.recip_wide`), added to the middle and low parts with
`sumDD`.  `Real.abs_log_sub_add_sum_range_le` bounds `log (1 + t) - (t - t²/2)` by
`|t|³/(1 - |t|)`, below `2^-152`, and `log x = log xh + log (1 + t)` (`log_dd`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAsymLog
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD LgammaLogAccKern

set_option exponentiation.threshold 4096

/-- The code's correction of the middle and low parts for `xl`. -/
def corr (l1 l2 xh xl : Float) : Float × Float :=
  if xl != 0.0 then
    sumDD l1 l2 (mulDDD xl (1.0 / xh) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / xh) (-xh) 1.0 * (1.0 / xh))).1
      ((mulDDD xl (1.0 / xh) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / xh) (-xh) 1.0 * (1.0 / xh))).2 -
        (mulDDD xl (1.0 / xh) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / xh) (-xh) 1.0 * (1.0 / xh))).1 *
          (mulDDD xl (1.0 / xh) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / xh) (-xh) 1.0 * (1.0 / xh))).1 / 2.0)
  else (l1, l2)

/-- `log (1 + t)` against `t - t²/2`. -/
theorem log_two (t : ℝ) (ht : |t| ≤ 1 / 2 ^ 51) :
    |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ 1 / 2 ^ 152 := by
  have h1 : |-t| < 1 := by rw [abs_neg]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 < 1)]
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  replace h : |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ |t| ^ (2 + 1) / (1 - |t|) := by
    convert h using 2
    push_cast
    ring
  have h3 : |t| ^ (2 + 1) ≤ (1 / 2 ^ 51) ^ 3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
  have h4 : (1 : ℝ) / 2 ≤ 1 - |t| := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 ≤ 1 / 2)]
  have h5 : |t| ^ (2 + 1) / (1 - |t|) ≤ 2 * (1 / 2 ^ 51) ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg t) (2 + 1)]
  linarith [(by norm_num : (2 : ℝ) * (1 / 2 ^ 51) ^ 3 ≤ 1 / 2 ^ 152)]

set_option maxHeartbeats 2000000 in
/-- **The logarithm of `xh + xl`.** -/
theorem log_dd (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (xh xl : Float)
    (hxh : Finite xh.toBits) (hxl : Finite xl.toBits) (hlo : 15 / 4 ≤ value xh.toBits)
    (hhi : value xh.toBits ≤ 2 ^ 120) (hlb : |value xl.toBits| ≤ value xh.toBits / 2 ^ 51) :
    let T := Lgamma.asLogdAccurate Tgamma.logdTable H xh
    let L := corr T.2.1 T.2.2 xh xl
    Finite T.1.toBits ∧ Finite L.1.toBits ∧ Finite L.2.toBits ∧
      |value T.1.toBits + value L.1.toBits + value L.2.toBits -
          Real.log (value xh.toBits + value xl.toBits)| ≤ 1 / 2 ^ 88 + 1 / 2 ^ 140 ∧
      |value L.1.toBits| ≤ |value T.1.toBits| / 2 ^ 50 + 1 / 2 ^ 48 ∧
      |value L.2.toBits| ≤ |value T.1.toBits| / 2 ^ 99 + 1 / 2 ^ 97 := by
  intro T L
  set vx := value xh.toBits with hvx
  set vl := value xl.toBits with hvl
  have hx0 : 0 < vx := by linarith
  obtain ⟨t1f, t2f, t3f, te, t2b, t3b⟩ := LgammaLogdAcc.acc_abs hF hLA xh hxh hx0
  rw [show Lgamma.asLogdAccurate Tgamma.logdTable H xh = T from rfl] at t1f t2f t3f te t2b t3b
  set l0 := value T.1.toBits with hl0
  set l1 := value T.2.1.toBits with hl1
  set l2 := value T.2.2.toBits with hl2
  by_cases hz : xl != 0.0
  swap
  · -- `xl = 0`: the parts are unchanged and `vl = 0`
    have hL : L = (T.2.1, T.2.2) := by
      show corr T.2.1 T.2.2 xh xl = (T.2.1, T.2.2)
      unfold corr; simp only [hz, Bool.false_eq_true, ↓reduceIte]
    have hq : (xl == 0.0) = true := by
      by_contra h
      exact hz (by simp [bne, h])
    have hvl0 : vl = 0 := by
      rw [hvl, (F64UpperWord.float_beq_iff xl 0.0 hxl Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_finite).mp hq]
      exact Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_value
    rw [hL]
    refine ⟨t1f, t2f, t3f, ?_, ?_, ?_⟩
    · show |l0 + l1 + l2 - Real.log (vx + vl)| ≤ 1 / 2 ^ 88 + 1 / 2 ^ 140
      rw [hvl0, add_zero]
      linarith [(by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 140)]
    · show |l1| ≤ |l0| / 2 ^ 50 + 1 / 2 ^ 48
      have : |l0| / 2 ^ 51 ≤ |l0| / 2 ^ 50 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 ≤ 1 / 2 ^ 48)]
    · show |l2| ≤ |l0| / 2 ^ 99 + 1 / 2 ^ 97
      have : |l0| / 2 ^ 100 ≤ |l0| / 2 ^ 99 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 ≤ 1 / 2 ^ 97)]
  -- `xl ≠ 0`
  set R := 1 / vx with hRdef
  have hR0 : 0 < R := by positivity
  have hRvx : R * vx = 1 := by rw [hRdef]; field_simp
  obtain ⟨hzf, hcf, hz1, hc1, hzc⟩ := LgammaRecip.recip_wide hF xh hxh
    (by rw [abs_of_pos hx0]; linarith) (by rw [abs_of_pos hx0]; linarith [(by norm_num : (2 : ℝ) ^ 120 ≤ 2 ^ 170)])
  rw [abs_of_pos (show (0 : ℝ) < 1 / vx by positivity)] at hz1 hc1 hzc
  set zh := 1.0 / xh with hzhdef
  set c := Library.Numerics.Arithmetic.Fma.Fma.fma zh (-xh) 1.0 * zh with hcdef
  have hzb : |value zh.toBits| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub (value zh.toBits) R
    rw [abs_of_pos hR0] at this
    linarith
  -- `D = mulDDD xl zh c ≈ t = vl R`
  have hH : |value zh.toBits| * |vl| ≤ (1 + 1 / 2 ^ 52) / 2 ^ 51 := by
    calc |value zh.toBits| * |vl| ≤ R * (1 + 1 / 2 ^ 52) * (vx / 2 ^ 51) :=
          mul_le_mul hzb hlb (abs_nonneg _) (mul_nonneg hR0.le (by norm_num))
      _ = R * vx * (1 + 1 / 2 ^ 52) / 2 ^ 51 := by ring
      _ = (1 + 1 / 2 ^ 52) / 2 ^ 51 := by rw [hRvx, one_mul]
  have hLw : |value c.toBits| * |vl| ≤ 1 / 2 ^ 101 := by
    calc |value c.toBits| * |vl| ≤ R / 2 ^ 50 * (vx / 2 ^ 51) :=
          mul_le_mul hc1 hlb (abs_nonneg _) (div_nonneg hR0.le (by norm_num))
      _ = R * vx / 2 ^ 101 := by ring
      _ = 1 / 2 ^ 101 := by rw [hRvx]
  obtain ⟨d1f, d2f, de, d2b, d1b⟩ := mulDDD_spec hF xl zh c hxl hzf hcf _ _ hH hLw
    (by norm_num) (by norm_num)
  set D := mulDDD xl zh c with hDdef
  set t := vl * R with htdef
  have ht : |t| ≤ 1 / 2 ^ 51 := by
    rw [htdef, abs_mul, abs_of_pos hR0]
    calc |vl| * R ≤ vx / 2 ^ 51 * R := mul_le_mul_of_nonneg_right hlb hR0.le
      _ = R * vx / 2 ^ 51 := by ring
      _ = 1 / 2 ^ 51 := by rw [hRvx]
  have hDt : |value D.1.toBits + value D.2.toBits - t| ≤ 1 / 2 ^ 150 := by
    have h1 : |vl * (value zh.toBits + value c.toBits) - t| ≤ 1 / 2 ^ 151 := by
      rw [htdef, show vl * (value zh.toBits + value c.toBits) - vl * R =
        vl * (value zh.toBits + value c.toBits - R) by ring, abs_mul]
      calc |vl| * |value zh.toBits + value c.toBits - R| ≤ vx / 2 ^ 51 * (R / 2 ^ 100) :=
            mul_le_mul hlb hzc (abs_nonneg _) (div_nonneg hx0.le (by norm_num))
        _ = R * vx / 2 ^ 151 := by ring
        _ = 1 / 2 ^ 151 := by rw [hRvx]
    have h2 := abs_add_le (value D.1.toBits + value D.2.toBits - vl * (value zh.toBits + value c.toBits))
      (vl * (value zh.toBits + value c.toBits) - t)
    rw [show value D.1.toBits + value D.2.toBits - vl * (value zh.toBits + value c.toBits) +
      (vl * (value zh.toBits + value c.toBits) - t) = value D.1.toBits + value D.2.toBits - t by ring]
      at h2
    linarith [(by norm_num : (3 * (1 / 2 ^ 101) + (1 + 1 / 2 ^ 52) / 2 ^ 51 / 2 ^ 51) / 2 ^ 53 +
      1 / 2 ^ 1072 + 1 / 2 ^ 151 ≤ (1 : ℝ) / 2 ^ 150)]
  have hD2 : |value D.2.toBits| ≤ 1 / 2 ^ 100 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 101 * (1 + 1 / 2 ^ 51) + (1 + 1 / 2 ^ 52) / 2 ^ 51 / 2 ^ 52 +
      1 / 2 ^ 1071 ≤ 1 / 2 ^ 100)]
  have hD1 : |value D.1.toBits| ≤ 1 / 2 ^ 50 := by
    linarith [(by norm_num : (1 + 1 / 2 ^ 52 : ℝ) / 2 ^ 51 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 50)]
  -- `E = D1 D1 / 2` and `F = D2 - E`
  have hE := fapprox_mul (fapprox_self D.1 d1f) (fapprox_self D.1 d1f) (1 / 2 ^ 50) (1 / 2 ^ 50)
    hD1 hD1 (1 / 2 ^ 100) (by norm_num) (by norm_num)
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hE
  have two_f : Finite (2.0 : Float).toBits := by
    rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl]; unfold CodeLib.IEEE64.Finite; decide
  have two_v : value (2.0 : Float).toBits = 2 := by
    rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl,
      ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x4000000000000000 = 2 by decide +kernel]
    norm_num
  have hE2 := fapprox_div hE (fapprox_self _ two_f) (1 / 2 ^ 100) 2
    (by
      rw [abs_mul]
      have := mul_le_mul hD1 hD1 (abs_nonneg _) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (1 / 2 ^ 50) = 1 / 2 ^ 100)])
    (by rw [two_v]; norm_num) (by norm_num) (1 / 2 ^ 100) (by norm_num) (by norm_num)
  rw [two_v] at hE2
  simp only [mul_zero, zero_div, add_zero, sub_zero] at hE2
  have hEb : |value D.1.toBits * value D.1.toBits / 2| ≤ 1 / 2 ^ 101 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul hD1 hD1 (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (1 / 2 ^ 50) / 2 = 1 / 2 ^ 101)]
  have hFa := fapprox_sub (fapprox_self D.2 d2f) hE2 (1 / 2 ^ 99) (by
      have := abs_sub (value D.2.toBits) (value D.1.toBits * value D.1.toBits / 2)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 101 + (0 + ((1 / 2 ^ 100 / 2 ^ 53 +
        1 / 2 ^ 1075) / 2 + 1 / 2 ^ 100 / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ 1 / 2 ^ 99)])
    (by norm_num)
  set F := D.2 - D.1 * D.1 / 2.0 with hFdef
  have hFe : |value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)| ≤
      1 / 2 ^ 150 := by
    have := hFa.2
    linarith [(by norm_num : (0 : ℝ) + ((1 / 2 ^ 100 / 2 ^ 53 + 1 / 2 ^ 1075) / 2 +
      1 / 2 ^ 100 / 2 ^ 53 + 1 / 2 ^ 1075) + 1 / 2 ^ 99 / 2 ^ 53 ≤ 1 / 2 ^ 150)]
  have hFb : |value F.toBits| ≤ 1 / 2 ^ 99 := by
    have h1 := abs_sub_abs_le_abs_sub (value F.toBits)
      (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)
    have h2 := abs_sub (value D.2.toBits) (value D.1.toBits * value D.1.toBits / 2)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 101 + 1 / 2 ^ 150 ≤ 1 / 2 ^ 99)]
  -- the sum of the parts
  have hl1b : |l1| ≤ |l0| / 2 ^ 51 + 1 / 2 ^ 50 := t2b
  have hl2b : |l2| ≤ |l0| / 2 ^ 100 + 1 / 2 ^ 100 := t3b
  have hl0b : |l0| ≤ 84 := by
    have h1 : Real.log vx ≤ 832 / 10 := by
      have h2 : Real.log vx ≤ Real.log (2 ^ 120) := Real.log_le_log hx0 hhi
      rw [Real.log_pow] at h2
      have h3 := Real.log_two_lt_d9
      push_cast at h2
      norm_num at h3
      linarith
    have h4 : 0 ≤ Real.log vx := Real.log_nonneg (by linarith)
    have := abs_sub_abs_le_abs_sub l0 (l0 + l1 + l2 - Real.log vx)
    rw [show l0 - (l0 + l1 + l2 - Real.log vx) = Real.log vx - l1 - l2 by ring] at this
    have h5 := abs_sub (Real.log vx - l1) l2
    have h6 := abs_sub (Real.log vx) l1
    rw [abs_of_nonneg h4] at h6
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 50 + 1 / 2 ^ 100 ≤ 1)]
  have hlim1 : |l1| < 2 ^ 898 := by linarith [(by norm_num : (84 : ℝ) / 2 ^ 51 + 1 / 2 ^ 50 < 2 ^ 898)]
  have hlimD : |value D.1.toBits| < 2 ^ 898 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 < 2 ^ 898)]
  obtain ⟨s1f, s2f, se, s2b, s1b⟩ := sumDD_spec T.2.1 T.2.2 D.1 F t2f t3f d1f hFa.1 hlim1 hlimD
    (|l2| + |value F.toBits|) le_rfl (by linarith [(by norm_num : (84 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 +
      1 / 2 ^ 99 ≤ 2 ^ 800)])
  have hL : L = sumDD T.2.1 T.2.2 D.1 F := by
    show corr T.2.1 T.2.2 xh xl = _
    unfold corr; simp only [hz, ↓reduceIte]; rfl
  rw [hL]
  set s1 := value (sumDD T.2.1 T.2.2 D.1 F).1.toBits with hs1
  set s2 := value (sumDD T.2.1 T.2.2 D.1 F).2.toBits with hs2
  have hs1b : |s1| ≤ |l0| / 2 ^ 50 + 1 / 2 ^ 48 := by
    have h1 := abs_add_le l1 (value D.1.toBits)
    have h2 := mul_le_mul_of_nonneg_right (show |l1 + value D.1.toBits| ≤ |l0| / 2 ^ 51 + 1 / 2 ^ 50 +
      1 / 2 ^ 50 by linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have h3 : (|l0| / 2 ^ 51 + 1 / 2 ^ 50 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
        |l0| / 2 ^ 50 + 1 / 2 ^ 48 := by
      have : (|l0| / 2 ^ 51 + 1 / 2 ^ 50 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 =
          |l0| * ((1 + 1 / 2 ^ 51) / 2 ^ 51) + ((1 / 2 ^ 50 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) +
            1 / 2 ^ 1073) := by ring
      rw [this]
      have h4 := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 51 ≤ 1 / 2 ^ 50)
        (abs_nonneg l0)
      linarith [(by norm_num : (1 / 2 ^ 50 + 1 / 2 ^ 50 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
        1 / 2 ^ 48), (by ring : |l0| * (1 / 2 ^ 50) = |l0| / 2 ^ 50)]
    linarith
  refine ⟨t1f, s1f, s2f, ?_, hs1b, ?_⟩
  · -- the error
    have hlog : Real.log (vx + vl) = Real.log vx + Real.log (1 + t) := by
      have h1t : (1 : ℝ) + t ≠ 0 := by
        have := (abs_le.mp ht).1
        exact ne_of_gt (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 < 1)])
      rw [← Real.log_mul hx0.ne' h1t]
      congr 1
      rw [htdef, hRdef]; field_simp
    have hlt := log_two t ht
    have hDD : |value D.1.toBits * value D.1.toBits - t ^ 2| ≤ 1 / 2 ^ 148 := by
      have h1 : |value D.1.toBits - t| ≤ 1 / 2 ^ 99 := by
        have := abs_sub (value D.1.toBits + value D.2.toBits - t) (value D.2.toBits)
        rw [show value D.1.toBits + value D.2.toBits - t - value D.2.toBits = value D.1.toBits - t by
          ring] at this
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 150 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 99)]
      rw [show value D.1.toBits * value D.1.toBits - t ^ 2 = (value D.1.toBits - t) *
        (value D.1.toBits + t) by ring, abs_mul]
      have h2 : |value D.1.toBits + t| ≤ 1 / 2 ^ 49 := by
        have := abs_add_le (value D.1.toBits) t
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 51 ≤ 1 / 2 ^ 49)]
      have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 * (1 / 2 ^ 49) = 1 / 2 ^ 148)]
    have hsum : |s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))| ≤ 1 / 2 ^ 144 := by
      have h1 : |s1| / 2 ^ 52 ≤ (84 / 2 ^ 50 + 1 / 2 ^ 48) / 2 ^ 52 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith [(by norm_num : (3 * (84 / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 2 ^ 99) + (84 / 2 ^ 50 +
        1 / 2 ^ 48) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤ (1 : ℝ) / 2 ^ 144)]
    rw [hlog]
    have hid : l0 + s1 + s2 - (Real.log vx + Real.log (1 + t)) =
        (l0 + l1 + l2 - Real.log vx) + (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))) +
        (value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)) +
        (value D.1.toBits + value D.2.toBits - t) -
        (value D.1.toBits * value D.1.toBits - t ^ 2) / 2 -
        (Real.log (1 + t) - (t - t ^ 2 / 2)) := by ring
    rw [hid]
    have a1 := abs_add_le ((l0 + l1 + l2 - Real.log vx) +
      (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))) +
      (value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)) +
      (value D.1.toBits + value D.2.toBits - t) -
      (value D.1.toBits * value D.1.toBits - t ^ 2) / 2)
      (-(Real.log (1 + t) - (t - t ^ 2 / 2)))
    rw [← sub_eq_add_neg, abs_neg] at a1
    have a2 := abs_sub ((l0 + l1 + l2 - Real.log vx) +
      (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))) +
      (value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)) +
      (value D.1.toBits + value D.2.toBits - t))
      ((value D.1.toBits * value D.1.toBits - t ^ 2) / 2)
    have a3 := abs_add_le ((l0 + l1 + l2 - Real.log vx) +
      (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))) +
      (value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2)))
      (value D.1.toBits + value D.2.toBits - t)
    have a4 := abs_add_le ((l0 + l1 + l2 - Real.log vx) +
      (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits))))
      (value F.toBits - (value D.2.toBits - value D.1.toBits * value D.1.toBits / 2))
    have a5 := abs_add_le (l0 + l1 + l2 - Real.log vx)
      (s1 + s2 - (l1 + l2 + (value D.1.toBits + value F.toBits)))
    have a6 : |(value D.1.toBits * value D.1.toBits - t ^ 2) / 2| ≤ 1 / 2 ^ 149 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 148 / 2 = 1 / 2 ^ 149)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 144 + 1 / 2 ^ 150 + 1 / 2 ^ 150 + 1 / 2 ^ 149 +
      1 / 2 ^ 152 ≤ 1 / 2 ^ 140)]
  · have h1 : |s1| / 2 ^ 51 ≤ (|l0| / 2 ^ 50 + 1 / 2 ^ 48) / 2 ^ 51 :=
      div_le_div_of_nonneg_right hs1b (by norm_num)
    have h2 : (|l2| + |value F.toBits|) * (1 + 1 / 2 ^ 51) ≤
        (|l0| / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 2 ^ 99) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h3 : (|l0| / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 2 ^ 99) * (1 + 1 / 2 ^ 51) +
        (|l0| / 2 ^ 50 + 1 / 2 ^ 48) / 2 ^ 51 + 1 / 2 ^ 1073 ≤ |l0| / 2 ^ 99 + 1 / 2 ^ 97 := by
      have : (|l0| / 2 ^ 100 + 1 / 2 ^ 100 + 1 / 2 ^ 99) * (1 + 1 / 2 ^ 51) +
          (|l0| / 2 ^ 50 + 1 / 2 ^ 48) / 2 ^ 51 + 1 / 2 ^ 1073 =
          |l0| * ((1 + 1 / 2 ^ 51) / 2 ^ 100 + 1 / 2 ^ 101) + ((1 / 2 ^ 100 + 1 / 2 ^ 99) *
            (1 + 1 / 2 ^ 51) + 1 / 2 ^ 99 + 1 / 2 ^ 1073) := by ring
      rw [this]
      have h4 := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 100 +
        1 / 2 ^ 101 ≤ 1 / 2 ^ 99) (abs_nonneg l0)
      linarith [(by norm_num : (1 / 2 ^ 100 + 1 / 2 ^ 99 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 99 +
        1 / 2 ^ 1073 ≤ 1 / 2 ^ 97), (by ring : |l0| * (1 / 2 ^ 99) = |l0| / 2 ^ 99)]
    linarith

#print axioms log_dd

end Library.Numerics.Float64.Lgamma.LgammaAsymLog
