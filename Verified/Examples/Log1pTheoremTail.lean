import Verified.Examples.Log1pTheoremK0
import LeanExe.ProofKit.F64HalfUlp
import LeanExe.ProofKit.F64WithinSelf
import LeanExe.ProofKit.F64Near
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
`Log1p.log1pTail f c k hu` for `k ≠ 0`, against `y = K log 2 + log (1 + f) + log (1 + t)`, where
`K` is the value of `kd`, `c` approximates `t` within `et`, and `A = kd ln2Hi` is exact.  The
general path computes `A - G` with `G = (f²/2 - (P + (kd ln2Lo + c))) - f`; the exact value of
`A - G` is `K (ln2Hi + ln2Lo) + t + 2 s + s R(s)`, which differs from `y` by `|K| 2 ^ -81`, the
kernel's error, and `2 t²`.  The sums round within half a spacing of their binades
(`F64HalfUlp`).  For `hu = 0` the polynomial is `f²/2 (1 - 2f/3)`, and for `f = 0` the result is
`A + (c + kd ln2Lo)`.  Each path ends with `F64RoundNearest`, whose criterion charges nothing for
the last rounding.  The `_near` theorems bound the exact value of the last operation (`F64Near.Near`), and the
step theorems follow from them; `tail_big_near` gives the bound for `K ≥ 50`.
-/

namespace Verified.Examples.Log1pTheoremTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest F64HalfUlp PolyBound Log1pTheoremBranches
  Log1pTheoremCore Log1pTheoremConst Log1pTheoremK0

set_option exponentiation.threshold 4096

/-- `log (1 + t)` within `2 t²` of `t`. -/
theorem log_near_t (t : ℝ) (ht : |t| ≤ 1 / 2) : |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add] at h
  rw [abs_neg] at h
  have h1 : |t| ^ (1 + 1) / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by linarith), show |t| ^ (1 + 1) = t ^ 2 by rw [sq_abs]]
    nlinarith [sq_nonneg t]
  rw [show Real.log (1 + t) - t = -t + Real.log (1 + t) by ring, add_comm 1 t]
  rw [add_comm 1 t] at h
  linarith

theorem abs_log_t (t : ℝ) (ht : |t| ≤ 1 / 4) : |Real.log (1 + t)| ≤ 2 * |t| := by
  have h := log_near_t t (by linarith)
  have h2 : t ^ 2 ≤ |t| / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg t]
  have := abs_sub_abs_le_abs_sub (Real.log (1 + t)) t
  have := abs_nonneg t
  linarith

/-- `K ln2Hi + K ln2Lo` against `K log 2`. -/
theorem ln2_part (K : ℝ) :
    |K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2)| ≤ |K| / 2 ^ 81 := by
  rw [abs_mul]
  have := ln2_close
  calc |K| * |value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2| ≤
      |K| * (1 / 2 ^ 81) := mul_le_mul_of_nonneg_left this (abs_nonneg K)
    _ = |K| / 2 ^ 81 := by ring

theorem lo_approx : FApprox ln2LoF (value 0x3DEA39EF35793C76) 0 :=
  fapprox_ofBits _ (by unfold CodeLib.IEEE64.Finite; decide +kernel)

theorem lo_bound : |value 0x3DEA39EF35793C76| ≤ 191 / 10 ^ 12 :=
  le_trans (abs_value_le _ ((191 / 10 ^ 12 : ℚ)) (by decide +kernel)) (by norm_num)

/-- `kd ln2Lo + c`. -/
theorem c_approx (k : UInt64) (c : Float) (K t et KM T : ℝ) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hKM : |K| ≤ KM) (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000) (hT : T ≤ 1)
    (het : et ≤ 1) :
    FApprox (LogCoreBits.kdOf k * ln2LoF + c) (K * value 0x3DEA39EF35793C76 + t)
      (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et +
        (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
          2 ^ 53) := by
  have hB := fapprox_mul hkd lo_approx KM (191 / 10 ^ 12) hKM lo_bound (KM * (191 / 10 ^ 12))
    (by linarith) (by nlinarith)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hB
  refine fapprox_add hB hc _ ?_ (by nlinarith)
  have h1 : |K * value 0x3DEA39EF35793C76| ≤ KM * (191 / 10 ^ 12) := by
    rw [abs_mul]
    exact mul_le_mul hKM lo_bound (abs_nonneg _) ((abs_nonneg K).trans hKM)
  have := abs_add_le (K * value 0x3DEA39EF35793C76) t
  linarith

/-- The common last step: `A - G` against `y` when `A` is exact. -/
theorem sub_close (A G : Float) (vA vG eG y d : ℝ) (hA : FApprox A vA 0) (hG : FApprox G vG eG)
    (hd : |vA - vG - y| ≤ d) : 0 + eG + |vA - vG - y| ≤ eG + d := by
  linarith

/-- The general path's `G` and its exact value's distance from `y`. -/
theorem tail_s_G (f c : Float) (k : UInt64) (K t et KM T F0 eh MP eP Lm : ℝ) (gD gE gG : ℕ)
    (hf : Finite f.toBits) (hv : -1 < value f.toBits) (hσ1 : |value f.toBits| ≤ F0)
    (hqA : FApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits) eh)
    (hPA : FApprox (POf f) (Pstar (value f.toBits)) eP) (hPM : |Pstar (value f.toBits)| ≤ MP)
    (hkd : FApprox (LogCoreBits.kdOf k) K 0) (hKM : |K| ≤ KM) (hc : FApprox c t et) (ht : |t| ≤ T)
    (hKM1 : KM ≤ 2000) (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hlog : |Real.log (1 + value f.toBits)| ≤ Lm)
    (hs : |sStar (value f.toBits)| ≤ 1716 / 10000)
    (hgD : gD ≤ 1023) (hgE : gE ≤ 1023) (hgG : gG ≤ 1023)
    (hSD : MP + (KM * (191 / 10 ^ 12) + T) + (eP + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 +
      et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
        2 ^ 53)) < 2 ^ (53 + gD) / 2 ^ 1074)
    (hSE : F0 * F0 / 2 + (MP + (KM * (191 / 10 ^ 12) + T)) + (eh + (eP +
      (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T +
        (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074)) <
      2 ^ (53 + gE) / 2 ^ 1074)
    (hSG : Lm + 1716 / 10000 * ((93 / 128) / 2 ^ 58) + (KM * (191 / 10 ^ 12) + T) +
      (eh + (eP + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) +
        T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53) +
          2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074) < 2 ^ (53 + gG) / 2 ^ 1074) :
    FApprox ((hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f)
      (value f.toBits / 2 * value f.toBits - (Pstar (value f.toBits) +
        (K * value 0x3DEA39EF35793C76 + t)) - value f.toBits)
      (eh + (eP + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) +
        T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53) +
          2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074 + 0 + 2 ^ gG / 2 / 2 ^ 1074) ∧
    |K * value 0x3FE62E42FEE00000 - (value f.toBits / 2 * value f.toBits -
        (Pstar (value f.toBits) + (K * value 0x3DEA39EF35793C76 + t)) - value f.toBits) -
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t))| ≤
      |K| / 2 ^ 81 + |sStar (value f.toBits)| * ((93 / 128) / 2 ^ 58) + 2 * t ^ 2 := by
  set v := value f.toBits with hvdef
  have hC := c_approx k c K t et KM T hkd hKM hc ht hKM1 (by linarith) het
  have hCM : |K * value 0x3DEA39EF35793C76 + t| ≤ KM * (191 / 10 ^ 12) + T := by
    have h1 : |K * value 0x3DEA39EF35793C76| ≤ KM * (191 / 10 ^ 12) := by
      rw [abs_mul]
      exact mul_le_mul hKM lo_bound (abs_nonneg _) ((abs_nonneg K).trans hKM)
    have := abs_add_le (K * value 0x3DEA39EF35793C76) t
    linarith
  have hD := fapprox_add_half hPA hC gD hgD (by
    have := abs_add_le (Pstar v) (K * value 0x3DEA39EF35793C76 + t)
    linarith)
  have hvv : |v / 2 * v| ≤ F0 * F0 / 2 := by
    rw [abs_mul, abs_div, abs_two]
    have := mul_le_mul hσ1 hσ1 (abs_nonneg v) ((abs_nonneg v).trans hσ1)
    nlinarith
  have hE := fapprox_sub_half hqA hD gE hgE (by
    have := abs_sub (v / 2 * v) (Pstar v + (K * value 0x3DEA39EF35793C76 + t))
    have := abs_add_le (Pstar v) (K * value 0x3DEA39EF35793C76 + t)
    linarith)
  have hid := tail_identity v (by linarith)
  have hker := log_kernel v hv hs
  have hk2 : |2 * sStar v + sStar v * polyR (sStar v)| ≤
      Lm + 1716 / 10000 * ((93 / 128) / 2 ^ 58) := by
    have h1 : |sStar v| * ((93 / 128) / 2 ^ 58) ≤ 1716 / 10000 * ((93 / 128) / 2 ^ 58) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have := abs_sub_abs_le_abs_sub (2 * sStar v + sStar v * polyR (sStar v))
      (Real.log (1 + v))
    rw [abs_sub_comm] at hker
    linarith
  have hGv : v / 2 * v - (Pstar v + (K * value 0x3DEA39EF35793C76 + t)) - v =
      -(2 * sStar v + sStar v * polyR (sStar v)) - (K * value 0x3DEA39EF35793C76 + t) := by
    rw [← hid]
    ring
  have hG := fapprox_sub_half hE (approx_self f.toBits hf) gG hgG (by
    rw [hGv]
    have := abs_sub (-(2 * sStar v + sStar v * polyR (sStar v)))
      (K * value 0x3DEA39EF35793C76 + t)
    rw [abs_neg] at this
    linarith)
  refine ⟨hG, ?_⟩
  rw [hGv]
  have hl2 := ln2_part K
  have hlt := log_near_t t (by linarith)
  have heq : K * value 0x3FE62E42FEE00000 - (-(2 * sStar v + sStar v * polyR (sStar v)) -
      (K * value 0x3DEA39EF35793C76 + t)) - (K * Real.log 2 + Real.log (1 + v) +
        Real.log (1 + t)) =
      K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2) +
        ((2 * sStar v + sStar v * polyR (sStar v)) - Real.log (1 + v)) -
          (Real.log (1 + t) - t) := by ring
  rw [heq]
  have h3 := abs_sub (K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2) +
    ((2 * sStar v + sStar v * polyR (sStar v)) - Real.log (1 + v))) (Real.log (1 + t) - t)
  have h4 := abs_add_le (K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 -
    Real.log 2)) ((2 * sStar v + sStar v * polyR (sStar v)) - Real.log (1 + v))
  rw [abs_sub_comm] at hker
  linarith

theorem fsapprox_abs {x : Float} {v s M e S : ℝ} (h : FSApprox x v s M e) (hs : s ≤ S) :
    FApprox x v (e * S) ∧ |v| ≤ M * S :=
  ⟨h.approx.mono (mul_le_mul_of_nonneg_left hs h.e_nonneg),
    h.2.2.1.trans (mul_le_mul_of_nonneg_left hs h.M_nonneg)⟩

theorem log_range (v : ℝ) (h1 : -2929 / 10000 ≤ v) (h2 : v ≤ 41422 / 100000) :
    |Real.log (1 + v)| ≤ 34659 / 100000 := by
  have hl := log_ge (-2929 / 10000) (-34659 / 100000) 8 (by norm_num) (by norm_num)
    (by decide +kernel)
  have hu := log_le (41422 / 100000) (34659 / 100000) 8 (by norm_num) (by norm_num)
    (by decide +kernel)
  push_cast at hl hu
  rw [abs_le]
  constructor
  · have h3 : Real.log (1 + -2929 / 10000) ≤ Real.log (1 + v) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  · have h3 : Real.log (1 + v) ≤ Real.log (1 + 41422 / 100000) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith

theorem ln2_bounds : 6931471803 / 10 ^ 10 < Real.log 2 ∧ Real.log 2 < 6931471808 / 10 ^ 10 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- An upper bound of `|y|` that keeps every rounded value of the tail finite. -/
theorem y_lt (K v t KM Lm : ℝ) (hKM : |K| ≤ KM) (hKM1 : KM ≤ 2000)
    (hlog : |Real.log (1 + v)| ≤ Lm) (hLm : Lm ≤ 1) (ht : |t| ≤ 1 / 4) :
    |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| < 2 ^ 1022 := by
  have hl2 := ln2_bounds
  have hlt := abs_log_t t ht
  have h1 : |K * Real.log 2| ≤ 2000 * (6931471808 / 10 ^ 10) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
    exact mul_le_mul (hKM.trans hKM1) hl2.2.le (by linarith) (by norm_num)
  have h2 := abs_add_le (K * Real.log 2 + Real.log (1 + v)) (Real.log (1 + t))
  have h3 := abs_add_le (K * Real.log 2) (Real.log (1 + v))
  have h4 : (2000 * (6931471808 / 10 ^ 10) + 1 + 1 : ℝ) < 2 ^ 1022 := by norm_num
  linarith

/-- A lower bound of `|y|` from `|K| ≥ KL`. -/
theorem y_ge (K v t KL T V : ℝ) (hKL0 : 0 ≤ KL) (hKL : KL ≤ |K|) (ht : |t| ≤ T) (hT : T ≤ 1 / 4)
    (hlv : |Real.log (1 + v)| ≤ V) :
    KL * (6931471803 / 10 ^ 10) - 2 * T - V ≤
      |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
  have hl2b := ln2_bounds
  have hlt2 := abs_log_t t (ht.trans hT)
  have h1 : KL * (6931471803 / 10 ^ 10) ≤ |K * Real.log 2| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
    exact mul_le_mul hKL hl2b.1.le (by norm_num) (hKL0.trans hKL)
  have h2 := abs_sub_abs_le_abs_sub (K * Real.log 2) (-(Real.log (1 + v) + Real.log (1 + t)))
  rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h2
  have h3 := abs_add_le (Real.log (1 + v)) (Real.log (1 + t))
  linarith

/-- The general path's error: the exact value of the last difference lies within `E` of `y`, for
`E < Y ≤ |y|`. -/
theorem finish_s_near (f c : Float) (k : UInt64) (K t et KM T F0 Mh eh MP eP Lm E Y : ℝ)
    (gD gE gG : ℕ) (hf : Finite f.toBits) (hv : -1 < value f.toBits)
    (hσ1 : |value f.toBits| ≤ F0)
    (hq : FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) Mh eh)
    (hP : FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) MP eP)
    (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000) (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hlog : |Real.log (1 + value f.toBits)| ≤ Lm) (hLm : Lm ≤ 1)
    (hs : |sStar (value f.toBits)| ≤ 1716 / 10000)
    (hgD : gD ≤ 1023) (hgE : gE ≤ 1023) (hgG : gG ≤ 1023)
    (hSD : MP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) + T) + (eP * (F0 * (F0 * F0)) +
      (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T +
        (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53)) < 2 ^ (53 + gD) / 2 ^ 1074)
    (hSE : F0 * F0 / 2 + (MP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) + T)) +
      (eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 +
        et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
          2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074)) < 2 ^ (53 + gE) / 2 ^ 1074)
    (hSG : Lm + 1716 / 10000 * ((93 / 128) / 2 ^ 58) + (KM * (191 / 10 ^ 12) + T) +
      (eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 +
        et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
          2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074) < 2 ^ (53 + gG) / 2 ^ 1074)
    (hE : eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 +
      1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 +
        1 / 2 ^ 1075 + et)) / 2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074 + 0 +
          2 ^ gG / 2 / 2 ^ 1074 + (KM / 2 ^ 81 + 1716 / 10000 * ((93 / 128) / 2 ^ 58) +
            2 * T ^ 2) ≤ E)
    (hY : Y ≤ |K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)|)
    (hEY : E < Y) :
    F64Near.Near
      (LogCoreBits.kdOf k * ln2HiF - ((hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f)).toBits
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)) E := by
  set v := value f.toBits with hvdef
  have hσ0 := abs_nonneg v
  have hF0 : 0 ≤ F0 := hσ0.trans hσ1
  have hq2 := fsapprox_abs hq (mul_le_mul hσ1 hσ1 hσ0 hF0)
  have hP3 := fsapprox_abs hP (mul_le_mul hσ1 (mul_le_mul hσ1 hσ1 hσ0 hF0)
    (mul_nonneg hσ0 hσ0) hF0)
  obtain ⟨hG, hd⟩ := tail_s_G f c k K t et KM T F0 (eh * (F0 * F0)) (MP * (F0 * (F0 * F0)))
    (eP * (F0 * (F0 * F0))) Lm gD gE gG hf hv hσ1 hq2.1 hP3.1 hP3.2 hkd hKM hc ht hKM1 hT het
    hlog hs hgD hgE hgG hSD hSE hSG
  have hsk : |sStar v| * ((93 / 128) / 2 ^ 58) ≤ 1716 / 10000 * ((93 / 128) / 2 ^ 58) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  have hK81 : |K| / 2 ^ 81 ≤ KM / 2 ^ 81 := div_le_div_of_nonneg_right hKM (by positivity)
  have ht2 : 2 * t ^ 2 ≤ 2 * T ^ 2 := by
    have : t ^ 2 ≤ T ^ 2 := by
      rw [← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    linarith
  have hyt := y_lt K v t KM Lm hKM hKM1 hlog hLm (ht.trans hT)
  exact F64Near.near_sub hA hG _ E ((sub_close _ _ _ _ _ _ _ hA hG hd).trans (by linarith))
    (by linarith) (by linarith [(by norm_num : (2 : ℝ) ^ 1022 + 2 ^ 1022 = 2 ^ 1023)])

/-- The general path within one step, for a criterion binade `a` below `Y ≤ |y|`. -/
theorem finish_s (f c : Float) (k : UInt64) (K t et KM T F0 Mh eh MP eP Lm E Y : ℝ)
    (gD gE gG a : ℕ) (hf : Finite f.toBits) (hv : -1 < value f.toBits)
    (hσ1 : |value f.toBits| ≤ F0)
    (hq : FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) Mh eh)
    (hP : FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) MP eP)
    (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000) (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hlog : |Real.log (1 + value f.toBits)| ≤ Lm) (hLm : Lm ≤ 1)
    (hs : |sStar (value f.toBits)| ≤ 1716 / 10000)
    (hgD : gD ≤ 1023) (hgE : gE ≤ 1023) (hgG : gG ≤ 1023)
    (hSD : MP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) + T) + (eP * (F0 * (F0 * F0)) +
      (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T +
        (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53)) < 2 ^ (53 + gD) / 2 ^ 1074)
    (hSE : F0 * F0 / 2 + (MP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) + T)) +
      (eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 +
        et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
          2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074)) < 2 ^ (53 + gE) / 2 ^ 1074)
    (hSG : Lm + 1716 / 10000 * ((93 / 128) / 2 ^ 58) + (KM * (191 / 10 ^ 12) + T) +
      (eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 +
        et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) /
          2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074) < 2 ^ (53 + gG) / 2 ^ 1074)
    (hE : eh * (F0 * F0) + (eP * (F0 * (F0 * F0)) + (KM * (191 / 10 ^ 12) / 2 ^ 53 +
      1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T + (KM * (191 / 10 ^ 12) / 2 ^ 53 +
        1 / 2 ^ 1075 + et)) / 2 ^ 53) + 2 ^ gD / 2 / 2 ^ 1074) + 2 ^ gE / 2 / 2 ^ 1074 + 0 +
          2 ^ gG / 2 / 2 ^ 1074 + (KM / 2 ^ 81 + 1716 / 10000 * ((93 / 128) / 2 ^ 58) +
            2 * T ^ 2) ≤ E)
    (ha1 : 1 ≤ a) (ha : a < 2047) (hEa : E < (2 : ℝ) ^ (a - 1) / 2 ^ 1074)
    (hY : Y ≤ |K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)|)
    (hYa : value (UInt64.ofNat (a * 2 ^ 52)) + E ≤ Y) :
    F64SignedRounding.WithinSteps 1
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t))
      (LogCoreBits.kdOf k * ln2HiF - ((hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f)).toBits := by
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value a ha1 (by omega)]
    positivity
  refine (finish_s_near f c k K t et KM T F0 Mh eh MP eP Lm E Y gD gE gG hf hv hσ1 hq hP hkd hA hKM
    hc ht hKM1 hT het hlog hLm hs hgD hgE hgG hSD hSE hSG hE hY (by linarith)).within_one a ha1 ha
    (hYa.trans hY) hEa ?_
  exact (y_lt K _ t KM Lm hKM hKM1 hlog hLm (ht.trans hT)).trans (by norm_num)

/-- `f = 0`: the error of `A + (c + kd ln2Lo)`. -/
theorem finish_z_near (c : Float) (k : UInt64) (v K t et KM KL T E : ℝ) (hv0 : v = 0)
    (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hKL0 : 0 ≤ KL) (hKL : KL ≤ |K|) (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000)
    (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hE : et + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075) + (T + KM * (191 / 10 ^ 12) +
      (et + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075))) / 2 ^ 53 +
        (KM / 2 ^ 81 + 2 * T ^ 2) ≤ E)
    (hEY : E < KL * (6931471803 / 10 ^ 10) - 2 * T) :
    F64Near.Near (LogCoreBits.kdOf k * ln2HiF + (c + LogCoreBits.kdOf k * ln2LoF)).toBits
      (K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)) E := by
  subst hv0
  have hB := fapprox_mul hkd lo_approx KM (191 / 10 ^ 12) hKM lo_bound (KM * (191 / 10 ^ 12))
    (by linarith) (by nlinarith)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hB
  have hlo : |K * value 0x3DEA39EF35793C76| ≤ KM * (191 / 10 ^ 12) := by
    rw [abs_mul]
    exact mul_le_mul hKM lo_bound (abs_nonneg _) ((abs_nonneg K).trans hKM)
  have hC := fapprox_add hc hB (T + KM * (191 / 10 ^ 12) +
    (et + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075))) (by
      have := abs_add_le t (K * value 0x3DEA39EF35793C76)
      linarith) (by nlinarith)
  have hl2 := ln2_part K
  have hlt := log_near_t t (by linarith)
  have hK81 : |K| / 2 ^ 81 ≤ KM / 2 ^ 81 := div_le_div_of_nonneg_right hKM (by positivity)
  have ht2 : 2 * t ^ 2 ≤ 2 * T ^ 2 := by
    have : t ^ 2 ≤ T ^ 2 := by
      rw [← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    linarith
  rw [add_zero, Real.log_one, add_zero]
  have hd : |K * value 0x3FE62E42FEE00000 + (t + K * value 0x3DEA39EF35793C76) -
      (K * Real.log 2 + Real.log (1 + t))| ≤ |K| / 2 ^ 81 + 2 * t ^ 2 := by
    have heq : K * value 0x3FE62E42FEE00000 + (t + K * value 0x3DEA39EF35793C76) -
        (K * Real.log 2 + Real.log (1 + t)) =
        K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2) -
          (Real.log (1 + t) - t) := by ring
    rw [heq]
    have := abs_sub (K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2))
      (Real.log (1 + t) - t)
    linarith
  have hl2b := ln2_bounds
  have hlt2 := abs_log_t t (by linarith)
  have hy : KL * (6931471803 / 10 ^ 10) - 2 * T ≤ |K * Real.log 2 + Real.log (1 + t)| := by
    have h1 : KL * (6931471803 / 10 ^ 10) ≤ |K * Real.log 2| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
      exact mul_le_mul hKL hl2b.1.le (by norm_num) (hKL0.trans hKL)
    have := abs_sub_abs_le_abs_sub (K * Real.log 2) (-Real.log (1 + t))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  have h1 : |K * Real.log 2| ≤ 2000 * (6931471808 / 10 ^ 10) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
    exact mul_le_mul (hKM.trans hKM1) hl2b.2.le (by linarith) (by norm_num)
  have h2 := abs_add_le (K * Real.log 2) (Real.log (1 + t))
  have h4 : (2000 * (6931471808 / 10 ^ 10) + 1 : ℝ) < 2 ^ 1022 := by norm_num
  exact F64Near.near_add hA hC _ E (by linarith) (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1022 + 2 ^ 1022 = 2 ^ 1023)])

/-- `f = 0`: `A + (c + kd ln2Lo)`. -/
theorem finish_z (c : Float) (k : UInt64) (v K t et KM KL T E : ℝ) (a : ℕ) (hv0 : v = 0)
    (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hKL0 : 0 ≤ KL) (hKL : KL ≤ |K|) (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000)
    (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hE : et + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075) + (T + KM * (191 / 10 ^ 12) +
      (et + (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075))) / 2 ^ 53 +
        (KM / 2 ^ 81 + 2 * T ^ 2) ≤ E)
    (ha1 : 1 ≤ a) (ha : a < 2047) (hEa : E < (2 : ℝ) ^ (a - 1) / 2 ^ 1074)
    (hYa : value (UInt64.ofNat (a * 2 ^ 52)) + E ≤ KL * (6931471803 / 10 ^ 10) - 2 * T) :
    F64SignedRounding.WithinSteps 1 (K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t))
      (LogCoreBits.kdOf k * ln2HiF + (c + LogCoreBits.kdOf k * ln2LoF)).toBits := by
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value a ha1 (by omega)]
    positivity
  have hlv : |Real.log (1 + v)| ≤ 0 := by rw [hv0, add_zero, Real.log_one, abs_zero]
  have hy := y_ge K v t KL T 0 hKL0 hKL ht hT hlv
  have hEY : E < KL * (6931471803 / 10 ^ 10) - 2 * T := by
    generalize value (UInt64.ofNat (a * 2 ^ 52)) = B at hB0 hYa
    linarith
  have hBy : value (UInt64.ofNat (a * 2 ^ 52)) + E ≤
      |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
    generalize value (UInt64.ofNat (a * 2 ^ 52)) = B at hYa ⊢
    linarith
  refine (finish_z_near c k v K t et KM KL T E hv0 hkd hA hKM hKL0 hKL hc ht hKM1 hT het hE
    hEY).within_one a ha1 ha hBy hEa ?_
  exact (y_lt K v t KM 0 hKM hKM1 hlv (by norm_num) (ht.trans hT)).trans (by norm_num)

theorem c23_close : |value 0x3FE5555555555555 - 2 / 3| ≤ 1 / 2 ^ 53 := by
  rw [← ratOfWord_cast, show ratOfWord 0x3FE5555555555555 = 6004799503160661 / 9007199254740992 by
    decide +kernel, abs_le]
  constructor <;> norm_num

/-- `log (1 + v)` against its cubic Taylor polynomial. -/
theorem log_cubic (v : ℝ) (hv : |v| ≤ 1 / 2) :
    |Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3)| ≤ 2 * v ^ 4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -v) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at h
  rw [abs_neg] at h
  have h1 : |v| ^ (3 + 1) / (1 - |v|) ≤ 2 * v ^ 4 := by
    rw [div_le_iff₀ (by linarith), show |v| ^ (3 + 1) = v ^ 4 by
      rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, ← sq_abs v]; ring]
    nlinarith [pow_two_nonneg (v ^ 2)]
  have heq : Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3) =
      (0 + (-v) ^ (0 + 1) / ((0 : ℕ) + 1) + (-v) ^ (1 + 1) / ((1 : ℕ) + 1) +
        (-v) ^ (2 + 1) / ((2 : ℕ) + 1)) + Real.log (1 + v) := by
    push_cast
    ring
  rw [heq]
  rw [add_comm 1 v] at h ⊢
  linarith

/-- `hu = 0`, `f ≠ 0`: the error of `A - ((f²/2 (1 - 2f/3) - (kd ln2Lo + c)) - f)`. -/
theorem finish_q_near (f c : Float) (k : UInt64) (K t et KM KL T E : ℝ)
    (hf : Finite f.toBits) (hv1 : |value f.toBits| ≤ 1 / 2 ^ 19)
    (hv0 : 1 / 2 ^ 1000 ≤ |value f.toBits|) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hKL0 : 0 ≤ KL) (hKL : KL ≤ |K|) (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000)
    (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hE : 1 / 2 ^ 60 + et + (KM * (191 / 10 ^ 12) + T + et) / 2 ^ 50 + KM / 2 ^ 81 +
      2 * T ^ 2 ≤ E)
    (hEY : E < KL * (6931471803 / 10 ^ 10) - 2 * T - 2 / 2 ^ 19) :
    F64Near.Near
      (LogCoreBits.kdOf k * ln2HiF - ((RqOf f - (LogCoreBits.kdOf k * ln2LoF + c)) - f)).toBits
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)) E := by
  set v := value f.toBits with hvdef
  have hKM0 : 0 ≤ KM := (abs_nonneg K).trans hKM
  have het0 : 0 ≤ et := (abs_nonneg _).trans hc.2
  have hT0 : 0 ≤ T := (abs_nonneg t).trans ht
  have hfa : FApprox f v 0 := approx_self f.toBits hf
  have hh : FApprox (0.5 * f) (v / 2) 0 := by
    obtain ⟨h1, h2⟩ := half_float f hf hv0
    exact ⟨h1, by rw [h2, sub_self, abs_zero]⟩
  have hv2 : |v / 2| ≤ 1 / 2 ^ 20 := by
    rw [abs_div, abs_two]
    have : (1 : ℝ) / 2 ^ 20 = 1 / 2 ^ 19 / 2 := by norm_num
    linarith
  have hq := Approx.mono (fapprox_mul hh hfa (1 / 2 ^ 20) (1 / 2 ^ 19) hv2 hv1 (1 / 2 ^ 39)
    (by norm_num) (by norm_num)) (e' := 1 / 2 ^ 91) (by norm_num)
  have hcw := fapprox_ofBits 0x3FE5555555555555 (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have hc23 := c23_close
  have hcM : |value 0x3FE5555555555555| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value 0x3FE5555555555555) (2 / 3)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at this
    have : (1 : ℝ) / 2 ^ 53 ≤ 1 / 3 := by norm_num
    linarith
  have hw := Approx.mono (fapprox_mul hcw hfa 1 (1 / 2 ^ 19) hcM hv1 (1 / 2 ^ 19)
    (by norm_num) (by norm_num)) (e' := 1 / 2 ^ 71) (by norm_num)
  have h1 : FApprox (1.0 : Float) 1 0 := by
    unfold FApprox
    rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [show value 0x3FF0000000000000 = 1 by
      rw [← ratOfWord_cast, show ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]; norm_num]
    norm_num
  have hwv : |value 0x3FE5555555555555 * v| ≤ 1 / 2 ^ 19 := by
    rw [abs_mul]
    have := mul_le_mul hcM hv1 (abs_nonneg v) (by norm_num)
    linarith
  have hom := Approx.mono (fapprox_sub h1 hw (1 + 1 / 2 ^ 19 + 1 / 2 ^ 71) (by
    have := abs_sub (1 : ℝ) (value 0x3FE5555555555555 * v)
    rw [abs_one] at this
    linarith) (by norm_num)) (e' := 1 / 2 ^ 52) (by norm_num)
  have hvq : |v / 2 * v| ≤ 1 / 2 ^ 39 := by
    rw [abs_mul]
    have := mul_le_mul hv2 hv1 (abs_nonneg v) (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 20 * (1 / 2 ^ 19) = 1 / 2 ^ 39 := by norm_num
    linarith
  have hom1 : |1 - value 0x3FE5555555555555 * v| ≤ 2 := by
    have := abs_sub (1 : ℝ) (value 0x3FE5555555555555 * v)
    rw [abs_one] at this
    have : (1 : ℝ) / 2 ^ 19 ≤ 1 := by norm_num
    linarith
  have hR := Approx.mono (fapprox_mul hq hom (1 / 2 ^ 39) 2 hvq hom1 (1 / 2 ^ 37) (by norm_num)
    (by norm_num)) (e' := 1 / 2 ^ 88) (by norm_num)
  have hC := c_approx k c K t et KM T hkd hKM hc ht hKM1 (by linarith) het
  have hlo : |K * value 0x3DEA39EF35793C76| ≤ KM * (191 / 10 ^ 12) := by
    rw [abs_mul]
    exact mul_le_mul hKM lo_bound (abs_nonneg _) hKM0
  have hCM : |K * value 0x3DEA39EF35793C76 + t| ≤ KM * (191 / 10 ^ 12) + T := by
    have := abs_add_le (K * value 0x3DEA39EF35793C76) t
    linarith
  have hRM : |v / 2 * v * (1 - value 0x3FE5555555555555 * v)| ≤ 2 / 2 ^ 39 := by
    rw [abs_mul]
    have := mul_le_mul hvq hom1 (abs_nonneg _) (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 39 * 2 = 2 / 2 ^ 39 := by ring
    linarith
  set eC := KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et + (KM * (191 / 10 ^ 12) + T +
    (KM * (191 / 10 ^ 12) / 2 ^ 53 + 1 / 2 ^ 1075 + et)) / 2 ^ 53 with heC
  have heC1 : eC ≤ 2 := by rw [heC]; linarith
  have hE2 := fapprox_sub hR hC (2 / 2 ^ 39 + (KM * (191 / 10 ^ 12) + T) + (1 / 2 ^ 88 + eC))
    (by
      have := abs_sub (v / 2 * v * (1 - value 0x3FE5555555555555 * v))
        (K * value 0x3DEA39EF35793C76 + t)
      linarith) (by linarith)
  set eE := 1 / 2 ^ 88 + eC + (2 / 2 ^ 39 + (KM * (191 / 10 ^ 12) + T) + (1 / 2 ^ 88 + eC)) /
    2 ^ 53 with heE
  have heE1 : eE ≤ 3 := by rw [heE]; linarith
  have hG := fapprox_sub hE2 hfa (2 / 2 ^ 39 + (KM * (191 / 10 ^ 12) + T) + eE + 1 / 2 ^ 19)
    (by
      have h3 := abs_sub (v / 2 * v * (1 - value 0x3FE5555555555555 * v) -
        (K * value 0x3DEA39EF35793C76 + t)) v
      have h4 := abs_sub (v / 2 * v * (1 - value 0x3FE5555555555555 * v))
        (K * value 0x3DEA39EF35793C76 + t)
      linarith) (by linarith)
  -- the exact value's distance from `y`
  have hcub := log_cubic v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 2)])
  have hv3 : |v| ^ 3 ≤ 1 / 2 ^ 57 := by
    have := pow_le_pow_left₀ (abs_nonneg v) hv1 3
    linarith [show ((1 : ℝ) / 2 ^ 19) ^ 3 = 1 / 2 ^ 57 by norm_num]
  have hv4 : v ^ 4 ≤ 1 / 2 ^ 76 := by
    have := pow_le_pow_left₀ (abs_nonneg v) hv1 4
    rw [show |v| ^ 4 = v ^ 4 by rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, ← sq_abs v]; ring] at this
    linarith [show ((1 : ℝ) / 2 ^ 19) ^ 4 = 1 / 2 ^ 76 by norm_num]
  have hc3 : |(value 0x3FE5555555555555 / 2 - 1 / 3) * v ^ 3| ≤ 1 / 2 ^ 54 * (1 / 2 ^ 57) := by
    rw [abs_mul, abs_pow]
    apply mul_le_mul _ hv3 (by positivity) (by norm_num)
    rw [show value 0x3FE5555555555555 / 2 - 1 / 3 = (value 0x3FE5555555555555 - 2 / 3) / 2 by
      ring, abs_div, abs_two]
    have : (1 : ℝ) / 2 ^ 54 = 1 / 2 ^ 53 / 2 := by norm_num
    linarith
  have hpoly : |v - v / 2 * v * (1 - value 0x3FE5555555555555 * v) - Real.log (1 + v)| ≤
      2 / 2 ^ 76 + 1 / 2 ^ 54 * (1 / 2 ^ 57) := by
    have heq : v - v / 2 * v * (1 - value 0x3FE5555555555555 * v) - Real.log (1 + v) =
        (value 0x3FE5555555555555 / 2 - 1 / 3) * v ^ 3 -
          (Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3)) := by ring
    rw [heq]
    have := abs_sub ((value 0x3FE5555555555555 / 2 - 1 / 3) * v ^ 3)
      (Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3))
    linarith
  have hl2 := ln2_part K
  have hlt := log_near_t t (by linarith)
  have hK81 : |K| / 2 ^ 81 ≤ KM / 2 ^ 81 := div_le_div_of_nonneg_right hKM (by positivity)
  have ht2 : 2 * t ^ 2 ≤ 2 * T ^ 2 := by
    have : t ^ 2 ≤ T ^ 2 := by
      rw [← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    linarith
  have hd : |K * value 0x3FE62E42FEE00000 - (v / 2 * v * (1 - value 0x3FE5555555555555 * v) -
      (K * value 0x3DEA39EF35793C76 + t) - v) - (K * Real.log 2 + Real.log (1 + v) +
        Real.log (1 + t))| ≤ |K| / 2 ^ 81 + (2 / 2 ^ 76 + 1 / 2 ^ 54 * (1 / 2 ^ 57)) +
          2 * t ^ 2 := by
    have heq : K * value 0x3FE62E42FEE00000 - (v / 2 * v * (1 - value 0x3FE5555555555555 * v) -
        (K * value 0x3DEA39EF35793C76 + t) - v) - (K * Real.log 2 + Real.log (1 + v) +
          Real.log (1 + t)) =
        K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2) +
          (v - v / 2 * v * (1 - value 0x3FE5555555555555 * v) - Real.log (1 + v)) -
            (Real.log (1 + t) - t) := by ring
    rw [heq]
    have h3 := abs_sub (K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 -
      Real.log 2) + (v - v / 2 * v * (1 - value 0x3FE5555555555555 * v) - Real.log (1 + v)))
      (Real.log (1 + t) - t)
    have h4 := abs_add_le (K * (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 -
      Real.log 2)) (v - v / 2 * v * (1 - value 0x3FE5555555555555 * v) - Real.log (1 + v))
    linarith
  have hl2b := ln2_bounds
  have hlt2 := abs_log_t t (by linarith)
  have hlv := abs_log_t v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 4)])
  have hy : KL * (6931471803 / 10 ^ 10) - 2 * T - 2 / 2 ^ 19 ≤
      |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
    have h1 : KL * (6931471803 / 10 ^ 10) ≤ |K * Real.log 2| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
      exact mul_le_mul hKL hl2b.1.le (by norm_num) (hKL0.trans hKL)
    have h2 := abs_sub_abs_le_abs_sub (K * Real.log 2)
      (-(Real.log (1 + v) + Real.log (1 + t)))
    rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h2
    have h3 := abs_add_le (Real.log (1 + v)) (Real.log (1 + t))
    linarith
  unfold RqOf hfsqOf
  have hyt := y_lt K v t KM (2 / 2 ^ 19) hKM hKM1 (by linarith) (by norm_num) (ht.trans hT)
  refine F64Near.near_sub hA hG _ E ?_ (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1022 + 2 ^ 1022 = 2 ^ 1023)])
  have := sub_close _ _ _ _ _ _ _ hA hG hd
  rw [heE, heC] at this
  linarith

/-- `hu = 0`, `f ≠ 0`: `A - ((f²/2 (1 - 2f/3) - (kd ln2Lo + c)) - f)`.  The rounding errors
other than `c`'s and those proportional to `kd ln2Lo + c` stay below `2 ^ -60`. -/
theorem finish_q (f c : Float) (k : UInt64) (K t et KM KL T E : ℝ) (a : ℕ)
    (hf : Finite f.toBits) (hv1 : |value f.toBits| ≤ 1 / 2 ^ 19)
    (hv0 : 1 / 2 ^ 1000 ≤ |value f.toBits|) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0) (hKM : |K| ≤ KM)
    (hKL0 : 0 ≤ KL) (hKL : KL ≤ |K|) (hc : FApprox c t et) (ht : |t| ≤ T) (hKM1 : KM ≤ 2000)
    (hT : T ≤ 1 / 4) (het : et ≤ 1)
    (hE : 1 / 2 ^ 60 + et + (KM * (191 / 10 ^ 12) + T + et) / 2 ^ 50 + KM / 2 ^ 81 +
      2 * T ^ 2 ≤ E)
    (ha1 : 1 ≤ a) (ha : a < 2047) (hEa : E < (2 : ℝ) ^ (a - 1) / 2 ^ 1074)
    (hYa : value (UInt64.ofNat (a * 2 ^ 52)) + E ≤
      KL * (6931471803 / 10 ^ 10) - 2 * T - 2 / 2 ^ 19) :
    F64SignedRounding.WithinSteps 1
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t))
      (LogCoreBits.kdOf k * ln2HiF - ((RqOf f - (LogCoreBits.kdOf k * ln2LoF + c)) - f)).toBits := by
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value a ha1 (by omega)]
    positivity
  have hlv : |Real.log (1 + value f.toBits)| ≤ 2 / 2 ^ 19 := by
    have := abs_log_t (value f.toBits) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 4)])
    linarith
  have hy := y_ge K (value f.toBits) t KL T (2 / 2 ^ 19) hKL0 hKL ht hT hlv
  have hEY : E < KL * (6931471803 / 10 ^ 10) - 2 * T - 2 / 2 ^ 19 := by
    generalize value (UInt64.ofNat (a * 2 ^ 52)) = B at hB0 hYa
    linarith
  have hBy : value (UInt64.ofNat (a * 2 ^ 52)) + E ≤
      |K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)| := by
    generalize value (UInt64.ofNat (a * 2 ^ 52)) = B at hYa ⊢
    linarith
  refine (finish_q_near f c k K t et KM KL T E hf hv1 hv0 hkd hA hKM hKL0 hKL hc ht hKM1 hT het hE
    hEY).within_one a ha1 ha hBy hEa ?_
  exact (y_lt K _ t KM (2 / 2 ^ 19) hKM hKM1 hlv (by norm_num) (ht.trans hT)).trans (by norm_num)

set_option maxHeartbeats 1000000 in
/-- `K = -1` and `f ≥ 0.285`: `|G| ≥ 1/4`, so `A - G` is exact, and the error stays below one and
a half spacings of `[1/4, 1/2)`. -/
theorem finish_d (f c : Float) (k : UInt64) (t et : ℝ) (hf : Finite f.toBits)
    (hv1 : 285 / 1000 ≤ value f.toBits) (hv2 : value f.toBits ≤ 41422 / 100000)
    (hkd : FApprox (LogCoreBits.kdOf k) (-1) 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (-1 * value 0x3FE62E42FEE00000) 0)
    (hc : FApprox c t et) (ht : |t| ≤ 1 / 2 ^ 52) (het : et ≤ 1 / 2 ^ 60) :
    F64SignedRounding.WithinSteps 1
      (-1 * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t))
      (LogCoreBits.kdOf k * ln2HiF - ((hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f)).toBits := by
  set v := value f.toBits with hvdef
  have hσ : |v| = v := abs_of_pos (by linarith)
  have hc3 := core_P3 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hσ1 : |v| ≤ 41422 / 100000 := by rw [hσ]; exact hv2
  have hσ0 := abs_nonneg v
  have hq2 := fsapprox_abs hc3.1 (mul_le_mul hσ1 hσ1 hσ0 (by norm_num))
  have hP3 := fsapprox_abs hc3.2 (mul_le_mul hσ1 (mul_le_mul hσ1 hσ1 hσ0 (by norm_num))
    (mul_nonneg hσ0 hσ0) (by norm_num))
  have hlog := log_range v (by linarith) hv2
  have hs := sstar_le v (by linarith) hv2
  have hKM : |(-1 : ℝ)| ≤ 1 := by norm_num
  obtain ⟨hG, hd⟩ := tail_s_G f c k (-1) t et 1 (1 / 2 ^ 52) (41422 / 100000) _ _ _ _
    1016 1018 1020 hf (by linarith) hσ1 hq2.1 hP3.1 hP3.2 hkd hKM hc ht (by norm_num)
    (by norm_num) (by linarith) hlog hs (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith)
  -- `|G| ≥ 1/4`
  have hl0 := log_ge (285 / 1000) (2507 / 10000) 6 (by norm_num) (by norm_num) (by decide +kernel)
  have hlv : (2507 / 10000 : ℝ) ≤ Real.log (1 + v) := by
    push_cast at hl0
    exact hl0.trans (Real.log_le_log (by norm_num) (by linarith))
  have hid := tail_identity v (by linarith)
  have hker := log_kernel v (by linarith) hs
  have hlo : |(-1) * value 0x3DEA39EF35793C76| ≤ 191 / 10 ^ 12 := by
    rw [abs_mul]
    have := lo_bound
    norm_num at this ⊢
    exact this
  have hGv : v / 2 * v - (Pstar v + (-1 * value 0x3DEA39EF35793C76 + t)) - v =
      -(2 * sStar v + sStar v * polyR (sStar v)) - (-1 * value 0x3DEA39EF35793C76 + t) := by
    rw [← hid]
    ring
  have hsk : |sStar v| * ((93 / 128) / 2 ^ 58) ≤ 1716 / 10000 * ((93 / 128) / 2 ^ 58) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  have hGa := hG.2
  rw [hGv] at hGa
  have hk1 := abs_le.mp hker
  have hk1_l := hk1.1
  have hk1_r := hk1.2
  have hta := abs_le.mp ht
  have hta_l := hta.1
  have hta_r := hta.2
  have hloa := abs_le.mp hlo
  have hloa_l := hloa.1
  have hloa_r := hloa.2
  have hGabs := abs_le.mp hGa
  have hGabs_l := hGabs.1
  have hGabs_r := hGabs.2
  have hG4 : 1 / 4 ≤ |value ((hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f).toBits| := by
    rw [abs_of_neg (by norm_num at hGabs ⊢; nlinarith)]
    norm_num at hGabs ⊢
    nlinarith
  -- `A - G` is exact
  set Af := LogCoreBits.kdOf k * ln2HiF with hAf
  set Gf := (hfsqOf f - (POf f + (LogCoreBits.kdOf k * ln2LoF + c))) - f with hGf
  have hAv : value Af.toBits = -value 0x3FE62E42FEE00000 := by
    have := hA.2
    rw [sub_eq_zero.mp (abs_nonpos_iff.mp this)]
    ring
  have hhi : Wasm.IEEE64.scaledValue 0x3FE62E42FEE00000 =
      (0x162E42FEE00000 * 2 : ℤ) * 2 ^ 1020 := by decide +kernel
  have hsA : Wasm.IEEE64.scaledValue Af.toBits = -((0x162E42FEE00000 * 2 : ℤ) * 2 ^ 1020) := by
    have h1 : (Wasm.IEEE64.scaledValue Af.toBits : ℝ) =
        -(Wasm.IEEE64.scaledValue 0x3FE62E42FEE00000 : ℝ) := by
      have := hAv
      simp only [value] at this
      field_simp at this
      linarith
    rw [← hhi]
    exact_mod_cast h1
  have hGm : 2 ^ (52 + 1020) ≤ Wasm.IEEE64.scaledMagnitude Gf.toBits := by
    have h1 := abs_value Gf.toBits
    rw [h1] at hG4
    have : (2 : ℝ) ^ (52 + 1020) ≤ Wasm.IEEE64.scaledMagnitude Gf.toBits := by
      rw [le_div_iff₀ (by positivity)] at hG4
      norm_num at hG4 ⊢
      linarith
    exact_mod_cast this
  obtain ⟨g, hg⟩ := F64NearestSum.magnitude_dvd Gf.toBits 1020 hGm
  have hsG : ∃ g' : ℤ, Wasm.IEEE64.scaledValue Gf.toBits = g' * 2 ^ 1020 := by
    simp only [Wasm.IEEE64.scaledValue]
    split
    · exact ⟨-(g : ℤ), by rw [hg]; push_cast; ring⟩
    · exact ⟨g, by rw [hg]; push_cast; ring⟩
  obtain ⟨g', hg'⟩ := hsG
  set z : ℤ := -(0x162E42FEE00000 * 2 : ℤ) - g' with hz
  have hdiff : Wasm.IEEE64.scaledValue Af.toBits - Wasm.IEEE64.scaledValue Gf.toBits =
      z * 2 ^ 1020 := by rw [hsA, hg', hz]; ring
  -- `|A - G| ≤ 1/2`
  have hl2b := ln2_bounds
  have htl := abs_log_t t (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1 / 4)])
  have hS : |value Af.toBits - value Gf.toBits| ≤ 1 / 2 := by
    have hhiv : value 0x3FE62E42FEE00000 = 2977044471 / 4294967296 := by
      rw [← ratOfWord_cast, show ratOfWord 0x3FE62E42FEE00000 = 2977044471 / 4294967296 by
        decide +kernel]
      norm_num
    have hlog' := (abs_le.mp hlog).2
    rw [hAv, hhiv]
    rw [abs_le]
    constructor <;> linarith
  have hzb : z.natAbs ≤ 2 ^ 53 := by
    have h1 : |((z : ℤ) : ℝ)| * 2 ^ 1020 / 2 ^ 1074 ≤ 1 / 2 := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1020), ← abs_mul]
      have h5 : ((z : ℤ) : ℝ) * 2 ^ 1020 =
          (Wasm.IEEE64.scaledValue Af.toBits : ℝ) - Wasm.IEEE64.scaledValue Gf.toBits := by
        exact_mod_cast hdiff.symm
      rw [h5]
      have h6 := hS
      simp only [value] at h6
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)] at h6
      exact h6
    have h2 : |((z : ℤ) : ℝ)| ≤ 2 ^ 53 := by
      rw [mul_div_assoc, show (2 : ℝ) ^ 1020 / 2 ^ 1074 = 1 / 2 ^ 54 by norm_num] at h1
      have : |((z : ℤ) : ℝ)| * (1 / 2 ^ 54) ≤ 1 / 2 := h1
      nlinarith
    have h3 : (z.natAbs : ℝ) ≤ 2 ^ 53 := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h2
    exact_mod_cast h3
  have hex := F64GridExact.sub_grid_exact Af.toBits Gf.toBits hA.1 hG.1 z 1020 hdiff hzb
    (by norm_num)
  have hval : value (Af - Gf).toBits = value Af.toBits - value Gf.toBits := by
    rw [F64Bits.toBits_sub]
    simp only [value]
    rw [hex.2]
    push_cast
    ring
  -- the criterion of one and a half spacings
  have hE : |value (Af - Gf).toBits - (-1 * Real.log 2 + Real.log (1 + v) + Real.log (1 + t))| ≤
      (6 / 5) / 2 ^ 54 := by
    rw [hval]
    have hcl := fapprox_diff_close hA hG (-1 * Real.log 2 + Real.log (1 + v) + Real.log (1 + t))
    rw [← hvdef] at hd hcl
    have hsk2 : |sStar v| * ((93 / 128) / 2 ^ 58) ≤ 1716 / 10000 * ((93 / 128) / 2 ^ 58) := hsk
    have ht2 : 2 * t ^ 2 ≤ 2 * (1 / 2 ^ 52) ^ 2 := by
      have : t ^ 2 ≤ (1 / 2 ^ 52) ^ 2 := by
        rw [← sq_abs t]
        exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      linarith
    linarith
  have hy : value (UInt64.ofNat (1021 * 2 ^ 52)) + (6 / 5) / 2 ^ 54 ≤
      |-1 * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
    rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]
    obtain ⟨hab_l, hab_r⟩ := abs_le.mp htl
    have hlu := (abs_le.mp hlog).2
    rw [abs_of_neg (by linarith)]
    norm_num
    linarith
  rw [hAf, hGf] at hex hE
  exact F64WithinSelf.abs_finish _ (by rw [F64Bits.toBits_sub]; exact hex.1) _ _ 1021
    (by norm_num) (by norm_num) hE hy (by norm_num)

theorem zero_bits_value : value (0.0 : Float).toBits = 0 := by
  rw [show (0.0 : Float).toBits = 0 from rfl]
  simp [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
    Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]

theorem beq_zero_iff (f : Float) (hf : Finite f.toBits) :
    (f == 0.0) = true ↔ value f.toBits = 0 := by
  rw [F64UpperWord.float_beq_iff f 0.0 hf (by
    rw [show (0.0 : Float).toBits = 0 from rfl]; unfold CodeLib.IEEE64.Finite; decide),
    zero_bits_value]

set_option maxHeartbeats 2000000 in
/-- `log1pTail` for `k ≠ 0` within one step, for a correction `c` within `2 ^ -60` of `t`. -/
theorem tail_main (f c : Float) (k hu : UInt64) (K t et : ℝ) (hf : Finite f.toBits)
    (hv1 : -2929 / 10000 ≤ value f.toBits) (hv2 : value f.toBits ≤ 41422 / 100000)
    (hhu1 : (hu == 0) = false → 1 / 2 ^ 30 ≤ |value f.toBits|)
    (hhu2 : (hu == 0) = true → |value f.toBits| ≤ 1 / 2 ^ 19)
    (hvz : value f.toBits ≠ 0 → 1 / 2 ^ 1000 ≤ |value f.toBits|)
    (hk : (k == 0) = false) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0)
    (hK : K = 1 ∨ K = -1 ∨ (2 ≤ |K| ∧ |K| ≤ 1100))
    (hc : FApprox c t et) (ht : |t| ≤ 1 / 2 ^ 52) (het : et ≤ 1 / 2 ^ 60) :
    F64SignedRounding.WithinSteps 1
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t))
      (Log1p.log1pTail f c k hu).toBits := by
  set v := value f.toBits with hvdef
  have hKM : |K| ≤ 1100 := by
    rcases hK with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · exact h.2
  have hK1 : 1 ≤ |K| := by
    rcases hK with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · linarith [h.1]
  have hl2b := ln2_bounds
  have hlog := log_range v hv1 hv2
  have htl := abs_log_t t (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1 / 4)])
  have htl' := abs_le.mp htl
  have hlv := abs_le.mp hlog
  have hlv_l := hlv.1
  have hlv_r := hlv.2
  have hta := abs_le.mp ht
  have hta_l := hta.1
  have hta_r := hta.2
  cases hhu : (hu == 0)
  · -- the general path
    rw [Log1pTheoremBranches.tail_s_eq f c k hu hk hhu]
    have hσ0 := hhu1 hhu
    have hs := sstar_le v (by linarith) hv2
    by_cases hfar : 2 ≤ |K| ∨ (K = 1 ∧ -175 / 1000 ≤ v) ∨ (K = -1 ∧ v ≤ 2125 / 10000)
    · have hc4 := core_P4 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
      have hY : (5004 / 10000 : ℝ) ≤ |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
        rcases hfar with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h3 : 2 * (6931471803 / 10 ^ 10) ≤ |K * Real.log 2| := by
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
            exact mul_le_mul h hl2b.1.le (by norm_num) (by linarith)
          have h4 := abs_sub_abs_le_abs_sub (K * Real.log 2)
            (-(Real.log (1 + v) + Real.log (1 + t)))
          rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h4
          have h5 := abs_add_le (Real.log (1 + v)) (Real.log (1 + t))
          have : |t| ≤ 1 / 2 ^ 52 := ht
          norm_num at this
          linarith
        · have hl := log_ge (-175 / 1000) (-19238 / 100000) 8 (by norm_num) (by norm_num)
            (by decide +kernel)
          push_cast at hl
          have h3 : Real.log (1 + -175 / 1000) ≤ Real.log (1 + v) :=
            Real.log_le_log (by norm_num) (by linarith)
          have hl' : -19238 / 100000 ≤ Real.log (1 + v) := by linarith
          rw [h1, one_mul, abs_of_pos (by linarith)]
          linarith
        · have hl := log_le (2125 / 10000) (19269 / 100000) 8 (by norm_num) (by norm_num)
            (by decide +kernel)
          push_cast at hl
          have h3 : Real.log (1 + v) ≤ Real.log (1 + 2125 / 10000) :=
            Real.log_le_log (by linarith) (by linarith)
          have hl' : Real.log (1 + v) ≤ 19269 / 100000 := by linarith
          rw [h1, abs_of_neg (by linarith)]
          linarith
      refine finish_s f c k K t et 1100 (1 / 2 ^ 52) (41422 / 100000) _ _ _ _ (34659 / 100000)
        ((3 / 2) / 2 ^ 54) (5004 / 10000) 1016 1018 1020 1022 hf (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩) hc4.1 hc4.2 hkd hA hKM hc ht (by norm_num)
        (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) hlog (by norm_num) hs
        (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num)
        (by norm_num) hY ?_
      all_goals first
        | (norm_num; done)
        | (rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
        | (norm_num at het ⊢; linarith)
    · push_neg at hfar
      obtain ⟨hK2, hfar1, hfar2⟩ := hfar
      rcases hK with hK1' | hK1' | hK1'
      · -- `K = 1`, `f < -0.175`
        have hv3 : v < -175 / 1000 := hfar1 hK1'
        have hc1 := core_P1 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
        have hY : (3465 / 10000 : ℝ) ≤ |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
          rw [hK1', one_mul, abs_of_pos (by linarith)]
          linarith
        refine finish_s f c k K t et 1 (1 / 2 ^ 52) (293 / 1000) _ _ _ _ (34659 / 100000)
          ((95 / 100) / 2 ^ 54) (3465 / 10000) 1015 1017 1020 1021 hf (by linarith)
          (abs_le.mpr ⟨by linarith, by linarith⟩) hc1.1 hc1.2 hkd hA (by rw [hK1']; norm_num) hc
          ht (by norm_num) (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
          hlog (by norm_num) hs (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
          (by norm_num) (by norm_num) (by norm_num) hY ?_
        all_goals first
          | (norm_num; done)
          | (rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
          | (norm_num at het ⊢; linarith)
      · -- `K = -1`, `f > 0.2125`
        have hv3 : 2125 / 10000 < v := hfar2 hK1'
        by_cases hv4 : v < 285 / 1000
        · have hc2 := core_P2 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
          have hl := log_le (285 / 1000) (25076 / 100000) 8 (by norm_num) (by norm_num)
            (by decide +kernel)
          push_cast at hl
          have h3 : Real.log (1 + v) ≤ Real.log (1 + 285 / 1000) :=
            Real.log_le_log (by linarith) (by linarith)
          have hl' : Real.log (1 + v) ≤ 25076 / 100000 := by linarith
          have hY : (3465 / 10000 : ℝ) ≤
              |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
            rw [hK1', abs_of_neg (by linarith)]
            linarith
          refine finish_s f c k K t et 1 (1 / 2 ^ 52) (285 / 1000) _ _ _ _ (25076 / 100000)
            ((90 / 100) / 2 ^ 54) (3465 / 10000) 1014 1017 1020 1021 hf (by linarith)
            (abs_le.mpr ⟨by linarith, by linarith⟩) hc2.1 hc2.2 hkd hA (by rw [hK1']; norm_num)
            hc ht (by norm_num) (by norm_num)
            (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
            (by rw [abs_le]; constructor <;>
              linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + v)]) (by norm_num) hs
            (by norm_num)
            (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num) hY ?_
          all_goals first
            | (norm_num; done)
            | (rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
            | (norm_num at het ⊢; linarith)
        · push_neg at hv4
          rw [hK1'] at hkd hA ⊢
          exact finish_d f c k t et hf hv4 hv2 hkd hA hc ht het
      · exact absurd hK1'.1 (not_le.mpr hK2)
  · -- `hu = 0`
    have hσ := hhu2 hhu
    cases hz : (f == 0.0)
    · rw [Log1pTheoremBranches.tail_q_eq f c k hu hk hhu hz]
      have hv0 : v ≠ 0 := by
        intro h
        have := (beq_zero_iff f hf).mpr h
        rw [hz] at this
        exact Bool.false_ne_true this
      refine finish_q f c k K t et 1100 1 (1 / 2 ^ 52) ((3 / 2) / 2 ^ 54) 1022 hf hσ (hvz hv0) hkd
        hA hKM (by norm_num) hK1 hc ht (by norm_num) (by norm_num)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) ?_ (by norm_num) (by norm_num)
        (by norm_num) ?_
      · norm_num at het ⊢
        linarith
      · rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
        norm_num
    · have hv0 : v = 0 := (beq_zero_iff f hf).mp hz
      rw [Log1pTheoremBranches.tail_z_eq f c k hu hk hhu hz]
      refine finish_z c k v K t et 1100 1 (1 / 2 ^ 52) ((3 / 2) / 2 ^ 54) 1022 hv0 hkd hA hKM
        (by norm_num) hK1 hc ht (by norm_num) (by norm_num)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) ?_ (by norm_num) (by norm_num)
        (by norm_num) ?_
      · norm_num at het ⊢
        linarith
      · rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
        norm_num

set_option maxHeartbeats 2000000 in
/-- `log1pTail` for `K ≥ 50`, where `y` exceeds 32, for a correction within `2 ^ -52` of `t`. -/
theorem tail_big_near (f c : Float) (k hu : UInt64) (K t et : ℝ) (hf : Finite f.toBits)
    (hv1 : -2929 / 10000 ≤ value f.toBits) (hv2 : value f.toBits ≤ 41422 / 100000)
    (hhu1 : (hu == 0) = false → 1 / 2 ^ 30 ≤ |value f.toBits|)
    (hhu2 : (hu == 0) = true → |value f.toBits| ≤ 1 / 2 ^ 19)
    (hvz : value f.toBits ≠ 0 → 1 / 2 ^ 1000 ≤ |value f.toBits|)
    (hk : (k == 0) = false) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0)
    (hK1 : 50 ≤ K) (hK2 : K ≤ 1100)
    (hc : FApprox c t et) (ht : |t| ≤ 1 / 2 ^ 53) (het : et ≤ 1 / 2 ^ 52) :
    F64Near.Near (Log1p.log1pTail f c k hu).toBits
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)) (6 / 2 ^ 54) := by
  set v := value f.toBits with hvdef
  have hKa : |K| = K := abs_of_pos (by linarith)
  have hKM : |K| ≤ 1100 := by rw [hKa]; exact hK2
  have hKL : 50 ≤ |K| := by rw [hKa]; exact hK1
  have ht' : |t| ≤ 1 / 2 ^ 52 := ht.trans (by norm_num)
  have hl2b := ln2_bounds
  have hlog := log_range v hv1 hv2
  have htl := abs_log_t t (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 ≤ 1 / 4)])
  cases hhu : (hu == 0)
  · rw [Log1pTheoremBranches.tail_s_eq f c k hu hk hhu]
    have hσ0 := hhu1 hhu
    have hs := sstar_le v (by linarith) hv2
    have hc4 := core_P4 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
    have hY : (34 : ℝ) ≤ |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
      have h3 : 50 * (6931471803 / 10 ^ 10) ≤ K * Real.log 2 :=
        mul_le_mul hK1 hl2b.1.le (by norm_num) (by linarith)
      have h4 := (abs_le.mp hlog).1
      have h5 := (abs_le.mp htl).1
      rw [abs_of_pos (by linarith)]
      linarith
    refine finish_s_near f c k K t et 1100 (1 / 2 ^ 52) (41422 / 100000) _ _ _ _ (34659 / 100000)
      (6 / 2 ^ 54) 34 1016 1018 1020 hf (by linarith)
      (abs_le.mpr ⟨by linarith, by linarith⟩) hc4.1 hc4.2 hkd hA hKM hc ht' (by norm_num)
      (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1)]) hlog (by norm_num) hs
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ hY (by norm_num)
    all_goals first
      | (norm_num; done)
      | (norm_num at het ⊢; linarith)
  · have hσ := hhu2 hhu
    cases hz : (f == 0.0)
    · rw [Log1pTheoremBranches.tail_q_eq f c k hu hk hhu hz]
      have hv0 : v ≠ 0 := by
        intro h
        have := (beq_zero_iff f hf).mpr h
        rw [hz] at this
        exact Bool.false_ne_true this
      refine finish_q_near f c k K t et 1100 50 (1 / 2 ^ 52) (6 / 2 ^ 54) hf hσ (hvz hv0) hkd
        hA hKM (by norm_num) hKL hc ht' (by norm_num) (by norm_num)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1)]) ?_ (by norm_num)
      norm_num at het ⊢
      linarith
    · have hv0 : v = 0 := (beq_zero_iff f hf).mp hz
      rw [Log1pTheoremBranches.tail_z_eq f c k hu hk hhu hz]
      refine finish_z_near c k v K t et 1100 50 (1 / 2 ^ 52) (6 / 2 ^ 54) hv0 hkd hA hKM
        (by norm_num) hKL hc ht' (by norm_num) (by norm_num)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1)]) ?_ (by norm_num)
      norm_num at het ⊢
      linarith

end Verified.Examples.Log1pTheoremTail
