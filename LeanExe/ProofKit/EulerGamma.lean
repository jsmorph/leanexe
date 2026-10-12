import LeanExe.ProofKit.PolyCalc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
Rational enclosures of `log 2` and of Euler's constant `γ = Real.eulerMascheroniConstant`, which
Mathlib bounds only by `1/2 < γ < 2/3`.

`log 2` comes from the series of `log (1 + x)` at `x = -1/2` with 100 terms, within `2 ^ -100`.

For `γ`, `emSeq n = H n - log n + corr (1/n)` adds to `H n - log n`, which tends to `γ`, the
Euler–Maclaurin corrections `corr t = -t/2 + t ^ 2/12 - t ^ 4/120 + t ^ 6/252 - t ^ 8/240 +
t ^ 10/132`, so `emSeq n` tends to `γ` as well.  With `t = 1/n`, the step
`emSeq (n + 1) - emSeq n = t/(1 + t) - log (1 + t) + corr (t/(1 + t)) - corr t` times
`(1 + t) ^ 10` is the polynomial `pList` minus `(1 + t) ^ 10 log (1 + t)`.  Replacing the
logarithm by 24 terms of its series leaves the polynomial `qList`, whose coefficients below
`t ^ 13` the kernel finds to be zero, and the series' remainder, below `2 t ^ 25`.  So each step
is at most `K t ^ 13` for `t ≤ 1/128`, the steps from `n = 128` on add up to at most
`K / (128 ^ 11 · 127)`, and `γ` lies within that of `emSeq 128`, whose value is rational except
for `log 128 = 7 log 2`.  The enclosure is `gammaLo ≤ γ ≤ gammaHi`, of width below `2 ^ -84`.
-/

namespace LeanExe.ProofKit.EulerGamma

open Real Finset Filter Topology PolyBound PolyChecks PolyCalc TaylorRemainder AsinRemainder

/-- `log 2` from 100 terms of `-log (1 - x)` at `x = 1/2`. -/
def logTwo : ℚ := -evalQ (log1pCoeffs 100) (-1 / 2)

theorem log_two_close : |Real.log 2 - logTwo| ≤ (1 / 2 : ℝ) ^ 100 := by
  have h := log1p_remainder (-1 / 2) (by norm_num [abs_of_neg]) 100
  have hl : Real.log (1 + -1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) + -1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [hl, show (-1 / 2 : ℝ) = ((-1 / 2 : ℚ) : ℝ) by norm_num, ← evalQ_cast] at h
  rw [logTwo, Rat.cast_neg]
  have e : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num [abs_of_neg]
  rw [show ((-1 / 2 : ℚ) : ℝ) = -1 / 2 by norm_num, e] at h
  calc |Real.log 2 - -((evalQ (log1pCoeffs 100) (-1 / 2) : ℚ) : ℝ)|
      = |-Real.log 2 - ((evalQ (log1pCoeffs 100) (-1 / 2) : ℚ) : ℝ)| := by
        rw [← abs_neg]; ring_nf
    _ ≤ (1 / 2) ^ (100 + 1) / (1 - 1 / 2) := h
    _ = (1 / 2) ^ 100 := by norm_num

/-- The Euler–Maclaurin corrections `-t/2 + t^2/12 - t^4/120 + t^6/252 - t^8/240 + t^10/132`. -/
def corr : List ℚ := [0, -1 / 2, 1 / 12, 0, -1 / 120, 0, 1 / 252, 0, -1 / 240, 0, 1 / 132]

/-- `H n - log n` with the Euler–Maclaurin corrections. -/
noncomputable def emSeq (n : ℕ) : ℝ := harmonic n - Real.log n + eval corr (1 / n)

theorem tendsto_emSeq : Tendsto emSeq atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => eval corr (1 / (n : ℝ))) atTop (𝓝 (eval corr 0)) :=
    ((continuous_eval corr).tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  have h0 : eval corr 0 = 0 := by simp [corr]
  rw [h0] at h2
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-- `(1 + t) ^ 10 (t/(1 + t) + corr (t/(1 + t)) - corr t)`. -/
def pList : List ℚ :=
  addP (addP (scaleP (1 / 2) (mulP (mono 1) (pow1 9))) (scaleP (1 / 2) (mulP (mono 1) (pow1 10))))
    (addP (scaleP (1 / 12) (mulP (mono 2) (subP (pow1 8) (pow1 10))))
      (addP (scaleP (-1 / 120) (mulP (mono 4) (subP (pow1 6) (pow1 10))))
        (addP (scaleP (1 / 252) (mulP (mono 6) (subP (pow1 4) (pow1 10))))
          (addP (scaleP (-1 / 240) (mulP (mono 8) (subP (pow1 2) (pow1 10))))
            (scaleP (1 / 132) (mulP (mono 10) (subP (pow1 0) (pow1 10))))))))

/-- `pList` minus `(1 + t) ^ 10` times 24 terms of the series of `log (1 + t)`. -/
def qList : List ℚ := subP pList (mulP (pow1 10) (log1pCoeffs 24))

/-- The bound on `qList / t ^ 13` for `t ≤ 1/128`. -/
def qBound : ℚ := 27 / 100

theorem qList_checks :
    (qList.take 13).all (fun a => decide (a = 0)) = true ∧
      absSum (1 / 128) (qList.drop 13) ≤ qBound := by
  decide +kernel

theorem pList_eq (t : ℝ) (ht : 0 < t) :
    (1 + t) ^ 10 * (t / (1 + t) + eval corr (t / (1 + t)) - eval corr t) = eval pList t := by
  simp only [pList, eval_addP, eval_scaleP, eval_mulP, eval_subP, eval_pow1, eval_mono, corr,
    eval_cons, eval_nil]
  have h1 : (1 + t) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The step of `emSeq` for `t = 1/n ≤ 1/128`. -/
theorem step_bound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 128) :
    |t / (1 + t) - Real.log (1 + t) + eval corr (t / (1 + t)) - eval corr t| ≤
      ((qBound : ℝ) + 2 / 128 ^ 12) * t ^ 13 := by
  obtain ⟨hz, hb⟩ := qList_checks
  have hq : eval qList t = t ^ 13 * eval (qList.drop 13) t := by
    rw [eval_take_drop qList 13 t, eval_eq_zero_of_all _ hz, zero_add]
  have hqb : |eval (qList.drop 13) t| ≤ qBound := by
    refine (abs_eval_le (1 / 128) (by norm_num) _ t ?_).trans (by exact_mod_cast hb)
    rw [abs_of_pos ht, show ((1 / 128 : ℚ) : ℝ) = 1 / 128 by norm_num]
    exact ht1
  have hlog := log1p_remainder t (by rw [abs_of_pos ht]; linarith) 24
  rw [abs_of_pos ht] at hlog
  have hpow : t ^ (24 + 1) / (1 - t) ≤ 2 * t ^ 25 := by
    rw [div_le_iff₀ (by linarith)]
    have e25 : t ^ (24 + 1) = t ^ 25 := by norm_num
    have h0 : 0 ≤ t ^ 25 := by positivity
    have h1 : 0 ≤ t ^ 25 * (1 - 2 * t) := mul_nonneg h0 (by linarith)
    rw [e25]
    nlinarith [h1]
  have hrel : (1 + t) ^ 10 * (t / (1 + t) - Real.log (1 + t) + eval corr (t / (1 + t)) - eval corr t) =
      eval qList t + (1 + t) ^ 10 * (eval (log1pCoeffs 24) t - Real.log (1 + t)) := by
    have := pList_eq t ht
    rw [qList, eval_subP, eval_mulP, eval_pow1]
    linear_combination this
  set D := t / (1 + t) - Real.log (1 + t) + eval corr (t / (1 + t)) - eval corr t
  have hpos : (1 : ℝ) ≤ (1 + t) ^ 10 := one_le_pow₀ (by linarith)
  have hD0 : |(1 + t) ^ 10 * D| ≤ qBound * t ^ 13 + (1 + t) ^ 10 * (2 * t ^ 25) := by
    rw [hrel, hq]
    calc |t ^ 13 * eval (qList.drop 13) t + (1 + t) ^ 10 * (eval (log1pCoeffs 24) t - Real.log (1 + t))|
        ≤ |t ^ 13 * eval (qList.drop 13) t| + |(1 + t) ^ 10 * (eval (log1pCoeffs 24) t - Real.log (1 + t))| :=
          abs_add_le _ _
      _ ≤ t ^ 13 * qBound + (1 + t) ^ 10 * (2 * t ^ 25) := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 13),
            abs_of_pos (by positivity : (0 : ℝ) < (1 + t) ^ 10), abs_sub_comm]
          gcongr
          exact hlog.trans hpow
      _ = qBound * t ^ 13 + (1 + t) ^ 10 * (2 * t ^ 25) := by ring
  have hD : |D| * (1 + t) ^ 10 ≤ qBound * t ^ 13 + (1 + t) ^ 10 * (2 * t ^ 25) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 + t) ^ 10), mul_comm] at hD0
    exact hD0
  have h25 : 2 * t ^ 25 ≤ 2 / 128 ^ 12 * t ^ 13 := by
    have : t ^ 12 ≤ (1 / 128) ^ 12 := pow_le_pow_left₀ ht.le ht1 12
    have h13 : 0 ≤ t ^ 13 := by positivity
    calc 2 * t ^ 25 = 2 * t ^ 12 * t ^ 13 := by ring
      _ ≤ 2 * (1 / 128) ^ 12 * t ^ 13 := by gcongr
      _ = 2 / 128 ^ 12 * t ^ 13 := by ring
  have hq0 : (0 : ℝ) ≤ qBound := by norm_num [qBound]
  have h1 : |D| ≤ qBound * t ^ 13 + 2 * t ^ 25 := by
    by_contra hc
    push Not at hc
    have : (qBound * t ^ 13 + 2 * t ^ 25) * (1 + t) ^ 10 < |D| * (1 + t) ^ 10 :=
      mul_lt_mul_of_pos_right hc (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hpos (by positivity : (0 : ℝ) ≤ qBound * t ^ 13)]
  linarith

theorem emSeq_step (n : ℕ) (hn : 128 ≤ n) :
    |emSeq (n + 1) - emSeq n| ≤ ((qBound : ℝ) + 2 / 128 ^ 12) * (1 / (n : ℝ)) ^ 13 := by
  have hn' : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have e : emSeq (n + 1) - emSeq n =
      (1 / n) / (1 + 1 / n) - Real.log (1 + 1 / n) + eval corr ((1 / n) / (1 + 1 / n)) -
        eval corr (1 / n) := by
    have h1 : (1 / (n : ℝ)) / (1 + 1 / n) = 1 / ((n : ℝ) + 1) := by field_simp
    have h2 : Real.log (1 + 1 / (n : ℝ)) = Real.log ((n : ℝ) + 1) - Real.log n := by
      rw [← Real.log_div (by positivity) hpos.ne']
      congr 1
      field_simp
    rw [h1, h2, emSeq, emSeq, harmonic_succ]
    push_cast
    ring
  rw [e]
  exact step_bound (1 / n) (by positivity) (by rw [div_le_div_iff₀ hpos (by norm_num)]; linarith)

/-- The bound on the steps from 128 on. -/
noncomputable def tailBound : ℝ := ((qBound : ℝ) + 2 / 128 ^ 12) / (128 ^ 11 * 127)

theorem emSeq_partial (k : ℕ) :
    |emSeq (k + 128) - emSeq 128| ≤
      ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127 - 1 / ((k : ℝ) + 127)) := by
  have hK : (0 : ℝ) ≤ (qBound : ℝ) + 2 / 128 ^ 12 := by norm_num [qBound]
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := emSeq_step (k + 128) (by omega)
    have hm : (128 : ℝ) ≤ ((k + 128 : ℕ) : ℝ) := by exact_mod_cast (by omega : 128 ≤ k + 128)
    set m : ℝ := ((k + 128 : ℕ) : ℝ) with hmdef
    have hmk : m = (k : ℝ) + 128 := by rw [hmdef]; push_cast; ring
    have hstep : (1 / m) ^ 13 ≤ 1 / 128 ^ 11 * (1 / ((k : ℝ) + 127) - 1 / ((k : ℝ) + 1 + 127)) := by
      have hm0 : (0 : ℝ) < m := by linarith
      have e1 : 1 / ((k : ℝ) + 127) - 1 / ((k : ℝ) + 1 + 127) = 1 / ((m - 1) * m) := by
        rw [hmk]
        have h1 : (0 : ℝ) < (k : ℝ) + 127 := by positivity
        have h2 : (0 : ℝ) < (k : ℝ) + 1 + 127 := by positivity
        have h3 : (0 : ℝ) < (k : ℝ) + 128 - 1 := by linarith
        field_simp
        ring
      rw [e1, one_div_pow, div_mul_div_comm, one_mul]
      apply one_div_le_one_div_of_le (by nlinarith)
      have h11 : (128 : ℝ) ^ 11 ≤ m ^ 11 := pow_le_pow_left₀ (by norm_num) hm 11
      have hm1 : (m - 1) * m ≤ m ^ 2 := by nlinarith
      calc (128 : ℝ) ^ 11 * ((m - 1) * m) ≤ m ^ 11 * m ^ 2 := by
            apply mul_le_mul h11 hm1 (by nlinarith) (by positivity)
        _ = m ^ 13 := by ring
    have e : k + 1 + 128 = (k + 128) + 1 := by ring
    rw [e]
    calc |emSeq (k + 128 + 1) - emSeq 128|
        ≤ |emSeq (k + 128 + 1) - emSeq (k + 128)| + |emSeq (k + 128) - emSeq 128| := by
          have := abs_add_le (emSeq (k + 128 + 1) - emSeq (k + 128)) (emSeq (k + 128) - emSeq 128)
          rwa [sub_add_sub_cancel] at this
      _ ≤ ((qBound : ℝ) + 2 / 128 ^ 12) * (1 / m) ^ 13 +
          ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127 - 1 / ((k : ℝ) + 127)) := add_le_add hs ih
      _ ≤ ((qBound : ℝ) + 2 / 128 ^ 12) * (1 / 128 ^ 11 * (1 / ((k : ℝ) + 127) - 1 / ((k : ℝ) + 1 + 127))) +
          ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127 - 1 / ((k : ℝ) + 127)) := by gcongr
      _ = ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127 - 1 / (((k + 1 : ℕ) : ℝ) + 127)) := by
          push_cast; ring

theorem gamma_close_emSeq : |eulerMascheroniConstant - emSeq 128| ≤ tailBound := by
  have ht : Tendsto (fun k => |emSeq (k + 128) - emSeq 128|) atTop
      (𝓝 |eulerMascheroniConstant - emSeq 128|) :=
    (((tendsto_add_atTop_iff_nat 128).mpr tendsto_emSeq).sub_const _).abs
  refine le_of_tendsto' ht fun k => (emSeq_partial k).trans ?_
  have hK : (0 : ℝ) ≤ (qBound : ℝ) + 2 / 128 ^ 12 := by norm_num [qBound]
  have : 0 ≤ 1 / ((k : ℝ) + 127) := by positivity
  rw [tailBound]
  calc ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127 - 1 / ((k : ℝ) + 127))
      ≤ ((qBound : ℝ) + 2 / 128 ^ 12) / 128 ^ 11 * (1 / 127) := by gcongr; linarith
    _ = ((qBound : ℝ) + 2 / 128 ^ 12) / (128 ^ 11 * 127) := by ring

/-- `H 128 + corr (1/128) - 7 logTwo`, the center of the enclosure. -/
def gammaMid : ℚ := harmonic 128 + evalQ corr (1 / 128) - 7 * logTwo

/-- The radius of the enclosure. -/
def gammaRad : ℚ := (qBound + 2 / 128 ^ 12) / (128 ^ 11 * 127) + 7 / 2 ^ 100

theorem gamma_close : |eulerMascheroniConstant - gammaMid| ≤ gammaRad := by
  have h1 := gamma_close_emSeq
  have h2 := log_two_close
  have e : emSeq 128 = ((harmonic 128 + evalQ corr (1 / 128) : ℚ) : ℝ) - 7 * Real.log 2 := by
    rw [emSeq, Rat.cast_add, evalQ_cast]
    have : Real.log ((128 : ℕ) : ℝ) = 7 * Real.log 2 := by
      rw [show ((128 : ℕ) : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    rw [this]
    push_cast
    ring
  rw [e] at h1
  rw [gammaMid, gammaRad]
  push_cast
  rw [tailBound] at h1
  push_cast at h1
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem gamma_rad_small : gammaRad < 1 / 2 ^ 84 := by
  rw [gammaRad, qBound]
  norm_num

#print axioms log_two_close
#print axioms gamma_close
#print axioms gamma_rad_small

end LeanExe.ProofKit.EulerGamma
