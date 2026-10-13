import LeanExe.ProofKit.PolyCalculus
import LeanExe.ProofKit.PolyCalc
import LeanExe.ProofKit.RealErf
import LeanExe.ProofKit.BesselConstants

/-!
Bounds on `erf` near a rational center `c` from its series at 0, for the certificates of the
polynomials of `Erfc.erfc`.  `ser n` is the partial sum `x Σ (-1)^k x^(2k)/(k! (2k + 1))` of `n`
terms, so that `erf x` lies within `scale |x|^(2n+1)/(n! (2n+1))` of `scale (ser n) (x)`
(`RealErf.erf_series`).  Shifted to `c` and cut after degree `J`, its low part is compared with a
polynomial `P` by `PolyBound.check`, its high part is bounded by `PolyBound.absSum`, and `2/√π` lies
within `2 ^ -160` of the middle of `[sLo, sHi]` by Machin's formula for `π`
(`BesselConstants.pi_encl`).  `row_sound` collects these into `|P z - erf (c + z)| ≤ rowBound` for
`|z| ≤ r`.  `erfcLo` is a lower bound on `erfc x` from the same series.
-/

namespace Verified.Examples.ErfcSeries

open LeanExe.ProofKit PolyBound PolyChecks PolyCalculus PolyCalc RealErf BesselConstants

set_option exponentiation.threshold 4096

/-- A lower bound on `2/√π`. -/
def sLo : ℚ := 1649128000240172121335468122222580532118151184855 / 2 ^ 160

/-- An upper bound on `2/√π`. -/
def sHi : ℚ := 1649128000240172121335468122222580532118151184856 / 2 ^ 160

theorem pi_le : Real.pi ≤ ((piMid + piRad : ℚ) : ℝ) := by
  have h := pi_encl
  unfold Encl at h
  push_cast
  linarith [(abs_le.mp h).2]

theorem pi_ge : ((piMid - piRad : ℚ) : ℝ) ≤ Real.pi := by
  have h := pi_encl
  unfold Encl at h
  push_cast
  linarith [(abs_le.mp h).1]

theorem scale_lo : (sLo : ℝ) ≤ scale := by
  have hs : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hc : sLo ^ 2 * (piMid + piRad) ≤ 4 := by
    decide +kernel
  have hc' : ((sLo : ℚ) : ℝ) ^ 2 * ((piMid + piRad : ℚ) : ℝ) ≤ 4 := by exact_mod_cast hc
  have h0 : (0 : ℝ) ≤ sLo := by
    have : (0 : ℚ) ≤ sLo := by unfold sLo; norm_num
    exact_mod_cast this
  unfold scale
  rw [le_div_iff₀ hs]
  have h1 : ((sLo : ℚ) : ℝ) ^ 2 * Real.pi ≤ 4 :=
    le_trans (mul_le_mul_of_nonneg_left pi_le (by positivity)) hc'
  nlinarith [sq_nonneg ((sLo : ℝ) * √Real.pi - 2), mul_nonneg h0 hs.le]

theorem scale_hi : scale ≤ (sHi : ℝ) := by
  have hs : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hc : 4 ≤ sHi ^ 2 * (piMid - piRad) := by
    decide +kernel
  have hc' : (4 : ℝ) ≤ ((sHi : ℚ) : ℝ) ^ 2 * ((piMid - piRad : ℚ) : ℝ) := by exact_mod_cast hc
  have h0 : (0 : ℝ) ≤ sHi := by
    have : (0 : ℚ) ≤ sHi := by unfold sHi; norm_num
    exact_mod_cast this
  unfold scale
  rw [div_le_iff₀ hs]
  have h1 : 4 ≤ ((sHi : ℚ) : ℝ) ^ 2 * Real.pi :=
    le_trans hc' (mul_le_mul_of_nonneg_left pi_ge (by positivity))
  nlinarith [sq_nonneg ((sHi : ℝ) * √Real.pi - 2), mul_nonneg h0 hs.le]

/-- The partial sum of `n` terms of `∫₀ˣ exp (-t²) dt` as a polynomial in `x`. -/
def ser (n : ℕ) : List ℚ := oddP (erfCoeffs n)

theorem eval_take_drop (k : ℕ) : ∀ (q : List ℚ) (z : ℝ),
    eval q z = eval (q.take k) z + z ^ k * eval (q.drop k) z := by
  induction k with
  | zero => intro q z; simp
  | succ k ih =>
    intro q z
    cases q with
    | nil => simp
    | cons a q =>
      simp only [List.take_succ_cons, List.drop_succ_cons, eval_cons]
      rw [ih q z]
      ring

/-- The remainder bound of the series of `n` terms at `|x| ≤ X`. -/
def serRem (n : ℕ) (X : ℚ) : ℚ := X ^ (2 * n + 1) / ((n.factorial * (2 * n + 1) : ℕ) : ℚ)

theorem erf_ser (n : ℕ) (x : ℝ) (X : ℚ) (hX : |x| ≤ X) :
    |erf x - scale * eval (ser n) x| ≤ scale * (serRem n X : ℝ) := by
  have h := erf_series n x
  rw [ser, eval_oddP]
  refine h.trans ?_
  have hp : (0 : ℝ) < ((n.factorial * (2 * n + 1) : ℕ) : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ scale_pos.le
  unfold serRem
  push_cast
  gcongr

/-- The bound of `row_sound`: the check's `ε`, the width of the enclosure of `2/√π`, the high part
of the shifted series, and the series' remainder. -/
def rowBound (n J : ℕ) (c r ε : ℚ) : ℚ :=
  ε + (sHi - sLo) / 2 * absSum r ((shift c (ser n)).take (J + 1)) +
    sHi * (r ^ (J + 1) * absSum r ((shift c (ser n)).drop (J + 1)) + serRem n (qabs c + r))

/-- The check of `row_sound`: `P` against the shifted series cut after degree `J`, times the middle
of the enclosure of `2/√π`. -/
def rowCheck (n J : ℕ) (c r ε : ℚ) (P : List ℚ) (d : ℕ) : Bool :=
  check (subP P (scaleP ((sLo + sHi) / 2) ((shift c (ser n)).take (J + 1)))) (-r) r ε d

theorem row_sound (n J : ℕ) (c r ε : ℚ) (P : List ℚ) (d : ℕ) (hr : 0 ≤ r)
    (hc : rowCheck n J c r ε P d = true) (z : ℝ) (hz : |z| ≤ r) :
    |eval P z - erf (c + z)| ≤ (rowBound n J c r ε : ℝ) := by
  unfold rowBound
  push_cast
  set Q := shift c (ser n)
  set lo := Q.take (J + 1)
  set hi := Q.drop (J + 1)
  have hQ : eval Q z = eval (ser n) (c + z) := eval_shift c (ser n) z
  have hsplit := eval_take_drop (J + 1) Q z
  have hchk := check_sound _ _ _ _ _ hc z (by push_cast; linarith [(abs_le.mp hz).1])
    (by linarith [(abs_le.mp hz).2])
  rw [eval_subP, eval_scaleP] at hchk
  have hlo := abs_eval_le r hr lo z hz
  have hhi := abs_eval_le r hr hi z hz
  have hzk : |z ^ (J + 1)| ≤ (r : ℝ) ^ (J + 1) := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz _
  have hX : |(c : ℝ) + z| ≤ ((qabs c + r : ℚ) : ℝ) := by
    push_cast; rw [qabs_cast]; exact (abs_add_le _ _).trans (by linarith)
  have hser := erf_ser n ((c : ℝ) + z) _ hX
  have hsl := scale_lo
  have hsh := scale_hi
  have hσ : |(((sLo + sHi) / 2 : ℚ) : ℝ) - scale| ≤ ((sHi - sLo) / 2 : ℚ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hrem0 : (0 : ℝ) ≤ (serRem n (qabs c + r) : ℚ) := by
    unfold serRem; have : (0 : ℚ) ≤ qabs c := by unfold qabs; split <;> linarith
    positivity
  have e1 : eval P z - erf (c + z) = (eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * eval lo z) +
      ((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * eval lo z -
      scale * (z ^ (J + 1) * eval hi z) + (scale * eval (ser n) (c + z) - erf (c + z)) := by
    rw [← hQ, hsplit]; ring
  rw [e1]
  have k1 : |(((sLo + sHi) / 2 : ℚ) : ℝ) - scale| * |eval lo z| ≤
      ((sHi - sLo) / 2 : ℚ) * (absSum r lo : ℝ) :=
    mul_le_mul hσ hlo (abs_nonneg _) (by push_cast; linarith)
  have k2 : |z ^ (J + 1) * eval hi z| ≤ (r : ℝ) ^ (J + 1) * (absSum r hi : ℝ) := by
    rw [abs_mul]; exact mul_le_mul hzk hhi (abs_nonneg _) (by positivity)
  have k3 : scale * |z ^ (J + 1) * eval hi z| ≤ (sHi : ℝ) * ((r : ℝ) ^ (J + 1) * (absSum r hi : ℝ)) :=
    mul_le_mul hsh k2 (abs_nonneg _) (by linarith [scale_pos])
  have k4 : scale * (serRem n (qabs c + r) : ℝ) ≤ (sHi : ℝ) * (serRem n (qabs c + r) : ℝ) :=
    mul_le_mul_of_nonneg_right hsh hrem0
  have k5 : |scale * eval (ser n) (c + z) - erf (c + z)| ≤ scale * (serRem n (qabs c + r) : ℝ) := by
    rw [abs_sub_comm]; exact hser
  set A := eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * eval lo z
  set B := ((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * eval lo z
  have t1 := abs_add_le (A + B - scale * (z ^ (J + 1) * eval hi z))
    (scale * eval (ser n) (c + z) - erf (c + z))
  have t2 : |A + B - scale * (z ^ (J + 1) * eval hi z)| ≤
      |A + B| + |scale * (z ^ (J + 1) * eval hi z)| := by
    have := abs_add_le (A + B) (-(scale * (z ^ (J + 1) * eval hi z)))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have hB : |B| ≤ ((sHi : ℝ) - sLo) / 2 * (absSum r lo : ℝ) := by
    show |((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * eval lo z| ≤ _
    rw [abs_mul]
    have := k1
    push_cast at this ⊢
    exact this
  have t3 := abs_add_le A B
  rw [abs_mul scale, abs_of_pos scale_pos] at t2
  linarith

/-- A lower bound on `erfc x` from the series of `n` terms. -/
def erfcLo (n : ℕ) (x : ℚ) : ℚ := 1 - sHi * (evalQ (ser n) x + serRem n x)

theorem erfc_ge (n : ℕ) (x : ℚ) (hx : 0 ≤ x) (hpos : 0 ≤ evalQ (ser n) x + serRem n x) :
    (erfcLo n x : ℝ) ≤ erfc x := by
  have h := erf_ser n (x : ℝ) x (le_of_eq (abs_of_nonneg (by exact_mod_cast hx)))
  have hq : eval (ser n) (x : ℝ) = (evalQ (ser n) x : ℝ) := (PolyCalc.evalQ_cast _ _).symm
  rw [hq] at h
  have hp : (0 : ℝ) ≤ (evalQ (ser n) x : ℝ) + (serRem n x : ℝ) := by exact_mod_cast hpos
  have h1 : erf x ≤ scale * ((evalQ (ser n) x : ℝ) + (serRem n x : ℝ)) := by
    have := (abs_le.mp h).2; linarith
  have h2 : scale * ((evalQ (ser n) x : ℝ) + (serRem n x : ℝ)) ≤
      (sHi : ℝ) * ((evalQ (ser n) x : ℝ) + (serRem n x : ℝ)) :=
    mul_le_mul_of_nonneg_right scale_hi hp
  unfold erfc erfcLo
  push_cast
  linarith

#print axioms scale_lo
#print axioms scale_hi
#print axioms row_sound
#print axioms erfc_ge

end Verified.Examples.ErfcSeries
