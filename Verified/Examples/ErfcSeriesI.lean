import Verified.Examples.ErfcSeries

/-!
`ErfcSeries.row_sound` with the shift in integer arithmetic.  The series of `n` terms has the
coefficients `(-1)^k/(k! (2k + 1))`; times a common denominator `D` (`serD`) and with the variable
scaled by `s`, they become integers (`serI`, `eval_serI`).  For a center `m/s` the kernel then
shifts by the integer `m`, so every rational in the shift has denominator 1 and needs no
reduction, and divides only the `J + 1` low coefficients by `D s^(2n-1)` (`rowLo`).  The high part
is bounded by the sum of the absolute values of the shifted integers (`rowTail`), since
`|s z| ≤ 1`.  `row_soundI` states the result in the form of `row_sound`.
-/

namespace Verified.Examples.ErfcSeriesI

open LeanExe.ProofKit PolyBound PolyChecks PolyCalculus PolyCalc RealErf ErfcSeries TaylorRemainder

set_option exponentiation.threshold 4096

/-- A common denominator of the first `n` coefficients of the series. -/
def serD (n : ℕ) : ℕ :=
  (List.range n).foldl (fun a k => Nat.lcm a (k.factorial * (2 * k + 1))) 1

/-- The series of `n` terms times `D s^(2n-1)`, as a polynomial in `s x`. -/
def serI (n D s : ℕ) : List ℚ :=
  oddP ((List.range n).map fun k =>
    (-1) ^ k * ((D / (k.factorial * (2 * k + 1)) : ℕ) : ℚ) * (s : ℚ) ^ (2 * (n - 1 - k)))

theorem eval_serI (n D s : ℕ) (hn : 1 ≤ n) (hD : ∀ k < n, k.factorial * (2 * k + 1) ∣ D)
    (x : ℝ) : eval (serI n D s) ((s : ℝ) * x) = D * (s : ℝ) ^ (2 * n - 1) * eval (ser n) x := by
  rw [serI, eval_oddP, eval_map_range, ser, eval_oddP, erfCoeffs, eval_map_range]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.mp hk
  have hm : (k.factorial * (2 * k + 1) : ℕ) ≠ 0 := by positivity
  have hdiv : ((D / (k.factorial * (2 * k + 1)) : ℕ) : ℝ) =
      (D : ℝ) / ((k.factorial * (2 * k + 1) : ℕ) : ℝ) :=
    Nat.cast_div (hD k hk') (by exact_mod_cast hm)
  have hm' : ((k.factorial * (2 * k + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  rw [hdiv, show 2 * n - 1 = 2 * (n - 1 - k) + (2 * k + 1) by omega, pow_add]
  push_cast at hm'
  field_simp
  push_cast
  ring

/-- The coefficients `a_i s^i` of `p (s z)`. -/
def scaleVarP (s : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: scaleP s (scaleVarP s p)

theorem eval_scaleVarP (s : ℚ) (p : List ℚ) (z : ℝ) :
    eval (scaleVarP s p) z = eval p (s * z) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [scaleVarP, eval_cons, eval_scaleP, ih]
    ring

/-- The shifted integer series for the center `m/s`. -/
def rowB (n m s : ℕ) : List ℚ := shift (m : ℚ) (serI n (serD n) s)

/-- The denominator `D s^(2n-1)`. -/
def rowDen (n s : ℕ) : ℚ := (serD n : ℚ) * (s : ℚ) ^ (2 * n - 1)

/-- The low part of the series at `m/s + z`, cut after degree `J`, as a polynomial in `z`. -/
def rowLo (n J m s : ℕ) : List ℚ :=
  scaleP (1 / rowDen n s) (scaleVarP s ((rowB n m s).take (J + 1)))

/-- The bound on the high part. -/
def rowTail (n J m s : ℕ) : ℚ := absSum 1 ((rowB n m s).drop (J + 1)) / rowDen n s

/-- The bound of `row_soundI`. -/
def rowBoundI (n J m s : ℕ) (ε : ℚ) : ℚ :=
  ε + (sHi - sLo) / 2 * absSum (1 / s) (rowLo n J m s) +
    sHi * (rowTail n J m s + serRem n ((m : ℚ) / s + 1 / s))

/-- The check of `row_soundI`, with the divisibility conditions of `serD`. -/
def rowCheckI (n J m s : ℕ) (ε : ℚ) (P : List ℚ) (d : ℕ) : Bool :=
  decide (∀ k < n, serD n % (k.factorial * (2 * k + 1)) = 0) &&
    check (subP P (scaleP ((sLo + sHi) / 2) (rowLo n J m s))) (-(1 / s)) (1 / s) ε d

theorem series_split (n J m s : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hD : ∀ k < n, k.factorial * (2 * k + 1) ∣ serD n) (z : ℝ) (hz : |z| ≤ 1 / (s : ℝ)) :
    |eval (ser n) ((m : ℝ) / s + z) - eval (rowLo n J m s) z| ≤ rowTail n J m s := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hD0 : (0 : ℝ) < serD n := by
    have : 0 < serD n := by
      unfold serD
      suffices ∀ (l : List ℕ) (a : ℕ), 0 < a → 0 < l.foldl
          (fun a k => Nat.lcm a (k.factorial * (2 * k + 1))) a from this _ 1 one_pos
      intro l
      induction l with
      | nil => intro a ha; exact ha
      | cons k l ih => intro a ha; exact ih _ (Nat.lcm_pos ha (by positivity))
    exact_mod_cast this
  have hden : (0 : ℝ) < rowDen n s := by
    unfold rowDen; push_cast; positivity
  have hsz : |(s : ℝ) * z| ≤ 1 := by
    rw [abs_mul, abs_of_pos hs']
    calc (s : ℝ) * |z| ≤ s * (1 / s) := by gcongr
      _ = 1 := by field_simp
  have h1 : eval (ser n) ((m : ℝ) / s + z) * rowDen n s =
      eval (rowB n m s) ((s : ℝ) * z) := by
    rw [rowB, eval_shift, show ((m : ℚ) : ℝ) + (s : ℝ) * z = (s : ℝ) * ((m : ℝ) / s + z) by
      push_cast; field_simp, eval_serI n (serD n) s hn hD]
    unfold rowDen; push_cast; ring
  have h2 := eval_take_drop (J + 1) (rowB n m s) ((s : ℝ) * z)
  have h3 : eval (rowLo n J m s) z * rowDen n s =
      eval ((rowB n m s).take (J + 1)) ((s : ℝ) * z) := by
    rw [rowLo, eval_scaleP, eval_scaleVarP]
    push_cast
    field_simp
  have h4 : |((s : ℝ) * z) ^ (J + 1) * eval ((rowB n m s).drop (J + 1)) ((s : ℝ) * z)| ≤
      absSum 1 ((rowB n m s).drop (J + 1)) := by
    rw [abs_mul, abs_pow]
    have := abs_eval_le 1 (by norm_num) ((rowB n m s).drop (J + 1)) ((s : ℝ) * z)
      (by push_cast; exact hsz)
    calc |(s : ℝ) * z| ^ (J + 1) * |eval ((rowB n m s).drop (J + 1)) ((s : ℝ) * z)|
        ≤ 1 * (absSum 1 ((rowB n m s).drop (J + 1)) : ℝ) :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hsz) this (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have e1 : eval (ser n) ((m : ℝ) / s + z) - eval (rowLo n J m s) z =
      ((s : ℝ) * z) ^ (J + 1) * eval ((rowB n m s).drop (J + 1)) ((s : ℝ) * z) / rowDen n s := by
    rw [eq_div_iff hden.ne', sub_mul]
    linarith [h1, h2, h3]
  rw [e1, abs_div, abs_of_pos hden, rowTail]
  push_cast
  rw [div_le_div_iff_of_pos_right hden]
  exact h4

theorem row_soundI (n J m s : ℕ) (ε : ℚ) (P : List ℚ) (d : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hc : rowCheckI n J m s ε P d = true) (z : ℝ) (hz : |z| ≤ 1 / (s : ℝ)) :
    |eval P z - erf ((m : ℝ) / s + z)| ≤ (rowBoundI n J m s ε : ℝ) := by
  simp only [rowCheckI, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hD', hck⟩ := hc
  have hD : ∀ k < n, k.factorial * (2 * k + 1) ∣ serD n := fun k hk =>
    Nat.dvd_of_mod_eq_zero (hD' k hk)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsplit := series_split n J m s hn hs hD z hz
  have hchk := check_sound _ _ _ _ _ hck z (by push_cast; linarith [(abs_le.mp hz).1])
    (by push_cast; linarith [(abs_le.mp hz).2])
  rw [eval_subP, eval_scaleP] at hchk
  have hlo := abs_eval_le (1 / s) (by positivity) (rowLo n J m s) z (by push_cast; exact hz)
  have hX : |(m : ℝ) / s + z| ≤ (((m : ℚ) / s + 1 / s : ℚ) : ℝ) := by
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hser := erf_ser n ((m : ℝ) / s + z) _ hX
  have hsl := scale_lo
  have hsh := scale_hi
  have hσ : |(((sLo + sHi) / 2 : ℚ) : ℝ) - scale| ≤ ((sHi - sLo) / 2 : ℚ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have hrem0 : (0 : ℝ) ≤ (serRem n ((m : ℚ) / s + 1 / s) : ℚ) := by
    unfold serRem; push_cast; positivity
  set L := eval (rowLo n J m s) z
  set S := eval (ser n) ((m : ℝ) / s + z)
  have e1 : eval P z - erf ((m : ℝ) / s + z) = (eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * L) +
      ((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * L + scale * (L - S) +
      (scale * S - erf ((m : ℝ) / s + z)) := by ring
  rw [e1]
  have k1 : |((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * L| ≤
      ((sHi - sLo) / 2 : ℚ) * (absSum (1 / s) (rowLo n J m s) : ℝ) := by
    rw [abs_mul]; exact mul_le_mul hσ hlo (abs_nonneg _) (by push_cast; linarith)
  have k2 : |scale * (L - S)| ≤ sHi * (rowTail n J m s : ℝ) := by
    rw [abs_mul, abs_of_pos scale_pos, abs_sub_comm]
    exact mul_le_mul hsh hsplit (abs_nonneg _) (by linarith [scale_pos])
  have k3 : |scale * S - erf ((m : ℝ) / s + z)| ≤ sHi * (serRem n ((m : ℚ) / s + 1 / s) : ℝ) := by
    rw [abs_sub_comm]
    exact hser.trans (mul_le_mul_of_nonneg_right hsh hrem0)
  have t1 := abs_add_le ((eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * L) +
    ((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * L + scale * (L - S)) (scale * S - erf ((m : ℝ) / s + z))
  have t2 := abs_add_le (eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * L +
    ((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * L) (scale * (L - S))
  have t3 := abs_add_le (eval P z - (((sLo + sHi) / 2 : ℚ) : ℝ) * L)
    (((((sLo + sHi) / 2 : ℚ) : ℝ) - scale) * L)
  unfold rowBoundI
  push_cast at k1 k2 k3 hchk t1 t2 t3 ⊢
  linarith

#print axioms eval_serI
#print axioms row_soundI

end Verified.Examples.ErfcSeriesI
