import Library.Numerics.Float64.Log2.Compiled
import Library.Numerics.Float64.Log.LogTables
import Library.Numerics.Float64.Exp.ExpReductionBounds

/-!
Facts about each of the 64 entries of Arm's `log2` tables, checked by the kernel over the
rationals as `LogTables` checks the tables of `log`.  Entry `i` describes the center
`c = chi + clo` of subinterval `i` of `[0x1.6p-1, 0x1.6p0)`: `c invc` is within `2 ^ -100` of 1,
`(z - c) invc` stays within `0.00776` for `z` in the subinterval, `chi` lies on the grid of
`2 ^ -53` between `1/2` and `3/2`, `|clo| ≤ 2 ^ -50`, `logc` lies on the grid of `2 ^ -42` with
`|logc| ≤ 27/50`, and `|logc| ≥ 1/20` outside the seven subintervals 35 to 41 around 1.  `logc` is
within `2 ^ -65` of `log2 c`, from exponentials of `logc · S ∓ 2 ^ -66` bracketing `c`, where `S`
is the split of `log 2` within `2 ^ -92` of `log 2` from `ExpReductionBounds`.
-/

namespace Library.Numerics.Float64.Log2.Log2Tables
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound TaylorRemainder Library.Numerics.Float64.Log.LogTables

def invcQ (i : Nat) : ℚ := ratOfWord Log2.log2Table[2 * i]!
def logcQ (i : Nat) : ℚ := ratOfWord Log2.log2Table[2 * i + 1]!
def chiQ (i : Nat) : ℚ := ratOfWord Log2.log2Table2[2 * i]!
def cloQ (i : Nat) : ℚ := ratOfWord Log2.log2Table2[2 * i + 1]!
def centerQ (i : Nat) : ℚ := chiQ i + cloQ i

/-- The lower end of subinterval `i`. -/
def lowQ (i : Nat) : ℚ := if i < 40 then ((88 + i : Nat) : ℚ) / 128 else ((24 + i : Nat) : ℚ) / 64

/-- The upper end of subinterval `i`. -/
def highQ (i : Nat) : ℚ := if i < 40 then ((89 + i : Nat) : ℚ) / 128 else ((25 + i : Nat) : ℚ) / 64

def tolerance2 : ℚ := 1 / 2 ^ 66

theorem checked_entries : ∀ i : Fin 64,
    Finite Log2.log2Table[2 * i.val]! ∧ Finite Log2.log2Table[2 * i.val + 1]! ∧
    Finite Log2.log2Table2[2 * i.val]! ∧ Finite Log2.log2Table2[2 * i.val + 1]! ∧
    0 < invcQ i.val ∧ invcQ i.val ≤ 3 / 2 ∧
    qabs (centerQ i.val * invcQ i.val - 1) ≤ 1 / 2 ^ 100 ∧
    -(776 / 100000) ≤ (lowQ i.val - centerQ i.val) * invcQ i.val ∧
    (highQ i.val - centerQ i.val) * invcQ i.val ≤ 776 / 100000 ∧
    1 / 2 ≤ chiQ i.val ∧ chiQ i.val ≤ 3 / 2 ∧
    Wasm.IEEE64.scaledValue Log2.log2Table2[2 * i.val]! % 2 ^ 1021 = 0 ∧
    Wasm.IEEE64.scaledValue Log2.log2Table[2 * i.val + 1]! % 2 ^ 1032 = 0 ∧
    qabs (cloQ i.val) ≤ 1 / 2 ^ 50 ∧
    qabs (logcQ i.val) ≤ 27 / 50 ∧
    (i.val ≤ 34 ∨ 42 ≤ i.val → 1 / 20 ≤ qabs (logcQ i.val)) := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem checked_logs : ∀ i : Fin 64,
    evalQ (expCoeffs 20) (logcQ i.val * Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo - tolerance2) +
      expRemainder ≤ centerQ i.val ∧
    centerQ i.val ≤
      evalQ (expCoeffs 20) (logcQ i.val * Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo + tolerance2) -
        expRemainder := by
  decide +kernel

/-- `logc` is within `2 ^ -65` of `log2 c`. -/
theorem log2_center (i : Fin 64) :
    0 < (centerQ i.val : ℝ) ∧
      |Real.log (centerQ i.val : ℝ) / Real.log 2 - (logcQ i.val : ℝ)| ≤ 1 / 2 ^ 65 := by
  obtain ⟨hlo, hhi⟩ := checked_logs i
  have hl := (checked_entries i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl' : |(logcQ i.val : ℝ)| ≤ 27 / 50 := by
    have h : ((qabs (logcQ i.val) : ℚ) : ℝ) ≤ ((27 / 50 : ℚ) : ℝ) := Rat.cast_le.mpr hl
    rw [qabs_cast] at h
    exact h.trans (by norm_num)
  obtain ⟨hL1, hL2⟩ := Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_enclosure
  simp only [Library.Numerics.Float64.Exp.ExpReductionBounds.lowerLogTwo, Library.Numerics.Float64.Exp.ExpReductionBounds.upperLogTwo] at hL1 hL2
  push_cast at hL1 hL2
  have hSq : (69 / 100 : ℚ) ≤ Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo ∧
      Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo ≤ 7 / 10 := by decide +kernel
  have hSb : (69 / 100 : ℝ) ≤ (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) ∧
      (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) ≤ 7 / 10 := by
    constructor
    · have h := Rat.cast_le (K := ℝ) |>.mpr hSq.1
      push_cast at h
      exact h
    · have h := Rat.cast_le (K := ℝ) |>.mpr hSq.2
      push_cast at h
      exact h
  have htol : ((tolerance2 : ℚ) : ℝ) = 1 / 2 ^ 66 := by norm_num [tolerance2]
  have hprod : |(logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)| ≤ 27 / 50 * (7 / 10) := by
    rw [abs_mul, abs_of_pos (by linarith [hSb.1] : (0 : ℝ) < (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ))]
    exact mul_le_mul hl' hSb.2 (by linarith [hSb.1]) (by norm_num)
  have hx1 : |(logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) - 1 / 2 ^ 66| ≤ 2 / 5 := by
    rw [abs_le] at hprod ⊢
    constructor <;> linarith [hprod.1, hprod.2, (by norm_num : (0 : ℝ) < 1 / 2 ^ 66),
      (by norm_num : (1 : ℝ) / 2 ^ 66 < 1 / 100)]
  have hx2 : |(logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) + 1 / 2 ^ 66| ≤ 2 / 5 := by
    rw [abs_le] at hprod ⊢
    constructor <;> linarith [hprod.1, hprod.2, (by norm_num : (0 : ℝ) < 1 / 2 ^ 66),
      (by norm_num : (1 : ℝ) / 2 ^ 66 < 1 / 100)]
  have hdown := abs_le.mp (exp_near _ hx1)
  have hup := abs_le.mp (exp_near _ hx2)
  have hlo' : ((evalQ (expCoeffs 20) (logcQ i.val * Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo - tolerance2) +
      expRemainder : ℚ) : ℝ) ≤ (centerQ i.val : ℝ) := Rat.cast_le.mpr hlo
  have hhi' : (centerQ i.val : ℝ) ≤ ((evalQ (expCoeffs 20)
      (logcQ i.val * Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo + tolerance2) - expRemainder : ℚ) : ℝ) :=
    Rat.cast_le.mpr hhi
  rw [Rat.cast_add, evalQ_cast, Rat.cast_sub, Rat.cast_mul, htol] at hlo'
  rw [Rat.cast_sub, evalQ_cast, Rat.cast_add, Rat.cast_mul, htol] at hhi'
  have hc0 : 0 < (centerQ i.val : ℝ) := by
    have := Real.exp_pos ((logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) - 1 / 2 ^ 66)
    linarith [hdown.2]
  have hlogc : |Real.log (centerQ i.val : ℝ) - (logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)| ≤ 1 / 2 ^ 66 := by
    rw [abs_le]
    constructor
    · have h : Real.exp ((logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) - 1 / 2 ^ 66) ≤ (centerQ i.val : ℝ) := by
        linarith [hdown.2]
      have := (Real.le_log_iff_exp_le hc0).mpr h
      linarith
    · have h : (centerQ i.val : ℝ) ≤ Real.exp ((logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) + 1 / 2 ^ 66) := by
        linarith [hup.1]
      have := (Real.log_le_iff_le_exp hc0).mpr h
      linarith
  refine ⟨hc0, ?_⟩
  have hln2 : (689 / 1000 : ℝ) ≤ Real.log 2 := by linarith [hSb.1, hL1]
  have hdiff : |Real.log (centerQ i.val : ℝ) - (logcQ i.val : ℝ) * Real.log 2| ≤
      1 / 2 ^ 66 + 27 / 50 * (1 / 2 ^ 92) := by
    have h3 : |(logcQ i.val : ℝ) * ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) - Real.log 2)| ≤ 27 / 50 * (1 / 2 ^ 92) := by
      rw [abs_mul]
      apply mul_le_mul hl' _ (abs_nonneg _) (by norm_num)
      rw [abs_le]
      constructor <;> linarith
    calc _ = |(Real.log (centerQ i.val : ℝ) - (logcQ i.val : ℝ) * (Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ)) +
          (logcQ i.val : ℝ) * ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℝ) - Real.log 2)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlogc h3)
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [show Real.log (centerQ i.val : ℝ) / Real.log 2 - (logcQ i.val : ℝ) =
    (Real.log (centerQ i.val : ℝ) - (logcQ i.val : ℝ) * Real.log 2) / Real.log 2 by
      field_simp, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have : (1 : ℝ) / 2 ^ 66 + 27 / 50 * (1 / 2 ^ 92) ≤ 1 / 2 ^ 65 * (689 / 1000) := by norm_num
  nlinarith

#print axioms checked_entries
#print axioms checked_logs
#print axioms log2_center

end Library.Numerics.Float64.Log2.Log2Tables
