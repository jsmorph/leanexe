import Verified.Examples.TrigMediumConst
import Verified.Examples.TrigMediumFn
import Verified.Examples.TrigDistance

/-!
The three outcomes of fdlibm's medium reduction on words.  With `N` the count and
`r = x - N π/2`, the first step gives `y0 + y1 = R1 - W1`, the second `R2 - W2'`, and the third
`R3 - W3'`, each within `2 ^ -60` relative of `r` when the step's exponent test stops there.
-/

namespace Verified.Examples.TrigMediumCases

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigSmall TrigMediumConst
  TrigMediumFn

def R1 (X F : UInt64) : UInt64 := Wasm.IEEE64.sub X (Wasm.IEEE64.mul F pio2_1)
def W1 (F : UInt64) : UInt64 := Wasm.IEEE64.mul F pio2_1t
def Y0 (X F : UInt64) : UInt64 := Wasm.IEEE64.sub (R1 X F) (W1 F)
def W2 (F : UInt64) : UInt64 := Wasm.IEEE64.mul F pio2_2
def R2 (X F : UInt64) : UInt64 := Wasm.IEEE64.sub (R1 X F) (W2 F)
def A2 (F : UInt64) : UInt64 := Wasm.IEEE64.mul F pio2_2t
def W2' (X F : UInt64) : UInt64 :=
  Wasm.IEEE64.sub (A2 F) (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (R2 X F)) (W2 F))
def Y0b (X F : UInt64) : UInt64 := Wasm.IEEE64.sub (R2 X F) (W2' X F)
def W3 (F : UInt64) : UInt64 := Wasm.IEEE64.mul F pio2_3
def R3 (X F : UInt64) : UInt64 := Wasm.IEEE64.sub (R2 X F) (W3 F)
def A3 (F : UInt64) : UInt64 := Wasm.IEEE64.mul F pio2_3t
def W3' (X F : UInt64) : UInt64 :=
  Wasm.IEEE64.sub (A3 F) (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (R3 X F)) (W3 F))
def Y0c (X F : UInt64) : UInt64 := Wasm.IEEE64.sub (R3 X F) (W3' X F)

/-- The hypotheses shared by the three outcomes. -/
structure Med (X F : UInt64) (N : Nat) : Prop where
  Xf : Finite X
  x1 : 1 ≤ value X
  x2 : value X * (2 / Real.pi) ≤ 2 ^ 20
  Ff : Finite F
  N1 : 1 ≤ N
  N2 : N ≤ 2 ^ 20
  Fv : Wasm.IEEE64.scaledValue F = (N : Int) * 2 ^ 1074
  Nx : |(N : ℝ) - value X * (2 / Real.pi)| ≤ 1 / 2 + 1 / 2 ^ 30
  dist : 1 / 2 ^ 63 < |value X * (2 / Real.pi) - N|

/-- A word whose exponent field is at least that of `X` minus `k` has more than `|X| / 2 ^ (k+1)`
in magnitude. -/
theorem exp_lower (Y X : UInt64) (k : Nat) (hk : k + 1 ≤ Wasm.IEEE64.exponent X)
    (hY : Wasm.IEEE64.exponent X ≤ Wasm.IEEE64.exponent Y + k) :
    |value X| / 2 ^ (k + 1) < |value Y| := by
  have hXb := grid_bound X
  have hYl := grid_lower Y (by omega)
  have e : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent X - 1)) / 2 ^ 1074 / 2 ^ (k + 1) ≤
      (2 : ℝ) ^ (52 + (Wasm.IEEE64.exponent Y - 1)) / 2 ^ 1074 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [← pow_add]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h := div_lt_div_of_pos_right hXb (show (0 : ℝ) < 2 ^ (k + 1) by positivity)
  linarith

/-- A word whose exponent field is more than `k` below that of `X` has less than `|X| / 2 ^ k`
in magnitude. -/
theorem exp_upper (Y X : UInt64) (k : Nat) (hk : k + 2 ≤ Wasm.IEEE64.exponent X)
    (hY : Wasm.IEEE64.exponent Y + k < Wasm.IEEE64.exponent X) :
    |value Y| < |value X| / 2 ^ k := by
  have hYb := grid_bound Y
  have hXl := grid_lower X (by omega)
  have e : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent Y - 1)) / 2 ^ 1074 ≤
      (2 : ℝ) ^ (52 + (Wasm.IEEE64.exponent X - 1)) / 2 ^ 1074 / 2 ^ k := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [← pow_add]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h := div_le_div_of_nonneg_right hXl (show (0 : ℝ) ≤ 2 ^ k by positivity)
  linarith

theorem pio2_values :
    value pio2_1 = 1686629713 / 2 ^ 30 ∧ value pio2_2 = 2242054355 / 2 ^ 65 ∧
      value pio2_3 = 160220439 / 2 ^ 96 ∧
      1 / 2 ^ 34 ≤ value pio2_1t ∧ value pio2_1t ≤ 1 / 2 ^ 33 ∧
      1 / 2 ^ 69 ≤ value pio2_2t ∧ value pio2_2t ≤ 1 / 2 ^ 68 ∧
      1 / 2 ^ 104 ≤ value pio2_3t ∧ value pio2_3t ≤ 1 / 2 ^ 103 := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, l1, u1, l2, u2, l3, u3⟩ := consts_checked
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TrigSmall.value_of_scaled, h1]
    push_cast
    rw [show (1074 : Nat) = 1044 + 30 by norm_num, pow_add]
    field_simp
  · rw [TrigSmall.value_of_scaled, h2]
    push_cast
    rw [show (1074 : Nat) = 1009 + 65 by norm_num, pow_add]
    field_simp
  · rw [TrigSmall.value_of_scaled, h3]
    push_cast
    rw [show (1074 : Nat) = 978 + 96 by norm_num, pow_add]
    field_simp
  · rw [TrigSmall.value_of_scaled, le_div_iff₀ hp]
    have : ((2 : Int) ^ 1040 : ℝ) ≤ (Wasm.IEEE64.scaledValue pio2_1t : ℝ) := by exact_mod_cast l1
    calc (1 : ℝ) / 2 ^ 34 * 2 ^ 1074 = 2 ^ 1040 := by
          rw [show (1074 : Nat) = 34 + 1040 by norm_num, pow_add]; field_simp
      _ ≤ _ := by exact_mod_cast this
  · rw [TrigSmall.value_of_scaled, div_le_iff₀ hp]
    have : (Wasm.IEEE64.scaledValue pio2_1t : ℝ) ≤ ((2 : Int) ^ 1041 : ℝ) := by exact_mod_cast u1
    calc (Wasm.IEEE64.scaledValue pio2_1t : ℝ) ≤ 2 ^ 1041 := by exact_mod_cast this
      _ = 1 / 2 ^ 33 * 2 ^ 1074 := by
          rw [show (1074 : Nat) = 33 + 1041 by norm_num, pow_add]; field_simp
  · rw [TrigSmall.value_of_scaled, le_div_iff₀ hp]
    have : ((2 : Int) ^ 1005 : ℝ) ≤ (Wasm.IEEE64.scaledValue pio2_2t : ℝ) := by exact_mod_cast l2
    calc (1 : ℝ) / 2 ^ 69 * 2 ^ 1074 = 2 ^ 1005 := by
          rw [show (1074 : Nat) = 69 + 1005 by norm_num, pow_add]; field_simp
      _ ≤ _ := by exact_mod_cast this
  · rw [TrigSmall.value_of_scaled, div_le_iff₀ hp]
    have : (Wasm.IEEE64.scaledValue pio2_2t : ℝ) ≤ ((2 : Int) ^ 1006 : ℝ) := by exact_mod_cast u2
    calc (Wasm.IEEE64.scaledValue pio2_2t : ℝ) ≤ 2 ^ 1006 := by exact_mod_cast this
      _ = 1 / 2 ^ 68 * 2 ^ 1074 := by
          rw [show (1074 : Nat) = 68 + 1006 by norm_num, pow_add]; field_simp
  · rw [TrigSmall.value_of_scaled, le_div_iff₀ hp]
    have : ((2 : Int) ^ 970 : ℝ) ≤ (Wasm.IEEE64.scaledValue pio2_3t : ℝ) := by exact_mod_cast l3
    calc (1 : ℝ) / 2 ^ 104 * 2 ^ 1074 = 2 ^ 970 := by
          rw [show (1074 : Nat) = 104 + 970 by norm_num, pow_add]; field_simp
      _ ≤ _ := by exact_mod_cast this
  · rw [TrigSmall.value_of_scaled, div_le_iff₀ hp]
    have : (Wasm.IEEE64.scaledValue pio2_3t : ℝ) ≤ ((2 : Int) ^ 971 : ℝ) := by exact_mod_cast u3
    calc (Wasm.IEEE64.scaledValue pio2_3t : ℝ) ≤ 2 ^ 971 := by exact_mod_cast this
      _ = 1 / 2 ^ 103 * 2 ^ 1074 := by
          rw [show (1074 : Nat) = 103 + 971 by norm_num, pow_add]; field_simp

/-- A product away from underflow and overflow is within `2 ^ -52` relative. -/
theorem mul_rel (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hlo : 1 / 2 ^ 900 ≤ |value a * value b|) (hhi : |value a * value b| ≤ 2 ^ 100) :
    Finite (Wasm.IEEE64.mul a b) ∧
      |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ |value a * value b| / 2 ^ 52 := by
  have hmin : minNormal64 ≤ |value a * value b| := by
    have : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 900 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    unfold minNormal64
    linarith
  have hmax : |value a * value b| < 2 ^ 1022 :=
    lt_of_le_of_lt hhi (pow_lt_pow_right₀ (by norm_num) (by norm_num))
  obtain ⟨hf, he⟩ := F64ArithmeticBounds.mul_error_scaled a b ha hb _ hmin hmax le_rfl
  refine ⟨hf, he.trans (le_of_eq ?_)⟩
  simp only [arithmeticEpsilon]
  ring

/-- The facts shared by the three outcomes: the bounds of `r = x - N π/2`, the exact first
difference `R1 = x - N pio2_1`, and the rounded `W1 ≈ N pio2_1t`. -/
theorem med_common (X F : UInt64) (N : Nat) (h : Med X F N) :
    1 / 2 ^ 63 ≤ |value X - N * (Real.pi / 2)| ∧
      |value X - N * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 28 ∧
      (N : ℝ) ≤ 6 / 5 * value X ∧
      1023 ≤ Wasm.IEEE64.exponent X ∧ Wasm.IEEE64.exponent X ≤ 1043 ∧
      Finite (R1 X F) ∧ value (R1 X F) = value X - N * value pio2_1 ∧
      (2 : Int) ^ 1009 ∣ Wasm.IEEE64.scaledValue (R1 X F) ∧
      Finite (W1 F) ∧ |value (W1 F) - N * value pio2_1t| ≤ N * value pio2_1t / 2 ^ 52 ∧
      |value (R1 X F) - value (W1 F) - (value X - N * (Real.pi / 2))| ≤ value X / 2 ^ 84 := by
  obtain ⟨hP1, -, -, hP1tl, hP1tu, -, -, -, -⟩ := pio2_values
  have hpc := pio2_close
  rw [abs_le] at hpc
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hx1 := h.x1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.N1
  have hN2 : (N : ℝ) ≤ 2 ^ 20 := by exact_mod_cast h.N2
  have hNx := h.Nx
  rw [abs_le] at hNx
  have hr : value X - N * (Real.pi / 2) = Real.pi / 2 * (value X * (2 / Real.pi) - N) := by
    field_simp
  have hrl : 1 / 2 ^ 63 ≤ |value X - N * (Real.pi / 2)| := by
    rw [hr, abs_mul, abs_of_pos (by positivity)]
    have := h.dist
    nlinarith
  have hru : |value X - N * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 28 := by
    rw [hr, abs_mul, abs_of_pos (by positivity)]
    have : |value X * (2 / Real.pi) - N| ≤ 1 / 2 + 1 / 2 ^ 30 := by
      rw [abs_sub_comm]; rw [abs_le]; exact hNx
    nlinarith
  have h2pi : 2 / Real.pi ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hNle : (N : ℝ) ≤ 6 / 5 * value X := by nlinarith
  have hE1 : 1023 ≤ Wasm.IEEE64.exponent X := F64Magnitude.exponent_ge_of_one_le X hx1
  have hE2 : Wasm.IEEE64.exponent X ≤ 1043 := by
    by_contra hc
    have hl := grid_lower X (by omega)
    have h21 : (2 : ℝ) ^ 21 ≤ (2 : ℝ) ^ (52 + (Wasm.IEEE64.exponent X - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [abs_of_pos (by linarith)] at hl
    have : value X * (2 / Real.pi) ≥ 2 ^ 21 * (2 / 3.15) := by
      have h2 : 2 / 3.15 ≤ 2 / Real.pi := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith
      nlinarith
    have := h.x2
    norm_num at *
    linarith
  -- `C = N · pio2_1` and `R1`.
  obtain ⟨-, -, -, -, -, -, hs1, -, -, -, -, -, -, -, -⟩ := consts_checked
  obtain ⟨hCf, hCs⟩ := mul_count F pio2_1 N 1686629713 1044 h.Ff consts_checked.1 h.Fv h.N1 h.N2
    hs1 (by norm_num) (by norm_num) (by norm_num)
  have hCv : value (Wasm.IEEE64.mul F pio2_1) = N * value pio2_1 := by
    rw [TrigSmall.value_of_scaled, hCs, hP1]
    push_cast
    rw [show (1074 : Nat) = 1044 + 30 by norm_num, pow_add]
    field_simp
  have hdX : (2 : Int) ^ 1022 ∣ Wasm.IEEE64.scaledValue X :=
    dvd_trans (pow_dvd_pow 2 (by omega)) (grid_dvd X)
  have hdC : (2 : Int) ^ 1022 ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul F pio2_1) := by
    rw [hCs]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _
  have hxc : |value X - value (Wasm.IEEE64.mul F pio2_1)| ≤ 1 := by
    rw [hCv]
    have e : value X - N * value pio2_1 = (value X - N * (Real.pi / 2)) +
        N * (Real.pi / 2 - value pio2_1) := by ring
    rw [e]
    have h1 : |(N : ℝ) * (Real.pi / 2 - value pio2_1)| ≤ 2 ^ 20 * (1 / 2 ^ 33 + 1 / 2 ^ 86) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]
      apply mul_le_mul hN2 _ (abs_nonneg _) (by positivity)
      rw [abs_le]
      constructor <;> linarith
    have := abs_add_le (value X - N * (Real.pi / 2)) (N * (Real.pi / 2 - value pio2_1))
    have : (2 : ℝ) ^ 20 * (1 / 2 ^ 33 + 1 / 2 ^ 86) ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨hRf, hRv⟩ := sub_exact X _ h.Xf hCf 1022 (by norm_num) hdX hdC (by
    have : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by
      rw [show (53 + 1022 : Nat) = 1074 + 1 by norm_num, pow_add]
      field_simp
    rw [this]
    linarith)
  rw [hCv] at hRv
  have hRd : (2 : Int) ^ 1009 ∣ Wasm.IEEE64.scaledValue (R1 X F) := by
    have hsd := scaled_of_value_sub X (Wasm.IEEE64.mul F pio2_1) (R1 X F) (by rw [R1, hRv, hCv])
    rw [hsd]
    exact dvd_sub (dvd_trans (pow_dvd_pow 2 (by norm_num)) hdX)
      (dvd_trans (pow_dvd_pow 2 (by norm_num)) hdC)
  -- `W1 ≈ N · pio2_1t`.
  have hFv : value F = N := by
    rw [TrigSmall.value_of_scaled, h.Fv]
    push_cast
    rw [mul_div_assoc, div_self (pow_ne_zero _ (by norm_num)), mul_one]
  have hP1t0 : 0 ≤ value pio2_1t := le_trans (by norm_num) hP1tl
  have hNt : |value F * value pio2_1t| = N * value pio2_1t := by
    rw [hFv, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hP1t0)]
  obtain ⟨hWf, hWe⟩ := mul_rel F pio2_1t h.Ff consts_checked.2.1 (by
      rw [hNt]
      have h900 : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 34 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
      calc (1 : ℝ) / 2 ^ 900 ≤ 1 * (1 / 2 ^ 34) := by rw [one_mul]; exact h900
        _ ≤ N * value pio2_1t := mul_le_mul hN1 hP1tl (by norm_num) (Nat.cast_nonneg _))
    (by
      rw [hNt]
      calc (N : ℝ) * value pio2_1t ≤ 2 ^ 20 * (1 / 2 ^ 33) :=
            mul_le_mul hN2 hP1tu hP1t0 (by norm_num)
        _ ≤ 2 ^ 100 := by norm_num)
  rw [hNt, hFv] at hWe
  refine ⟨hrl, hru, hNle, hE1, hE2, hRf, hRv, hRd, hWf, hWe, ?_⟩
  have e : value (R1 X F) - value (W1 F) - (value X - N * (Real.pi / 2)) =
      N * (Real.pi / 2 - value pio2_1 - value pio2_1t) + (N * value pio2_1t - value (W1 F)) := by
    rw [R1, hRv]
    ring
  rw [e]
  have h1 : |(N : ℝ) * (Real.pi / 2 - value pio2_1 - value pio2_1t)| ≤ N * (1 / 2 ^ 86) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [abs_le]
    constructor <;> linarith
  have h2 : |(N : ℝ) * value pio2_1t - value (W1 F)| ≤ N * (1 / 2 ^ 33) / 2 ^ 52 := by
    rw [abs_sub_comm]
    refine hWe.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hP1tu (by positivity)
  have := abs_add_le (N * (Real.pi / 2 - value pio2_1 - value pio2_1t))
    (N * value pio2_1t - value (W1 F))
  have h3 : (N : ℝ) * (1 / 2 ^ 86) + N * (1 / 2 ^ 33) / 2 ^ 52 ≤ value X / 2 ^ 84 := by
    have e2 : (N : ℝ) * (1 / 2 ^ 86) + N * (1 / 2 ^ 33) / 2 ^ 52 = N * (3 / 2 ^ 86) := by ring
    rw [e2]
    have h4 : (N : ℝ) * (3 / 2 ^ 86) ≤ 6 / 5 * value X * (3 / 2 ^ 86) :=
      mul_le_mul_of_nonneg_right hNle (by positivity)
    have e3 : 6 / 5 * value X * (3 / 2 ^ 86) = value X * (18 / 5 / 2 ^ 86) := by ring
    have e4 : value X / 2 ^ 84 = value X * (4 / 2 ^ 86) := by ring
    have h5 : value X * (18 / 5 / 2 ^ 86) ≤ value X * (4 / 2 ^ 86) :=
      mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
    linarith
  linarith

#print axioms mul_rel
#print axioms med_common
#print axioms exp_lower
#print axioms exp_upper
#print axioms pio2_values

end Verified.Examples.TrigMediumCases
