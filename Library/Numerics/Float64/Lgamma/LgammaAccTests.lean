import Library.Numerics.Float64.Lgamma.LgammaAccWin

/-!
The tests of `Lgamma.accurate` on the reals.  `win_test` reads the window test
`(x - c).abs < 0.25` at `x ≥ 1/4` as `|x - c| < 1/4`: from `c/2` to `2 c` the subtraction is exact
(Sterbenz), and elsewhere `|x - c| ≥ 1/2`, so the rounded difference is at least `1/2 - 2^-54`.
`lt_test` reads a comparison with a literal.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccTests
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx LgammaAccWin

set_option exponentiation.threshold 4096

theorem c025 : Finite (0.25 : Float).toBits ∧ value (0.25 : Float).toBits = 1 / 4 := by
  have h := lit 0.25 0x3FD0000000000000 (1 / 4) rfl (by decide) (by decide +kernel)
  push_cast at h
  exact h

theorem c00 : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 :=
  ⟨LgammaAccAdd.zero_finite, LgammaAccAdd.zero_value⟩

/-- A comparison of finite doubles as a comparison of their values. -/
theorem lt_test (a b : Float) (va vb : ℝ) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hva : value a.toBits = va) (hvb : value b.toBits = vb) : a < b ↔ va < vb := by
  rw [F64UpperWord.float_lt_iff _ _ ha hb, hva, hvb]

/-- **The window test** about `c`, at `x ≥ 1/4`. -/
theorem win_test (x c : Float) (cv : ℝ) (hx : Finite x.toBits) (hc : Finite c.toBits)
    (hcv : value c.toBits = cv) (hc1 : cv = 1 / 2 ∨ 1 ≤ cv) (hc2 : cv ≤ 4)
    (hx0 : 1 / 4 ≤ value x.toBits) (hxb : value x.toBits ≤ 2 ^ 1000) :
    (x - c).abs < 0.25 ↔ (cv - 1 / 4 < value x.toBits ∧ value x.toBits < cv + 1 / 4) := by
  have hc12 : 1 / 2 ≤ cv := by rcases hc1 with h | h <;> linarith
  constructor
  · intro h
    have hdf : Finite (x - c).toBits := by
      have := fapprox_sub (approx_self _ hx) (approx_self _ hc) (|value x.toBits - value c.toBits|)
        (by simp) (by rw [hcv, abs_lt]; constructor <;>
          linarith [(by norm_num : (2 : ℝ) ^ 1000 + 4 < 2 ^ 1023)])
      exact this.1
    obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float _ hdf
    have h' := (lt_test _ _ _ _ haf c025.1 hav c025.2).mp h
    by_cases hS : cv / 2 ≤ value x.toBits ∧ value x.toBits ≤ 2 * cv
    · obtain ⟨-, hv⟩ := sub_exact x c hx hc
        (by rw [hcv, abs_of_nonneg (by linarith : (0 : ℝ) ≤ value x.toBits), abs_le]
            constructor <;> linarith [hS.1, hS.2])
        (by rw [hcv, abs_of_nonneg (by linarith : (0 : ℝ) ≤ cv), abs_le]
            constructor <;> linarith [hS.1, hS.2])
        (by rw [hcv, abs_of_nonneg (by linarith)]; linarith [(by norm_num : (4 : ℝ) < 2 ^ 1021)])
      rw [hv, hcv, abs_lt] at h'
      constructor <;> linarith [h'.1, h'.2]
    · exfalso
      have hy : 1 / 2 ≤ |value x.toBits - cv| := by
        rcases not_and_or.mp hS with h1 | h1
        · push_neg at h1
          rcases hc1 with hc | hc
          · rw [hc] at h1; linarith
          · rw [abs_of_neg (by linarith)]; linarith
        · push_neg at h1
          rw [abs_of_pos (by linarith)]; linarith
      have ha := fapprox_sub (approx_self _ hx) (approx_self _ hc)
        (|value x.toBits - value c.toBits|) (by simp)
        (by rw [hcv, abs_lt]; constructor <;>
          linarith [(by norm_num : (2 : ℝ) ^ 1000 + 4 < 2 ^ 1023)])
      obtain ⟨-, he⟩ := ha
      rw [hcv] at he
      simp only [add_zero, zero_add] at he
      have := abs_sub_abs_le_abs_sub (value x.toBits - cv) (value (x - c).toBits)
      rw [abs_sub_comm (value x.toBits - cv)] at this
      have : |value x.toBits - cv| / 2 ^ 53 ≤ |value x.toBits - cv| / 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith
  · rintro ⟨h1, h2⟩
    obtain ⟨hdf, hdv, -⟩ := win_sub x c cv hx hc hcv hc12 hc2 h1 h2
    obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float _ hdf
    rw [lt_test _ _ _ _ haf c025.1 hav c025.2, hdv, abs_lt]
    constructor <;> linarith

end Library.Numerics.Float64.Lgamma.LgammaAccTests
