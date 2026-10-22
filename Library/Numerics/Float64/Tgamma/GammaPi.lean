import Library.Numerics.Float64.Trig.TrigPi

/-!
Bounds on `π` within `2 ^ -128` for the Taylor models of `lgamma`, from `TrigPi`'s enclosure by
Machin's formula: `piLo128 ≤ π ≤ piLo128 + 2 ^ -128`.  Mathlib's 20-digit bounds limit a model's
error to about `10 ^ -21`, which the error budget of `cr_lgamma` near its zeros cannot afford.
-/

namespace Library.Numerics.Float64.Tgamma.GammaPi

/-- `⌊π · 2 ^ 128⌋ / 2 ^ 128`. -/
def piLo128 : ℚ := 1069028584064966747859680373161870783300 / 2 ^ 128

/-- `piLo128 + 2 ^ -128`. -/
def piHi128 : ℚ := 1069028584064966747859680373161870783301 / 2 ^ 128

theorem checked : piLo128 ≤ Library.Numerics.Float64.Trig.TrigPi.piApprox - Library.Numerics.Float64.Trig.TrigPi.piError ∧
    Library.Numerics.Float64.Trig.TrigPi.piApprox + Library.Numerics.Float64.Trig.TrigPi.piError ≤ piHi128 := by
  decide +kernel

theorem pi_bounds128 : (piLo128 : ℝ) ≤ Real.pi ∧ Real.pi ≤ piHi128 := by
  obtain ⟨h1, h2⟩ := checked
  have h1' : (piLo128 : ℝ) ≤ ((Library.Numerics.Float64.Trig.TrigPi.piApprox - Library.Numerics.Float64.Trig.TrigPi.piError : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : ((Library.Numerics.Float64.Trig.TrigPi.piApprox + Library.Numerics.Float64.Trig.TrigPi.piError : ℚ) : ℝ) ≤ piHi128 := by exact_mod_cast h2
  exact ⟨h1'.trans Library.Numerics.Float64.Trig.TrigPi.pi_lower, Library.Numerics.Float64.Trig.TrigPi.pi_upper.trans h2'⟩

#print axioms pi_bounds128

end Library.Numerics.Float64.Tgamma.GammaPi
