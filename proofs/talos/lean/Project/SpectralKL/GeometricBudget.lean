import Project.SpectralKL.MatrixAdaptive

namespace Project.SpectralKL.GeometricBudget

/-- Increasing search: each call consumes one step and updates the exact error bound. -/
def depth (rho bound budget : ℚ) : Nat → Nat
  | 0 => 0
  | fuel+1 => if bound ≤ budget then 0 else 1+depth rho (rho*bound) budget fuel

theorem depth_le (rho bound budget : ℚ) (fuel : Nat) :
    depth rho bound budget fuel ≤ fuel := by
  induction fuel generalizing bound with
  | zero => simp [depth]
  | succ fuel ih =>
    simp only [depth]
    split
    · omega
    · have h := ih (rho*bound); omega

theorem depth_budget (rho bound budget : ℚ) (fuel : Nat)
    (h : rho^fuel*bound ≤ budget) :
    rho^(depth rho bound budget fuel)*bound ≤ budget := by
  induction fuel generalizing bound with
  | zero => simpa [depth] using h
  | succ fuel ih =>
    simp only [depth]
    split
    · rename_i hb; simpa using hb
    · have hn : rho^fuel*(rho*bound) ≤ budget := by
        simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using h
      simpa [pow_add,mul_assoc,mul_comm,mul_left_comm] using ih (rho*bound) hn

/-- An elementary geometric bound gives a finite search budget without logarithms. -/
theorem geometric_bound (rho : ℚ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (k : Nat) :
    rho^k*(1+(k:ℚ)*(1-rho)) ≤ 1 := by
  have ht : 0 ≤ 1-rho := sub_nonneg.mpr h1
  induction k with
  | zero => simp
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left ih h0
    have hp : rho^(k+1) ≤ 1 := pow_le_one₀ h0 h1
    have hh := mul_le_mul_of_nonneg_right hp ht
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    rw [pow_succ] at hh
    nlinarith

def fuel (rho bound budget : ℚ) : Nat := ⌈bound/(budget*(1-rho))⌉₊

theorem fuel_budget (rho bound budget : ℚ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (he : 0 < budget) : rho^(fuel rho bound budget)*bound ≤ budget := by
  let k := fuel rho bound budget
  have ht : 0 < 1-rho := sub_pos.mpr h1
  have hc : bound/(budget*(1-rho)) ≤ (k:ℚ) := Nat.le_ceil _
  have hb : bound ≤ (k:ℚ)*(budget*(1-rho)) := (div_le_iff₀ (mul_pos he ht)).mp hc
  have hs := geometric_bound rho h0 h1.le k
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg h0 k)
  have hu := mul_le_mul_of_nonneg_left hs he.le
  have hp : 0 ≤ budget*rho^k := mul_nonneg he.le (pow_nonneg h0 k)
  change rho^k*bound ≤ budget
  nlinarith

def select (rho bound budget : ℚ) : Nat := depth rho bound budget (fuel rho bound budget)

theorem select_budget (rho bound budget : ℚ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (he : 0 < budget) : rho^(select rho bound budget)*bound ≤ budget :=
  depth_budget rho bound budget _ (fuel_budget rho bound budget h0 h1 he)

#print axioms select_budget
end Project.SpectralKL.GeometricBudget
