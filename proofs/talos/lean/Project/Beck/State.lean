import Project.Beck.Boundary

namespace Project.Beck.State

open LeanExe.Examples.Beck

structure Supported (input : Input) : Prop where
  capacity : input.jobs ≤ 6
  binary : ∀ job < input.jobs, ∀ category < input.categories,
    input.incidence[job * input.categories + category]! = 0 ∨
      input.incidence[job * input.categories + category]! = 1
  overlap : ∀ job : Fin input.jobs,
    (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap

structure Valid (jobs : Nat) (x : Point) (round : Nat) : Prop where
  size : x.numerators.size = jobs
  positive : 0 < x.denominator.toNat
  denominator : x.denominator.toNat ≤ 120 ^ round
  cube : ∀ job < jobs, |Arithmetic.value x.numerators[job]!| ≤ (x.denominator.toNat : ℤ)

def coordinate (x : Point) (job : Nat) : ℚ :=
  (Arithmetic.value x.numerators[job]! : ℚ) / x.denominator.toNat

theorem frozen_iff (x : Point) (job : Nat) :
    frozen x job = true ↔ |Arithmetic.value x.numerators[job]!| = (x.denominator.toNat : ℤ) := by
  simp only [frozen, beq_iff_eq, ← UInt64.toNat_inj]
  constructor
  · intro h
    exact (Arithmetic.magnitude_exact _).symm.trans (congrArg Int.ofNat h)
  · intro h
    exact_mod_cast (Arithmetic.magnitude_exact _).trans h

theorem initial (jobs : Nat) : Valid jobs ⟨1, Array.replicate jobs 0⟩ 0 := by
  constructor
  · simp
  · change 0 < (1 : UInt64).toNat
    decide
  · simp
  · intro job hj
    simp [getElem!_pos (Array.replicate jobs (0 : UInt64)) job (by simpa), Arithmetic.value]

theorem gap_exact (D p d : UInt64) (bound : D.toNat ≤ 120 ^ 5)
    (cube : |Arithmetic.value p| ≤ (D.toNat : ℤ)) :
    ((gap D p d).toNat : ℤ) =
      if negative d then (D.toNat : ℤ) + Arithmetic.value p else (D.toNat : ℤ) - Arithmetic.value p := by
  have dSmall : D.toNat < 9223372036854775808 := by norm_num at bound; omega
  have dValue := Arithmetic.value_small D dSmall
  have cube' := abs_le.mp cube
  have addFits : Arithmetic.Fits (Arithmetic.value D + Arithmetic.value p) := by
    rw [dValue]
    dsimp [Arithmetic.Fits]
    norm_num at bound
    omega
  have subFits : Arithmetic.Fits (Arithmetic.value D - Arithmetic.value p) := by
    rw [dValue]
    dsimp [Arithmetic.Fits]
    norm_num at bound
    omega
  unfold gap
  split
  · have eq := Arithmetic.add_exact D p addFits
    have nonnegative : 0 ≤ Arithmetic.value (D + p) := by rw [eq, dValue]; omega
    rw [← Arithmetic.value_nonnegative _ nonnegative, eq, dValue]
  · have eq := Arithmetic.sub_exact D p subFits
    have nonnegative : 0 ≤ Arithmetic.value (D - p) := by rw [eq, dValue]; omega
    rw [← Arithmetic.value_nonnegative _ nonnegative, eq, dValue]

theorem gap_bounds (D p d : UInt64) (bound : D.toNat ≤ 120 ^ 5)
    (cube : |Arithmetic.value p| ≤ (D.toNat : ℤ)) :
    (gap D p d).toNat ≤ 2 * D.toNat := by
  have eq := gap_exact D p d bound cube
  have cube' := abs_le.mp cube
  split_ifs at eq <;> omega

theorem gap_positive (x : Point) (job : Nat) (d : UInt64)
    (bound : x.denominator.toNat ≤ 120 ^ 5)
    (cube : |Arithmetic.value x.numerators[job]!| ≤ (x.denominator.toNat : ℤ))
    (live : frozen x job = false) : 0 < (gap x.denominator x.numerators[job]! d).toNat := by
  have strict : |Arithmetic.value x.numerators[job]!| < (x.denominator.toNat : ℤ) := by
    have different : |Arithmetic.value x.numerators[job]!| ≠ (x.denominator.toNat : ℤ) := by
      intro equal
      have := (frozen_iff x job).mpr equal
      simp [live] at this
    omega
  have cube' := abs_lt.mp strict
  have eq := gap_exact x.denominator x.numerators[job]! d bound cube
  split_ifs at eq <;> omega

theorem update_exact (D p d speed distance : UInt64)
    (hD : 0 < D.toNat ∧ D.toNat ≤ 120 ^ 5)
    (hp : |Arithmetic.value p| ≤ (D.toNat : ℤ)) (hd : |Arithmetic.value d| ≤ 120)
    (hs : 0 < speed.toNat ∧ speed.toNat ≤ 120) (hg : distance.toNat ≤ 2 * D.toNat) :
    (D * speed).toNat = D.toNat * speed.toNat ∧
      Arithmetic.value (p * speed + distance * d) =
        Arithmetic.value p * speed.toNat + distance.toNat * Arithmetic.value d := by
  have bounds := Arithmetic.update_bounds (D.toNat : ℤ) (Arithmetic.value p) (Arithmetic.value d)
    (speed.toNat : ℤ) (distance.toNat : ℤ)
    (by exact_mod_cast hD) hp hd (by exact_mod_cast hs)
    ⟨by positivity, by exact_mod_cast hg⟩
  have speedValue := Arithmetic.value_small speed (by omega)
  have distanceValue := Arithmetic.value_small distance (by norm_num at hD; omega)
  have pProduct : Arithmetic.value (p * speed) = Arithmetic.value p * speed.toNat := by
    rw [Arithmetic.mul_exact _ _ (by rw [speedValue]; exact bounds.2.1), speedValue]
  have dProduct : Arithmetic.value (distance * d) = distance.toNat * Arithmetic.value d := by
    rw [Arithmetic.mul_exact _ _ (by rw [distanceValue]; exact bounds.2.2.1), distanceValue]
  refine ⟨Boundary.product_exact D speed (by omega) hs.2, ?_⟩
  rw [Arithmetic.add_exact _ _ (by rw [pProduct, dProduct]; exact bounds.2.2.2.1), pProduct, dProduct]

end Project.Beck.State
