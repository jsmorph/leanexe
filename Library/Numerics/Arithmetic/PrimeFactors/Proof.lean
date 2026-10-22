import Library.Numerics.Arithmetic.PrimeFactors.Program
import Library.Numerics.Arithmetic.PrimeFactors.Spec
import Mathlib.Tactic.IntervalCases

namespace Library.Numerics.Arithmetic.PrimeFactors

theorem primeFactorsList_small {n : Nat} (h : n ≤ 1) : n.primeFactorsList = [] := by
  interval_cases n <;> simp

/-- `countFactors` with its three arguments as one tuple. -/
def countTuple (x : UInt64 × UInt64 × UInt64) : UInt64 := countFactors x.1 x.2.1 x.2.2

/-- The termination measure of `countFactors`. -/
def countMeasure (x : UInt64 × UInt64 × UInt64) : Nat :=
  x.1.toNat * 2 ^ 64 + (x.1.toNat - x.2.1.toNat)

theorem countFactors_stop {r d c : UInt64} (h1 : r ≤ 1 ∨ d ≤ 1) : countFactors r d c = c := by
  rw [countFactors, ite_eq_left h1]

theorem countFactors_last {r d c : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : r / d < d) :
    countFactors r d c = c + 1 := by
  rw [countFactors, ite_eq_right h1, ite_eq_left h2]

theorem countFactors_div {r d c : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d)
    (h3 : r % d = 0) : countFactors r d c = countFactors (r / d) d (c + 1) := by
  rw [countFactors, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]

theorem countFactors_next {r d c : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d)
    (h3 : ¬r % d = 0) : countFactors r d c = countFactors r (d + 1) c := by
  rw [countFactors, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- Past the first two tests, the divisor is at least 2 and at most `r / d`. -/
theorem countFactors_bounds {r d : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d) :
    2 ≤ d.toNat ∧ d.toNat ≤ r.toNat / d.toNat := by
  simp only [not_or, UInt64.not_le, UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at h2
  omega

theorem measure_div {r d c c' : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d) :
    countMeasure (r / d, d, c') < countMeasure (r, d, c) := by
  obtain ⟨hd, hle⟩ := countFactors_bounds h1 h2
  have hq : r.toNat / d.toNat ≤ r.toNat / 2 := Nat.div_le_div_left hd (by decide)
  have hm := Nat.mul_le_mul_right (2 ^ 64) (show r.toNat / d.toNat + 1 ≤ r.toNat by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  simp only [countMeasure, UInt64.toNat_div]
  omega

theorem divisor_succ {r d : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d) :
    (d + 1).toNat = d.toNat + 1 := by
  obtain ⟨hd, hle⟩ := countFactors_bounds h1 h2
  have hq : r.toNat / d.toNat ≤ r.toNat / 2 := Nat.div_le_div_left hd (by decide)
  have hr := r.toNat_lt
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem measure_next {r d c : UInt64} (h1 : ¬(r ≤ 1 ∨ d ≤ 1)) (h2 : ¬r / d < d) :
    countMeasure (r, d + 1, c) < countMeasure (r, d, c) := by
  obtain ⟨hd, hle⟩ := countFactors_bounds h1 h2
  have hq : r.toNat / d.toNat ≤ r.toNat / 2 := Nat.div_le_div_left hd (by decide)
  simp only [countMeasure, divisor_succ h1 h2]
  omega

/-- `countFactors` adds to `count` the number of prime factors of `remaining` when every prime
factor of `remaining` is at least `divisor`, which is at least 2. -/
theorem countFactors_eq (k : Nat) : ∀ (r d c : UInt64), countMeasure (r, d, c) = k →
    2 ≤ d.toNat → (∀ p, p.Prime → p ∣ r.toNat → d.toNat ≤ p) →
    countFactors r d c = c + UInt64.ofNat r.toNat.primeFactorsList.length := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro r d c hk hd hmin
  by_cases h1 : r ≤ 1 ∨ d ≤ 1
  · have hr1 : r.toNat ≤ 1 := by
      rcases h1 with h | h
      · exact UInt64.le_iff_toNat_le.mp h
      · have := UInt64.le_iff_toNat_le.mp h; simp at this; omega
    rw [countFactors_stop h1, primeFactorsList_small hr1]
    simp
  have hr2 : 2 ≤ r.toNat := by
    simp only [not_or, UInt64.not_le, UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1; omega
  have hdiv : (r / d).toNat = r.toNat / d.toNat := UInt64.toNat_div r d
  by_cases h2 : r / d < d
  · rw [countFactors_last h1 h2]
    have hlt : r.toNat / d.toNat < d.toNat := by
      rw [← hdiv]; exact UInt64.lt_iff_toNat_lt.mp h2
    have hprime : r.toNat.Prime := by
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hp := Nat.minFac_prime (show r.toNat ≠ 1 by omega)
      have hle := hmin _ hp (Nat.minFac_dvd _)
      have hdd : d.toNat * d.toNat ≤ r.toNat :=
        le_trans (Nat.mul_le_mul hle hle) (by rw [← pow_two]; exact hsq)
      have : d.toNat ≤ r.toNat / d.toNat := (Nat.le_div_iff_mul_le (by omega)).mpr hdd
      omega
    rw [Nat.primeFactorsList_prime hprime]
    simp
  by_cases h3 : r % d = 0
  · rw [countFactors_div h1 h2 h3]
    have hdvd : d.toNat ∣ r.toNat := by
      apply Nat.dvd_of_mod_eq_zero
      have := congrArg UInt64.toNat h3
      rwa [UInt64.toNat_mod] at this
    have hmf : r.toNat.minFac = d.toNat :=
      le_antisymm (Nat.minFac_le_of_dvd hd hdvd)
        (hmin _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _))
    have hlist : r.toNat.primeFactorsList = d.toNat :: (r.toNat / d.toNat).primeFactorsList := by
      obtain ⟨m, hm⟩ : ∃ m, r.toNat = m + 2 := ⟨r.toNat - 2, by omega⟩
      rw [hm, Nat.primeFactorsList_add_two, ← hm, hmf]
    have hrec := ih _ (hk ▸ measure_div (c' := c + 1) h1 h2) (r / d) d (c + 1) rfl hd
      (fun p hp hpd => hmin p hp (by
        rw [hdiv] at hpd; exact Nat.dvd_trans hpd (Nat.div_dvd_of_dvd hdvd)))
    rw [hrec, hlist, hdiv, List.length_cons, UInt64.ofNat_add]
    simp only [UInt64.ofNat_one]
    ac_rfl
  · rw [countFactors_next h1 h2 h3]
    have hd1 := divisor_succ h1 h2
    exact ih _ (hk ▸ measure_next h1 h2) r (d + 1) c rfl (by omega) (fun p hp hpd => by
        have := hmin p hp hpd
        rw [hd1]
        rcases Nat.lt_or_eq_of_le this with h | h
        · omega
        · exfalso
          apply h3
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_mod, h]
          simpa using Nat.mod_eq_zero_of_dvd hpd)

/-- The program computes the specification on every word. -/
theorem compute_eq (n : UInt64) : compute n = expected n := by
  rw [compute, countFactors_eq _ n 2 0 rfl (by decide) fun p hp _ => hp.two_le]
  simp [expected]

end Library.Numerics.Arithmetic.PrimeFactors
