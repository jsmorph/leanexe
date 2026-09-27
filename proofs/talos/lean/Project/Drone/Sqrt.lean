import LeanExe.Examples.Drone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Project.Drone.Sqrt
open LeanExe.Examples.Drone

private theorem midpoint_nat (lo hi : UInt64) (hl : lo.toNat ≤ hi.toNat)
    (hh : hi.toNat ≤ 65536) :
    ((lo+hi)/2).toNat = (lo.toNat+hi.toNat)/2 := by
  rw [UInt64.toNat_div, UInt64.toNat_add]
  change ((lo.toNat+hi.toNat) % 18446744073709551616)/2 = _
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem square_nat (x : UInt64) (hx : x.toNat ≤ 65536) :
    (x*x).toNat = x.toNat*x.toNat := by
  rw [UInt64.toNat_mul]
  apply Nat.mod_eq_of_lt
  have : x.toNat*x.toNat ≤ 65536*65536 := Nat.mul_self_le_mul_self hx
  norm_num
  omega

private theorem increment_nat (x : UInt64) (hx : x.toNat ≤ 65536) :
    (x+1).toNat = x.toNat+1 := by
  rw [UInt64.toNat_add]
  change (x.toNat+1) % 18446744073709551616 = x.toNat+1
  exact Nat.mod_eq_of_lt (by omega)

/-- The search maintains a bracket containing the least square upper bound.
The width hypothesis makes the fuel a proved termination budget. -/
theorem search_correct (fuel : Nat) (n lo hi : UInt64)
    (hlh : lo.toNat ≤ hi.toNat) (hhi : hi.toNat ≤ 65536)
    (hupper : n.toNat ≤ hi.toNat*hi.toNat)
    (hlower : ∀ j, j < lo.toNat → j*j < n.toNat)
    (hwidth : hi.toNat-lo.toNat < 2^fuel) :
    (sqrtSearch fuel n lo hi).toNat ≤ hi.toNat ∧
    n.toNat ≤ (sqrtSearch fuel n lo hi).toNat*(sqrtSearch fuel n lo hi).toNat ∧
    ∀ j, j < (sqrtSearch fuel n lo hi).toNat → j*j < n.toNat := by
  induction fuel generalizing lo hi with
  | zero =>
    have heq : lo.toNat = hi.toNat := by simpa using (show lo.toNat = hi.toNat by
      simp only [pow_zero] at hwidth
      omega)
    simp only [sqrtSearch]
    exact ⟨hlh, heq ▸ hupper, hlower⟩
  | succ fuel ih =>
    by_cases hlt : lo < hi
    · have hltN : lo.toNat < hi.toNat := (UInt64.lt_iff_toNat_lt).mp hlt
      let mid := (lo+hi)/2
      have hm : mid.toNat = (lo.toNat+hi.toNat)/2 := midpoint_nat lo hi hlh hhi
      have hml : lo.toNat ≤ mid.toNat := by omega
      have hmh : mid.toNat < hi.toNat := by omega
      have hmb : mid.toNat ≤ 65536 := by omega
      have hsq := square_nat mid hmb
      have hinc := increment_nat mid hmb
      have hpow : 2^(fuel+1) = 2^fuel*2 := by rw [pow_succ]
      rw [hpow] at hwidth
      simp only [sqrtSearch, if_pos hlt]
      change (if mid*mid < n then sqrtSearch fuel n (mid+1) hi
        else sqrtSearch fuel n lo mid).toNat ≤ hi.toNat ∧ _
      by_cases htest : mid*mid < n
      · rw [if_pos htest]
        have htestN : mid.toNat*mid.toNat < n.toNat := by
          have := (UInt64.lt_iff_toNat_lt).mp htest
          rwa [hsq] at this
        apply ih (mid+1) hi (by omega) hhi hupper
        · intro j hj
          have hjm : j ≤ mid.toNat := by omega
          exact lt_of_le_of_lt (Nat.mul_self_le_mul_self hjm) htestN
        · omega
      · rw [if_neg htest]
        have htestN : n.toNat ≤ mid.toNat*mid.toNat := by
          have : ¬(mid*mid).toNat < n.toNat := by
            simpa only [← UInt64.lt_iff_toNat_lt] using htest
          rw [hsq] at this
          omega
        obtain ⟨hr, hu, hl⟩ := ih lo mid hml hmb htestN hlower (by omega)
        exact ⟨by omega, hu, hl⟩
    · simp only [sqrtSearch, if_neg hlt]
      have heq : lo.toNat = hi.toNat := by
        rw [UInt64.lt_iff_toNat_lt] at hlt
        omega
      exact ⟨hlh, heq ▸ hupper, hlower⟩

/-- The executable UInt64 square root is the exact ceiling square root,
not merely a conservative bound, throughout its documented input range. -/
theorem ceilSqrt_correct (n : UInt64) (hn : n.toNat < 4294967296) :
    (ceilSqrt n).toNat ≤ 65536 ∧
    n.toNat ≤ (ceilSqrt n).toNat*(ceilSqrt n).toNat ∧
    ∀ j, j < (ceilSqrt n).toNat → j*j < n.toNat := by
  apply search_correct 17 n 0 65536
  · decide
  · decide
  · change n.toNat ≤ 4294967296
    omega
  · intro j hj
    simp at hj
  · decide

#print axioms ceilSqrt_correct
end Project.Drone.Sqrt
