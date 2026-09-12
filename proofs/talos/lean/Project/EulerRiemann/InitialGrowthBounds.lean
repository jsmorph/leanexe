import Project.EulerRiemann.InitialAllocationOrder

namespace Project.EulerRiemann.Execution

def initialRemainingBytes (count fuel target : Nat) : Nat :=
  168 * (1048576 - count) + 112 * fuel + 48 + initialBytes target

theorem initial_growth_count_bound (rounds : Nat) (hRounds : rounds ≤ 20) :
    2 ^ rounds ≤ 1048576 := by
  calc
    2 ^ rounds ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hRounds
    _ = 1048576 := by norm_num

theorem initial_growth_double_bound (rounds : Nat) (hRounds : rounds < 20) :
    2 ^ rounds + 2 ^ rounds ≤ 1048576 := by
  simpa only [Nat.pow_succ, Nat.mul_two] using
    initial_growth_count_bound (rounds + 1) (by omega)

theorem initial_growth_index_bound (rounds index : Nat)
    (hRounds : rounds < 20) (hIndex : index < 2 ^ rounds) :
    index + 2 ^ rounds < 1048576 := by
  have hDouble := initial_growth_double_bound rounds hRounds
  omega

theorem initial_remaining_step (count fuel target : Nat)
    (hCount : count + count ≤ 1048576) (hFuel : 0 < fuel) :
    initialRemainingBytes count fuel target =
      (48 + initialBytes count) + (48 + initialBytes (count + count)) +
        initialRemainingBytes (count + count) (fuel - 1) target := by
  simp only [initialRemainingBytes, initialBytes]
  omega

theorem initial_growth_allocations_fit (top count fuel target limit : Nat)
    (hCount : count + count ≤ 1048576) (hFuel : 0 < fuel)
    (hReserve : top + initialRemainingBytes count fuel target ≤ limit) :
    top + 48 + initialBytes count ≤ limit ∧
      top + (48 + initialBytes count) + 48 + initialBytes (count + count) ≤ limit := by
  rw [initial_remaining_step count fuel target hCount hFuel] at hReserve
  omega

theorem initial_growth_reserve_step (top count fuel target limit : Nat)
    (hCount : count + count ≤ 1048576) (hFuel : 0 < fuel)
    (hReserve : top + initialRemainingBytes count fuel target ≤ limit) :
    (top + (48 + initialBytes count) + (48 + initialBytes (count + count))) +
      initialRemainingBytes (count + count) (fuel - 1) target ≤ limit := by
  rw [initial_remaining_step count fuel target hCount hFuel] at hReserve
  omega

theorem initial_extract_allocation_fits (top count fuel target limit : Nat)
    (hReserve : top + initialRemainingBytes count fuel target ≤ limit) :
    top + 48 + initialBytes target ≤ limit := by
  unfold initialRemainingBytes at hReserve
  omega

theorem initial_remaining_bound (target : Nat) (hTarget : target ≤ 640000) :
    initialRemainingBytes 1 20 target ≤ 212002896 := by
  simp only [initialRemainingBytes, initialBytes]
  omega

#print axioms initial_growth_count_bound
#print axioms initial_growth_double_bound
#print axioms initial_growth_index_bound
#print axioms initial_remaining_step
#print axioms initial_growth_allocations_fit
#print axioms initial_growth_reserve_step
#print axioms initial_extract_allocation_fits
#print axioms initial_remaining_bound

end Project.EulerRiemann.Execution
