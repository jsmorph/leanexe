import Project.Drone.ExecutionHistoryInvariant
import Project.Drone.ExecutionUnwindInvariant

namespace Project.Drone.Execution

/-- A conservative allocation budget, counting every allocation even when free blocks are reused. -/
def computeCost (size : Nat) : Nat :=
  56 + (advanceCost 45 0 + (56 + (historyCost (size - 1) 0 + (56 + unwindCost size 0))))

theorem appendCost_formula (count size : Nat) :
    appendCost count size = count * (60 + 8 * size) + 4 * count * count := by
  induction count generalizing size with
  | zero => simp [appendCost]
  | succ count ih => rw [appendCost, ih]; simp only [pushCost]; ring

theorem advanceCost_formula (count size : Nat) :
    advanceCost count size = count * (180 + 24 * size) + 36 * count * count := by
  induction count generalizing size with
  | zero => simp [advanceCost]
  | succ count ih => rw [advanceCost, ih]; simp only [rowPushCost, pushCost]; ring

theorem historyCost_formula (count size : Nat) :
    historyCost count size = count * (83756 + 360 * size) + 8100 * count * count := by
  induction count generalizing size with
  | zero => simp [historyCost]
  | succ count ih => rw [historyCost, ih, advanceCost_formula, appendCost_formula]; ring

theorem unwindCost_formula (count size : Nat) :
    unwindCost count size = 56 + 8 * size + count * (136 + 16 * size) + 16 * count * count := by
  induction count generalizing size with
  | zero => simp [unwindCost, reverseCost]; omega
  | succ count ih => rw [unwindCost, ih]; simp only [pushCost]; ring

theorem computeCost_bound (size : Nat) (hSize : size ≤ 64) : computeCost size ≤ 37580992 := by
  rw [computeCost, advanceCost_formula, historyCost_formula, unwindCost_formula]
  have hPrev : size - 1 ≤ 63 := by omega
  have hSquare : size * size ≤ 64 * 64 := Nat.mul_le_mul hSize hSize
  have hPrevSquare : (size - 1) * (size - 1) ≤ 63 * 63 := Nat.mul_le_mul hPrev hPrev
  nlinarith

theorem computeCost_empty_budget (size : Nat) : 56 ≤ computeCost size := by
  unfold computeCost
  omega

#print axioms computeCost_bound
end Project.Drone.Execution
