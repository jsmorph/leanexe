import Project.Beck.DigitMul
import Project.Beck.IntegerOrder

namespace Project.Beck.IntegerMul

open LeanExe.Examples.BeckExact IntegerAdd

theorem mul_correct (a b : Integer) (ha : Valid a) (hb : Valid b) :
    Valid (Integer.mul a b) ∧ value (Integer.mul a b) = value a * value b := by
  have product := DigitMul.mul_correct a.digits b.digits ha.1 hb.1
  refine ⟨make_valid _ _ product.1, ?_⟩
  rw [Integer.mul, make_value, product.2]
  cases signA : a.negative <;> cases signB : b.negative <;> simp [value, signA, signB]

#print axioms mul_correct

end Project.Beck.IntegerMul
