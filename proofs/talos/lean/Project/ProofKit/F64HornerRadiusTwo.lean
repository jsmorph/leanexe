import Project.ProofKit.F64Approximation

namespace Project.ProofKit.F64Horner
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem step_two {a x c : UInt64} {p q bound error coefficientError : ℝ}
    (ha : Approximation a p bound error) (hc : Approximation c q 1 coefficientError)
    (hx : Finite x) (bx : |value x| ≤ 2) (hlo : 1 ≤ bound) (hhi : bound ≤ 128) :
    Approximation (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)
      (p*value x+q) (2*bound+3) (2*error+coefficientError+514*arithmeticEpsilon) := by
  have heps : 0 ≤ arithmeticEpsilon ∧ 514*arithmeticEpsilon ≤ 1 := by
    norm_num [arithmeticEpsilon]
  have hm := ha.mul (Approximation.exact x hx 2 bx) bx
    (bound := 2*bound) (by linarith)
    (lt_of_le_of_lt (by linarith : 2*bound ≤ 256) (by norm_num)) (by linarith)
  have hs := hm.add hc (bound := 2*bound+2) (by linarith)
    (lt_of_le_of_lt (by linarith : 2*bound+2 ≤ 258) (by norm_num)) (by nlinarith)
  exact hs.weaken (by nlinarith) (by nlinarith)

#print axioms step_two
end Project.ProofKit.F64Horner
