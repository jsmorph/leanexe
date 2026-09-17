import Project.ExpNeg.Model
import Project.ExpNeg.Real
import Project.ExpNeg.Coefficients
import Project.ExpSmall.Numerical

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096

theorem polynomial_roundoff (x : UInt64) (hx : Finite x) (bx : |value x| ≤ 1) :
    Finite (polynomial x) ∧
      |value (polynomial x)-polynomialReal (value x)| ≤ 19*arithmeticEpsilon := by
  have h17 := step_scaled (resultBound := (2 / 355687428096000)) coefficient18 coefficient17 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h16 := step_scaled (resultBound := (2 / 20922789888000)) h17 coefficient16 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h15 := step_scaled (resultBound := (2 / 1307674368000)) h16 coefficient15 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h14 := step_scaled (resultBound := (2 / 87178291200)) h15 coefficient14 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h13 := step_scaled (resultBound := (2 / 6227020800)) h14 coefficient13 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h12 := step_scaled (resultBound := (2 / 479001600)) h13 coefficient12 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h11 := step_scaled (resultBound := (2 / 39916800)) h12 coefficient11 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h10 := step_scaled (resultBound := (2 / 3628800)) h11 coefficient10 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h9 := step_scaled (resultBound := (2 / 362880)) h10 coefficient9 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h8 := step_scaled (resultBound := (2 / 40320)) h9 coefficient8 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h7 := step_scaled (resultBound := (2 / 5040)) h8 coefficient7 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h6 := step_scaled (resultBound := (2 / 720)) h7 coefficient6 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h5 := step_scaled (resultBound := (2 / 120)) h6 coefficient5 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h4 := step_scaled (resultBound := (2 / 24)) h5 coefficient4 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h3 := step_scaled (resultBound := (2 / 6)) h4 coefficient3 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h2 := step_scaled (resultBound := (2 / 2)) h3 coefficient2 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h1 := step_scaled (resultBound := 3) h2 coefficient1 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have h0 := step_scaled (resultBound := 5) h1 coefficient0 hx bx
    (by norm_num [minNormal64]) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  refine ⟨h0.finite, ?_⟩
  have he := h0.accuracy
  change |value (polynomial x)-polynomialReal (value x)| ≤ _ at he
  exact he.trans (by norm_num [arithmeticEpsilon])

theorem polynomial_error (x : UInt64) (hx : Finite x) (bx : |value x| ≤ 1) :
    Finite (polynomial x) ∧
      |value (polynomial x)-Real.exp (value x)| ≤ 20*arithmeticEpsilon := by
  have hp := polynomial_roundoff x hx bx
  refine ⟨hp.1, (abs_sub_le _ _ _).trans ((add_le_add hp.2 (polynomialReal_error _ bx)).trans ?_)⟩
  norm_num [arithmeticEpsilon]

#print axioms polynomial_roundoff
#print axioms polynomial_error
end Project.ExpNeg
