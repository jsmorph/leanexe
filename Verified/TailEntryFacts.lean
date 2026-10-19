import Verified.TailState
import Verified.TailBound

namespace Verified

open Wasm

theorem LocalsHold.afterParamCopy {tys : List ValueType} {s s' : Locals}
    {p h : Nat} {ws : List Value} (length : ws.length = tys.length)
    (room : p + ws.length ≤ h) (half : s'.half = h)
    (params : ∀ j (hj : j < ws.length), s.get (p + j) = some ws[j])
    (low : ∀ j < h + p, s'.get j = s.get j)
    (copy : ∀ q, p ≤ q → q < p + tys.length → tys.getD (q - p) .i64 = .f64 →
      s'.get (q + h) = s.get q) : LocalsHold s' p tys ws := by
  intro k hk
  rw [half]
  by_cases hf : tys.getD k .i64 = .f64
  · rw [hf]
    change s'.get (p + k + h) = some ws[k]
    rw [copy (p + k) (by omega) (by omega) (by simpa using hf)]
    exact params k hk
  · have index : slotIndex h (p + k) (tys.getD k .i64) = p + k := by
      generalize tys.getD k .i64 = ty at hf ⊢
      cases ty <;> first | rfl | exact absurd rfl hf
    rw [index, low (p + k) (by omega)]
    exact params k hk

theorem TailFunc.function_numParams (func : TailFunc S) (typeIdx : Nat) :
    (func.function typeIdx).numParams = (if func.depth then 1 else 0) + widthSum func.params := by
  simp only [TailFunc.function, Function.numParams, codeParams, List.length_append,
    flatMap_types_length]
  cases func.depth <;> simp

theorem TailFunc.fits_of_depthCalls (func : TailFunc S) (funs : Funs S) (fits : Fits S)
    (decreases : func.Decreases funs) (hd : func.depth = false) (state : Env func.params) :
    func.fits funs fits state = true := by
  induction state using (measure (func.rank funs)).wf.induction with
  | h state ih =>
    rw [func.fits_eq funs fits decreases state,
      func.body.fits_of_depthCalls funs fits hd state, Bool.true_and]
    cases step : func.body.denote funs state with
    | inl next => exact ih next (decreases state next step)
    | inr value => rfl

#print axioms LocalsHold.afterParamCopy
#print axioms TailFunc.function_numParams
#print axioms TailFunc.fits_of_depthCalls

end Verified
