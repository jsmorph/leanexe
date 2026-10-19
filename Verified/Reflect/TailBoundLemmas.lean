import Verified.TailAllocExpand
import Verified.TailTransport

namespace Verified

theorem Tail.costAt_zero (step : α → Sum α β) (fuel : Nat) (state : α) :
    costAt step (fun _ => 0) fuel state = 0 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [costAt, Nat.zero_add]
    cases step state <;> simp [ih]

theorem TailFunc.bound_native {α β : Type} (func : TailFunc S)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (flatten : α → Env func.params) (flattenResult : β → func.result.denote)
    (step : α → Sum α β) (rank charge : α → Nat)
    (meaning : ∀ state, func.body.denote funs (flatten state) =
      Sum.map flatten flattenResult (step state))
    (rankEq : ∀ state, func.rank funs (flatten state) = rank state)
    (chargeEq : ∀ state,
      func.body.allocs funs flags bounds func.modes (func.paidParams flags)
        (entryModes func.params func.modes) (func.paidParams flags) (flatten state) = charge state)
    (state : α) :
    func.bound funs flags bounds (flatten state) = Tail.costAt step charge (rank state + 1) state := by
  unfold TailFunc.bound
  rw [rankEq]
  exact Tail.costAt_transport flatten flattenResult meaning charge _ chargeEq _ state

theorem TailFunc.fits_native {α β : Type} (func : TailFunc S)
    (funs : Funs S) (fits : Fits S)
    (flatten : α → Env func.params) (flattenResult : β → func.result.denote)
    (step : α → Sum α β) (rank : α → Nat) (valid : α → Bool)
    (meaning : ∀ state, func.body.denote funs (flatten state) =
      Sum.map flatten flattenResult (step state))
    (rankEq : ∀ state, func.rank funs (flatten state) = rank state)
    (validEq : ∀ state, func.body.fits funs fits (flatten state) = valid state)
    (state : α) :
    func.fits funs fits (flatten state) = Tail.fitsAt step valid (rank state + 1) state := by
  unfold TailFunc.fits
  rw [rankEq]
  exact Tail.fitsAt_transport flatten flattenResult meaning valid _ validEq _ state

#print axioms Tail.costAt_zero
#print axioms TailFunc.bound_native
#print axioms TailFunc.fits_native

end Verified
