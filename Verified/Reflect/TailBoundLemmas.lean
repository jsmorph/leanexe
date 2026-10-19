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

namespace Reflect

theorem bounds_get_hereTail (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (hd : f.depth = false)
    (env : Env f.params) :
    (Prog.boundsAt (.consTail f rest) (.cons F fs) k).get .here env =
      f.bound fs rest.flags (rest.boundsAt fs 0) env := by
  rw [Prog.boundsAt_consTail_here, hd]
  rfl

theorem bounds_get_hereTailDepth (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (hd : f.depth = true)
    (env : Env f.params) :
    (Prog.boundsAt (.consTail f rest) (.cons F fs) k).get .here env =
      f.boundAt fs rest.flags (rest.boundsAt fs) k env := by
  rw [Prog.boundsAt_consTail_here, hd]
  rfl

theorem bounds_get_thereTail {g : Sig} (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.boundsAt (.consTail f rest) (.cons F fs) k).get (.there v) env =
      (rest.boundsAt fs k).get v env := rfl

theorem fits_get_hereTailDepth (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (hd : f.depth = true)
    (env : Env f.params) :
    (Prog.fitsAt (.consTail f rest) (.cons F fs) k).get .here env =
      f.fitsAt fs (rest.fitsAt fs) k env := by
  rw [Prog.fitsAt_consTail_here, hd]
  rfl

theorem fits_get_thereTail {g : Sig} (f : TailFunc S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.fitsAt (.consTail f rest) (.cons F fs) k).get (.there v) env =
      (rest.fitsAt fs k).get v env := rfl

end Reflect

end Verified
