import Verified.TailCompile
import Verified.Bound

namespace Verified

theorem TailBody.fits_of_depthCalls (funs : Funs S) (fits : Fits S)
    (body : TailBody S params result Γ) :
    body.depthCalls = false → ∀ env, body.fits funs fits env = true := by
  induction body with
  | ret value => exact value.fits_of_depthCalls funs fits
  | next args =>
    intro hd env
    exact argsAll_true fun i => (args i).fits_of_depthCalls funs fits (argsAny_eq_false hd i) env
  | treeCase x empty nodes he hn =>
    intro hd env
    simp only [TailBody.depthCalls, Bool.or_eq_false_iff] at hd
    simp only [TailBody.fits]
    cases env.get x with
    | nil h => exact he h (by simpa only [dite_eq_left h] using hd.1) env
    | node r words arrays buffers children =>
      exact hn r (argsAny_eq_false hd.2 r) (Env.treeFields _ r words arrays buffers children env)
  | _ => intro hd env; simp_all [TailBody.depthCalls, TailBody.fits,
      Bool.or_eq_false_iff, Expr.fits_of_depthCalls]

theorem TailFunc.bound_eq (func : TailFunc S) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (decreases : func.Decreases funs) (state : Env func.params) :
    func.bound funs flags bounds state =
      func.body.allocs funs flags bounds func.modes (func.paidParams flags)
        (entryModes func.params func.modes) (func.paidParams flags) state +
        (func.body.denote funs state).elim (func.bound funs flags bounds) (fun _ => 0) :=
  Tail.costAt_rank_eq _ _ decreases _ state

theorem TailFunc.fits_eq (func : TailFunc S) (funs : Funs S) (fits : Fits S)
    (decreases : func.Decreases funs) (state : Env func.params) :
    func.fits funs fits state = (func.body.fits funs fits state &&
      (func.body.denote funs state).elim (func.fits funs fits) (fun _ => true)) :=
  Tail.fitsAt_rank_eq _ _ decreases _ state

#print axioms TailBody.fits_of_depthCalls
#print axioms TailFunc.bound_eq
#print axioms TailFunc.fits_eq

end Verified
