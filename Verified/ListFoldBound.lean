import Verified.ListFoldState
import Verified.TailExpand

namespace Verified

theorem argsSum_eq_zero {n : Nat} {f : Fin n → Nat} (h : ∀ i, f i = 0) : argsSum f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg₂ Nat.add (h 0) (ih (fun i => h i.succ))

namespace ListFold

theorem next_allocs {S : List Sig} {e : Elem} {captures : List Ty}
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (targetPaid : List Bool) (modes : List Mode) (paid : List Bool)
    (env : Env (.elem e :: context e captures)) :
    (TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).allocs
      funs flags bounds [] targetPaid modes paid env = 0 := by
  simp only [TailBody.allocs]
  have charge (i : Fin (params e captures).length) :
      (if ((params e captures).get i).scalar then
        ((nextArgs (S := S) e captures).get i).allocs funs flags bounds modes paid
          (fun k => argsAny fun j => ((nextArgs (S := S) e captures).get j).uses k) env
      else if paramMode (params e captures) [] i = .owned then
        ((nextArgs (S := S) e captures).get i).ownedCost modes
          (fun k => (argsAny fun j => ((nextArgs (S := S) e captures).get j).uses k) &&
            !(argsAny fun j => callMovesAt modes (fun _ => false)
              (g := tailSig (params e captures) (.elem e) [])
              (nextArgs (S := S) e captures).get j &&
                ((nextArgs (S := S) e captures).get j).uses k)) env else 0) = 0 := by
    obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
    cases hs : ((params e captures).get i).scalar
    · simp
    · rw [hx]
      simp only [↓reduceIte, Expr.allocs, Var.cost]
      split
      · exact Ty.copyCost_of_scalar _ _ hs
      · rfl
  rw [argsSum_eq_zero charge]
  simp only [Nat.zero_add, tailCredits, Sig.paidSel, Sig.mode, tailSig, paramMode_default,
    show (Mode.borrowed == Mode.owned) = false from rfl,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact argsSum_eq_zero (fun _ => rfl)

theorem next_fits {S : List Sig} {e : Elem} {captures : List Ty}
    (funs : Funs S) (fits : Fits S) (env : Env (.elem e :: context e captures)) :
    (TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).fits funs fits env = true := by
  apply argsAll_true
  intro i
  obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
  simp only [hx, Expr.fits]

theorem body_allocs {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e))
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
    (tailBody body).allocs funs flags bounds [] (List.replicate (params e captures).length false)
      (paramModes (params e captures) []) (List.replicate (params e captures).length false)
      (.cons root (.cons acc captured)) =
      match root with
      | .nil => 0
      | .node words children => body.allocs funs flags bounds
          (listShape.modes .borrowed (paramModes (params e captures) []))
          (List.replicate listShape.bindCount false ++ List.replicate (params e captures).length false)
          (bodyLive e captures)
          (Env.treeFields listShape words children (.cons root (.cons acc captured))) := by
  cases root with
  | nil => simp [tailBody, TailBody.allocs, Expr.allocs, Var.cost, modeAt,
      paramMode, coerceCost, Ty.copyCost, Expr.denote, Env.get, Expr.mode, Var.index]
  | node words children =>
    rw [tailBody, TailBody.allocs]
    simp only [Env.get]
    rw [TailBody.allocs, next_allocs, Nat.add_zero]
    have hl : (fun i => (TailBody.next (result := .elem e)
        (nextArgs (S := S) e captures).get).uses (i + 1)) = bodyLive e captures :=
      funext next_uses
    rw [hl]
    have rootMode : (paramModes (params e captures) []).getD 0 .borrowed = .borrowed :=
      paramMode_default _ 0
    simp only [Var.cost, modeAt, Var.index, rootMode, reduceCtorEq, false_and,
      ↓reduceIte, Nat.zero_add]

#print axioms next_allocs
#print axioms next_fits
#print axioms body_allocs

theorem body_fits {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (funs : Funs S) (fits : Fits S)
    (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
    (tailBody body).fits funs fits (.cons root (.cons acc captured)) =
      match root with
      | .nil => true
      | .node words children => body.fits funs fits
          (Env.treeFields listShape words children (.cons root (.cons acc captured))) := by
  cases root with
  | nil => rfl
  | node words children =>
    rw [tailBody, TailBody.fits]
    simp only [Env.get]
    rw [TailBody.fits, next_fits, Bool.and_true]

end ListFold
end Verified
