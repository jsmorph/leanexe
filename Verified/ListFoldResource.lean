import Verified.ListFoldBound

namespace Verified.ListFold

theorem func_bound {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
    (func body place).bound funs flags bounds (.cons root (.cons acc captured)) =
      costWith (body.denote funs)
        (body.allocs funs flags bounds
          (listShape.modes .borrowed (paramModes (params e captures) []))
          (List.replicate listShape.bindCount false ++ List.replicate (params e captures).length false)
          (bodyLive e captures))
        (.cons root (.cons acc captured)) := by
  have charge (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
      (func body place).body.allocs funs flags bounds (func body place).modes
        ((func body place).paidParams flags)
        (entryModes (func body place).params (func body place).modes)
        ((func body place).paidParams flags) (.cons root (.cons acc captured)) =
      match root with
      | .nil => 0
      | .node words children => body.allocs funs flags bounds
          (listShape.modes .borrowed (paramModes (params e captures) []))
          (List.replicate listShape.bindCount false ++ List.replicate (params e captures).length false)
          (bodyLive e captures)
          (Env.treeFields listShape words children (.cons root (.cons acc captured))) := by
    rw [func_paidParams]
    change (tailBody body).allocs funs flags bounds [] _ (entryModes (params e captures) []) _ _ = _
    rw [show entryModes (params e captures) [] = paramModes (params e captures) [] from
      paramSlots_modes _ _ _]
    exact body_allocs body funs flags bounds root acc captured
  have step (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
      (func body place).body.denote funs (.cons root (.cons acc captured)) =
      match root with
      | .nil => .inr acc
      | .node words children => .inl (.cons (children ⟨0, by decide⟩)
          (.cons (body.denote funs (Env.treeFields listShape words children
            (.cons root (.cons acc captured)))) captured)) :=
    tailBody_denote body funs root acc captured
  rw [← Tree.ofList_toList root]
  generalize root.toList = xs
  induction xs generalizing acc captured with
  | nil =>
    rw [TailFunc.bound_eq _ _ _ _ (func_decreases body place funs), charge, step]
    rfl
  | cons head tail ih =>
    rw [TailFunc.bound_eq _ _ _ _ (func_decreases body place funs), charge, step]
    simp only [Tree.ofList, Sum.elim_inl, Sum.elim_inr]
    rw [ih]
    rfl

theorem func_fits {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (funs : Funs S) (fits : Fits S)
    (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
    (func body place).fits funs fits (.cons root (.cons acc captured)) =
      fitsWith (body.denote funs) (body.fits funs fits) (.cons root (.cons acc captured)) := by
  rw [← Tree.ofList_toList root]
  generalize root.toList = xs
  induction xs generalizing acc captured with
  | nil =>
    rw [TailFunc.fits_eq _ _ _ (func_decreases body place funs)]
    rfl
  | cons head tail ih =>
    rw [TailFunc.fits_eq _ _ _ (func_decreases body place funs)]
    change ((tailBody body).fits funs fits (.cons (Tree.ofList (head :: tail)) (.cons acc captured)) &&
      ((tailBody body).denote funs (.cons (Tree.ofList (head :: tail)) (.cons acc captured))).elim
        ((func body place).fits funs fits) (fun _ => true)) = _
    rw [body_fits, tailBody_denote]
    simp only [Tree.ofList, Sum.elim_inl]
    rw [ih]
    rfl

#print axioms func_bound
#print axioms func_fits

theorem func_bound_env {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (env : Env (params e captures)) :
    (func body place).bound funs flags bounds env =
      costWith (body.denote funs)
        (body.allocs funs flags bounds
          (listShape.modes .borrowed (paramModes (params e captures) []))
          (List.replicate listShape.bindCount false ++ List.replicate (params e captures).length false)
          (bodyLive e captures)) env := by
  cases env with
  | cons root env => cases env with
    | cons acc captured => exact func_bound body place funs flags bounds root acc captured

theorem func_fits_env {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (funs : Funs S) (fits : Fits S) (env : Env (params e captures)) :
    (func body place).fits funs fits env = fitsWith (body.denote funs) (body.fits funs fits) env := by
  cases env with
  | cons root env => cases env with
    | cons acc captured => exact func_fits body place funs fits root acc captured

end Verified.ListFold
