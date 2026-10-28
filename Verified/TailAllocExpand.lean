import Verified.TailExpand

namespace Verified

theorem shift_false (k : Nat) : shift k (fun _ => false) = (fun _ => false) := by
  funext i
  simp [shift]

theorem coerceCost_callResult (t : Ty) (v : t.denote) :
    coerceCost t (if t.scalar then .borrowed else .owned) .owned v = 0 := by
  cases h : t.scalar
  · simp [coerceCost]
  · simpa [h, coerceCost] using t.copyCost_of_scalar v h

theorem TailBody.fits_toExpr {S : List Sig} {params Γ : List Ty} {result : Ty}
    (body : TailBody S params result Γ) (targetModes : List Mode) (depth : Bool)
    (M : Env params → result.denote) (funs : Funs S) (fits : Fits S) (env : Env Γ) :
    (body.toExpr ⟨params, result, true, targetModes, depth⟩ rfl rfl).fits
        (.cons M funs) (.cons (fun _ => true) fits) env = body.fits funs fits env := by
  induction body <;>
    simp_all [TailBody.toExpr, TailBody.fits, Expr.fits, Expr.fits_weakenFuns,
      Expr.denote_weakenFuns, Fits.get]

theorem TailBody.allocs_toExpr {S : List Sig} {params Γ : List Ty} {result : Ty}
    (body : TailBody S params result Γ) (targetModes : List Mode) (depth : Bool)
    (M : Env params → result.denote) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (nextPaid : List Bool) (rf : Bool) (modes : List Mode) (paid : List Bool) (env : Env Γ) :
    body.allocs funs flags bounds targetModes nextPaid modes paid env =
      (body.toExpr ⟨params, result, true, targetModes, depth⟩ rfl rfl).allocs
          (.cons M funs) (.cons nextPaid rf flags) (.cons (fun _ => 0) bounds)
          modes paid (fun _ => false) env +
        coerceCost result
          ((body.toExpr ⟨params, result, true, targetModes, depth⟩ rfl rfl).mode modes) .owned
          ((body.toExpr ⟨params, result, true, targetModes, depth⟩ rfl rfl).denote (.cons M funs) env) := by
  induction body generalizing modes paid with
  | ret value =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs_weakenFuns, Expr.mode_renameFuns,
      Expr.denote_weakenFuns]
  | next args =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs, Expr.mode, Expr.denote,
      coerceCost_callResult, Nat.add_zero, Bounds.get, Expr.allocs_weakenFuns,
      Expr.uses_renameFuns, Expr.ownedCost_renameFuns, callMovesAt_renameFuns,
      Expr.paidVar_renameFuns, Expr.denote_weakenFuns, Bool.false_or, tailCredits,
      callCredits, Flags.params, Flags.toList, FVar.index, List.getD_cons_zero, Funs.get]
    rfl
  | ite cond yes no hy hn =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs, Expr.mode, Expr.denote,
      Expr.allocs_weakenFuns, Expr.denote_weakenFuns,
      TailBody.uses_toExpr, Bool.false_or]
    cases cond.denote funs env
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hn]
      simp only [Nat.add_assoc, coerceCost_join_right]
    · simp only [↓reduceIte]
      rw [hy]
      simp only [Nat.add_assoc, coerceCost_join_left]
  | letE value body ih =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs, Expr.mode, Expr.denote,
      Expr.allocs_weakenFuns, Expr.mode_renameFuns, Expr.denote_weakenFuns, Expr.paid_weakenFuns,
      TailBody.uses_toExpr, Bool.false_or]
    rw [ih]
    simp only [shift_false, Nat.add_assoc]
  | letPair value body ih =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs, Expr.mode, Expr.denote,
      Expr.allocs_weakenFuns, Expr.mode_renameFuns, Expr.denote_weakenFuns, Expr.paid_weakenFuns,
      TailBody.uses_toExpr, Bool.false_or]
    rw [ih]
    simp only [shift_false, Nat.add_assoc]
  | treeCase x empty nodes he hn =>
    simp only [TailBody.toExpr, TailBody.allocs, Expr.allocs, Expr.mode, Expr.denote,
      TailBody.uses_toExpr, Bool.false_or]
    cases env.get x with
    | nil h =>
      simp only [modeAt, shift_false]
      rw [he h]
      simp only [Nat.add_assoc]
      congr 1
      exact (coerceCost_trans _ _ _ _ (fun hm => recordsJoin_init _ _ (by
        rw [dite_eq_left h]; exact hm))).symm
    | node r words arrays buffers children =>
      simp only [modeAt, shift_false]
      rw [hn r]
      simp only [shift_false, Nat.add_assoc]
      congr 2
      refine (coerceCost_trans _ _ _ _ fun hm => ?_).symm
      exact recordsJoin_at _ _ r hm

#print axioms TailBody.fits_toExpr
#print axioms TailBody.allocs_toExpr

end Verified
