import Verified.TailBound
import Verified.FunRenameBound

namespace Verified

theorem Flags.params_cons_there {S : List Sig} {g h : Sig} (flags : Flags S)
    (pf : List Bool) (rf : Bool) (f : FVar S h) :
    (Flags.cons (g := g) pf rf flags).params (.there f) = flags.params f := by
  simp [Flags.params, Flags.toList, FVar.index]

theorem Flags.result_cons_there {S : List Sig} {g h : Sig} (flags : Flags S)
    (pf : List Bool) (rf : Bool) (f : FVar S h) :
    (Flags.cons (g := g) pf rf flags).result (.there f) = flags.result f := by
  simp [Flags.result, Flags.toList, FVar.index]

theorem Expr.paid_weakenFuns {S : List Sig} {g : Sig} (e : Expr S Γ t)
    (flags : Flags S) (pf : List Bool) (rf : Bool) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) :
    (e.renameFuns (fun f => FVar.there (h := g) f)).paid (.cons pf rf flags) modes paid live =
      e.paid flags modes paid live :=
  Expr.paid_renameFuns _ flags (.cons pf rf flags)
    (fun f => Flags.params_cons_there flags pf rf f)
    (fun f => Flags.result_cons_there flags pf rf f) e modes paid live

theorem Expr.allocs_weakenFuns {S : List Sig} {g : Sig} (e : Expr S Γ t)
    (M : Env g.params → g.result.denote) (funs : Funs S) (flags : Flags S)
    (pf : List Bool) (rf : Bool) (bounds : Bounds S) (B : Env g.params → Nat)
    (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (env : Env Γ) :
    (e.renameFuns (fun f => .there f)).allocs (.cons M funs) (.cons pf rf flags) (.cons B bounds)
      modes paid live env = e.allocs funs flags bounds modes paid live env :=
  Expr.allocs_renameFuns _ funs (.cons M funs) (fun _ _ => rfl) flags (.cons pf rf flags)
    (fun f => Flags.params_cons_there flags pf rf f)
    (fun f => Flags.result_cons_there flags pf rf f) bounds (.cons B bounds)
    (fun _ _ => rfl) e modes paid live env

theorem Expr.fits_weakenFuns {S : List Sig} {g : Sig} (e : Expr S Γ t)
    (M : Env g.params → g.result.denote) (funs : Funs S) (fits : Fits S)
    (F : Env g.params → Bool) (env : Env Γ) :
    (e.renameFuns (fun f => .there f)).fits (.cons M funs) (.cons F fits) env =
      e.fits funs fits env :=
  Expr.fits_renameFuns _ funs (.cons M funs) (fun _ _ => rfl) fits (.cons F fits)
    (fun _ _ => rfl) e env

theorem Ty.copyCost_of_scalar (t : Ty) (v : t.denote) (h : t.scalar = true) : t.copyCost v = 0 := by
  induction t with
  | elem e => rfl
  | array e => simp [Ty.scalar] at h
  | tree shape => simp [Ty.scalar] at h
  | treeHeader shape => simp [Ty.scalar] at h
  | pair a b ha hb =>
    simp only [Ty.scalar, Bool.and_eq_true] at h
    simp only [Ty.copyCost, ha v.1 h.1, hb v.2 h.2, Nat.add_zero]

theorem coerceCost_join_left (t : Ty) (a b : Mode) (v : t.denote) :
    coerceCost t a (a.join b) v + coerceCost t (a.join b) .owned v = coerceCost t a .owned v := by
  cases a <;> cases b <;> simp [coerceCost, Mode.join]

theorem coerceCost_join_right (t : Ty) (a b : Mode) (v : t.denote) :
    coerceCost t b (a.join b) v + coerceCost t (a.join b) .owned v = coerceCost t b .owned v := by
  cases a <;> cases b <;> simp [coerceCost, Mode.join]

theorem TailBody.uses_toExpr (body : TailBody S params result Γ) (targetModes : List Mode)
    (depth : Bool) (i : Nat) :
    (body.toExpr ⟨params, result, true, targetModes, depth⟩ rfl rfl).uses i = body.uses i := by
  induction body generalizing i <;>
    simp_all [TailBody.toExpr, Expr.uses, Expr.uses_renameFuns, TailBody.uses]

#print axioms Expr.allocs_weakenFuns
#print axioms TailBody.uses_toExpr

end Verified
