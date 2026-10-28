import Verified.Bound
import Verified.FunRename

namespace Verified

theorem Expr.useMask_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).useMask = e.useMask := by
  induction e <;> simp_all [Expr.renameFuns, Expr.useMask]

theorem Expr.uses_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) (i : Nat) :
    (e.renameFuns ρ).uses i = e.uses i := by
  rw [← Expr.usesFast_eq, ← Expr.usesFast_eq]
  simp only [Expr.usesFast, Expr.useMask_renameFuns]

theorem Expr.varIndex_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).varIndex? = e.varIndex? := by
  cases e <;> rfl

theorem Expr.isPlace_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).isPlace = e.isPlace := by
  induction e <;> simp_all [Expr.renameFuns, Expr.isPlace]

theorem Expr.mode_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t)
    (modes : List Mode) : (e.renameFuns ρ).mode modes = e.mode modes := by
  induction e generalizing modes <;> simp_all [Expr.renameFuns, Expr.mode]

theorem Expr.paidVar_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t)
    (paid : List Bool) : (e.renameFuns ρ).paidVar paid = e.paidVar paid := by
  cases e <;> rfl

theorem Expr.ownedCost_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t)
    (modes : List Mode) (live : Nat → Bool) (env : Env Γ) :
    (e.renameFuns ρ).ownedCost modes live env = e.ownedCost modes live env := by
  cases e <;> rfl

theorem Expr.grows_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (flags : Flags S) (target : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), target.params (ρ f) = flags.params f)
    (e : Expr S Γ t) : (e.renameFuns ρ).grows target = e.grows flags := by
  induction e with
  | call f args ih =>
    exact congrArg₂ Bool.or (congrArg argsAny (funext ih))
      (congrArg (fun values : List Bool => values.any id) (params f))
  | treeNode r reuse words arrays buffers children hw ha hb hc =>
    exact congrArg₂ Bool.or
      (congrArg₂ Bool.or (congrArg₂ Bool.or (congrArg argsAny (funext hw))
        (congrArg argsAny (funext hc))) (congrArg argsAny (funext ha)))
      (congrArg argsAny (funext hb))
  | treeCase x empty nodes he hn =>
    simp only [Expr.renameFuns, Expr.grows_treeCase]
    exact congrArg₂ Bool.or (by split <;> simp_all) (congrArg argsAny (funext hn))
  | listFold args body ha hb =>
    exact congrArg₂ Bool.or (congrArg argsAny (funext ha)) hb
  | loop count init cond body hn hi hc hb =>
    exact congrArg₂ Bool.or (congrArg₂ Bool.or (congrArg₂ Bool.or hn hi) hc) hb
  | ite cond yes no hc hy hn =>
    exact congrArg₂ Bool.or (congrArg₂ Bool.or hc hy) hn
  | _ => first | rfl | assumption | apply congrArg₂ Bool.or <;> assumption

theorem Expr.foldStep_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (x : Var Γ (.array e)) (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    Expr.foldStep x (body.renameFuns ρ) = (Expr.foldStep x body).renameFuns ρ := rfl

theorem Expr.paid_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (flags : Flags S) (target : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), target.params (ρ f) = flags.params f)
    (result : ∀ {g : Sig} (f : FVar S g), target.result (ρ f) = flags.result f)
    (e : Expr S Γ t) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) :
    (e.renameFuns ρ).paid target modes paid live = e.paid flags modes paid live := by
  induction e generalizing modes paid live <;> try rfl
  all_goals
    simp_all [Expr.renameFuns, Expr.paid, Expr.mode_renameFuns, Expr.uses_renameFuns,
      Expr.grows_renameFuns ρ flags target params, Expr.foldStep_renameFuns]

theorem Expr.bodyPaid_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (flags : Flags S) (target : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), target.params (ρ f) = flags.params f)
    (result : ∀ {g : Sig} (f : FVar S g), target.result (ρ f) = flags.result f)
    (e : Expr S Γ t) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) :
    (e.renameFuns ρ).bodyPaid target modes paid live = e.bodyPaid flags modes paid live := by
  induction e generalizing modes paid live
  case ite c a b _ iha ihb => simp only [Expr.renameFuns, Expr.bodyPaid, iha, ihb]
  case letE value body _ ih =>
    simp only [Expr.renameFuns, Expr.bodyPaid, ih, Expr.mode_renameFuns, Expr.uses_renameFuns,
      Expr.paid_renameFuns ρ flags target params result]
  case letPair value body _ ih =>
    simp only [Expr.renameFuns, Expr.bodyPaid, ih, Expr.mode_renameFuns, Expr.uses_renameFuns,
      Expr.paid_renameFuns ρ flags target params result]
  all_goals exact Expr.paid_renameFuns ρ flags target params result _ modes paid live

theorem Expr.buys_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (targetFuns : Funs T)
    (functions : ∀ {g : Sig} (f : FVar S g) env, targetFuns.get (ρ f) env = funs.get f env)
    (flags : Flags S) (target : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), target.params (ρ f) = flags.params f)
    (result : ∀ {g : Sig} (f : FVar S g), target.result (ρ f) = flags.result f)
    (e : Expr S Γ t) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (env : Env Γ) :
    (e.renameFuns ρ).buys targetFuns target modes paid live env =
      e.buys funs flags modes paid live env := by
  induction e generalizing modes paid live
  case ite c a b _ iha ihb =>
    simp only [Expr.renameFuns, Expr.buys, iha, ihb,
      Expr.bodyPaid_renameFuns ρ flags target params result,
      Expr.denote_renameFuns ρ funs targetFuns functions]
  case letE value body _ ih =>
    simp only [Expr.renameFuns, Expr.buys, ih, Expr.mode_renameFuns, Expr.uses_renameFuns,
      Expr.paid_renameFuns ρ flags target params result,
      Expr.denote_renameFuns ρ funs targetFuns functions]
  case letPair value body _ ih =>
    simp only [Expr.renameFuns, Expr.buys, ih, Expr.mode_renameFuns, Expr.uses_renameFuns,
      Expr.paid_renameFuns ρ flags target params result,
      Expr.denote_renameFuns ρ funs targetFuns functions]
  all_goals rfl

theorem callMovesAt_renameFuns {S T : List Sig} (ρ : FunRenaming S T) {Γ : List Ty} {g : Sig}
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i))
    (modes : List Mode) (live : Nat → Bool) (i : Fin g.params.length) :
    callMovesAt modes live (fun j => (args j).renameFuns ρ) i = callMovesAt modes live args i := by
  simp only [callMovesAt, Expr.varIndex_renameFuns, Expr.uses_renameFuns]

theorem Expr.statePaid_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (flags : Flags S) (target : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), target.params (ρ f) = flags.params f)
    (result : ∀ {g : Sig} (f : FVar S g), target.result (ρ f) = flags.result f)
    (modes : List Mode) (paid : List Bool) (live : Nat → Bool)
    (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t) :
    Expr.statePaid target modes paid live (init.renameFuns ρ) (cond.renameFuns ρ)
      (body.renameFuns ρ) = Expr.statePaid flags modes paid live init cond body := by
  simp only [Expr.statePaid, Expr.mode_renameFuns, Expr.uses_renameFuns,
    Expr.grows_renameFuns ρ flags target params,
    Expr.bodyPaid_renameFuns ρ flags target params result]

theorem callCredits_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (targetFuns : Funs T)
    (functions : ∀ {g : Sig} (f : FVar S g) env, targetFuns.get (ρ f) env = funs.get f env)
    (flags : Flags S) (targetFlags : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), targetFlags.params (ρ f) = flags.params f)
    {Γ : List Ty} {g : Sig} (f : FVar S g)
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i))
    (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (env : Env Γ) :
    callCredits targetFuns targetFlags modes paid live (ρ f) (fun i => (args i).renameFuns ρ) env =
      callCredits funs flags modes paid live f args env := by
  simp only [callCredits, params, callMovesAt_renameFuns, Expr.paidVar_renameFuns,
    Expr.denote_renameFuns ρ funs targetFuns functions]

set_option maxHeartbeats 1000000 in
theorem Expr.allocs_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (targetFuns : Funs T)
    (functions : ∀ {g : Sig} (f : FVar S g) env, targetFuns.get (ρ f) env = funs.get f env)
    (flags : Flags S) (targetFlags : Flags T)
    (params : ∀ {g : Sig} (f : FVar S g), targetFlags.params (ρ f) = flags.params f)
    (result : ∀ {g : Sig} (f : FVar S g), targetFlags.result (ρ f) = flags.result f)
    (bounds : Bounds S) (targetBounds : Bounds T)
    (cost : ∀ {g : Sig} (f : FVar S g) env, targetBounds.get (ρ f) env = bounds.get f env)
    (e : Expr S Γ t) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (env : Env Γ) :
    (e.renameFuns ρ).allocs targetFuns targetFlags targetBounds modes paid live env =
      e.allocs funs flags bounds modes paid live env := by
  induction e generalizing modes paid live with
  | listFold args body ha hb =>
    have hd : (body.renameFuns ρ).denote targetFuns = body.denote funs :=
      funext (fun env => Expr.denote_renameFuns ρ funs targetFuns functions body env)
    have hc (ms : List Mode) (pf : List Bool) (lf : Nat → Bool) :
        (body.renameFuns ρ).allocs targetFuns targetFlags targetBounds ms pf lf =
          body.allocs funs flags bounds ms pf lf := funext (hb ms pf lf)
    simp only [Expr.renameFuns, Expr.allocs, Expr.uses_renameFuns, ha, hd, hc,
      Expr.denote_renameFuns ρ funs targetFuns functions]
  | _ =>
    simp_all
      [Expr.renameFuns, Expr.allocs, loopAlloc, loopAllocWith, Expr.foldStep_renameFuns, Expr.statePaid,
      Expr.mode_renameFuns, Expr.uses_renameFuns, Expr.ownedCost_renameFuns,
      Expr.paid_renameFuns ρ flags targetFlags params result,
      Expr.bodyPaid_renameFuns ρ flags targetFlags params result,
      Expr.buys_renameFuns ρ funs targetFuns functions flags targetFlags params result,
      Expr.grows_renameFuns ρ flags targetFlags params, callMovesAt_renameFuns,
      callCredits_renameFuns ρ funs targetFuns functions flags targetFlags params,
      Expr.denote_renameFuns ρ funs targetFuns functions, Expr.denote]
    all_goals rfl

theorem Expr.fits_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (targetFuns : Funs T)
    (functions : ∀ {g : Sig} (f : FVar S g) env, targetFuns.get (ρ f) env = funs.get f env)
    (fits : Fits S) (targetFits : Fits T)
    (frames : ∀ {g : Sig} (f : FVar S g) env, targetFits.get (ρ f) env = fits.get f env)
    (e : Expr S Γ t) (env : Env Γ) :
    (e.renameFuns ρ).fits targetFuns targetFits env = e.fits funs fits env := by
  induction e with
  | listFold args body ha hb =>
    have hd : (body.renameFuns ρ).denote targetFuns = body.denote funs :=
      funext (fun env => Expr.denote_renameFuns ρ funs targetFuns functions body env)
    have hf : (body.renameFuns ρ).fits targetFuns targetFits = body.fits funs fits := funext hb
    simp only [Expr.renameFuns, Expr.fits, ha, hd, hf,
      Expr.denote_renameFuns ρ funs targetFuns functions]
  | _ =>
    simp_all [Expr.renameFuns, Expr.fits, Expr.denote_renameFuns ρ funs targetFuns functions]

#print axioms Expr.useMask_renameFuns
#print axioms Expr.mode_renameFuns
#print axioms Expr.grows_renameFuns
#print axioms Expr.paid_renameFuns
#print axioms Expr.allocs_renameFuns
#print axioms Expr.fits_renameFuns

end Verified
