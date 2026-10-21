import Verified.WGSL.Params

namespace Verified.WGSL

def Params.get : {Γ : List Ty} → {t : Ty} → Params Γ → Var Γ t → Param t
  | _, _, .cons p _, .here => p
  | _, _, .cons _ rest, .there v => rest.get v

theorem Params.args_get (params : Params Γ) (env : Verified.Env Γ) (v : Var Γ t) :
    (params.args env)[v.index]? = some ((params.get v).arg (env.get v)) := by
  induction v with
  | here => cases params; cases env; rfl
  | there v ih =>
      cases params with
      | cons p rest =>
          cases env with
          | cons x env => exact ih rest env

theorem Params.kinds_get (params : Params Γ) (v : Var Γ t) :
    params.kinds[v.index]? = some (params.get v).kind := by
  induction v with
  | here => cases params; rfl
  | there v ih => cases params; exact ih _

theorem Params.context_get (params : Params Γ) (v : Var Γ t)
    (count : LeanExe.WGSL.Count) (start : Nat) :
    (params.context count start).get v = (params.get v).rep (start + v.index) count := by
  induction v generalizing start with
  | here => cases params; rfl
  | there v ih =>
      cases params with
      | cons p rest =>
          simp only [Params.context, Context.get, Params.get, Var.index]
          rw [ih rest (start + 1)]
          congr 1
          omega

end Verified.WGSL
