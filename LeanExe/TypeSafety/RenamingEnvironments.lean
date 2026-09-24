import LeanExe.TypeSafety.Renaming

/-!
# Exact environment correspondence for renaming

Every lookup, including an absent lookup, agrees after applying the index map.
This raw relation is independent of context typing: it compares runtime values,
which need not determine unique types. Neither injectivity nor total source
variable availability is assumed.

These support lemmas do not yet assert correspondence of machine executions.
-/

namespace LeanExe.TypeSafety

/-- All present and absent lookups agree at the renamed index. -/
def EnvCorresponds (mapping : Renaming) (source target : Env) : Prop :=
  ∀ index, lookup target (mapping index) = lookup source index

theorem EnvCorresponds.lookup (corresponds : EnvCorresponds mapping source target) (index : Nat) :
    lookup target (mapping index) = lookup source index := corresponds index

theorem EnvCorresponds.refl (env : Env) : EnvCorresponds (fun index => index) env env :=
  fun _ => rfl

/-- No index becomes available when both environments are empty. -/
theorem EnvCorresponds.empty (mapping : Renaming) : EnvCorresponds mapping [] [] :=
  fun _ => rfl

theorem EnvCorresponds.comp (first : EnvCorresponds firstMap firstEnv middleEnv)
    (second : EnvCorresponds secondMap middleEnv lastEnv) :
    EnvCorresponds (fun index => secondMap (firstMap index)) firstEnv lastEnv :=
  fun index => (second (firstMap index)).trans (first index)

/-- Both evaluations bind the same value at index zero. -/
theorem EnvCorresponds.lift (corresponds : EnvCorresponds mapping source target) (value : Value) :
    EnvCorresponds (Renaming.lift mapping) (value :: source) (value :: target) := by
  intro index
  cases index with
  | zero => rfl
  | succ index => exact corresponds index

/-- Constructor and product patterns prepend the same ordered field values. -/
theorem EnvCorresponds.prefix (corresponds : EnvCorresponds mapping source target)
    (values : Env) :
    EnvCorresponds (Renaming.liftN values.length mapping) (values ++ source) (values ++ target) := by
  induction values with
  | nil => exact corresponds
  | cons value values ih => exact EnvCorresponds.lift ih value

/-- Inserting an environment preserves both successful and missing free lookups. -/
theorem EnvCorresponds.shift (env extra : Env) :
    EnvCorresponds (fun index => index + extra.length) env (extra ++ env) := by
  induction extra with
  | nil => exact fun _ => rfl
  | cons _ _ ih => exact fun index => ih index

/-- Renaming preserves branch absence, position, and explicit constructor arity. -/
theorem renameBranches_lookup (mapping : Renaming) (branches : List (Nat × Expr)) (index : Nat) :
    lookup (renameBranches mapping branches) index =
      (lookup branches index).map
        (fun branch => (branch.1, branch.2.rename (Renaming.liftN branch.1 mapping))) := by
  induction branches generalizing index with
  | nil => rfl
  | cons branch rest ih =>
      obtain ⟨arity, body⟩ := branch
      cases index with
      | zero => rfl
      | succ index => exact ih index

end LeanExe.TypeSafety
