import LeanExe.Extract.ScalarStepMatcher
import LeanExe.Source.ScalarMatcherExpansion

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Expand a checked matcher application after its arguments have been expanded. -/
def expandStepMatcherHead (env : Lean.Environment) : Lean.Expr → Lean.Expr
  | .app (.app (.app (.app (.const name [.succ .zero]) motive) value) doneBody) yieldBody =>
      match findStepMatcher? env name with
      | some _ => StepMatcher.cases (.succ .zero) motive value doneBody yieldBody
      | none => StepMatcher.call name motive value doneBody yieldBody
  | source => source

theorem expandStepMatcherHead_normalizes (env : Lean.Environment) (source : Lean.Expr) :
    StepMatcher.HeadExpansion env source (expandStepMatcherHead env source) := by
  fun_cases expandStepMatcherHead env source with
  | case1 name motive value doneBody yieldBody candidate found =>
    obtain ⟨level, shape⟩ := candidate
    exact .matcher (findStepMatcher_sound found)
  | case2 name motive value doneBody yieldBody absent =>
    apply StepMatcher.HeadExpansion.unchanged
    intro other otherMotive otherValue otherDone otherYield same defined
    have names : name = other := congrArg (fun expression => expression.getAppFn.constName!) same
    subst other
    obtain ⟨level, shape, found⟩ := findStepMatcher_accepts defined
    simp [absent] at found
  | case3 source excluded =>
    apply StepMatcher.HeadExpansion.unchanged
    intro name motive value doneBody yieldBody same _
    exact excluded name motive value doneBody yieldBody same

theorem expandStepMatcherHead_accepts {env : Lean.Environment} {source target : Lean.Expr}
    (head : StepMatcher.HeadExpansion env source target) : expandStepMatcherHead env source = target := by
  cases head with
  | unchanged source unrecognized =>
    fun_cases expandStepMatcherHead env source with
    | case1 name motive value doneBody yieldBody candidate found =>
      obtain ⟨level, shape⟩ := candidate
      exact False.elim (unrecognized name motive value doneBody yieldBody rfl (findStepMatcher_sound found))
    | case2 => rfl
    | case3 => rfl
  | matcher defined =>
    obtain ⟨level, shape, found⟩ := findStepMatcher_accepts defined
    simp [StepMatcher.call, Lean.mkAppN, Lean.mkApp, expandStepMatcherHead, found]

/-- Traverse the original body without changing binder positions or visibility. -/
def expandStepMatchers (env : Lean.Environment) : Lean.Expr → Lean.Expr
  | .app function argument => expandStepMatcherHead env (.app (expandStepMatchers env function) (expandStepMatchers env argument))
  | .lam name domain body bi => .lam name (expandStepMatchers env domain) (expandStepMatchers env body) bi
  | .forallE name domain body bi => .forallE name (expandStepMatchers env domain) (expandStepMatchers env body) bi
  | .letE name type value body nondep => .letE name (expandStepMatchers env type) (expandStepMatchers env value) (expandStepMatchers env body) nondep
  | .mdata data body => .mdata data (expandStepMatchers env body)
  | .proj type index body => .proj type index (expandStepMatchers env body)
  | source => source

theorem expandStepMatchers_normalizes (env : Lean.Environment) (source : Lean.Expr) :
    StepMatcher.Normalizes env source (expandStepMatchers env source) := by
  induction source with
  | bvar index => exact .bvar index
  | fvar id => exact .fvar id
  | mvar id => exact .mvar id
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | app function argument ihf iha => exact .app ihf iha (expandStepMatcherHead_normalizes env _)
  | lam name domain body bi ihd ihb => exact .lam ihd ihb
  | forallE name domain body bi ihd ihb => exact .forallE ihd ihb
  | letE name type value body nondep iht ihv ihb => exact .letE iht ihv ihb
  | mdata data body ih => exact .mdata ih
  | proj type index body ih => exact .proj ih

theorem expandStepMatchers_accepts {env : Lean.Environment} {source target : Lean.Expr}
    (normalized : StepMatcher.Normalizes env source target) : expandStepMatchers env source = target := by
  induction normalized with
  | bvar | fvar | mvar | sort | const | lit => rfl
  | app _ _ head ihf iha =>
    simpa only [expandStepMatchers, ihf, iha] using expandStepMatcherHead_accepts head
  | lam _ _ ihd ihb => simp only [expandStepMatchers, ihd, ihb]
  | forallE _ _ ihd ihb => simp only [expandStepMatchers, ihd, ihb]
  | letE _ _ _ iht ihv ihb => simp only [expandStepMatchers, iht, ihv, ihb]
  | mdata _ ih => simp only [expandStepMatchers, ih]
  | proj _ ih => simp only [expandStepMatchers, ih]

theorem expandStepMatchers_correct (env : Lean.Environment) (source : Lean.Expr) :
    StepMatcher.Expansion env source (expandStepMatchers env source) :=
  (expandStepMatchers_normalizes env source).expansion

end LeanExe.Extract.Core
