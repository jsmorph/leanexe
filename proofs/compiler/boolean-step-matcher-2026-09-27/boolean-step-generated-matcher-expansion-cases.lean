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

/-- Traverse the original body without changing binder positions or visibility. -/
def expandStepMatchers (env : Lean.Environment) : Lean.Expr → Lean.Expr
  | .app function argument => expandStepMatcherHead env (.app (expandStepMatchers env function) (expandStepMatchers env argument))
  | .lam name domain body bi => .lam name (expandStepMatchers env domain) (expandStepMatchers env body) bi
  | .forallE name domain body bi => .forallE name (expandStepMatchers env domain) (expandStepMatchers env body) bi
  | .letE name type value body nondep => .letE name (expandStepMatchers env type) (expandStepMatchers env value) (expandStepMatchers env body) nondep
  | .mdata data body => .mdata data (expandStepMatchers env body)
  | .proj type index body => .proj type index (expandStepMatchers env body)
  | source => source

example (env : Lean.Environment) (source : Lean.Expr) : True := by
  fun_cases expandStepMatcherHead env source <;> trivial
#print expandStepMatcherHead.fun_cases_unfolding
end LeanExe.Extract.Core
