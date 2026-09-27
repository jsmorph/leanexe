import LeanExe.Extract.ScalarFunc
import LeanExe.Extract.ScalarMatcherExpansion

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Preserve direct extraction, then expand only checked environment declarations. -/
def extractScalarEnvironmentFunc (env : Lean.Environment) (name : Lean.Name) (exportName : Option String)
    (type source : Lean.Expr) : Option LeanExe.IR.Func :=
  match extractScalarFunc name exportName type source with
  | some func => some func
  | none => extractScalarFunc name exportName type (expandStepMatchers env source)

theorem extractScalarEnvironmentFunc_of_direct {env : Lean.Environment} {name : Lean.Name}
    {exportName : Option String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    extractScalarEnvironmentFunc env name exportName type source = some func := by
  simp [extractScalarEnvironmentFunc, compiled]

theorem extractScalarEnvironmentFunc_cases {env : Lean.Environment} {name : Lean.Name}
    {exportName : Option String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarEnvironmentFunc env name exportName type source = some func) :
    ∃ target, StepMatcher.Expansion env source target ∧
      extractScalarFunc name exportName type target = some func := by
  unfold extractScalarEnvironmentFunc at compiled
  split at compiled
  · rename_i found matched
    cases compiled
    exact ⟨source, .refl source, matched⟩
  · exact ⟨expandStepMatchers env source, expandStepMatchers_correct env source, compiled⟩

theorem extractScalarEnvironmentFunc_accepts {env : Lean.Environment} {type source : Lean.Expr}
    (supported : StepMatcher.EnvironmentSupported env type source)
    (name : Lean.Name) (exportName : Option String) :
    ∃ func, extractScalarEnvironmentFunc env name exportName type source = some func := by
  rcases supported with direct | ⟨target, normalized, grammar⟩
  · obtain ⟨func, compiled⟩ := extractScalarFunc_accepts direct name exportName
    exact ⟨func, extractScalarEnvironmentFunc_of_direct compiled⟩
  · cases direct : extractScalarFunc name exportName type source with
    | some func => exact ⟨func, extractScalarEnvironmentFunc_of_direct direct⟩
    | none =>
      obtain ⟨func, compiled⟩ := extractScalarFunc_accepts grammar name exportName
      exact ⟨func, by simp [extractScalarEnvironmentFunc, direct, expandStepMatchers_accepts normalized, compiled]⟩

theorem extractScalarEnvironmentFunc_correct {env : Lean.Environment} {name : Lean.Name}
    {exportName : Option String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarEnvironmentFunc env name exportName type source = some func)
    (args : List UInt64) (length : args.length = func.params) :
    ∃ value, StepMatcher.EnvironmentApply env source [] args value ∧ func.ScalarEval args value := by
  obtain ⟨target, expanded, extracted⟩ := extractScalarEnvironmentFunc_cases compiled
  obtain ⟨value, applied, evaluated⟩ := extractScalarFunc_correct extracted args length
  exact ⟨value, .expanded expanded applied, evaluated⟩

end LeanExe.Extract.Core
