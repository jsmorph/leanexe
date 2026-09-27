import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Reuse a checked word loop and replace its result with a Boolean conversion. -/
def extractScalarBooleanRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match source with
  | .letE _ (.const ``UInt64 []) value body _ => do
      let plan ← extractScalarRangeExitWith locals slot value
      let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
      pure { plan with result }
  | source =>
      match _wrapped : booleanRangeWrapper? source with
      | some (_, body) => extractScalarBooleanRangeWith locals slot body
      | none => none
termination_by sizeOf source
decreasing_by exact booleanRangeWrapper_size _wrapped

@[simp] theorem extractScalarBooleanRangeWith_let (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (do
      let plan ← extractScalarRangeExitWith locals slot value
      let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
      pure { plan with result }) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_wrapped (locals : List ScalarBinding) (slot : Nat)
    (wrapper : BooleanWrapper) (body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (wrapper.expr body) =
      extractScalarBooleanRangeWith locals slot body := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
  all_goals rw [extractScalarBooleanRangeWith.eq_def]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem extractScalarBooleanRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
  | letResult value body =>
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [hp, hr]⟩
  | wrapped wrapper _ ih => simpa using ih locals typed total

theorem extractScalarBooleanRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan) :
    BooleanRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanRangeWith locals slot source generalizing plan with
  | case1 name value body nondep =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    exact .letResult (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case2 source notLet wrapper body parsed ih =>
    rw [booleanRangeWrapper_sound parsed]
    exact .wrapped wrapper (ih compiled)
  | case3 => contradiction

end LeanExe.Extract.Core
