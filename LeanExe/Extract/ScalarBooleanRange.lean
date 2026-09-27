import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Reuse a checked word loop and replace its result with a Boolean conversion. -/
def extractScalarBooleanRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match source with
  | .letE _ (.const ``UInt64 []) value body _ =>
      match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match booleanRangeBindTypes? input domain output with
      | none => none
      | some _ =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeExitWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
              pure { plan with result }
  | source =>
      match _wrapped : booleanRangeWrapper? source with
      | some (_, body) => extractScalarBooleanRangeWith locals slot body
      | none => none
termination_by sizeOf source
decreasing_by
  all_goals first | (simp_wf; omega) | exact booleanRangeWrapper_size _wrapped

@[simp] theorem extractScalarBooleanRangeWith_let (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_bind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input : ResultType) (output : BooleanType)
    (value body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bind name binder input output value body) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  rw [BooleanRange.bind, BooleanBindingForm.expr, extractScalarBooleanRangeWith, booleanRangeBindTypes_accepts]

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
  | letBefore value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
  | bindBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
  | letResult value body =>
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [rangeExitSupported_excludes_pure value, hp, hr]⟩
  | bindResult input output value body =>
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [rangeExitSupported_excludes_pure value, hp, hr]⟩
  | wrapped wrapper _ ih => simpa using ih locals typed total

theorem extractScalarBooleanRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan) :
    BooleanRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanRangeWith locals slot source generalizing plan with
  | case1 locals name value body nondep bound matched ih =>
    exact .letBefore (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case2 locals name value body nondep notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    exact .letResult (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case3 => contradiction
  | case4 locals input output value name domain body binder types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case5 locals input output value name domain body binder types parsed notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindResult types.1 types.2 (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case6 locals source notLet notBind wrapper body parsed ih =>
    rw [booleanRangeWrapper_sound parsed]
    exact .wrapped wrapper (ih compiled)
  | case7 => contradiction

end LeanExe.Extract.Core
