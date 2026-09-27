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
  | .letE _ (.const ``Bool []) value body _ =>
      match extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value) with
      | none => none
      | some flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body
  | .letE name (.app (.const ``Id [.zero]) type) value body nondep =>
      extractScalarBooleanRangeWith locals slot (.letE name type value body nondep)
  | .letE _ (.forallE _ (.const ``UInt64 []) resultType _) (.lam _ (.const ``UInt64 []) value _) body _ =>
      match scalarResultType? resultType with
      | none => none
      | some _ =>
          match extractScalarExprWith (.word (.u64 0) :: locals) value with
          | none => none
          | some _ => extractScalarBooleanRangeWith
              (.function false (fun argument => extractScalarExprWith (.word argument :: locals) value) :: locals) slot body
  | .letE _ (.forallE _ (.const ``Bool []) resultType _) (.lam _ (.const ``Bool []) value _) body _ =>
      match scalarResultType? resultType with
      | none => none
      | some _ =>
          match extractScalarExprWith (.boolean (.u64 0) :: locals) value with
          | none => none
          | some _ => extractScalarBooleanRangeWith
              (.booleanFunction (fun argument => extractScalarExprWith (.boolean argument :: locals) value) :: locals) slot body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match booleanRangeBindTypes? input domain output with
      | none =>
          match booleanRangeFlagBindTypes? input domain output with
          | none => none
          | some _ =>
              match extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value) with
              | none => none
              | some flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body
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

@[simp] theorem extractScalarBooleanRangeWith_letFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``Bool []) value body nondep) = (do
      let flag ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      extractScalarBooleanRangeWith (.boolean flag :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith]
  cases extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value) <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_bindFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input output : BooleanType) (value body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bindBoolean name binder input output value body) = (do
      let flag ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      extractScalarBooleanRangeWith (.boolean flag :: locals) slot body) := by
  rw [BooleanRange.bindBoolean, BooleanBindingForm.expr, extractScalarBooleanRangeWith,
    booleanRangeBindTypes_not_boolean, booleanRangeFlagBindTypes_accepts]
  cases extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value) <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_idLet (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.app (.const ``Id [.zero]) type) value body nondep) =
      extractScalarBooleanRangeWith locals slot (.letE name type value body nondep) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.function false (fun argument => extractScalarExprWith (.word argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_accepts]
  cases extractScalarExprWith (.word (.u64 0) :: locals) value <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_letBooleanFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.booleanFunction (fun argument => extractScalarExprWith (.boolean argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_accepts]
  cases extractScalarExprWith (.boolean (.u64 0) :: locals) value <;> rfl

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
  | @letFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function false f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letFn]; simp [hc, ht, f]⟩
  | @letBooleanFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.boolean argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.booleanFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBooleanFn]; simp [hc, ht, f]⟩
  | letFlagBefore value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
  | bindFlagBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
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
  | idLet type _ ih => simpa only [extractScalarBooleanRangeWith_idLet] using ih locals typed total
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
  | case4 locals name value body nondep flag matched ih =>
    exact .letFlagBefore (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case5 locals name type value body nondep ih => exact .idLet type (ih compiled)
  | case6 => contradiction
  | case7 => contradiction
  | case8 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case9 => contradiction
  | case10 => contradiction
  | case11 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letBooleanFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case12 => contradiction
  | case13 => contradiction
  | case14 locals input output value name domain body binder notWord types parsed flag matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case15 locals input output value name domain body binder types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case16 locals input output value name domain body binder types parsed notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindResult types.1 types.2 (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case17 locals source notLet notFlag notIdLet notFunction notBooleanFunction notBind wrapper body parsed ih =>
    rw [booleanRangeWrapper_sound parsed]
    exact .wrapped wrapper (ih compiled)
  | case18 => contradiction

end LeanExe.Extract.Core
