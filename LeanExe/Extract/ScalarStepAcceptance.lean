import LeanExe.Extract.ScalarStepEquations

namespace LeanExe.Extract.Core

/-- Every independently supported step compiles under total, correctly typed
bindings, including closures checked with any compiled scalar argument. -/
theorem extractScalarStepWith_accepts {source : Lean.Expr}
    {types : List LeanExe.Source.Scalar.Step.BindingKind}
    (supported : LeanExe.Source.Scalar.Step.Supported types source)
    (locals : List ScalarStepBinding) (typed : locals.map ScalarStepBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ target, extractScalarStepWith locals source = some target := by
  have scalar {source : Lean.Expr} {types : List LeanExe.Source.Scalar.Step.BindingKind}
      {locals : List ScalarStepBinding}
      (supported : LeanExe.Source.Scalar.SupportedWith
        (types.map LeanExe.Source.Scalar.Step.BindingKind.toScalar) source)
      (typed : locals.map ScalarStepBinding.kind = types)
      (total : ∀ binding ∈ locals, binding.Total) :=
    extractScalarExprWith_accepts supported _ (scalarStepBindings_typed typed)
      (scalarStepBindings_total total)
  have extend {locals : List ScalarStepBinding} {head : ScalarStepBinding}
      (total : ∀ binding ∈ locals, binding.Total) (headTotal : head.Total) :
      ∀ binding ∈ head :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact headTotal
    · exact total binding member
  induction supported generalizing locals with
  | yieldValue value =>
    obtain ⟨value, hv⟩ := scalar value typed total
    exact ⟨⟨value, .u64 0⟩, by rw [extractScalarStepWith_yield]; simp [hv]⟩
  | doneValue value =>
    obtain ⟨value, hv⟩ := scalar value typed total
    exact ⟨⟨value, .u64 1⟩, by rw [extractScalarStepWith_done]; simp [hv]⟩
  | yieldDirect value =>
    obtain ⟨value, hv⟩ := scalar value typed total
    exact ⟨⟨value, .u64 0⟩, by rw [extractScalarStepWith_yieldDirect]; simp [hv]⟩
  | doneDirect value =>
    obtain ⟨value, hv⟩ := scalar value typed total
    exact ⟨⟨value, .u64 1⟩, by rw [extractScalarStepWith_doneDirect]; simp [hv]⟩
  | choose op type left right _ _ iht ihe =>
    obtain ⟨a, ha⟩ := scalar left typed total
    obtain ⟨b, hb⟩ := scalar right typed total
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨⟨.ite (lowerComparison op a b) t.value e.value,
      .ite (lowerComparison op a b) t.done e.done⟩, by
        rw [extractScalarStepWith_branch]; simp [ha, hb, ht, he]⟩
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := scalar value typed total
    obtain ⟨target, ht⟩ := ih (.scalar (.word bound) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_letE]; simp [hb, ht]⟩
  | idBind value _ ih =>
    obtain ⟨bound, hb⟩ := scalar value typed total
    obtain ⟨target, ht⟩ := ih (.scalar (.word bound) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_bind]; simp [hb, ht]⟩
  | apply present argument =>
    obtain ⟨f, hf⟩ := scalarStepFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := scalar argument typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarStepWith]; simp [hf, ScalarStepBinding.function?, ha, ht]⟩
  | unitApply present argument =>
    obtain ⟨f, hf⟩ := scalarStepFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := scalar argument typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarStepWith]; simp [hf, ScalarStepBinding.function?, ha, ht]⟩
  | @letFn a types b name typeName typeBi paramName paramBi nondep type function _ ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word argument :: locals.map ScalarStepBinding.toScalar)
      (by simpa [ScalarBinding.kind] using scalarStepBindings_typed typed) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact scalarStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals.map ScalarStepBinding.toScalar) a
    obtain ⟨target, ht⟩ := ih (.scalar (.function false f) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letFn]; simp [hc, ht, f]⟩
  | @letUnitFn a types b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type function _ ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word argument :: .unit :: locals.map ScalarStepBinding.toScalar)
      (by simpa [ScalarBinding.kind] using scalarStepBindings_typed typed) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact scalarStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: .unit :: locals.map ScalarStepBinding.toScalar) a
    obtain ⟨target, ht⟩ := ih (.scalar (.function true f) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letUnitFn]; simp [hc, ht, f]⟩
  | @letStepFn types a b name typeName typeBi paramName paramBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.scalar (.word argument) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarStepWith (.scalar (.word argument) :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function false f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letStepFn]; simp [hc, ht, f]⟩
  | @letUnitStepFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.scalar (.word argument) :: .scalar .unit :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend (extend total trivial) trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarStepWith (.scalar (.word argument) :: .scalar .unit :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function true f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letUnitStepFn]; simp [hc, ht, f]⟩
  | resultVar present =>
    obtain ⟨code, found⟩ := scalarStepResult_lookup (typed ▸ present)
    exact ⟨code, by rw [extractScalarStepWith]; simp [found, ScalarStepBinding.result?]⟩
  | idRun _ ih => simpa only [extractScalarStepWith_idRun] using ih locals typed total
  | idPure _ ih => simpa only [extractScalarStepWith_idPure] using ih locals typed total
  | letResult type _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.result bound :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_letResult]; simp [hb, ht]⟩
  | bindResult _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.result bound :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_bindResult]; simp [hb, ht]⟩
  | metadata _ ih => simpa only [extractScalarStepWith] using ih locals typed total

end LeanExe.Extract.Core
