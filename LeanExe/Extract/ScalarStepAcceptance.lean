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
  | chooseCompound guard type arguments _ _ iht ihe =>
    obtain ⟨c, hc⟩ := extractGuard_accepts guard.tree
      (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
      (fun operand member => scalar (arguments operand member) typed total)
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨⟨.ite c t.value e.value, .ite c t.done e.done⟩, by
      rw [extractScalarStepWith_compoundBranch]; simp [hc, ht, he]⟩
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := scalar value typed total
    obtain ⟨target, ht⟩ := ih (.scalar (.word bound) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_letE]; simp [hb, ht]⟩
  | idBind type value _ ih =>
    obtain ⟨bound, hb⟩ := scalar value typed total
    obtain ⟨target, ht⟩ := ih (.scalar (.word bound) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_bind]; simp [hb, ht]⟩
  | manyApply call present arguments =>
    obtain ⟨f, hf⟩ := scalarStepManyFunction_lookup (typed ▸ present)
    obtain ⟨compiledArguments, ha⟩ := extractScalarArguments_accepts call.arguments
      (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
      (fun operand member => scalar (arguments operand member) typed total)
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) compiledArguments
      (extractScalarArguments_length _ _ ha)
    exact ⟨target, by
      rw [extractScalarStepWith_manyApply]
      simp only [bind, hf, Option.bind_some, ScalarStepBinding.manyFunction?, beq_self_eq_true,
        ↓reduceIte, ha, ht]⟩
  | letManyStepFn shape _ _ ihf ihb =>
    have accepts (arguments : List LeanExe.IR.Expr) (len : arguments.length = shape.arity) :=
      ihf (arguments.reverse.map (fun argument => .scalar (.word argument)) ++ locals)
        (by simp [List.map_map, Function.comp_def, ScalarStepBinding.kind, ScalarBinding.kind,
          List.map_const', len, typed]) (scalarStepWords_total _ total)
    obtain ⟨checked, hc⟩ := accepts (List.replicate shape.arity (.u64 0)) (by simp)
    simp only [List.reverse_replicate, List.map_replicate] at hc
    let f := fun (arguments : List LeanExe.IR.Expr) => extractScalarStepWith
      (arguments.reverse.map (fun argument => .scalar (.word argument)) ++ locals) shape.body
    obtain ⟨target, ht⟩ := ihb (.manyFunction shape.arity f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letManyStepFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
  | binaryApply present first second =>
    obtain ⟨f, hf⟩ := scalarStepBinaryFunction_lookup (typed ▸ present)
    obtain ⟨a, ha⟩ := scalar first typed total
    obtain ⟨b, hb⟩ := scalar second typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) a b
    exact ⟨target, by
      rw [extractScalarStepWith_binaryApply _ _ _ _ first.not_unit]
      simp [hf, ScalarStepBinding.binaryFunction?, ha, hb, ht]⟩
  | @letBinaryStepFn types a b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type _ _ ihf ihb =>
    have accepts (first second : LeanExe.IR.Expr) := ihf
      (.scalar (.word second) :: .scalar (.word first) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend (extend total trivial) trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0) (.u64 0)
    let f := fun first second =>
      extractScalarStepWith (.scalar (.word second) :: .scalar (.word first) :: locals) a
    obtain ⟨target, ht⟩ := ihb (.binaryFunction f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letBinaryStepFn]; simp [hc, ht, f]⟩
  | apply present argument =>
    obtain ⟨f, hf⟩ := scalarStepFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := scalar argument typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarStepWith]; simp [hf, ScalarStepBinding.function?, ha, ht]⟩
  | unitApply unitForm present argument =>
    obtain ⟨f, hf⟩ := scalarStepFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := scalar argument typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarStepWith_unitApply]; simp [hf, ScalarStepBinding.function?, ha, ht]⟩
  | @letBinaryFn a types b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type function _ ih =>
    have accepts (first second : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word second :: .word first :: locals.map ScalarStepBinding.toScalar)
      (by simpa [ScalarBinding.kind] using scalarStepBindings_typed typed) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact scalarStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0) (.u64 0)
    let f := fun first second =>
      extractScalarExprWith (.word second :: .word first :: locals.map ScalarStepBinding.toScalar) a
    obtain ⟨target, ht⟩ := ih (.scalar (.binaryFunction f) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letBinaryFn]; simp [hc, ht, f]⟩
  | letManyFn shape function _ ih =>
    have accepts (arguments : List LeanExe.IR.Expr) (len : arguments.length = shape.arity) :=
      extractScalarExprWith_accepts function
        (arguments.reverse.map ScalarBinding.word ++ locals.map ScalarStepBinding.toScalar)
        (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len,
          scalarStepBindings_typed typed])
        (scalarWords_total _ (scalarStepBindings_total total))
    obtain ⟨checked, hc⟩ := accepts (List.replicate shape.arity (.u64 0)) (by simp)
    simp only [List.reverse_replicate, List.map_replicate] at hc
    let f := fun (arguments : List LeanExe.IR.Expr) => extractScalarExprWith
      (arguments.reverse.map ScalarBinding.word ++ locals.map ScalarStepBinding.toScalar) shape.body
    obtain ⟨target, ht⟩ := ih (.scalar (.manyFunction shape.arity f) :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letManyFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
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
  | @letUnitFn a types b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm function _ ih =>
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
  | @letUnitStepFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.scalar (.word argument) :: .scalar .unit :: locals)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, typed]) (extend (extend total trivial) trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarStepWith (.scalar (.word argument) :: .scalar .unit :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function true f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letUnitStepFn]; simp [hc, ht, f]⟩
  | applyResult present _ ih =>
    obtain ⟨f, hf⟩ := scalarStepResultFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := ih locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by
      rw [extractScalarStepWith]
      simp [hf, ScalarStepBinding.function?, ScalarStepBinding.resultFunction?, ha, ht]⟩
  | @letResultFn types a b name typeName typeBi paramName paramBi nondep input output _ _ ihf ihb =>
    have accepts (argument : ScalarStepCode) := ihf (.result argument :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total trivial)
    obtain ⟨checked, hc⟩ := accepts ⟨.u64 0, .u64 0⟩
    let f := fun argument => extractScalarStepWith (.result argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.resultFunction f :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total accepts)
    exact ⟨target, by rw [extractScalarStepWith_letResultFn]; simp [hc, ht, f]⟩
  | resultVar present =>
    obtain ⟨code, found⟩ := scalarStepResult_lookup (typed ▸ present)
    exact ⟨code, by rw [extractScalarStepWith]; simp [found, ScalarStepBinding.result?]⟩
  | idRun type _ ih => simpa only [extractScalarStepWith_idRun] using ih locals typed total
  | idPure type _ ih => simpa only [extractScalarStepWith_idPure] using ih locals typed total
  | letResult type _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.result bound :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_letResult]; simp [hb, ht]⟩
  | bindResult input output _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.result bound :: locals)
      (by simp [ScalarStepBinding.kind, typed]) (extend total trivial)
    exact ⟨target, by rw [extractScalarStepWith_bindResult]; simp [hb, ht]⟩
  | metadata _ ih => simpa only [extractScalarStepWith] using ih locals typed total

end LeanExe.Extract.Core
