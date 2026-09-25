import LeanExe.Extract.ScalarStepSupported

namespace LeanExe.Extract.Core

/-- Both step projections inherit scalar expression invariants. This supplies
arithmetic admission and local-read bounds without redoing source induction. -/
theorem extractScalarStepWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {source : Lean.Expr} {locals : List ScalarStepBinding} {target : ScalarStepCode}
    (compiled : extractScalarStepWith locals source = some target)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : target.Holds P := by
  have scalar {locals : List ScalarStepBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith (locals.map ScalarStepBinding.toScalar) source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled (scalarStepBindings_holds bindings)
  have expression {locals : List ScalarBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith locals source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled bindings
  have extend {locals : List ScalarStepBinding} {head : ScalarStepBinding}
      (bindings : ∀ binding ∈ locals, binding.Holds P) (headHolds : head.Holds P) :
      ∀ binding ∈ head :: locals, binding.Holds P := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact headHolds
    · exact bindings binding member
  have supported := extractScalarStepWith_supported compiled
  generalize htypes : locals.map ScalarStepBinding.kind = types at supported
  induction supported generalizing locals target with
  | yieldValue value =>
    rw [extractScalarStepWith_yield] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact ⟨scalar hv bindings, literal 0⟩
  | doneValue value =>
    rw [extractScalarStepWith_done] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact ⟨scalar hv bindings, literal 1⟩
  | yieldDirect value =>
    rw [extractScalarStepWith_yieldDirect] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact ⟨scalar hv bindings, literal 0⟩
  | doneDirect value =>
    rw [extractScalarStepWith_doneDirect] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, rfl⟩ := compiled
    exact ⟨scalar hv bindings, literal 1⟩
  | choose op type left right _ _ iht ihe =>
    rw [extractScalarStepWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := compiled
    obtain ⟨tv, td⟩ := iht ht bindings htypes
    obtain ⟨ev, ed⟩ := ihe he bindings htypes
    exact ⟨choice op a b t.value e.value (scalar ha bindings) (scalar hb bindings) tv ev,
      choice op a b t.done e.done (scalar ha bindings) (scalar hb bindings) td ed⟩
  | chooseCompound guard type arguments _ _ iht ihe =>
    rw [extractScalarStepWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := compiled
    obtain ⟨tv, td⟩ := iht ht bindings htypes
    obtain ⟨ev, ed⟩ := ihe he bindings htypes
    have preserve := extractGuard_choice P literal binary choice guard.tree _ hc
      (fun operand member expression found => scalar found bindings)
    exact ⟨preserve _ _ tv ev, preserve _ _ td ed⟩
  | letE value _ ih =>
    rw [extractScalarStepWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact ih ht (extend bindings (scalar hb bindings))
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
  | idBind type value _ ih =>
    rw [extractScalarStepWith_bind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact ih ht (extend bindings (scalar hb bindings))
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
  | binaryApply present first second =>
    rw [extractScalarStepWith_binaryApply _ _ _ _ first.not_unit] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, ⟨binding, found, matched⟩, a, ha, b, hb, ht⟩ := compiled
    have same := ScalarStepBinding.binaryFunction?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? found) a b target (scalar ha bindings) (scalar hb bindings) ht
  | letBinaryStepFn type _ _ ihf ihb =>
    rw [extractScalarStepWith_letBinaryStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, htypes])
    intro first second result hx hy compiled
    exact ihf compiled (extend (extend bindings hx) hy)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
  | @apply types index a present argument =>
    obtain ⟨f, hf⟩ := scalarStepFunction_lookup (htypes ▸ present)
    have found : locals[index]?.bind (ScalarStepBinding.function? false) = some f := by
      simp [hf, ScalarStepBinding.function?]
    rw [extractScalarStepWith, found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, ht⟩ := compiled
    exact bindings _ (List.mem_of_getElem? hf) arg target (scalar ha bindings) ht
  | unitApply present argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, ⟨binding, hb, matched⟩, arg, ha, ht⟩ := compiled
    have same := ScalarStepBinding.function?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? hb) arg target (scalar ha bindings) ht
  | letBinaryFn type function _ ih =>
    rw [extractScalarStepWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
    intro first second result hx hy compiled
    apply expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact hy
    rcases List.mem_cons.mp member with rfl | member
    · exact hx
    · exact scalarStepBindings_holds bindings binding member
  | letFn type function _ ih =>
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
    intro argument result ha compiled
    apply expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact ha
    · exact scalarStepBindings_holds bindings binding member
  | letUnitFn type function _ ih =>
    rw [extractScalarStepWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
    intro argument result ha compiled
    apply expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact ha
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact scalarStepBindings_holds bindings binding member
  | letStepFn type _ _ ihf ihb =>
    rw [extractScalarStepWith_letStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, htypes])
    intro argument result ha compiled
    exact ihf compiled (extend bindings ha)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
  | letUnitStepFn type _ _ ihf ihb =>
    rw [extractScalarStepWith_letUnitStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, htypes])
    intro argument result ha compiled
    exact ihf compiled (extend (extend bindings trivial) ha)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, htypes])
  | applyResult present _ ih =>
    obtain ⟨f, hf⟩ := scalarStepResultFunction_lookup (htypes ▸ present)
    rw [extractScalarStepWith] at compiled
    simp only [hf, Option.bind_some, ScalarStepBinding.function?, ScalarStepBinding.resultFunction?] at compiled
    simp only [bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, ht⟩ := compiled
    exact bindings _ (List.mem_of_getElem? hf) arg target (ih ha bindings htypes) ht
  | letResultFn input output _ _ ihf ihb =>
    rw [extractScalarStepWith_letResultFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht (extend bindings ?_) (by simp [ScalarStepBinding.kind, htypes])
    intro argument result ha compiled
    exact ihf compiled (extend bindings ha) (by simp [ScalarStepBinding.kind, htypes])
  | resultVar present =>
    rw [extractScalarStepWith] at compiled
    obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
    have same := ScalarStepBinding.result?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? found)
  | idRun type _ ih => exact ih (by simpa only [extractScalarStepWith_idRun] using compiled) bindings htypes
  | idPure type _ ih => exact ih (by simpa only [extractScalarStepWith_idPure] using compiled) bindings htypes
  | letResult type _ _ ihv ihb =>
    rw [extractScalarStepWith_letResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact ihb ht (extend bindings (ihv hb bindings htypes))
      (by simp [ScalarStepBinding.kind, htypes])
  | bindResult input output _ _ ihv ihb =>
    rw [extractScalarStepWith_bindResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact ihb ht (extend bindings (ihv hb bindings htypes))
      (by simp [ScalarStepBinding.kind, htypes])
  | metadata _ ih => exact ih (by simpa only [extractScalarStepWith] using compiled) bindings htypes

end LeanExe.Extract.Core
