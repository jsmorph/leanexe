import LeanExe.Extract.ScalarStepAcceptance
import LeanExe.Extract.ScalarStepSupported
import LeanExe.Extract.ScalarRangeStride
import LeanExe.Extract.ScalarRangeExitSyntax
import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.IR.ScalarRangeExitSlots

namespace LeanExe.Extract.Core

/-- One dynamic loop with a scalar accumulator and a pure result computation.
The allocated slots are accumulator, index, stop, and exit decision, in that order. -/
structure ScalarRangeExitPlan where
  count : LeanExe.IR.Expr
  initial : LeanExe.IR.Expr
  step : LeanExe.IR.Expr
  done : LeanExe.IR.Expr
  result : LeanExe.IR.Expr
  deriving Repr

def ScalarRangeExitPlan.body (plan : ScalarRangeExitPlan) (slot : Nat) : LeanExe.IR.Stmt :=
  .seq (.assign (slot + 2) plan.count)
    (.seq (.assign slot plan.initial)
      (.seq (.assign (slot + 1) (.u64 0))
        (.seq (.assign (slot + 3) (.u64 0))
          (.seq (.while (LeanExe.IR.rangeCondition slot)
            (LeanExe.IR.rangeExitBody slot plan.step plan.done))
            (.assign slot plan.result)))))

def ScalarRangeExitPlan.func (plan : ScalarRangeExitPlan) (name : Lean.Name)
    (exportName : Option String) (arity : Nat) : LeanExe.IR.Func :=
  { sourceName := name, exportName, params := arity, locals := arity + 4
    body := plan.body arity, results := [.local arity] }

/-- Extract a single early-exit range loop and surrounding pure computations.
The loop remains dynamic; its stop is evaluated once into a fresh local. -/
def extractScalarRangeExitWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match scalarRangeExit? source with
  | some view => do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1))))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }
  | none =>
      match source with
      | .app (.app (.const ``Id.run [.zero]) sourceType) body =>
          match scalarResultType? sourceType with
          | none => none
          | some _ => extractScalarRangeExitWith locals slot body
      | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero])))) sourceType) body =>
          match scalarResultType? sourceType with
          | none => none
          | some _ => extractScalarRangeExitWith locals slot body
      | .letE _ (.const ``UInt64 []) value body _ =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeExitWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) body
              pure { plan with result }
      | .letE _ (.forallE _ (.const ``UInt64 [])
          (.forallE _ (.const ``UInt64 []) resultType _) _)
          (.lam _ (.const ``UInt64 []) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
          match scalarResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
              let function := ScalarBinding.binaryFunction fun first second =>
                extractScalarExprWith (.word second :: .word first :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
      | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
          (.lam _ (.const ``UInt64 []) value _) body _ =>
          match scalarResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
              let function := ScalarBinding.function false fun argument =>
                extractScalarExprWith (.word argument :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
      | .letE _ (.forallE _ (.const ``Unit [])
          (.forallE _ (.const ``UInt64 []) resultType _) _)
          (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _
      | .letE _ (.forallE _ (.const ``PUnit [.succ .zero])
          (.forallE _ (.const ``UInt64 []) resultType _) _)
          (.lam _ (.const ``PUnit [.succ .zero]) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
          match scalarResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) value
              let function := ScalarBinding.function true fun argument =>
                extractScalarExprWith (.word argument :: .unit :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
      | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero]))) input) output) value)
          (.lam _ domain body _) =>
          match scalarBindTypes? input domain output with
          | none => none
          | some _ =>
              match extractScalarExprWith locals value with
              | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
              | none => do
                  let plan ← extractScalarRangeExitWith locals slot value
                  let result ← extractScalarExprWith (.word plan.result :: locals) body
                  pure { plan with result }
      | .mdata _ body => extractScalarRangeExitWith locals slot body
      | _ => none
termination_by sizeOf source

open LeanExe.Source.Scalar

theorem rangeExitSupported_excludes_pure {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) :
    extractScalarExprWith locals source = none := by
  induction supported generalizing locals with
  | range =>
    simp [Range.Exit.call, Range.Exit.head, Lean.mkAppN, Lean.mkApp,
      extractScalarExprWith, ScalarPrimitive.ofHead?]
  | letE value body ih =>
    rw [extractScalarExprWith]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | idRun type _ ih => simpa only [extractScalarExprWith_idRun] using ih locals
  | idPure type _ ih => simpa only [extractScalarExprWith_idPure] using ih locals
  | bindRight input output value body ih =>
    rw [extractScalarExprWith_idBind]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | bindLeft input output value body ih => simp [extractScalarExprWith_idBind, ih]
  | letFn type _ _ ih =>
    rw [extractScalarExprWith_letFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letBinaryFn type _ _ ih =>
    rw [extractScalarExprWith_letBinaryFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letUnitFn type unitForm _ _ ih =>
    rw [extractScalarExprWith_letUnitFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letLeft value body ih => simp [extractScalarExprWith, ih]
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals

theorem extractScalarRangeExitWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarRangeExitView) : extractScalarRangeExitWith locals slot view.source = (do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1))))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }) := by
  rw [extractScalarRangeExitWith.eq_def, scalarRangeExit_accepts]

@[simp] theorem extractScalarRangeExitWith_idRun (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) (type : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.run body type) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.run, extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

@[simp] theorem extractScalarRangeExitWith_idPure (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) (type : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.pure body type) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.pure, extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

theorem extractScalarRangeExitWith_letE (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name (.const ``UInt64 []) value body nondep) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) a
        extractScalarRangeExitWith (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals) a) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_accepts]
  · rfl
  · cases type <;> simp [ResultType.expr]

theorem extractScalarRangeExitWith_letBinaryFn (locals : List ScalarBinding) (slot : Nat)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarRangeExitWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

theorem extractScalarRangeExitWith_letUnitFn (locals : List ScalarBinding) (slot : Nat)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : UnitSyntax) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarRangeExitWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) slot b) := by
  cases unitForm <;> rw [UnitSyntax.type, extractScalarRangeExitWith, scalarResultType_accepts] <;> rfl

theorem extractScalarRangeExitWith_idBind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) (input output : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.bind name bi value body input output) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [Identity.bind, extractScalarRangeExitWith, scalarBindTypes_accepts]
  cases output <;> rfl

@[simp] theorem extractScalarRangeExitWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (.mdata data body) = extractScalarRangeExitWith locals slot body := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarRangeExitWith locals slot source = some plan := by
  have extend {locals : List ScalarBinding} (total : ∀ binding ∈ locals, binding.Total)
      (value : LeanExe.IR.Expr) : ∀ binding ∈ ScalarBinding.word value :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact total binding member
  induction supported generalizing locals with
  | @range types first count initial body indexName accumulatorName indexBi accumulatorBi indexType stride hf hc hi hs =>
    obtain ⟨f, ef⟩ := extractScalarExprWith_accepts hf.scalar locals typed total
    obtain ⟨c, ec⟩ := extractScalarExprWith_accepts hc.scalar locals typed total
    obtain ⟨i, ei⟩ := extractScalarExprWith_accepts hi locals typed total
    obtain ⟨code, es⟩ := extractScalarStepWith_accepts hs
      (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset f (scalarRangeScale stride.number (.local (slot + 1))))) ::
        locals.map ScalarStepBinding.scalar)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def, ← typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact total original present)
    refine ⟨{ count := scalarRangeTrips stride.number (scalarRangeDistance f c), initial := i, step := code.value, done := code.done, result := .local slot }, ?_⟩
    have equation := extractScalarRangeExitWith_call locals slot
      { indexType, stride, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
    simpa [ScalarRangeExitView.source, ef, ec, ei, es] using equation
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_letE]; simp [hb, hp]⟩
  | idRun type _ ih => simpa using ih locals typed total
  | idPure type _ ih => simpa using ih locals typed total
  | bindRight input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_idBind, hb]; exact hp⟩
  | bindLeft input output value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeExitWith_idBind, rangeExitSupported_excludes_pure value]; simp [hp, hr]⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letFn]; simp [hc, ht, f]⟩
  | @letBinaryFn types a b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type function _ ihb =>
    have accepts (first second : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word second :: .word first :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0) (.u64 0)
    let f := fun first second => extractScalarExprWith (.word second :: .word first :: locals) a
    obtain ⟨target, ht⟩ := ihb (.binaryFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarRangeExitWith_letBinaryFn]; simp [hc, ht, f]⟩
  | @letUnitFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: .unit :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: .unit :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function true f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarRangeExitWith_letUnitFn]; simp [hc, ht, f]⟩
  | letLeft value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeExitWith_letE, rangeExitSupported_excludes_pure value]; simp [hp, hr]⟩
  | metadata _ ih => simpa using ih locals typed total

/-- Successful range extraction admits the independently stated source grammar. -/
theorem extractScalarRangeExitWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith locals slot source = some plan) :
    Range.Exit.Supported (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarRangeExitWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRangeExit_sound matched
    subst source
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, count, hc, initial, hi, code, hs, _⟩ := compiled
    exact .range view.indexType view.stride (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hf)) (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hc)) (extractScalarExprWith_supported hi)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def]
        using extractScalarStepWith_supported hs)
  | case2 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case3 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.run body type) = some plan at compiled
    exact .idRun type (ih (by simpa only [extractScalarRangeExitWith_idRun] using compiled))
  | case4 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case5 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.pure body type) = some plan at compiled
    exact .idPure type (ih (by simpa only [extractScalarRangeExitWith_idPure] using compiled))
  | case6 locals name value body nondep bound matched notRange ih =>
    rw [extractScalarRangeExitWith_letE, matched] at compiled
    exact .letE (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case7 locals name value body nondep notPure notRange ih =>
    rw [extractScalarRangeExitWith_letE, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .letLeft (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case8 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case9 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBinaryFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case10 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    · simp [notRange, rejected] at compiled
    · exact excludedBinary
  | case11 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case12 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case13 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .unit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case14 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case15 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .punit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case16 locals input output value name domain body bi invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case17 locals input output value name domain body bi annotations typesMatched bound matched rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, matched] at compiled
    exact .bindRight inputType outputType (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case18 locals input output value name domain body bi annotations typesMatched notPure rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .bindLeft inputType outputType (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case19 locals data body rejected ih =>
    exact .metadata (ih (by simpa only [extractScalarRangeExitWith_metadata] using compiled))
  | case20 locals source rejected hrun hpure hlet hbinary hunary hunit hpunit hbind hmetadata =>
    rw [extractScalarRangeExitWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
