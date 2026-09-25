import LeanExe.Source.ScalarStep
import LeanExe.Source.ScalarRangeExitSyntax
import LeanExe.Source.ScalarRangeStride

namespace LeanExe.Source.Scalar.Range.Exit

/-- Native source evaluation of one range with yielding or done steps, with
pure scalar computations before and after it. -/
inductive Eval : Lean.Expr → List Scalar.Value → UInt64 → Prop where
  | range (indexType : IndexType) (stride : Stride) {stepFn : Nat → UInt64 → ForInStep UInt64}
      (first : Count.Eval firstExpr values begin) (count : Count.Eval countExpr values stop) (initial : EvalWith initialExpr values start)
      (step : ∀ index accumulator, Step.Eval body
        (.scalar (.word accumulator) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (stepFn index accumulator)) :
      Eval (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
        values (iterate (fun i accumulator => stepFn (begin + stride.number * i) accumulator)
          (trips (stop - begin) stride.number) 0 start)
  | letE (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (body : Eval e values result) : Eval (Identity.run e) values result
  | idPure (body : Eval e values result) : Eval (Identity.pure e) values result
  | bindRight (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (Identity.bind name bi a b) values y
  | bindLeft (value : Eval a values x) (body : EvalWith b (.word x :: values) y) :
      Eval (Identity.bind name bi a b) values y
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : Eval b (.function false f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letBinaryFn (type : ResultType)
      (function : ∀ x y, EvalWith a (.word y :: .word x :: values) (f x y))
      (body : Eval b (.binaryFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values outcome
  | letUnitFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values) (f x))
      (body : Eval b (.function true f :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | metadata (body : Eval e values result) : Eval (.mdata data e) values result

/-- Independent source support for a single bounded early-exit range. -/
inductive Supported : List Scalar.BindingKind → Lean.Expr → Prop where
  | range (indexType : IndexType) (stride : Stride) (first : Count.Supported types firstExpr) (count : Count.Supported types countExpr) (initial : SupportedWith types initialExpr)
      (step : Step.Supported
        (.scalar .word :: .scalar .natural :: types.map Step.BindingKind.scalar) body) :
      Supported types
        (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
  | letE (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (body : Supported types e) : Supported types (Identity.run e)
  | idPure (body : Supported types e) : Supported types (Identity.pure e)
  | bindRight (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (Identity.bind name bi a b)
  | bindLeft (value : Supported types a) (body : SupportedWith (.word :: types) b) :
      Supported types (Identity.bind name bi a b)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : Supported (.function false :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letBinaryFn (type : ResultType) (function : SupportedWith (.word :: .word :: types) a)
      (body : Supported (.binaryFunction :: types) b) :
      Supported types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | letUnitFn (type : ResultType) (function : SupportedWith (.word :: .unit :: types) a)
      (body : Supported (.function true :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | metadata (body : Supported types e) : Supported types (.mdata data e)

theorem Supported.evaluates {types : List Scalar.BindingKind} {expr : Lean.Expr}
    (supported : Supported types expr) (values : List Scalar.Value)
    (typed : values.map Scalar.Value.kind = types) : ∃ value, Eval expr values value := by
  classical
  induction supported generalizing values with
  | range indexType stride first count initial step =>
    obtain ⟨begin, hbegin⟩ := first.evaluates values typed
    obtain ⟨stop, hstop⟩ := count.evaluates values typed
    obtain ⟨start, hstart⟩ := initial.evaluates values typed
    have total (index : Nat) (value : UInt64) :=
      step.evaluates (.scalar (.word value) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (by simp [Step.Value.kind, Scalar.Value.kind, List.map_map, Function.comp_def, ← typed])
    let f := fun index value => (total index value).choose
    exact ⟨iterate (fun i accumulator => f (begin + stride.number * i) accumulator)
      (trips (stop - begin) stride.number) 0 start, .range indexType stride hbegin hstop hstart
      (fun index value => (total index value).choose_spec)⟩
  | letE value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .letE hx hy⟩
  | idRun _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idRun hv⟩
  | idPure _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idPure hv⟩
  | bindRight value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .bindRight hx hy⟩
  | bindLeft _ body ih =>
    obtain ⟨x, hx⟩ := ih values typed
    obtain ⟨y, hy⟩ := body.evaluates (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .bindLeft hx hy⟩
  | letFn type function _ ihb =>
    have total := fun x => function.evaluates (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
  | letBinaryFn type function _ ihb =>
    have total := fun x y => function.evaluates (.word y :: .word x :: values) (by simp [Value.kind, typed])
    let f := fun x y => (total x y).choose
    obtain ⟨value, hv⟩ := ihb (.binaryFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBinaryFn type (fun x y => (total x y).choose_spec) hv⟩
  | letUnitFn type function _ ihb =>
    have total := fun x => function.evaluates (.word x :: .unit :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letUnitFn type (fun x => (total x).choose_spec) hv⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar.Range.Exit
