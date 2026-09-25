import LeanExe.Source.ScalarStep
import LeanExe.Source.ScalarRangeExitSyntax
import LeanExe.Source.ScalarRangeExit

namespace LeanExe.Source.Scalar.Range.Exit

/-- Native source evaluation of one range with yielding or done steps, with
pure scalar computations before and after it. -/
inductive Eval : Lean.Expr → List Scalar.Value → UInt64 → Prop where
  | range (indexType : IndexType) (count : EvalWith countExpr values stop) (initial : EvalWith initialExpr values start)
      (step : ∀ index accumulator, Step.Eval body
        (.scalar (.word accumulator) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (stepFn index accumulator)) :
      Eval (call indexType countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
        values (iterate stepFn stop.toNat 0 start)
  | letE (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (body : Eval e values result) : Eval (Identity.run e) values result
  | idPure (body : Eval e values result) : Eval (Identity.pure e) values result
  | bindRight (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (Identity.bind name bi a b) values y
  | bindLeft (value : Eval a values x) (body : EvalWith b (.word x :: values) y) :
      Eval (Identity.bind name bi a b) values y
  | metadata (body : Eval e values result) : Eval (.mdata data e) values result

/-- Independent source support for a single bounded early-exit range. -/
inductive Supported : List Scalar.BindingKind → Lean.Expr → Prop where
  | range (indexType : IndexType) (count : SupportedWith types countExpr) (initial : SupportedWith types initialExpr)
      (step : Step.Supported
        (.scalar .word :: .scalar .natural :: types.map Step.BindingKind.scalar) body) :
      Supported types
        (call indexType countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
  | letE (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (body : Supported types e) : Supported types (Identity.run e)
  | idPure (body : Supported types e) : Supported types (Identity.pure e)
  | bindRight (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (Identity.bind name bi a b)
  | bindLeft (value : Supported types a) (body : SupportedWith (.word :: types) b) :
      Supported types (Identity.bind name bi a b)
  | metadata (body : Supported types e) : Supported types (.mdata data e)

theorem Supported.evaluates {types : List Scalar.BindingKind} {expr : Lean.Expr}
    (supported : Supported types expr) (values : List Scalar.Value)
    (typed : values.map Scalar.Value.kind = types) : ∃ value, Eval expr values value := by
  classical
  induction supported generalizing values with
  | range indexType count initial step =>
    obtain ⟨stop, hstop⟩ := count.evaluates values typed
    obtain ⟨start, hstart⟩ := initial.evaluates values typed
    have total (index : Nat) (value : UInt64) :=
      step.evaluates (.scalar (.word value) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (by simp [Step.Value.kind, Scalar.Value.kind, List.map_map, Function.comp_def, ← typed])
    let f := fun index value => (total index value).choose
    exact ⟨iterate f stop.toNat 0 start, .range indexType hstop hstart
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
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar.Range.Exit
