import LeanExe.Source.Scalar

namespace LeanExe.Source.Scalar

/-- One bounded range loop, surrounded by pure scalar computations. The step
always yields; index values retain their Nat type in the source environment. -/
inductive RangeSupportedWith : List BindingKind → Lean.Expr → Prop where
  | range (count : SupportedWith types countExpr) (initial : SupportedWith types initialExpr)
      (yielding : Range.YieldScalar body scalar)
      (step : SupportedWith (.word :: .natural :: types) scalar) :
      RangeSupportedWith types
        (Range.call countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
  | letE (value : SupportedWith types a) (body : RangeSupportedWith (.word :: types) b) :
      RangeSupportedWith types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (type : ResultType) (body : RangeSupportedWith types e) : RangeSupportedWith types (Identity.run e type)
  | idPure (type : ResultType) (body : RangeSupportedWith types e) : RangeSupportedWith types (Identity.pure e type)
  | bindRight (input output : ResultType) (value : SupportedWith types a) (body : RangeSupportedWith (.word :: types) b) :
      RangeSupportedWith types (Identity.bind name bi a b input output)
  | bindLeft (input output : ResultType) (value : RangeSupportedWith types a) (body : SupportedWith (.word :: types) b) :
      RangeSupportedWith types (Identity.bind name bi a b input output)
  | metadata (body : RangeSupportedWith types e) : RangeSupportedWith types (.mdata data e)

theorem RangeSupportedWith.evaluates {types : List BindingKind} {expr : Lean.Expr}
    (supported : RangeSupportedWith types expr) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ value, EvalWith expr values value := by
  classical
  induction supported generalizing values with
  | range count initial yielding step =>
    obtain ⟨stop, hstop⟩ := count.evaluates values typed
    obtain ⟨start, hstart⟩ := initial.evaluates values typed
    have total (index : Nat) (value : UInt64) :=
      step.evaluates (.word value :: .natural index :: values) (by simp [Value.kind, typed])
    let f := fun index value => (total index value).choose
    exact ⟨Range.iterate f stop.toNat 0 start, .range hstop hstart yielding
      (fun index value => (total index value).choose_spec)⟩
  | letE value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .letE hx hy⟩
  | idRun type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idRun type hv⟩
  | idPure type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idPure type hv⟩
  | bindRight input output value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .idBind input output hx hy⟩
  | bindLeft input output _ body ih =>
    obtain ⟨x, hx⟩ := ih values typed
    obtain ⟨y, hy⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .idBind input output hx hy⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar
