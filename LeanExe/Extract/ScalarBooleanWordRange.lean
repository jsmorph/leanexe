import LeanExe.Extract.ScalarBooleanRangeCorrectness
import LeanExe.Extract.ScalarBooleanRangeInvariant
import LeanExe.Source.ScalarBooleanWordRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Exact standard Id annotations for a Boolean action and word continuation. -/
def booleanWordRangeBindTypes? (input domain output : Lean.Expr) : Option (BooleanType × ResultType) := do
  let first ← booleanType? input
  let last ← scalarResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanWordRangeBindTypes_accepts (input : BooleanType) (output : ResultType) :
    booleanWordRangeBindTypes? input.expr input.expr output.expr = some (input, output) := by
  simp [booleanWordRangeBindTypes?]

theorem booleanWordRangeBindTypes_sound {input domain output : Lean.Expr}
    {first : BooleanType} {last : ResultType}
    (parsed : booleanWordRangeBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = last.expr := by
  simp only [booleanWordRangeBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨booleanType_sound ha, same ▸ booleanType_sound ha, scalarResultType_sound hb⟩
  · contradiction

/-- Reuse a Boolean loop and evaluate a pure word continuation at its final store. -/
def extractScalarBooleanWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match source with
  | .letE _ type value body _ =>
      match booleanType? type with
      | none => none
      | some _ => do
          let plan ← extractScalarBooleanRangeWith locals slot value
          let result ← extractScalarExprWith (.boolean plan.result :: locals) body
          pure { plan with result }
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match booleanWordRangeBindTypes? input domain output with
      | none => none
      | some _ => do
          let plan ← extractScalarBooleanRangeWith locals slot value
          let result ← extractScalarExprWith (.boolean plan.result :: locals) body
          pure { plan with result }
  | .app (.const ``Bool.toUInt64 []) value => extractScalarBooleanRangeWith locals slot value
  | .app (.app (.const ``Id.run [.zero]) type) body =>
      match scalarResultType? type with
      | none => none
      | some _ => extractScalarBooleanWordRangeWith locals slot body
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) type) body =>
      match scalarResultType? type with
      | none => none
      | some _ => extractScalarBooleanWordRangeWith locals slot body
  | .mdata _ body => extractScalarBooleanWordRangeWith locals slot body
  | _ => none
termination_by sizeOf source

/-- Every independently supported Boolean-to-word continuation is accepted. -/
theorem extractScalarBooleanWordRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanWordRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanWordRangeWith locals slot source = some plan := by
  induction supported with
  | letResult input value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by simp [extractScalarBooleanWordRangeWith, hp, ht]⟩
  | bindResult input output value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by simp [BooleanWordRange.bind, extractScalarBooleanWordRangeWith, hp, ht]⟩
  | converted value =>
    obtain ⟨plan, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩
  | run type _ ih =>
    obtain ⟨plan, hp⟩ := ih
    exact ⟨plan, by simp [Identity.run, extractScalarBooleanWordRangeWith, hp]⟩
  | pure type _ ih =>
    obtain ⟨plan, hp⟩ := ih
    exact ⟨plan, by simp [Identity.pure, extractScalarBooleanWordRangeWith, hp]⟩
  | metadata _ ih =>
    obtain ⟨plan, hp⟩ := ih
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩

/-- Successful extraction recovers the independently defined source grammar. -/
theorem extractScalarBooleanWordRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanWordRangeWith locals slot source = some plan) :
    BooleanWordRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanWordRangeWith locals slot source generalizing plan with
  | case1 => contradiction
  | case2 name type value body nondep input parsed =>
    rw [booleanType_sound parsed]
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, tail, ht, same⟩ := compiled
    exact .letResult input (extractScalarBooleanRangeWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case3 => contradiction
  | case4 input output value name domain body binder types parsed =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, tail, ht, same⟩ := compiled
    exact .bindResult types.1 types.2 (extractScalarBooleanRangeWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case5 => exact .converted (extractScalarBooleanRangeWith_supported compiled)
  | case6 => contradiction
  | case7 type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .run result (ih compiled)
  | case8 => contradiction
  | case9 type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .pure result (ih compiled)
  | case10 data body ih => exact .metadata (ih compiled)
  | case11 => contradiction

/-- Word tails use the Boolean binding at the final loop store. -/
theorem extractScalarBooleanWordRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarBooleanWordRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ result, BooleanWordRange.Eval source values result ∧ plan.Meaning saved result := by
  fun_induction extractScalarBooleanWordRangeWith locals saved.length source generalizing plan with
  | case1 => contradiction
  | case2 name type value body nondep input parsed =>
    rw [booleanType_sound parsed]
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, tail, ht, rfl⟩ := compiled
    obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      extractScalarBooleanRangeWith_correct saved values hp typed bindings total
    obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
      (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
    refine ⟨result, .letResult input evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro exitFlag
    exact extractScalarExprWith_correct continuation ht
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case3 => contradiction
  | case4 input output value name domain body binder types parsed =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, tail, ht, rfl⟩ := compiled
    obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      extractScalarBooleanRangeWith_correct saved values hp typed bindings total
    obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
      (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
    refine ⟨result, .bindResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro exitFlag
    exact extractScalarExprWith_correct continuation ht
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case5 =>
    obtain ⟨flag, evaluated, meaning⟩ := extractScalarBooleanRangeWith_correct saved values compiled typed bindings total
    exact ⟨flag.toUInt64, .converted evaluated, meaning⟩
  | case6 => contradiction
  | case7 type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .run result evaluated, meaning⟩
  | case8 => contradiction
  | case9 type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .pure result evaluated, meaning⟩
  | case10 data body ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .metadata evaluated, meaning⟩
  | case11 => contradiction

/-- The new word result preserves every invariant used by scalar WASM admission. -/
theorem extractScalarBooleanWordRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanWordRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarBooleanWordRangeWith locals slot source generalizing plan with
  | case1 => contradiction
  | case2 | case4 =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, tail, ht, rfl⟩ := compiled
    obtain ⟨count, initial, step, done, result⟩ :=
      extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index hp bindings
    refine ⟨count, initial, step, done, ?_⟩
    apply extractScalarExprWith_invariant P literal binary choice ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact result
    · exact bindings binding member
  | case3 => contradiction
  | case5 => exact extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index compiled bindings
  | case6 => contradiction
  | case7 type body result parsed ih => exact ih compiled
  | case8 => contradiction
  | case9 type body result parsed ih => exact ih compiled
  | case10 data body ih => exact ih compiled
  | case11 => contradiction

end LeanExe.Extract.Core
