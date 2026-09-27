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

@[simp] theorem booleanWordRangeBindTypes_not_word (input : ResultType) (domain output : Lean.Expr) :
    booleanWordRangeBindTypes? input.expr domain output = none := by
  simp [booleanWordRangeBindTypes?]

/-- Reuse a Boolean loop and evaluate a pure word continuation at its final store. -/
def extractScalarBooleanWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match source with
  | .letE _ type value body _ =>
      match booleanType? type with
      | none =>
          match scalarResultType? type with
          | none => none
          | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
            (fun bound => extractScalarBooleanWordRangeWith (.word bound :: locals) slot body)
            (fun _ => extractScalarBooleanWordRangeWith locals slot value)
            (fun bound => extractScalarExprWith (.word bound :: locals) body)
      | some _ => scalarRangeLoopFirstBinding
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.boolean bound :: locals) body)
        (fun _ => extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun bound => extractScalarBooleanWordRangeWith (.boolean bound :: locals) slot body)
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match booleanWordRangeBindTypes? input domain output with
      | none =>
          match scalarBindTypes? input domain output with
          | none => none
          | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
            (fun bound => extractScalarBooleanWordRangeWith (.word bound :: locals) slot body)
            (fun _ => extractScalarBooleanWordRangeWith locals slot value)
            (fun bound => extractScalarExprWith (.word bound :: locals) body)
      | some _ => scalarRangeLoopFirstBinding
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.boolean bound :: locals) body)
        (fun _ => extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun bound => extractScalarBooleanWordRangeWith (.boolean bound :: locals) slot body)
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
decreasing_by all_goals simp_wf; omega

/-- Every independently supported Boolean-to-word continuation is accepted. -/
theorem extractScalarBooleanWordRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanWordRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanWordRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
  | letFlagBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith, booleanType_accepts]
    exact scalarRangeLoopFirstBinding_accepts_scalar hb hp
  | bindFlagBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [BooleanWordRange.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_accepts]
    exact scalarRangeLoopFirstBinding_accepts_scalar hb hp
  | letWordBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith, booleanType_scalar, scalarResultType_accepts]
    exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
  | bindWordBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [Identity.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
    exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
  | letWordResult input _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith, booleanType_scalar, scalarResultType_accepts]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | bindWordResult input output _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    simp only [Identity.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | letResult input value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by simp [extractScalarBooleanWordRangeWith, scalarRangeLoopFirstBinding, hp, ht]⟩
  | bindResult input output value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by simp [BooleanWordRange.bind, extractScalarBooleanWordRangeWith, scalarRangeLoopFirstBinding, hp, ht]⟩
  | converted value =>
    obtain ⟨plan, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩
  | run type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [Identity.run, extractScalarBooleanWordRangeWith, hp]⟩
  | pure type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [Identity.pure, extractScalarBooleanWordRangeWith, hp]⟩
  | metadata _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩

theorem extractScalarBooleanWordRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanWordRangeWith locals slot source = some plan) :
    BooleanWordRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanWordRangeWith locals slot source generalizing plan with
  | case1 => contradiction
  | case2 locals name type value body nondep notBoolean input parsed bodyIH valueIH =>
    rw [scalarResultType_sound parsed]
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .letWordBefore input (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .letWordResult input (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case3 locals name type value body nondep input parsed bodyIH =>
    rw [booleanType_sound parsed]
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · exact .letResult input (extractScalarBooleanRangeWith_supported hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
    · exact .letFlagBefore input (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
  | case4 => contradiction
  | case5 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .bindWordBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .bindWordResult types.1 types.2 (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case6 locals input output value name domain body binder types parsed bodyIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · exact .bindResult types.1 types.2 (extractScalarBooleanRangeWith_supported hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
    · exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
  | case7 => exact .converted (extractScalarBooleanRangeWith_supported compiled)
  | case8 => contradiction
  | case9 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .run result (ih compiled)
  | case10 => contradiction
  | case11 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .pure result (ih compiled)
  | case12 locals data body ih => exact .metadata (ih compiled)
  | case13 => contradiction

theorem extractScalarBooleanWordRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarBooleanWordRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ result, BooleanWordRange.Eval source values result ∧ plan.Meaning saved result := by
  fun_induction extractScalarBooleanWordRangeWith locals saved.length source generalizing values plan with
  | case1 => contradiction
  | case2 locals name type value body nondep notBoolean input parsed bodyIH valueIH =>
    rw [scalarResultType_sound parsed]
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · obtain ⟨word, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.word word :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind evaluated matched) (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .letWordBefore input evaluated continuation, meaning⟩
    · obtain ⟨word, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.word word :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .letWordResult input evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case3 locals name type value body nondep input parsed bodyIH =>
    rw [booleanType_sound parsed]
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        extractScalarBooleanRangeWith_correct saved values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .letResult input evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .letFlagBefore input evaluated continuation, meaning⟩
  | case4 => contradiction
  | case5 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · obtain ⟨word, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.word word :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind evaluated matched) (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .bindWordBefore types.1 types.2 evaluated continuation, meaning⟩
    · obtain ⟨word, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.word word :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .bindWordResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case6 locals input output value name domain body binder types parsed bodyIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        extractScalarBooleanRangeWith_correct saved values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .bindResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .bindFlagBefore types.1 types.2 evaluated continuation, meaning⟩
  | case7 =>
    obtain ⟨flag, evaluated, meaning⟩ := extractScalarBooleanRangeWith_correct saved values compiled typed bindings total
    exact ⟨flag.toUInt64, .converted evaluated, meaning⟩
  | case8 => contradiction
  | case9 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .run result evaluated, meaning⟩
  | case10 => contradiction
  | case11 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .pure result evaluated, meaning⟩
  | case12 locals data body ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .metadata evaluated, meaning⟩
  | case13 => contradiction

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
  | case2 locals name type value body nondep notBoolean input parsed bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
    · obtain ⟨count, initial, step, done, result⟩ := valueIH hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
  | case3 locals name type value body nondep input parsed bodyIH =>
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨count, initial, step, done, result⟩ := extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
  | case4 => contradiction
  | case5 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
    · obtain ⟨count, initial, step, done, result⟩ := valueIH hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
  | case6 locals input output value name domain body binder types parsed bodyIH =>
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨count, initial, step, done, result⟩ := extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
  | case7 => exact extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index compiled bindings
  | case8 => contradiction
  | case9 locals type body result parsed ih => exact ih compiled bindings
  | case10 => contradiction
  | case11 locals type body result parsed ih => exact ih compiled bindings
  | case12 locals data body ih => exact ih compiled bindings
  | case13 => contradiction

end LeanExe.Extract.Core
