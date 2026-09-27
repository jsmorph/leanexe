import LeanExe.Extract.ScalarBooleanWordRange
import LeanExe.Source.ScalarWordRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Select a checked scalar or loop plan, or recursively compile word branches. -/
def extractScalarWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match extractScalarExprWith locals source with
  | some value => some (ScalarRangeExitPlan.scalar value)
  | none =>
    match extractScalarRangeExitWith locals slot source with
    | some plan => some plan
    | none =>
      match extractScalarBooleanWordRangeWith locals slot source with
      | some plan => some plan
      | none =>
        match source with
        | .letE _ (.forallE firstTypeName (.const ``UInt64 [])
            (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
            (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) body _ =>
            match scalarResultType? resultType with
            | none =>
                match scalarManyFunction?
                    (.forallE firstTypeName (.const ``UInt64 [])
                      (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
                    (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
                | none => none
                | some shape => do
                    let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
                    let function := ScalarBinding.manyFunction shape.arity fun arguments =>
                      extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
                let function := ScalarBinding.binaryFunction fun first second =>
                  extractScalarExprWith (.word second :: .word first :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
            (.lam _ (.const ``UInt64 []) value _) body _ =>
            match scalarResultType? resultType with
            | none =>
                match booleanType? resultType with
                | none => none
                | some _ => do
                    let expression ← booleanLocalOperands? value
                    let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
                      (.app (.const ``Bool.toUInt64 []) expression.expr)
                    let function := ScalarBinding.predicateFunction fun argument =>
                      extractScalarExprWith (.word argument :: locals)
                        (.app (.const ``Bool.toUInt64 []) expression.expr)
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
                let function := ScalarBinding.function false fun argument =>
                  extractScalarExprWith (.word argument :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
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
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE _ (.forallE _ (.const ``Bool []) resultType _)
            (.lam _ (.const ``Bool []) value _) body _ =>
            match scalarResultType? resultType with
            | none =>
                match booleanType? resultType with
                | none => none
                | some _ => do
                    let expression ← booleanLocalOperands? value
                    let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
                      (.app (.const ``Bool.toUInt64 []) expression.expr)
                    let function := ScalarBinding.booleanPredicateFunction fun argument =>
                      extractScalarExprWith (.boolean argument :: locals)
                        (.app (.const ``Bool.toUInt64 []) expression.expr)
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
                let function := ScalarBinding.booleanFunction fun argument =>
                  extractScalarExprWith (.boolean argument :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
            (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
            if input = domain then
              extractScalarWordRangeWith locals slot (.letE name
                (.forallE typeName input resultType typeBi) (.lam paramName domain value paramBi) body nondep)
            else none
        | .letE _ type value body _ =>
            match booleanType? type with
            | none =>
                match scalarResultType? type with
                | none => none
                | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
                  (fun bound => extractScalarWordRangeWith (.word bound :: locals) slot body)
                  (fun _ => extractScalarWordRangeWith locals slot value)
                  (fun bound => extractScalarExprWith (.word bound :: locals) body)
            | some _ => do
                let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
                extractScalarWordRangeWith (.boolean bound :: locals) slot body
        | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero]))) input) output) value)
            (.lam _ domain body _) =>
            match booleanWordRangeBindTypes? input domain output with
            | none =>
                match scalarBindTypes? input domain output with
                | none => none
                | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
                  (fun bound => extractScalarWordRangeWith (.word bound :: locals) slot body)
                  (fun _ => extractScalarWordRangeWith locals slot value)
                  (fun bound => extractScalarExprWith (.word bound :: locals) body)
            | some _ => do
                let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
                extractScalarWordRangeWith (.boolean bound :: locals) slot body
        | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no =>
            match scalarResultType? type with
            | none => none
            | some _ => do
                let guard ← extractScalarExprWith locals (BooleanRange.decision condition evidence)
                let first ← extractScalarWordRangeWith locals slot yes
                let second ← extractScalarWordRangeWith locals slot no
                pure (ScalarRangeExitPlan.choice guard first second)
        | .app (.app (.const ``Id.run [.zero]) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
              (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
                (.const ``Id.instMonad [.zero])))) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .mdata _ body => extractScalarWordRangeWith locals slot body
        | _ => none
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

/-- Every supported word computation has an emitted scalar or loop plan. -/
theorem extractScalarWordRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : WordRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarWordRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
  | scalar body =>
    obtain ⟨value, accepted⟩ := extractScalarExprWith_accepts body locals typed total
    exact ⟨ScalarRangeExitPlan.scalar value, by rw [extractScalarWordRangeWith.eq_def, accepted]⟩
  | rangeExit body =>
    obtain ⟨plan, accepted⟩ := extractScalarRangeExitWith_accepts body locals slot typed total
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · rw [accepted]
      exact ⟨plan, rfl⟩
  | booleanWord body =>
    obtain ⟨plan, accepted⟩ := extractScalarBooleanWordRangeWith_accepts body locals slot typed total
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · rw [accepted]
        exact ⟨plan, rfl⟩
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
    rw [extractScalarWordRangeWith]
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split
          · exact ⟨_, rfl⟩
          · simp [scalarResultType_accepts, hc, ht, f]
    · cases type <;> simp [ResultType.expr]
  | letPredicateFn expression type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression.expr)
    obtain ⟨target, ht⟩ := ihb (.predicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    rw [extractScalarWordRangeWith]
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split
          · exact ⟨_, rfl⟩
          · simp [scalarResultType_boolean, booleanType_accepts, booleanLocalOperands_expr, hc, ht, f]
    · cases type <;> simp [BooleanType.expr]
  | letBooleanPredicateFn expression type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.boolean argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression.expr)
    obtain ⟨target, ht⟩ := ihb (.booleanPredicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_boolean, booleanType_accepts, booleanLocalOperands_expr, hc, ht, f]
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
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hc, ht, f]
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
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hc, ht, f]
  | letManyFn shape function _ ihb =>
    have accepts (arguments : List LeanExe.IR.Expr) (len : arguments.length = shape.arity) :=
      extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
        (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len, typed])
        (scalarWords_total _ total)
    obtain ⟨checked, hc⟩ := accepts (List.replicate shape.arity (.u64 0)) (by simp)
    simp only [List.reverse_replicate, List.map_replicate] at hc
    let f := fun (arguments : List LeanExe.IR.Expr) => extractScalarExprWith
      (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
    obtain ⟨target, ht⟩ := ihb (.manyFunction shape.arity f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    rw [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow,
      Parameter.arrow, Parameter.lambda, Parameter.lambda, extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · rw [scalarFunctionSuffix_not_result shape.suffix shape.positive]
          have accepted := scalarManyFunction_accepts shape
          simp only [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at accepted
          rw [accepted]
          simp only [bind, hc, Option.bind_some, ht, f]
          exact ⟨target, rfl⟩
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
    cases unitForm <;> rw [UnitSyntax.type, extractScalarWordRangeWith]
    all_goals
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split
          · exact ⟨_, rfl⟩
          · simp [scalarResultType_accepts, hc, ht, f]
  | idFunctionInput input result _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simpa only [ite_true] using ⟨plan, hp⟩
  | letFlagBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [booleanType_accepts, hb, hp]
    all_goals cases input <;> simp [BooleanType.expr]
  | bindFlagBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [BooleanWordRange.bind]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [booleanWordRangeBindTypes_accepts, hb, hp]
  | letWordBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [booleanType_scalar, scalarResultType_accepts]
          exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
    all_goals cases input <;> simp [ResultType.expr]
  | bindWordBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [Identity.bind]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
          exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
  | letWordResult input _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [extractScalarWordRangeWith]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [booleanType_scalar, scalarResultType_accepts]
          exact scalarRangeValueBinding_accepts_loop hp ht
    all_goals cases input <;> simp [ResultType.expr]
  | bindWordResult input output _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    simp only [Identity.bind]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
          exact scalarRangeValueBinding_accepts_loop hp ht
  | choice type condition _ _ yesIH noIH =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yes, hy⟩ := yesIH locals typed total
    obtain ⟨no, hn⟩ := noIH locals typed total
    simp only [WordRange.choiceExpr]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hg, hy, hn]
  | run type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    simp only [Identity.run]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hp]
  | pure type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    simp only [Identity.pure]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hp]
  | metadata _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨plan, hp⟩



theorem extractScalarWordRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan) :
    WordRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarWordRangeWith locals slot source generalizing plan with
  | case1 locals source value matched => exact .scalar (extractScalarExprWith_supported matched)
  | case2 locals source notScalar before matched => exact .rangeExit (extractScalarRangeExitWith_supported matched)
  | case3 locals source notScalar notRange before matched => exact .booleanWord (extractScalarBooleanWordRangeWith_supported matched)
  | case4 => contradiction
  | case5 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    rw [sameType, sameValue]
    exact .letManyFn shape (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case6 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letBinaryFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case7 => contradiction
  | case8 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    rw [booleanType_sound parsed, booleanLocalOperands_sound parsedValue]
    exact .letPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih expression compiled)
  | case9 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case10 => contradiction
  | case11 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letUnitFn type .unit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case12 => contradiction
  | case13 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letUnitFn type .punit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    rw [booleanType_sound parsed, booleanLocalOperands_sound parsedValue]
    exact .letBooleanPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih expression compiled)
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letBooleanFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case17 locals name typeName resultType typeBi paramName input value paramBi body nondep noScalar noRange noBooleanWord ih =>
    exact .idFunctionInput input resultType (ih compiled)
  | case18 => contradiction
  | case19 => contradiction
  | case20 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed notScalar notRange notOld bodyIH valueIH =>
    rw [scalarResultType_sound parsed]
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .letWordBefore input (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .letWordResult input (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case21 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    exact .letFlagBefore input (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using bodyIH bound compiled)
  | case22 => contradiction
  | case23 locals input output value name domain body binder notBoolean types parsed notScalar notRange notOld bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .bindWordBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .bindWordResult types.1 types.2 (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case24 locals input output value name domain body binder types parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using bodyIH bound compiled)
  | case25 => contradiction
  | case26 locals type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .choice result (extractScalarExprWith_supported hg) (yesIH hy) (noIH hn)
  | case27 => contradiction
  | case28 locals type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    exact .run result (ih compiled)
  | case29 => contradiction
  | case30 locals type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    exact .pure result (ih compiled)
  | case31 locals data body notScalar notRange notBoolean ih => exact .metadata (ih compiled)
  | case32 => contradiction

/-- The selected word computation preserves its native source result. -/


theorem extractScalarWordRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarWordRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, WordRange.Eval source values value ∧ plan.Meaning saved value := by
  fun_induction extractScalarWordRangeWith locals saved.length source generalizing values plan with
  | case1 locals source target matched =>
    cases compiled
    obtain ⟨value, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    exact ⟨value, .scalar evaluated, ScalarRangeExitPlan.scalar_meaning (fun accumulator index stop done =>
      extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))⟩
  | case2 locals source notScalar before matched =>
    cases compiled
    obtain ⟨value, evaluated, meaning⟩ := extractScalarRangeExitWith_correct saved values matched typed bindings total
    exact ⟨value, .rangeExit evaluated, meaning⟩
  | case3 locals source notScalar notRange before matched =>
    cases compiled
    obtain ⟨value, evaluated, meaning⟩ := extractScalarBooleanWordRangeWith_correct saved values matched typed bindings total
    exact ⟨value, .booleanWord evaluated, meaning⟩
  | case4 => contradiction
  | case5 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    have supported := extractScalarExprWith_supported validated
    have function : SupportedWith (List.replicate shape.arity .word ++ locals.map ScalarBinding.kind) shape.body := by
      simpa [ScalarBinding.kind] using supported
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.manyFunction shape.arity f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro arguments native target len argumentsMeaning hc
        exact extractScalarExprWith_correct (meanings native (argumentsMeaning.length.symm.trans len)) hc
          ((bindings accumulator index stop exitFlag).words argumentsMeaning.reverse)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro arguments len
          exact extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
            (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len])
            (scalarWords_total _ total)
        · exact total binding member)
    rw [sameType, sameValue]
    exact ⟨flag, .letManyFn shape meanings evaluated, meaning⟩
  | case6 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x y : UInt64) := supported.evaluates (.word y :: .word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x y => (native x y).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.binaryFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro first x second y target hx hy hc
        exact extractScalarExprWith_correct ((native x y).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .word first) (value := .word x) hx).cons
            (binding := .word second) (value := .word y) hy)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro first second
          apply extractScalarExprWith_accepts supported (.word second :: .word first :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBinaryFn type (fun x y => (native x y).choose_spec) evaluated, meaning⟩
  | case7 => contradiction
  | case8 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    have sameType := booleanType_sound parsed
    subst resultType
    have sameValue := booleanLocalOperands_sound parsedValue
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : UInt64, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.word x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih expression (.predicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case9 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function false f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case10 => contradiction
  | case11 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .unit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case12 => contradiction
  | case13 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .punit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    have sameType := booleanType_sound parsed
    subst resultType
    have sameValue := booleanLocalOperands_sound parsedValue
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : Bool, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.boolean x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih expression (.booleanPredicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : Bool) := supported.evaluates (.boolean x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.booleanFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case17 locals name typeName resultType typeBi paramName input value paramBi body nondep noScalar noRange noBooleanWord ih =>
    obtain ⟨result, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨result, .idFunctionInput input resultType evaluated, meaning⟩
  | case18 => contradiction
  | case19 => contradiction
  | case20 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed notScalar notRange notOld bodyIH valueIH =>
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
  | case21 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
      intro accumulator index stop done
      exact (bindings accumulator index stop done).cons
        (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
    obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨result, .letFlagBefore input evaluated continuation, meaning⟩
  | case22 => contradiction
  | case23 locals input output value name domain body binder notBoolean types parsed notScalar notRange notOld bodyIH valueIH =>
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
  | case24 locals input output value name domain body binder types parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
      intro accumulator index stop done
      exact (bindings accumulator index stop done).cons
        (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
    obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨result, .bindFlagBefore types.1 types.2 evaluated continuation, meaning⟩
  | case25 => contradiction
  | case26 locals type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported hg).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have stable : ∀ accumulator index stop done,
        guard.ScalarEval (LeanExe.IR.rangeExitStore saved accumulator index stop done) flag.toUInt64
          (LeanExe.IR.rangeExitStore saved accumulator index stop done) := by
      intro accumulator index stop done
      exact extractScalarExprWith_correct evaluated hg (bindings accumulator index stop done)
    cases flag with
    | false =>
      obtain ⟨value, branch, meaning⟩ := noIH values hn typed bindings total
      exact ⟨value, .choice result evaluated branch, ScalarRangeExitPlan.choice_meaning stable meaning⟩
    | true =>
      obtain ⟨value, branch, meaning⟩ := yesIH values hy typed bindings total
      exact ⟨value, .choice result evaluated branch, ScalarRangeExitPlan.choice_meaning stable meaning⟩
  | case27 => contradiction
  | case28 locals type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .run result evaluated, meaning⟩
  | case29 => contradiction
  | case30 locals type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .pure result evaluated, meaning⟩
  | case31 locals data body notScalar notRange notBoolean ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .metadata evaluated, meaning⟩
  | case32 => contradiction



theorem extractScalarWordRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarWordRangeWith locals slot source generalizing plan with
  | case1 locals source target matched =>
    cases compiled
    exact ScalarRangeExitPlan.scalar_holds P literal
      (extractScalarExprWith_invariant P literal binary choice matched bindings)
  | case2 locals source notScalar before matched =>
    cases compiled
    exact extractScalarRangeExitWith_invariant P literal binary choice accumulator index matched bindings
  | case3 locals source notScalar notRange before matched =>
    cases compiled
    exact extractScalarBooleanWordRangeWith_invariant P literal binary choice accumulator index matched bindings
  | case4 => contradiction
  | case5 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro arguments target len holds extracted
      exact extractScalarExprWith_invariant P literal binary choice extracted (scalarWords_holds
        (fun argument member => holds argument (by simpa using member)) bindings)
    · exact bindings binding member
  | case6 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro first second target firstValid secondValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact secondValid
      rcases List.mem_cons.mp member with rfl | member
      · exact firstValid
      · exact bindings binding member
    · exact bindings binding member
  | case7 => contradiction
  | case8 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    apply ih expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case9 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case10 => contradiction
  | case11 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case12 => contradiction
  | case13 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    apply ih expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed noScalar noRange noBooleanWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case17 locals name typeName resultType typeBi paramName input value paramBi body nondep noScalar noRange noBooleanWord ih =>
    exact ih compiled bindings
  | case18 => contradiction
  | case19 => contradiction
  | case20 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed notScalar notRange notOld bodyIH valueIH =>
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
  | case21 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    apply bodyIH bound compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case22 => contradiction
  | case23 locals input output value name domain body binder notBoolean types parsed notScalar notRange notOld bodyIH valueIH =>
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
  | case24 locals input output value name domain body binder types parsed notScalar notRange notOld bodyIH =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, compiled⟩ := compiled
    apply bodyIH bound compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case25 => contradiction
  | case26 locals type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    exact ScalarRangeExitPlan.choice_holds P literal choice
      (extractScalarExprWith_invariant P literal binary choice hg bindings) (yesIH hy bindings) (noIH hn bindings)
  | case27 => contradiction
  | case28 locals type body result parsed notScalar notRange notBoolean ih => exact ih compiled bindings
  | case29 => contradiction
  | case30 locals type body result parsed notScalar notRange notBoolean ih => exact ih compiled bindings
  | case31 locals data body notScalar notRange notBoolean ih => exact ih compiled bindings
  | case32 => contradiction



end LeanExe.Extract.Core
