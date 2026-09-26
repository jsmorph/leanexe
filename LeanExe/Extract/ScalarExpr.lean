import LeanExe.Extract.ScalarExprCore

namespace LeanExe.Extract.Core

theorem extractScalarExprWith_correct {source : Lean.Expr} {values : List LeanExe.Source.Scalar.Value} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.EvalWith source values value)
    {locals : List ScalarBinding} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ScalarBindingsMatch locals values store) :
    target.ScalarEval store value store := by
  induction semantics generalizing locals target with
  | var h => exact bindings.word (by simpa only [extractScalarExprWith] using compiled) h
  | natural h => exact bindings.natural (by simpa only [extractScalarExprWith] using compiled) h
  | literal =>
    simp only [extractScalarExprWith, Option.some.injEq] at compiled
    subst target
    exact .const
  | ofNat =>
    simp only [extractScalarExprWith_literalExpr, Option.some.injEq] at compiled
    subst target
    exact .const
  | ofNatInstance meaning =>
    simp only [extractScalarExprWith_ofNatInstance _ meaning, Option.some.injEq] at compiled
    subst target
    exact .const
  | naturalLiteral meaning =>
    simp only [extractScalarExprWith_naturalLiteral _ _ meaning, Option.some.injEq] at compiled
    subst target
    exact .const
  | ofNatNatural numberMeaning instanceMeaning =>
    simp only [extractScalarExprWith_ofNatNatural _ numberMeaning instanceMeaning, Option.some.injEq] at compiled
    subst target
    exact .const
  | complement head _ ih =>
    rw [extractScalarExprWith_complement head] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨argument, ha, rfl⟩ := compiled
    exact lowerComplement_correct (ih ha bindings)
  | extremum op _ _ ihl ihr =>
    rw [extractScalarExprWith_extremum] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    exact lowerExtremum_correct op (ihl ha bindings) (ihr hb bindings)
  | @binary head f a values x b y op left right ihl ihr =>
    rw [extractScalarExprWith_binary op] at compiled
    obtain ⟨p, hp, hf⟩ := sourceHead_recognized op
    cases ha : extractScalarExprWith locals a with
    | none => simp [hp, ha] at compiled
    | some aIR =>
      cases hb : extractScalarExprWith locals b with
      | none => simp [hp, ha, hb] at compiled
      | some bIR =>
        have heq : p.lower aIR bIR = target := by simpa [hp, ha, hb] using compiled
        subst target
        rw [← hf]
        exact p.lower_correct (ihl ha bindings) (ihr hb bindings)
  | @choose a values x b y t e value op type left right branch ihl ihr ihb =>
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, rfl⟩ := compiled
    have condition := lowerComparison_correct op (ihl ha bindings) (ihr hb bindings)
    cases flag : op.denote x y with
    | false =>
      exact .iteFalse (by simpa [flag] using condition)
        (ihb (by simpa [flag] using he) bindings)
    | true =>
      exact .iteTrue (by simpa [flag] using condition)
        (ihb (by simpa [flag] using ht) bindings)
  | @chooseCompound values t e value guard type native _ _ ihArgs ihb =>
    rw [extractScalarExprWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractGuard_correct guard.tree _ native hc
      (fun operand member expression found => ihArgs operand member found bindings)
    cases flag : guard.denote native with
    | false =>
      exact .iteFalse (by simpa [flag] using condition)
        (ihb (by simpa [flag] using he) bindings)
    | true =>
      exact .iteTrue (by simpa [flag] using condition)
        (ihb (by simpa [flag] using ht) bindings)
  | @chooseDependent values t e value guard type tn fn tb fb native _ _ ihArgs ihb =>
    rw [extractScalarExprWith_dependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractGuard_correct guard _ native hc
      (fun operand member expression found => ihArgs operand member found bindings)
    cases flag : guard.denote native with
    | false =>
      exact .iteFalse (by simpa [flag] using condition)
        (ihb (by simpa [flag] using he) (bindings.cons (binding := .unit) (value := .unit) trivial))
    | true =>
      exact .iteTrue (by simpa [flag] using condition)
        (ihb (by simpa [flag] using ht) (bindings.cons (binding := .unit) (value := .unit) trivial))
  | @chooseBooleanDependent values t e value guard type tn fn tb fb native booleans variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_booleanDependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractBooleanLocalWith_correct guard.value _ native booleans hc bindings variables
      (fun operand member expression found => ihArgs operand member found bindings)
    cases flag : guard.value.denote native booleans with
    | false =>
      exact .iteFalse (by simpa [flag] using condition)
        (ihb (by simpa [flag] using he) (bindings.cons (binding := .unit) (value := .unit) trivial))
    | true =>
      exact .iteTrue (by simpa [flag] using condition)
        (ihb (by simpa [flag] using ht) (bindings.cons (binding := .unit) (value := .unit) trivial))
  | booleanWord expression variables _ ihArgs =>
    rw [extractScalarExprWith_booleanWord _ _ (fun negations index input same =>
      bindings.no_booleanPredicate_of_predicate (variables.functions index
        (by rw [same]; simp [LeanExe.Source.Scalar.BooleanLocal.functions])))
      (fun negations op left right same => hasBooleanPredicate_false (fun index member =>
        bindings.no_booleanPredicate_of_predicate (variables.functions index
          (by simpa [same, LeanExe.Source.Scalar.BooleanLocal.functions] using member))))
      (fun form negations unequal left right same => hasBooleanPredicate_false (fun index member =>
        bindings.no_booleanPredicate_of_predicate (variables.functions index
          (by simpa [same] using member))))
      (fun form negations unequal left right yes no same => hasBooleanPredicate_false (fun index member =>
        bindings.no_booleanPredicate_of_predicate (variables.functions index
          (by simpa [same] using member))))] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact guardWord_correct (extractBooleanLocalWith_correct expression _ _ _ hc bindings variables
      (fun operand member target found => ihArgs operand member found bindings))
  | @letBoolean values b value name nondep expression native booleans variables arguments body ihArgs ihb =>
    rw [extractScalarExprWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have meaning := extractBooleanLocalWith_correct expression _ native booleans hc bindings variables
      (fun operand member target found => ihArgs operand member found bindings)
    exact ihb ht (bindings.cons (binding := .boolean (guardWord c)) (value := .boolean _) (guardWord_correct meaning))
  | @idBindBoolean values b value name bi action type native booleans variables arguments body ihArgs ihb =>
    rw [extractScalarExprWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have meaning := extractBooleanLocalWith_correct action.leaf _ native booleans hc bindings variables
      (fun operand member target found => ihArgs operand member found bindings)
    exact ihb ht (bindings.cons (binding := .boolean (guardWord c)) (value := .boolean _) (guardWord_correct meaning))
  | @chooseBoolean values t e value guard type native booleans variables arguments branch ihArgs ihb =>
    rw [extractScalarExprWith_booleanBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractBooleanLocalWith_correct guard.value _ native booleans hc bindings variables
      (fun operand member expression found => ihArgs operand member found bindings)
    cases flag : guard.value.denote native booleans with
    | false => exact .iteFalse (by simpa [flag] using condition) (ihb (by simpa [flag] using he) bindings)
    | true => exact .iteTrue (by simpa [flag] using condition) (ihb (by simpa [flag] using ht) bindings)
  | letE value body ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ihb hc (bindings.cons (ihv hb bindings))
  | idRun type _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings
  | idPure type _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings
  | idBind input output value body ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ihb hc (bindings.cons (ihv hb bindings))
  | applyBoolean expression function variables _ ihArgs =>
    rw [extractScalarExprWith, bindings.no_wordFunction_of_boolean function,
      booleanLocalOperands_expr] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, condition, hc, ht⟩ := compiled
    have meaning := extractBooleanLocalWith_correct expression _ _ _ hc bindings variables
      (fun operand member expression found => ihArgs operand member found bindings)
    exact bindings.booleanFunction (Option.bind_eq_some_iff.mpr hf) function _ _ target
      (guardWord_correct meaning) ht
  | booleanChoiceWord form negations unequal left right yes no member function _ _ _ ihl ihr ihBranch =>
    rw [extractScalarExprWith_booleanChoice] at compiled
    split at compiled
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨first, hl, second, hr, trueBranch, ht, falseBranch, he, rfl⟩ := compiled
      apply booleanWordChoice_correct negations unequal (ihl hl bindings) (ihr hr bindings)
      split
      next selected => exact ihBranch (by simpa only [if_pos selected] using ht) bindings
      next selected => exact ihBranch (by simpa only [if_neg selected] using he) bindings
    · have absent := extractBooleanLocalWith_none_of_predicate_absent
        (value := form.local negations unequal left right yes no) (by simpa using member)
        (bindings.no_predicate_of_booleanPredicate function)
        (fun operand _member => extractScalarExprWith locals operand)
      rw [absent] at compiled
      contradiction
  | booleanEqualityWord form negations unequal left right member function _ _ ihl ihr =>
    rw [extractScalarExprWith_booleanEquality] at compiled
    split at compiled
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨first, hl, second, hr, rfl⟩ := compiled
      exact booleanWordEquality_correct form negations unequal (ihl hl bindings) (ihr hr bindings)
    · have absent := extractBooleanLocalWith_none_of_predicate_absent
        (value := form.local negations unequal left right) (by simpa using member)
        (bindings.no_predicate_of_booleanPredicate function)
        (fun operand _member => extractScalarExprWith locals operand)
      rw [absent] at compiled
      contradiction
  | booleanJunctionWord negations op left right member function _ _ ihl ihr =>
    rw [extractScalarExprWith_booleanJunction] at compiled
    split at compiled
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨first, hl, second, hr, rfl⟩ := compiled
      exact booleanWordJunction_correct negations op (ihl hl bindings) (ihr hr bindings)
    · have absent := extractBooleanLocalWith_none_of_predicate_absent
        (value := LeanExe.Source.Scalar.BooleanLocal.junction negations op left right)
        (by simpa [LeanExe.Source.Scalar.BooleanLocal.functions] using member)
        (bindings.no_predicate_of_booleanPredicate function)
        (fun operand _member => extractScalarExprWith locals operand)
      rw [absent] at compiled
      contradiction
  | applyBooleanPredicateWord negations function argument ihArg =>
    rw [extractScalarExprWith_applyBooleanPredicateWordOnly _ _ _ _
      (bindings.no_predicate_of_booleanPredicate function)] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨f, hf, argument, ha, result, hr, rfl⟩ := compiled
    exact booleanWordNegation_correct negations
      (bindings.booleanPredicateFunction (Option.bind_eq_some_iff.mpr hf) function _ _ result
        (ihArg ha bindings) hr)
  | apply function argument ih =>
    rw [extractScalarExprWith_wordApplyOnly _ _ _
      (bindings.no_booleanFunction_of_function function)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    exact bindings.function (Option.bind_eq_some_iff.mpr hf) function arg _ target (ih ha bindings) ht
  | letFn type function body ihf ihb =>
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    exact ihf value compiled (bindings.cons ha)
  | letPredicateFn expression type variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_letPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact guardWord_correct (extractBooleanLocalWith_correct expression _ _ _ hc
      (bindings.cons (binding := .word argument) (value := .word value) ha) (variables value)
      (fun operand member expression found => ihArgs value operand member found
        (bindings.cons (binding := .word argument) (value := .word value) ha)))
  | letBooleanPredicateFn expression type variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_letBooleanPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact guardWord_correct (extractBooleanLocalWith_correct expression _ _ _ hc
      (bindings.cons (binding := .boolean argument) (value := .boolean value) ha) (variables value)
      (fun operand member expression found => ihArgs value operand member found
        (bindings.cons (binding := .boolean argument) (value := .boolean value) ha)))
  | predicateInput input result _ ih =>
    rw [extractScalarExprWith_predicateInput] at compiled
    exact ih compiled bindings
  | letBooleanFn type function body ihf ihb =>
    rw [extractScalarExprWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    exact ihf value compiled (bindings.cons ha)
  | unitApply unitForm function argument ih =>
    rw [extractScalarExprWith_unitApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    exact bindings.function (Option.bind_eq_some_iff.mpr hf) function arg _ target (ih ha bindings) ht
  | letUnitFn type unitForm function body ihf ihb =>
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    exact ihf value compiled ((bindings.cons (binding := .unit) (value := .unit) trivial).cons ha)
  | binaryApply function first second ihFirst ihSecond =>
    rw [extractScalarExprWith_binaryApply _ _ _ _ first.not_unit] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, ht⟩ := compiled
    exact bindings.binaryFunction (Option.bind_eq_some_iff.mpr hf) function a _ b _ target
      (ihFirst ha bindings) (ihSecond hb bindings) ht
  | letBinaryFn type function body ihf ihb =>
    rw [extractScalarExprWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro first x second y target hx hy compiled
    exact ihf x y compiled ((bindings.cons (binding := .word first) (value := .word x) hx).cons
      (binding := .word second) (value := .word y) hy)
  | manyApply call function _ ihArgs =>
    rw [extractScalarExprWith_manyApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arguments, ha, ht⟩ := compiled
    apply bindings.manyFunction (Option.bind_eq_some_iff.mpr hf) function arguments _ target
      (extractScalarArguments_length _ _ ha) ?_ ht
    exact extractScalarArguments_relation call.arguments _ _ _ ha
      (fun operand member expression found => ihArgs operand member found bindings)
  | letManyFn shape function body ihf ihb =>
    rw [extractScalarExprWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro arguments native target len meanings compiled
    exact ihf native (meanings.length.symm.trans len) compiled (bindings.words meanings.reverse)
  | range => rw [extractScalarExprWith_range] at compiled; contradiction
  | idLet _ ih => exact ih (by simpa only [extractScalarExprWith_idLet] using compiled) bindings
  | ofNatTyped numberMeaning instanceMeaning =>
    simp only [extractScalarExprWith_ofNatTyped _ numberMeaning instanceMeaning, Option.some.injEq] at compiled
    subst target
    exact .const
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings

/-- General preservation for the production expression traversal. -/
theorem extractScalarExpr_correct {source : Lean.Expr} {values : List UInt64} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval source values value)
    {locals : List Nat} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExpr locals source = some target)
    (bindings : ScalarLocalsMatch locals values store) :
    target.ScalarEval store value store := by
  apply extractScalarExprWith_correct semantics compiled
  intro index binding value he hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he hv
  obtain ⟨slot, hs, rfl⟩ := he
  obtain ⟨word, hw, rfl⟩ := hv
  exact LeanExe.IR.Expr.ScalarEval.local ((bindings _ _ hs).trans hw)

theorem extractScalarExprWith_accepts {source : Lean.Expr} {types : List LeanExe.Source.Scalar.BindingKind}
    (supported : LeanExe.Source.Scalar.SupportedWith types source)
    (locals : List ScalarBinding) (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ target, extractScalarExprWith locals source = some target := by
  induction supported generalizing locals with
  | var hi =>
    obtain ⟨target, found⟩ := scalarWord_lookup (typed ▸ hi)
    exact ⟨target, by simpa only [extractScalarExprWith] using found⟩
  | natural present =>
    obtain ⟨target, found⟩ := scalarNatural_lookup (typed ▸ present)
    exact ⟨target, by simpa only [extractScalarExprWith] using found⟩
  | literal => exact ⟨.u64 _, by rw [extractScalarExprWith]⟩
  | ofNat => exact ⟨.u64 _, extractScalarExprWith_literalExpr _ _⟩
  | ofNatInstance meaning => exact ⟨.u64 _, extractScalarExprWith_ofNatInstance _ meaning⟩
  | naturalLiteral meaning => exact ⟨.u64 _, extractScalarExprWith_naturalLiteral _ _ meaning⟩
  | ofNatNatural numeral meaning => exact ⟨.u64 _, extractScalarExprWith_ofNatNatural _ numeral meaning⟩
  | complement head _ ih =>
    obtain ⟨argument, ha⟩ := ih locals typed total
    exact ⟨lowerComplement argument, by rw [extractScalarExprWith_complement head]; simp [ha]⟩
  | extremum op _ _ ihl ihr =>
    obtain ⟨a, ha⟩ := ihl locals typed total
    obtain ⟨b, hb⟩ := ihr locals typed total
    exact ⟨lowerExtremum op a b, by rw [extractScalarExprWith_extremum]; simp [ha, hb]⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceHead_recognized op
    obtain ⟨a, ha⟩ := ihl locals typed total
    obtain ⟨b, hb⟩ := ihr locals typed total
    exact ⟨p.lower a b, by rw [extractScalarExprWith_binary op]; simp [hp, ha, hb]⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨a, ha⟩ := ihl locals typed total
    obtain ⟨b, hb⟩ := ihr locals typed total
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨.ite (lowerComparison op a b) t e, by
      rw [extractScalarExprWith_branch]; simp [ha, hb, ht, he]⟩
  | chooseCompound guard type _ _ _ ihArgs iht ihe =>
    obtain ⟨c, hc⟩ := extractGuard_accepts guard.tree
      (fun operand _ => extractScalarExprWith locals operand)
      (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨.ite c t e, by rw [extractScalarExprWith_compoundBranch]; simp [hc, ht, he]⟩
  | chooseDependent guard type tn fn tb fb _ _ _ ihArgs iht ihe =>
    obtain ⟨c, hc⟩ := extractGuard_accepts guard
      (fun operand _ => extractScalarExprWith locals operand)
      (fun operand member => ihArgs operand member locals typed total)
    have extended : ∀ binding ∈ ScalarBinding.unit :: locals, binding.Total := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member
    obtain ⟨t, ht⟩ := iht (.unit :: locals) (by simp [ScalarBinding.kind, typed]) extended
    obtain ⟨e, he⟩ := ihe (.unit :: locals) (by simp [ScalarBinding.kind, typed]) extended
    exact ⟨.ite c t e, by rw [extractScalarExprWith_dependentBranch]; simp [hc, ht, he]⟩
  | chooseBooleanDependent guard type tn fn tb fb variables _ _ _ ihArgs iht ihe =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals guard.value
      (fun operand _ => extractScalarExprWith locals operand)
      (by simpa [typed] using variables)
      (fun operand member => ihArgs operand member locals typed total)
    have extended : ∀ binding ∈ ScalarBinding.unit :: locals, binding.Total := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member
    obtain ⟨t, ht⟩ := iht (.unit :: locals) (by simp [ScalarBinding.kind, typed]) extended
    obtain ⟨e, he⟩ := ihe (.unit :: locals) (by simp [ScalarBinding.kind, typed]) extended
    exact ⟨.ite c t e, by rw [extractScalarExprWith_booleanDependentBranch]; simp [hc, ht, he]⟩
  | booleanWord expression variables _ ihArgs =>
    obtain ⟨condition, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals expression
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => ihArgs operand member locals typed total)
    exact ⟨guardWord condition, by
      rw [extractScalarExprWith_booleanWord _ _ (fun negations index input same =>
        scalarBooleanPredicate_none_of_predicate (typed ▸ variables.functions index
          (by rw [same]; simp [LeanExe.Source.Scalar.BooleanLocal.functions])))
        (fun negations op left right same => hasBooleanPredicate_false (fun index member =>
          scalarBooleanPredicate_none_of_predicate (typed ▸ variables.functions index
            (by simpa [same, LeanExe.Source.Scalar.BooleanLocal.functions] using member))))
        (fun form negations unequal left right same => hasBooleanPredicate_false (fun index member =>
          scalarBooleanPredicate_none_of_predicate (typed ▸ variables.functions index
            (by simpa [same] using member))))
        (fun form negations unequal left right yes no same => hasBooleanPredicate_false (fun index member =>
          scalarBooleanPredicate_none_of_predicate (typed ▸ variables.functions index
            (by simpa [same] using member))))]
      simp [hc]⟩
  | letBoolean expression variables _ _ ihArgs ihb =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals expression
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨target, ht⟩ := ihb (.boolean (guardWord c) :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨target, by rw [extractScalarExprWith_letBoolean]; simp [hc, ht]⟩
  | idBindBoolean action type variables _ _ ihArgs ihb =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals action.leaf
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨target, ht⟩ := ihb (.boolean (guardWord c) :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨target, by rw [extractScalarExprWith_booleanBind]; simp [hc, ht]⟩
  | chooseBoolean guard type variables _ _ _ ihArgs iht ihe =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals guard.value
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨.ite c t e, by rw [extractScalarExprWith_booleanBranch]; simp [hc, ht, he]⟩
  | letE _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member; rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨target, by simp [extractScalarExprWith, hb, ht]⟩
  | idRun type _ ih => simpa only [extractScalarExprWith_idRun] using ih locals typed total
  | idPure type _ ih => simpa only [extractScalarExprWith_idPure] using ih locals typed total
  | idBind input output _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member; rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨target, by simp [hb, ht]⟩
  | applyBoolean expression present variables _ ihArgs =>
    obtain ⟨f, hf⟩ := scalarBooleanFunction_lookup (typed ▸ present)
    obtain ⟨condition, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals expression _
      (typed ▸ variables) (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) (guardWord condition)
    have found := congrArg (fun binding => binding.bind ScalarBinding.booleanFunction?) hf
    exact ⟨target, by rw [extractScalarExprWith_booleanApply _ _ _ _ found]; simp [hc, ht]⟩
  | booleanChoiceWord form negations unequal left right yes no member present _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨first, hl⟩ := ihl locals typed total
    obtain ⟨second, hr⟩ := ihr locals typed total
    obtain ⟨trueBranch, ht⟩ := iht locals typed total
    obtain ⟨falseBranch, he⟩ := ihe locals typed total
    have found := hasBooleanPredicate_of_kind member (typed ▸ present)
    exact ⟨booleanWordChoice negations unequal first second trueBranch falseBranch, by
      rw [extractScalarExprWith_booleanChoice]; simp [found, hl, hr, ht, he]⟩
  | booleanEqualityWord form negations unequal left right member present _ _ ihl ihr =>
    obtain ⟨first, hl⟩ := ihl locals typed total
    obtain ⟨second, hr⟩ := ihr locals typed total
    have found := hasBooleanPredicate_of_kind member (typed ▸ present)
    exact ⟨booleanWordEquality negations unequal first second, by
      rw [extractScalarExprWith_booleanEquality]; simp [found, hl, hr]⟩
  | booleanJunctionWord negations op left right member present _ _ ihl ihr =>
    obtain ⟨first, hl⟩ := ihl locals typed total
    obtain ⟨second, hr⟩ := ihr locals typed total
    have found := hasBooleanPredicate_of_kind member (typed ▸ present)
    exact ⟨booleanWordJunction negations op first second, by
      rw [extractScalarExprWith_booleanJunction]; simp [found, hl, hr]⟩
  | applyBooleanPredicateWord negations present _ ihArg =>
    obtain ⟨f, hf⟩ := scalarBooleanPredicateFunction_lookup (typed ▸ present)
    obtain ⟨argument, ha⟩ := ihArg locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) argument
    have found := congrArg (fun binding => binding.bind ScalarBinding.booleanPredicateFunction?) hf
    exact ⟨booleanWordNegation negations target, by
      rw [extractScalarExprWith_applyBooleanPredicateWord _ _ _ _ _ found]; simp [ha, ht]⟩
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := scalarFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := ih locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarExprWith]; simp [hf, ScalarBinding.function?, ha, ht]⟩
  | @letFn types a b name typeName typeBi paramName paramBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.word argument :: locals)
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
    exact ⟨target, by rw [extractScalarExprWith_letFn]; simp [hc, ht, f]⟩
  | letPredicateFn expression type variables _ _ ihArgs ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractBooleanLocalWith_accepts
      (.word argument :: locals) expression
      (fun operand _member => extractScalarExprWith (.word argument :: locals) operand)
      (by simpa [ScalarBinding.kind, typed] using variables)
      (fun operand member => ihArgs operand member (.word argument :: locals)
        (by simp [ScalarBinding.kind, typed]) (by
          intro binding member; rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => do
      let condition ← extractBooleanLocalWith (.word argument :: locals) expression
        (fun operand _member => extractScalarExprWith (.word argument :: locals) operand)
      pure (guardWord condition)
    obtain ⟨target, ht⟩ := ihb (.predicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · intro argument
          obtain ⟨condition, found⟩ := accepts argument
          exact ⟨guardWord condition, by simp [f, found]⟩
        · exact total binding member)
    refine ⟨target, ?_⟩
    rw [extractScalarExprWith_letPredicateFn]
    simp only [hc, bind, Option.bind_some]
    exact ht
  | letBooleanPredicateFn expression type variables _ _ ihArgs ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractBooleanLocalWith_accepts
      (.boolean argument :: locals) expression
      (fun operand _member => extractScalarExprWith (.boolean argument :: locals) operand)
      (by simpa [ScalarBinding.kind, typed] using variables)
      (fun operand member => ihArgs operand member (.boolean argument :: locals)
        (by simp [ScalarBinding.kind, typed]) (by
          intro binding member; rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => do
      let condition ← extractBooleanLocalWith (.boolean argument :: locals) expression
        (fun operand _member => extractScalarExprWith (.boolean argument :: locals) operand)
      pure (guardWord condition)
    obtain ⟨target, ht⟩ := ihb (.booleanPredicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · intro argument
          obtain ⟨condition, found⟩ := accepts argument
          exact ⟨guardWord condition, by simp [f, found]⟩
        · exact total binding member)
    refine ⟨target, ?_⟩
    rw [extractScalarExprWith_letBooleanPredicateFn]
    simp only [hc, bind, Option.bind_some]
    exact ht
  | predicateInput input result _ ih =>
    obtain ⟨target, ht⟩ := ih locals typed total
    exact ⟨target, by rw [extractScalarExprWith_predicateInput]; exact ht⟩
  | @letBooleanFn types a b name typeName typeBi paramName paramBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.boolean argument :: locals)
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
    exact ⟨target, by rw [extractScalarExprWith_letBooleanFn]; simp [hc, ht, f]⟩
  | unitApply unitForm present _ ih =>
    obtain ⟨f, hf⟩ := scalarFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := ih locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarExprWith_unitApply]; simp [hf, ScalarBinding.function?, ha, ht]⟩
  | @letUnitFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.word argument :: .unit :: locals)
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
    exact ⟨target, by rw [extractScalarExprWith_letUnitFn]; simp [hc, ht, f]⟩
  | binaryApply present first _ ihFirst ihSecond =>
    obtain ⟨f, hf⟩ := scalarBinaryFunction_lookup (typed ▸ present)
    obtain ⟨a, ha⟩ := ihFirst locals typed total
    obtain ⟨b, hb⟩ := ihSecond locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) a b
    exact ⟨target, by
      rw [extractScalarExprWith_binaryApply _ _ _ _ first.not_unit]
      simp [hf, ScalarBinding.binaryFunction?, ha, hb, ht]⟩
  | @letBinaryFn types a b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type _ _ ihf ihb =>
    have accepts (first second : LeanExe.IR.Expr) := ihf (.word second :: .word first :: locals)
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
    exact ⟨target, by rw [extractScalarExprWith_letBinaryFn]; simp [hc, ht, f]⟩
  | manyApply call present _ ihArgs =>
    obtain ⟨f, hf⟩ := scalarManyFunction_lookup (typed ▸ present)
    obtain ⟨arguments, ha⟩ := extractScalarArguments_accepts call.arguments
      (fun operand _ => extractScalarExprWith locals operand)
      (fun operand member => ihArgs operand member locals typed total)
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arguments
      (extractScalarArguments_length _ _ ha)
    exact ⟨target, by
      rw [extractScalarExprWith_manyApply]
      simp only [bind, hf, Option.bind_some, ScalarBinding.manyFunction?, beq_self_eq_true,
        ↓reduceIte, ha, ht]⟩
  | letManyFn shape _ _ ihf ihb =>
    have accepts (arguments : List LeanExe.IR.Expr) (len : arguments.length = shape.arity) :=
      ihf (arguments.reverse.map ScalarBinding.word ++ locals)
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
    exact ⟨target, by rw [extractScalarExprWith_letManyFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
  | idLet _ ih => simpa only [extractScalarExprWith_idLet] using ih locals typed total
  | ofNatTyped numeral meaning => exact ⟨.u64 _, extractScalarExprWith_ofNatTyped _ numeral meaning⟩
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals typed total

theorem extractScalarExpr_accepts {source : Lean.Expr} {arity : Nat}
    (supported : LeanExe.Source.Scalar.Supported arity source)
    (locals : List Nat) (len : locals.length = arity) :
    ∃ target, extractScalarExpr locals source = some target :=
  extractScalarExprWith_accepts supported _
    (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len])
    (by intro binding member; obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member; trivial)

/-- Success admits only the independently specified source grammar. -/
theorem extractScalarExprWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExprWith locals source = some target) :
    LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarExprWith.induct generalizing target with
  | case1 locals index =>
    exact .var (scalarWord_kind (by simpa only [extractScalarExprWith] using compiled))
  | case2 => exact .literal
  | case3 locals levels index =>
    exact .natural (scalarNatural_kind (by simpa only [extractScalarExprWith] using compiled))
  | case4 locals levels numeral noLiteral noVariable number parsed =>
    exact .naturalLiteral (naturalLiteral_sound parsed)
  | case5 locals levels numeral noLiteral noVariable rejected =>
    rw [extractScalarExprWith] at compiled
    · rw [rejected] at compiled
      contradiction
    all_goals assumption
  | case6 locals sourceType numeral evidence rejected =>
    simp [extractScalarExprWith, rejected] at compiled
  | case7 locals sourceType numeral evidence type matched number parsed accepted =>
    have same := scalarResultType_sound matched
    subst sourceType
    exact .ofNatTyped (naturalLiteral_sound parsed) (typedLiteralInstance_sound accepted)
  | case8 locals sourceType numeral evidence type matched number parsed rejected =>
    simp [extractScalarExprWith, matched, parsed, rejected] at compiled
  | case9 locals sourceType numeral evidence type matched rejected =>
    simp [extractScalarExprWith, matched, rejected] at compiled
  | case10 locals sourceType body rejected =>
    rw [extractScalarExprWith, rejected] at compiled
    contradiction
  | case11 locals sourceType body type matched ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.run body type) = some target at compiled
    exact .idRun type (ih (by simpa only [extractScalarExprWith_idRun] using compiled))
  | case12 locals sourceType body rejected =>
    rw [extractScalarExprWith, rejected] at compiled
    contradiction
  | case13 locals sourceType body type matched ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.pure body type) = some target at compiled
    exact .idPure type (ih (by simpa only [extractScalarExprWith_idPure] using compiled))
  | case14 locals input output value name domain body bi rejected rejectedBoolean =>
    rw [extractScalarExprWith, rejected, rejectedBoolean] at compiled
    contradiction
  | case15 locals input output value name domain body bi rejected type matched rejectedAction =>
    rw [extractScalarExprWith, rejected, matched, rejectedAction] at compiled
    contradiction
  | case16 locals input output value name domain body bi rejected type matched action parsed ihArgs ihb =>
    obtain ⟨hi, hd, ho⟩ := booleanBindType_sound _ matched
    have outputEq := scalarResultType_sound ho
    have valueEq := booleanAction_sound parsed
    subst input domain output value
    change extractScalarExprWith locals
      (LeanExe.Source.Scalar.BooleanIdentity.bind name bi action.expr body type.expr) = some target at compiled
    rw [extractScalarExprWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.idBindBoolean action type
    · exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact ihArgs operand member found
    · simpa [ScalarBinding.kind] using ihb c ht
  | case17 locals input output value name domain body bi annotations matched ihv ihb =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound matched
    subst input domain output
    change extractScalarExprWith locals
      (LeanExe.Source.Scalar.Identity.bind name bi value body inputType outputType) = some target at compiled
    rw [extractScalarExprWith_idBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .idBind inputType outputType (ihv hb) (by simpa [ScalarBinding.kind] using ihb bound ht)
  | case18 locals sourceType condition evidence t e rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case19 locals sourceType condition evidence t e type typeMatched rejected rejectedGuard rejectedLocal =>
    rw [extractScalarExprWith] at compiled
    rw [typeMatched, rejected, rejectedGuard, rejectedLocal] at compiled
    contradiction
  | case20 locals sourceType condition evidence t e type typeMatched rejected rejectedGuard guard matched ihArgs iht ihe =>
    have typeEq := scalarResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := booleanLocalGuard_sound matched
    subst condition evidence
    change extractScalarExprWith locals (guard.branch type.expr t e) = some target at compiled
    rw [extractScalarExprWith_booleanBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.chooseBoolean guard type
      (extractBooleanLocalWith_variables hc) _ (iht ht) (ihe he)
    intro operand member
    obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
    exact ihArgs operand member found
  | case21 locals sourceType condition evidence t e type typeMatched rejected guard matched ihArgs iht ihe =>
    have typeEq := scalarResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := compoundGuard_sound matched
    subst condition evidence
    change LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) (guard.branch type.expr t e)
    change extractScalarExprWith locals (guard.branch type.expr t e) = some target at compiled
    rw [extractScalarExprWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.chooseCompound guard type _ (iht ht) (ihe he)
    intro operand member
    obtain ⟨expression, found⟩ := extractGuard_operands guard.tree _ hc operand member
    exact ihArgs operand member found
  | case22 locals sourceType condition evidence t e type typeMatched op a b matched ihl ihr iht ihe =>
    have typeEq := scalarResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := comparison_sound matched
    subst condition evidence
    change LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) (op.branch a b t e type)
    change extractScalarExprWith locals (op.branch a b t e type) = some target at compiled
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, _⟩ := compiled
    exact .choose op type (ihl ha) (ihr hb) (iht ht) (ihe he)
  | case23 locals index argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .unit (scalarFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case24 locals index argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .punit (scalarFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case25 locals index first second excludedUnit excludedPUnit ihFirst ihSecond =>
    rw [extractScalarExprWith_binaryApply _ _ _ _ (by
      intro unitForm; cases unitForm
      · exact excludedUnit
      · exact excludedPUnit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, _⟩ := compiled
    exact .binaryApply (scalarBinaryFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ihFirst ha) (ihSecond hb)
  | case26 locals argument ih =>
    rw [extractScalarExprWith_complement .direct] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, ha, _⟩ := compiled
    exact .complement .direct (ih ha)
  | case27 locals argument ih =>
    rw [extractScalarExprWith_complement .canonical] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, ha, _⟩ := compiled
    exact .complement .canonical (ih ha)
  | case28 locals left right ihl ihr =>
    change extractScalarExprWith locals (LeanExe.Source.Scalar.Extremum.minimum.expr left right) = some target at compiled
    rw [extractScalarExprWith_extremum .minimum] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, _⟩ := compiled
    exact .extremum .minimum (ihl ha) (ihr hb)
  | case29 locals left right ihl ihr =>
    change extractScalarExprWith locals (LeanExe.Source.Scalar.Extremum.maximum.expr left right) = some target at compiled
    rw [extractScalarExprWith_extremum .maximum] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, _⟩ := compiled
    exact .extremum .maximum (ihl ha) (ihr hb)
  | case30 locals type condition evidence tn td t tb fn fd e fb rejected =>
    rw [extractScalarExprWith, rejected] at compiled
    contradiction
  | case31 locals type condition evidence tn td t tb fn fd e fb result matched rejected rejectedBoolean =>
    rw [extractScalarExprWith, matched, rejected, rejectedBoolean] at compiled
    contradiction
  | case32 locals sourceType condition evidence tn td t tb fn fd e fb type matched rejected guard parsed ihArgs iht ihe =>
    have typeEq := scalarResultType_sound matched
    subst sourceType
    obtain ⟨hc, hd, htDomain, heDomain⟩ := booleanLocalDependentGuard_sound parsed
    subst condition evidence td fd
    change extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = some target at compiled
    rw [extractScalarExprWith_booleanDependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.chooseBooleanDependent guard type tn fn tb fb
    · exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact ihArgs operand member found
    · simpa [ScalarBinding.kind] using iht ht
    · simpa [ScalarBinding.kind] using ihe he
  | case33 locals sourceType condition evidence tn td t tb fn fd e fb type matched guard parsed ihArgs iht ihe =>
    have typeEq := scalarResultType_sound matched
    subst sourceType
    obtain ⟨hc, hd, htDomain, heDomain⟩ := dependentGuard_sound parsed
    subst condition evidence td fd
    change extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = some target at compiled
    rw [extractScalarExprWith_dependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.chooseDependent guard type tn fn tb fb
    · intro operand member
      obtain ⟨expression, found⟩ := extractGuard_operands guard _ hc operand member
      exact ihArgs operand member found
    · simpa [ScalarBinding.kind] using iht ht
    · simpa [ScalarBinding.kind] using ihe he
  | case34 locals head left right excluded excludedRun excludedPure excludedBind excludedIf excludedUnit excludedPUnit excludedBinary excludedComplement excludedMin excludedMax excludedDependent p hp ihl ihr =>
    have meaning := ScalarPrimitive.ofHead_sound hp
    rw [extractScalarExprWith_binary meaning] at compiled
    simp only [bind, pure, hp, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, _⟩ := compiled
    exact .binary meaning (ihl ha) (ihr hb)
  | case35 locals head left right excluded excludedRun excludedPure excludedBind excludedIf excludedUnit excludedPUnit excludedBinary excludedComplement excludedMin excludedMax excludedDependent rejectedPrimitive rejectedCall =>
    rw [extractScalarExprWith] at compiled
    · rw [rejectedPrimitive, rejectedCall] at compiled
      contradiction
    all_goals assumption
  | case36 locals head left right excluded excludedRun excludedPure excludedBind excludedIf excludedUnit excludedPUnit excludedBinary excludedComplement excludedMin excludedMax excludedDependent rejectedPrimitive call matched ihArgs =>
    rw [scalarManyCall_sound matched] at compiled ⊢
    rw [extractScalarExprWith_manyApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arguments, ha, _⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.manyApply call
      (scalarManyFunction_kind (Option.bind_eq_some_iff.mpr hf))
    intro operand member
    obtain ⟨expression, found⟩ := extractScalarArguments_operands call.arguments _ ha operand member
    exact ihArgs operand member found
  | case37 locals name value body nondep rejected =>
    rw [extractScalarExprWith, rejected] at compiled
    contradiction
  | case38 locals name value body nondep expression matched ihArgs ihb =>
    have same := booleanLocalOperands_sound matched
    subst value
    rw [extractScalarExprWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply LeanExe.Source.Scalar.SupportedWith.letBoolean expression
      (extractBooleanLocalWith_variables hc) _ (by simpa [ScalarBinding.kind] using ihb c ht)
    intro operand member
    obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
    exact ihArgs operand member found
  | case39 locals name value body nondep ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (ihv hb) (by simpa [ScalarBinding.kind] using ihb bound ht)
  | case40 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected rejectedMany =>
    rw [extractScalarExprWith] at compiled
    rw [rejected, rejectedMany] at compiled
    contradiction
  | case41 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected shape matched ih0 ihf ihb =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound matched
    rw [sameType, sameValue] at compiled ⊢
    change extractScalarExprWith locals (shape.bind name body nondep) = some target at compiled
    change LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) (shape.bind name body nondep)
    rw [extractScalarExprWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letManyFn shape (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case42 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarExprWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBinaryFn type (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case43 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected noBoolean =>
    rw [extractScalarExprWith] at compiled
    · rw [rejected, noBoolean] at compiled
      contradiction
    · exact excludedBinary
  | case44 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected type matched noExpression =>
    rw [extractScalarExprWith] at compiled
    · rw [rejected, matched, noExpression] at compiled
      contradiction
    · exact excludedBinary
  | case45 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected type matched expression parsed ih0 ihf ihb =>
    have sameType := booleanType_sound matched
    have sameValue := booleanLocalOperands_sound parsed
    subst resultType
    subst value
    rw [extractScalarExprWith_letPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractBooleanLocalWith_variables hc)
      (fun operand member => by
        obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
        simpa [ScalarBinding.kind] using ih0 operand member found)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case46 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letFn type (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case47 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case48 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    change extractScalarExprWith locals (.letE name
      (.forallE unitTypeName (LeanExe.Source.Scalar.UnitSyntax.unit.type)
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName (LeanExe.Source.Scalar.UnitSyntax.unit.type)
        (.lam paramName (.const ``UInt64 []) value paramBi) unitBi) body nondep) = some target at compiled
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .unit (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case49 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case50 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    change extractScalarExprWith locals (.letE name
      (.forallE unitTypeName (LeanExe.Source.Scalar.UnitSyntax.punit.type)
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName (LeanExe.Source.Scalar.UnitSyntax.punit.type)
        (.lam paramName (.const ``UInt64 []) value paramBi) unitBi) body nondep) = some target at compiled
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .punit (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case51 locals index argument function matched ih =>
    rw [extractScalarExprWith, matched] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, ht⟩ := compiled
    exact .apply (scalarFunction_kind matched) (ih ha)
  | case52 locals index argument noWord noBoolean =>
    rw [extractScalarExprWith, noWord, noBoolean] at compiled
    contradiction
  | case53 locals index argument noWord expression parsed ihArgs =>
    rw [extractScalarExprWith, noWord, parsed] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨function, hf, condition, hc, ht⟩ := compiled
    rw [booleanLocalOperands_sound parsed]
    exact .applyBoolean expression
      (scalarBooleanFunction_kind (Option.bind_eq_some_iff.mpr hf))
      (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case54 locals name typeName resultType typeBi paramName value paramBi body nondep rejected noBoolean =>
    rw [extractScalarExprWith, rejected, noBoolean] at compiled
    contradiction
  | case55 locals name typeName resultType typeBi paramName value paramBi body nondep rejected type matched noExpression =>
    rw [extractScalarExprWith, rejected, matched, noExpression] at compiled
    contradiction
  | case56 locals name typeName resultType typeBi paramName value paramBi body nondep rejected type matched expression parsed ih0 ihf ihb =>
    have sameType := booleanType_sound matched
    have sameValue := booleanLocalOperands_sound parsed
    subst resultType
    subst value
    rw [extractScalarExprWith_letBooleanPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBooleanPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractBooleanLocalWith_variables hc)
      (fun operand member => by
        obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
        simpa [ScalarBinding.kind] using ih0 operand member found)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case57 locals name typeName resultType typeBi paramName value paramBi body nondep type matched ih0 ihf ihb =>
    have same := scalarResultType_sound matched
    subst resultType
    rw [extractScalarExprWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBooleanFn type (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case58 locals argument rejected =>
    rw [extractScalarExprWith] at compiled
    split at compiled
    next => contradiction
    next expression parsed => rw [rejected] at parsed; contradiction
  | case59 locals argument negations index input parsed function found _ ihArgument =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    change extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanGuardNegation.expr negations (.app (.bvar index) input))) = some target at compiled
    rw [extractScalarExprWith_applyBooleanPredicateWord _ _ _ _ _ found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨argument, ha, _⟩ := compiled
    exact .applyBooleanPredicateWord negations (scalarBooleanPredicateFunction_kind found)
      (ihArgument ha)
  | case60 locals argument negations index input parsed noBoolean _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    rw [extractScalarExprWith_booleanWord _ _ (by
      intro n i arg equality; cases equality; exact noBoolean) (by intros; contradiction)
      (by intro form n unequal left right same; cases form <;> cases same)
      (by intro form n unequal left right yes no same; cases form <;> cases same)] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case61 locals argument negations op left right parsed present _ ihl ihr =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    rw [extractScalarExprWith_booleanJunction] at compiled
    simp only [present, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, _⟩ := compiled
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp present
    exact .booleanJunctionWord negations op left right member
      (scalarBooleanPredicateFunction_kind found) (ihl hl) (ihr hr)
  | case62 locals argument negations op left right parsed absent _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    rw [extractScalarExprWith_booleanJunction, if_neg absent] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case63 locals argument negations unequal left right parsed present _ ihl ihr =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanEquality locals .equality negations unequal left right
    simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at equation
    rw [equation] at compiled
    simp only [present, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, _⟩ := compiled
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp present
    exact .booleanEqualityWord .equality negations unequal left right member
      (scalarBooleanPredicateFunction_kind found) (ihl hl) (ihr hr)
  | case64 locals argument negations unequal left right parsed absent _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanEquality locals .equality negations unequal left right
    simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at equation
    rw [equation, if_neg absent] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case65 locals argument negations unequal left right parsed present _ ihl ihr =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanEquality locals .decision negations unequal left right
    simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at equation
    rw [equation] at compiled
    simp only [present, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, _⟩ := compiled
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp present
    exact .booleanEqualityWord .decision negations unequal left right member
      (scalarBooleanPredicateFunction_kind found) (ihl hl) (ihr hr)
  | case66 locals argument negations unequal left right parsed absent _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanEquality locals .decision negations unequal left right
    simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at equation
    rw [equation, if_neg absent] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case67 locals argument negations unequal left right yes no parsed present _ ihl ihr iht ihe =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanChoice locals .ordinary negations unequal left right yes no
    simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at equation
    rw [equation] at compiled
    simp only [present, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, trueBranch, ht, falseBranch, he, _⟩ := compiled
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp present
    exact .booleanChoiceWord .ordinary negations unequal left right yes no member
      (scalarBooleanPredicateFunction_kind found) (ihl hl) (ihr hr) (iht ht) (ihe he)
  | case68 locals argument negations unequal left right yes no parsed absent _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanChoice locals .ordinary negations unequal left right yes no
    simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at equation
    rw [equation, if_neg absent] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case69 locals argument negations shape unequal left right yes no parsed present _ ihl ihr iht ihe =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanChoice locals (.dependent shape) negations unequal left right yes no
    simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at equation
    rw [equation] at compiled
    simp only [present, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, trueBranch, ht, falseBranch, he, _⟩ := compiled
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp present
    exact .booleanChoiceWord (.dependent shape) negations unequal left right yes no member
      (scalarBooleanPredicateFunction_kind found) (ihl hl) (ihr hr) (iht ht) (ihe he)
  | case70 locals argument negations shape unequal left right yes no parsed absent _ ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    have equation := extractScalarExprWith_booleanChoice locals (.dependent shape) negations unequal left right yes no
    simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at equation
    rw [equation, if_neg absent] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case71 locals argument expression parsed matched excluded excludedJunction excludedEquality excludedDecision excludedChoice excludedDependentChoice ihArgs =>
    have same := booleanLocalOperands_sound parsed
    subst argument
    rw [extractScalarExprWith_booleanWord _ _ (by
      intro negations index input equality
      subst expression
      exact False.elim (excluded negations index input matched rfl (HEq.refl _))) (by
      intro negations op left right equality
      subst expression
      exact False.elim (excludedJunction negations op left right matched rfl (HEq.refl _))) (by
      intro form negations unequal left right equality
      subst expression
      cases form with
      | equality => exact False.elim (excludedEquality negations unequal left right matched rfl (HEq.refl _))
      | decision => exact False.elim (excludedDecision negations unequal left right matched rfl (HEq.refl _))) (by
      intro form negations unequal left right yes no equality
      subst expression
      cases form with
      | ordinary => exact False.elim (excludedChoice negations unequal left right yes no matched rfl (HEq.refl _))
      | dependent shape => exact False.elim (excludedDependentChoice negations shape unequal left right yes no matched rfl (HEq.refl _)))] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact .booleanWord _ (extractBooleanLocalWith_variables hc)
      (fun operand member => ihArgs operand member
        (extractBooleanLocalWith_operands hc operand member).choose_spec)
  | case72 locals name typeName resultType typeBi paramName domain value paramBi body nondep rejected =>
    rw [extractScalarExprWith] at compiled
    simp [rejected] at compiled
  | case73 locals name typeName resultType typeBi paramName domain value paramBi body nondep inputType rejected foundInput =>
    rw [extractScalarExprWith] at compiled
    simp [foundInput, rejected] at compiled
  | case74 locals name typeName resultType typeBi paramName domain value paramBi body nondep inputType result foundResult foundInput ih =>
    rw [extractScalarExprWith] at compiled
    simp only [↓reduceIte, foundInput, foundResult] at compiled
    have inputEq := scalarResultType_sound foundInput
    have resultEq := booleanType_sound foundResult
    subst domain resultType
    exact .predicateInput inputType result (ih compiled)
  | case75 locals name typeName input resultType typeBi paramName domain value paramBi body nondep different =>
    rw [extractScalarExprWith] at compiled
    simp [different] at compiled
  | case76 locals name type value body nondep ih =>
    rw [extractScalarExprWith] at compiled
    exact .idLet (ih compiled)
  | case77 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarExprWith] using compiled))
  | case78 locals expr hvar hliteral hnatural hconverted hofNat hrun hpure hbind hchoice hunitApp hpunitApp hbin hboolLet hlet hletFn hletUnitFn hletPUnitFn happ hletBooleanFn hPredicateInput hidLet hmetadata =>
    rw [extractScalarExprWith] at compiled <;> first | assumption | contradiction

theorem extractScalarExpr_supported {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  simpa [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const'] using extractScalarExprWith_supported compiled

/-- A reusable closure property for the unchanged arithmetic backend. -/
theorem extractScalarExprWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {source : Lean.Expr} {locals : List ScalarBinding} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : P target := by
  have supported := extractScalarExprWith_supported compiled
  generalize htypes : locals.map ScalarBinding.kind = types at supported
  induction supported generalizing locals target with
  | @var types index hi =>
    have found : (locals[index]?.bind ScalarBinding.word?) = some target := by
      simpa only [extractScalarExprWith] using compiled
    obtain ⟨binding, hb, matched⟩ := Option.bind_eq_some_iff.mp found
    cases binding with
    | booleanPredicateFunction _ => contradiction
    | word expression => cases matched; exact bindings _ (List.mem_of_getElem? hb)
    | booleanFunction _ | predicateFunction _ | boolean _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => contradiction
  | @natural types index levels hi =>
    have found : (locals[index]?.bind ScalarBinding.natural?) = some target := by
      simpa only [extractScalarExprWith] using compiled
    obtain ⟨binding, hb, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.natural?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? hb)
  | literal =>
    simp only [extractScalarExprWith, Option.some.injEq] at compiled
    subst target
    exact literal _
  | ofNat =>
    simp only [extractScalarExprWith_literalExpr, Option.some.injEq] at compiled
    subst target
    exact literal _
  | ofNatInstance meaning =>
    simp only [extractScalarExprWith_ofNatInstance _ meaning, Option.some.injEq] at compiled
    subst target
    exact literal _
  | naturalLiteral meaning =>
    simp only [extractScalarExprWith_naturalLiteral _ _ meaning, Option.some.injEq] at compiled
    subst target
    exact literal _
  | ofNatNatural numberMeaning instanceMeaning =>
    simp only [extractScalarExprWith_ofNatNatural _ numberMeaning instanceMeaning, Option.some.injEq] at compiled
    subst target
    exact literal _
  | complement head _ ih =>
    rw [extractScalarExprWith_complement head] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨argument, ha, rfl⟩ := compiled
    exact binary .xor argument (.u64 18446744073709551615) (ih ha bindings htypes) (literal _)
  | extremum op _ _ ihl ihr =>
    rw [extractScalarExprWith_extremum] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    exact lowerExtremum_invariant P choice op a b (ihl ha bindings htypes) (ihr hb bindings htypes)
  | binary op _ _ ihl ihr =>
    rw [extractScalarExprWith_binary op] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := compiled
    exact binary p a b (ihl ha bindings htypes) (ihr hb bindings htypes)
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := compiled
    exact choice op a b t e (ihl ha bindings htypes) (ihr hb bindings htypes)
      (iht ht bindings htypes) (ihe he bindings htypes)
  | chooseCompound guard type _ _ _ ihArgs iht ihe =>
    rw [extractScalarExprWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := compiled
    exact extractGuard_choice P literal binary choice guard.tree _ hc
      (fun operand member expression found => ihArgs operand member found bindings htypes)
      t e (iht ht bindings htypes) (ihe he bindings htypes)
  | chooseDependent guard type tn fn tb fb _ _ _ ihArgs iht ihe =>
    rw [extractScalarExprWith_dependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := compiled
    have extended : ∀ binding ∈ ScalarBinding.unit :: locals, binding.Holds P := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    exact extractGuard_choice P literal binary choice guard _ hc
      (fun operand member expression found => ihArgs operand member found bindings htypes)
      t e (iht ht extended (by simp [ScalarBinding.kind, htypes]))
      (ihe he extended (by simp [ScalarBinding.kind, htypes]))
  | chooseBooleanDependent guard type tn fn tb fb variables _ _ _ ihArgs iht ihe =>
    rw [extractScalarExprWith_booleanDependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := compiled
    have extended : ∀ binding ∈ ScalarBinding.unit :: locals, binding.Holds P := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    exact extractBooleanLocalWith_choice P literal binary choice guard.value _ hc bindings
      (fun operand member expression found => ihArgs operand member found bindings htypes)
      t e (iht ht extended (by simp [ScalarBinding.kind, htypes]))
      (ihe he extended (by simp [ScalarBinding.kind, htypes]))
  | booleanWord expression variables _ ihArgs =>
    rw [extractScalarExprWith_booleanWord _ _ (fun negations index input same =>
      scalarBooleanPredicate_none_of_predicate (htypes ▸ variables.functions index
        (by rw [same]; simp [LeanExe.Source.Scalar.BooleanLocal.functions])))
      (fun negations op left right same => hasBooleanPredicate_false (fun index member =>
        scalarBooleanPredicate_none_of_predicate (htypes ▸ variables.functions index
          (by simpa [same, LeanExe.Source.Scalar.BooleanLocal.functions] using member))))
      (fun form negations unequal left right same => hasBooleanPredicate_false (fun index member =>
        scalarBooleanPredicate_none_of_predicate (htypes ▸ variables.functions index
          (by simpa [same] using member))))
      (fun form negations unequal left right yes no same => hasBooleanPredicate_false (fun index member =>
        scalarBooleanPredicate_none_of_predicate (htypes ▸ variables.functions index
          (by simpa [same] using member))))] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact extractBooleanLocalWith_choice P literal binary choice expression _ hc bindings
      (fun operand member target found => ihArgs operand member found bindings htypes)
      _ _ (literal 1) (literal 0)
  | letBoolean expression variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have bound := extractBooleanLocalWith_choice P literal binary choice expression _ hc bindings
      (fun operand member target found => ihArgs operand member found bindings htypes)
      _ _ (literal 1) (literal 0)
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact bound
    · exact bindings binding member
  | idBindBoolean action type variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have bound := extractBooleanLocalWith_choice P literal binary choice action.leaf _ hc bindings
      (fun operand member target found => ihArgs operand member found bindings htypes)
      _ _ (literal 1) (literal 0)
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact bound
    · exact bindings binding member
  | chooseBoolean guard type variables _ _ _ ihArgs iht ihe =>
    rw [extractScalarExprWith_booleanBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := compiled
    exact extractBooleanLocalWith_choice P literal binary choice guard.value _ hc bindings
      (fun operand member expression found => ihArgs operand member found bindings htypes)
      t e (iht ht bindings htypes) (ihe he bindings htypes)
  | letE _ _ ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings htypes
    · exact bindings expression member
  | idRun type _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings htypes
  | idPure type _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings htypes
  | idBind input output _ _ ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings htypes
    · exact bindings expression member
  | applyBoolean expression present variables _ ihArgs =>
    obtain ⟨f, hf⟩ := scalarBooleanFunction_lookup (htypes ▸ present)
    have found := congrArg (fun binding => binding.bind ScalarBinding.booleanFunction?) hf
    rw [extractScalarExprWith_booleanApply _ _ _ _ found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨condition, hc, ht⟩ := compiled
    have choice := extractBooleanLocalWith_choice P literal binary choice expression _ hc bindings
      (fun operand member expression found => ihArgs operand member found bindings htypes)
    exact bindings _ (List.mem_of_getElem? hf) (guardWord condition) target
      (choice _ _ (literal 1) (literal 0)) ht
  | booleanChoiceWord form negations unequal left right yes no member present _ _ _ _ ihl ihr iht ihe =>
    have found := hasBooleanPredicate_of_kind member (htypes ▸ present)
    rw [extractScalarExprWith_booleanChoice] at compiled
    simp only [found, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, trueBranch, ht, falseBranch, he, rfl⟩ := compiled
    exact booleanWordChoice_holds P literal choice negations unequal
      (ihl hl bindings htypes) (ihr hr bindings htypes) (iht ht bindings htypes) (ihe he bindings htypes)
  | booleanEqualityWord form negations unequal left right member present _ _ ihl ihr =>
    have found := hasBooleanPredicate_of_kind member (htypes ▸ present)
    rw [extractScalarExprWith_booleanEquality] at compiled
    simp only [found, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    exact booleanWordEquality_holds P literal choice negations unequal
      (ihl hl bindings htypes) (ihr hr bindings htypes)
  | booleanJunctionWord negations op left right member present _ _ ihl ihr =>
    have found := hasBooleanPredicate_of_kind member (htypes ▸ present)
    rw [extractScalarExprWith_booleanJunction] at compiled
    simp only [found, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    exact booleanWordJunction_holds P literal binary choice negations op
      (ihl hl bindings htypes) (ihr hr bindings htypes)
  | applyBooleanPredicateWord negations present _ ihArg =>
    obtain ⟨f, hf⟩ := scalarBooleanPredicateFunction_lookup (htypes ▸ present)
    have found := congrArg (fun binding => binding.bind ScalarBinding.booleanPredicateFunction?) hf
    rw [extractScalarExprWith_applyBooleanPredicateWord _ _ _ _ _ found] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨argument, ha, result, hr, rfl⟩ := compiled
    exact booleanWordNegation_holds P literal choice negations
      (bindings _ (List.mem_of_getElem? hf) argument result (ihArg ha bindings htypes) hr)
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := scalarFunction_lookup (htypes ▸ present)
    have found := congrArg (fun binding => binding.bind (ScalarBinding.function? false)) hf
    rw [extractScalarExprWith_wordApply _ _ _ _ found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, ht⟩ := compiled
    exact bindings _ (List.mem_of_getElem? hf) arg target (ih ha bindings htypes) ht
  | letFn type _ _ ihf ihb =>
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      · exact bindings binding member
    · exact bindings binding member
  | letPredicateFn expression type variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_letPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨condition, hc, rfl⟩ := compiled
      have inner : ∀ binding ∈ ScalarBinding.word argument :: locals, binding.Holds P := by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact ha
        · exact bindings binding member
      exact (extractBooleanLocalWith_choice P literal binary choice expression _ hc inner
        (fun operand member expression found => ihArgs operand member found inner
          (by simp [ScalarBinding.kind, htypes]))) _ _ (literal 1) (literal 0)
    · exact bindings binding member
  | letBooleanPredicateFn expression type variables _ _ ihArgs ihb =>
    rw [extractScalarExprWith_letBooleanPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨condition, hc, rfl⟩ := compiled
      have inner : ∀ binding ∈ ScalarBinding.boolean argument :: locals, binding.Holds P := by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact ha
        · exact bindings binding member
      exact (extractBooleanLocalWith_choice P literal binary choice expression _ hc inner
        (fun operand member expression found => ihArgs operand member found inner
          (by simp [ScalarBinding.kind, htypes]))) _ _ (literal 1) (literal 0)
    · exact bindings binding member
  | predicateInput input result _ ih =>
    rw [extractScalarExprWith_predicateInput] at compiled
    exact ih compiled bindings htypes
  | letBooleanFn type _ _ ihf ihb =>
    rw [extractScalarExprWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      · exact bindings binding member
    · exact bindings binding member
  | unitApply unitForm present _ ih =>
    rw [extractScalarExprWith_unitApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    obtain ⟨binding, hb, matched⟩ := hf
    have same := ScalarBinding.function?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? hb) arg target (ih ha bindings htypes) ht
  | letUnitFn type unitForm _ _ ihf ihb =>
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | binaryApply present first _ ihFirst ihSecond =>
    rw [extractScalarExprWith_binaryApply _ _ _ _ first.not_unit] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, ht⟩ := compiled
    obtain ⟨binding, found, matched⟩ := hf
    have same := ScalarBinding.binaryFunction?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? found) a b target
      (ihFirst ha bindings htypes) (ihSecond hb bindings htypes) ht
  | letBinaryFn type _ _ ihf ihb =>
    rw [extractScalarExprWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro first second target hx hy compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact hy
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      · exact bindings binding member
    · exact bindings binding member
  | manyApply call present _ ihArgs =>
    rw [extractScalarExprWith_manyApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arguments, ha, ht⟩ := compiled
    obtain ⟨binding, found, matched⟩ := hf
    have same := ScalarBinding.manyFunction?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? found) arguments target
      (extractScalarArguments_length _ _ ha)
      (extractScalarArguments_holds call.arguments _ P ha
        (fun operand member expression found => ihArgs operand member found bindings htypes)) ht
  | letManyFn shape _ _ ihf ihb =>
    rw [extractScalarExprWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro arguments target len holds compiled
      apply ihf compiled _
        (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len, htypes])
      exact scalarWords_holds (fun argument member => holds argument (by simpa using member)) bindings
    · exact bindings binding member
  | idLet _ ih => exact ih (by simpa only [extractScalarExprWith_idLet] using compiled) bindings htypes
  | ofNatTyped numberMeaning instanceMeaning =>
    simp only [extractScalarExprWith_ofNatTyped _ numberMeaning instanceMeaning, Option.some.injEq] at compiled
    subst target
    exact literal _
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings htypes

/-- Source support guarantees both admission and source/IR agreement. -/
theorem extractScalarExpr_total_correct {source : Lean.Expr} {locals : List Nat}
    (supported : LeanExe.Source.Scalar.Supported locals.length source)
    (values : List UInt64) (store : LeanExe.IR.ScalarStore)
    (len : values.length = locals.length)
    (bindings : ScalarLocalsMatch locals values store) :
    ∃ target value, extractScalarExpr locals source = some target ∧
      LeanExe.Source.Scalar.Eval source values value ∧ target.ScalarEval store value store := by
  obtain ⟨target, compiled⟩ := extractScalarExpr_accepts supported locals rfl
  obtain ⟨value, semantics⟩ := supported.evaluates values len
  exact ⟨target, value, compiled, semantics, extractScalarExpr_correct semantics compiled bindings⟩

end LeanExe.Extract.Core
