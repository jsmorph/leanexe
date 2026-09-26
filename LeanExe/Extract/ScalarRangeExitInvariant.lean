import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarStepInvariant

namespace LeanExe.Extract.Core

def ScalarRangeExitPlan.Holds (P : LeanExe.IR.Expr → Prop) (plan : ScalarRangeExitPlan) : Prop :=
  P plan.count ∧ P plan.initial ∧ P plan.step ∧ P plan.done ∧ P plan.result

/-- All five range expressions inherit every scalar invariant preserved by
literals, operations, conditionals and the two fresh readable loop locals. -/
theorem extractScalarRangeExitWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  have expression {locals : List ScalarBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith locals source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled bindings
  have extend {locals : List ScalarBinding} {target : LeanExe.IR.Expr}
      (bindings : ∀ binding ∈ locals, binding.Holds P) (value : P target) :
      ∀ binding ∈ ScalarBinding.word target :: locals, binding.Holds P := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact value
    · exact bindings binding member
  induction locals, source using extractScalarRangeExitWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRangeExit_sound matched
    subst source
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, count, hc, initial, hi, code, hs, rfl⟩ := compiled
    have pair := extractScalarStepWith_invariant P literal binary choice hs
    have both : code.Holds P := pair (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact accumulator
      rcases List.mem_cons.mp member with rfl | member
      · exact scalarRangeOffset_holds P binary (expression hf bindings)
          (scalarRangeScale_holds P literal binary view.stride.number index)
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact bindings original present)
    exact ⟨scalarRangeTrips_holds P literal binary choice view.stride.number
      (scalarRangeDistance_holds P literal binary choice (expression hf bindings) (expression hc bindings)), expression hi bindings, both.1, both.2, accumulator⟩
  | case2 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case3 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.run body type) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeExitWith_idRun] using compiled) bindings
  | case4 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case5 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.pure body type) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeExitWith_idPure] using compiled) bindings
  | case6 locals name value body nondep invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case7 locals name value body nondep boolean matched rejected ih =>
    have same := booleanLocalOperands_sound matched
    subst value
    rw [extractScalarRangeExitWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have bound := extractBooleanLocalWith_choice P literal binary choice boolean _ hc bindings
      (fun operand member target found => expression found bindings) _ _ (literal 1) (literal 0)
    apply ih c ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact bound
    · exact bindings binding member
  | case8 locals name value body nondep bound matched notRange ih =>
    rw [extractScalarRangeExitWith_letE, matched] at compiled
    exact ih compiled (extend bindings (expression matched bindings))
  | case9 locals name value body nondep notPure notRange ih =>
    rw [extractScalarRangeExitWith_letE, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, rfl⟩ := compiled
    obtain ⟨pc, pi, ps, pd, pr⟩ := ih hb bindings
    exact ⟨pc, pi, ps, pd, expression hr (extend bindings pr)⟩
  | case10 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected noMany notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected, noMany] at compiled
  | case11 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected shape matched notRange ihb =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound matched
    rw [sameType, sameValue] at compiled
    change extractScalarRangeExitWith locals slot (shape.bind name body nondep) = some plan at compiled
    rw [extractScalarRangeExitWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro arguments target len holds hc
      exact expression hc (scalarWords_holds
        (fun argument member => holds argument (by simpa using member)) bindings)
    · exact bindings binding member
  | case12 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro first second target hx hy hc
      exact expression hc (extend (extend bindings hx) hy)
    · exact bindings binding member
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    · simp [notRange, rejected] at compiled
    · exact excludedBinary
  | case14 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target hx hc
      exact expression hc (extend bindings hx)
    · exact bindings binding member
  | case15 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case16 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target hx hc
      apply expression hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case17 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case18 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target hx hc
      apply expression hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case19 locals input output value name domain body bi invalid invalidBoolean rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid, invalidBoolean] at compiled
  | case20 locals input output value name domain body bi invalid type matched invalidAction rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid, matched, invalidAction] at compiled
  | case21 locals input output value name domain body bi invalid type matched action parsed rejected ih =>
    obtain ⟨hi, hd, ho⟩ := booleanBindType_sound _ matched
    have outputEq := scalarResultType_sound ho
    have valueEq := booleanAction_sound parsed
    subst input domain output value
    change extractScalarRangeExitWith locals slot
      (LeanExe.Source.Scalar.BooleanIdentity.bind name bi action.expr body type.expr) = some plan at compiled
    rw [extractScalarRangeExitWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have bound := extractBooleanLocalWith_choice P literal binary choice action.leaf _ hc bindings
      (fun operand member target found => expression found bindings) _ _ (literal 1) (literal 0)
    apply ih c ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact bound
    · exact bindings binding member
  | case22 locals input output value name domain body bi annotations typesMatched bound matched rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, matched] at compiled
    exact ih compiled (extend bindings (expression matched bindings))
  | case23 locals input output value name domain body bi annotations typesMatched notPure rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, rfl⟩ := compiled
    obtain ⟨pc, pi, ps, pd, pr⟩ := ih hb bindings
    exact ⟨pc, pi, ps, pd, expression hr (extend bindings pr)⟩
  | case24 locals name typeName resultType typeBi paramName value paramBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case25 locals name typeName resultType typeBi paramName value paramBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    apply ihb ht
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target hx hc
      apply expression hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      · exact bindings binding member
    · exact bindings binding member
  | case26 locals name type value body nondep rejected ih =>
    change extractScalarRangeExitWith locals slot
      (LeanExe.Source.Scalar.idLetExpr name type value body nondep) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeExitWith_idLet] using compiled) bindings
  | case27 locals data body rejected ih =>
    exact ih (by simpa only [extractScalarRangeExitWith_metadata] using compiled) bindings
  | case28 locals source rejected hrun hpure hboolLet hlet hbinary hunary hunit hpunit hbind hidLet hmetadata =>
    rw [extractScalarRangeExitWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
