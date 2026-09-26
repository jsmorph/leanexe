import LeanExe.Extract.ScalarBooleanLocalParserEquations
import LeanExe.Extract.ScalarPropositionGuard
import LeanExe.Extract.ScalarBooleanRelation

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

@[simp] theorem booleanLocalOperands_compare (op : BooleanComparison) (a b : Lean.Expr) :
    booleanLocalOperands? (op.expr a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [BooleanComparison.expr, booleanLocalOperands?, ih, BooleanLocal.negate]
  | _ => simp [BooleanComparison.expr, BooleanComparison.atom, booleanLocalOperands?, booleanComparisonOperands?]

@[simp] theorem booleanLocalOperands_proposition (guard : PropositionGuard) (yes no : Lean.Expr) :
    booleanLocalOperands? (guard.branch yes no) = (do
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.proposition 0 guard t e)) := by
  rw [PropositionGuard.branch, booleanLocalOperands?]
  · rw [propositionGuard_accepts]
    rfl
  · intro left right equality
    exact propositionGuard_not_boolean_equal guard left right equality
  · intro left right equality
    exact propositionGuard_not_boolean_unequal guard left right equality

@[simp] theorem booleanLocalOperands_decision (guard : PropositionGuard) :
    booleanLocalOperands? guard.value.decisionExpr = some (.decision 0 guard) := by
  rw [DecidedGuard.decisionExpr, booleanLocalOperands?]
  · simp only [propositionGuard_accepts, Option.map_some]
  · intro left right equality
    exact propositionGuard_not_boolean_equal guard left right equality
  · intro left right equality
    exact propositionGuard_not_boolean_unequal guard left right equality

@[simp] theorem booleanLocalOperands_expr (guard : BooleanLocal) :
    booleanLocalOperands? guard.expr = some guard := by
  induction guard with
  | var n index =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | predicate n index argument =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | literal n value =>
    induction n with
    | zero => cases value <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLiteralExpr, booleanLocalOperands?]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | compare op a b => exact booleanLocalOperands_compare op a b
  | junction n op a b iha ihb =>
    induction n with
    | zero => cases op <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr,
        Junction.booleanExpr, booleanLocalOperands?, iha, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | choice n unequal a b t e iha ihb iht ihe =>
    induction n with
    | zero => cases unequal <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanChoiceExpr,
        booleanRelationCondition, booleanRelationEvidence, booleanLocalOperands?, iha, ihb, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | proposition n g t e iht ihe =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, iha, ihb, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | dependentProposition n shape g t e iht ihe =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | binding n name form value body type ihv ihb =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, ihv, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | wordBinding n name form value body type ihb =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | wrapped n wrapper body ihb =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | decision n g =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih


  | equality n unequal a b iha ihb =>
    induction n with
    | zero => cases unequal <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr,
        booleanEqualityExpr, booleanLocalOperands?, iha, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | relationDecision n unequal a b iha ihb =>
    induction n with
    | zero => cases unequal <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr,
        booleanRelationDecisionExpr, booleanRelationCondition, booleanRelationEvidence, booleanLocalOperands?, iha, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih

theorem booleanLocalOperands_sound {expression : Lean.Expr} {guard : BooleanLocal}
    (parsed : booleanLocalOperands? expression = some guard) : expression = guard.expr := by
  induction expression using booleanLocalOperands?.induct generalizing guard with
  | case1 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case2 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case3 inner ih =>
    rw [booleanLocalOperands?] at parsed
    obtain ⟨guard, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [BooleanLocal.negate_expr, ih found]
  | case4 | case5 => simp only [booleanLocalOperands?, Option.some.injEq] at parsed; subst guard; rfl
  | case6 index => simp only [booleanLocalOperands?, Option.some.injEq] at parsed; subst guard; rfl
  | case7 left right evidence yes no same iha ihb iht ihe =>
    rw [booleanLocalOperands?] at parsed
    simp only [same, ite_true, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanChoiceExpr]
    rw [decision, iha ha, ihb hb, iht ht, ihe he]
    rfl
  | case8 left right evidence yes no different => simp [booleanLocalOperands?, different] at parsed
  | case9 left right evidence yes no same iha ihb iht ihe =>
    rw [booleanLocalOperands?] at parsed
    simp only [same, ite_true, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanChoiceExpr]
    rw [decision, iha ha, ihb hb, iht ht, ihe he]
    rfl
  | case10 left right evidence yes no different => simp [booleanLocalOperands?, different] at parsed
  | case11 condition evidence yes no excludedEqual excludedUnequal iht ihe =>
    rw [booleanLocalOperands?] at parsed
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨g, hg, t, ht, e, he, rfl⟩ := parsed
      have guard := propositionGuard_sound hg
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, PropositionGuard.branch]
      rw [guard.1, guard.2, iht ht, ihe he]
    · exact excludedEqual
    · exact excludedUnequal
  | case12 left right evidence tn td yesBody ti fn fd noBody fi same bodies =>
    rw [booleanLocalOperands?.eq_10] at parsed
    simp only [same, ite_true] at parsed
    rw [bodies] at parsed
    contradiction
  | case13 left right evidence tn td yesBody ti fn fd noBody fi same yes no bodies iha ihb iht ihe =>
    rw [booleanLocalOperands?.eq_10] at parsed
    simp only [same, ite_true] at parsed
    rw [bodies] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    obtain ⟨trueType, falseType, yesShape, noShape⟩ := booleanProofBodies_sound bodies
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanProofBranch.expr]
    rw [trueType, falseType, yesShape, noShape, decision, iha ha, ihb hb, iht ht, ihe he]
    rfl
  | case14 left right evidence tn td yesBody ti fn fd noBody fi different =>
    rw [booleanLocalOperands?.eq_10] at parsed
    simp only [different] at parsed
    contradiction
  | case15 left right evidence tn td yesBody ti fn fd noBody fi same bodies =>
    rw [booleanLocalOperands?.eq_11] at parsed
    simp only [same, ite_true] at parsed
    rw [bodies] at parsed
    contradiction
  | case16 left right evidence tn td yesBody ti fn fd noBody fi same yes no bodies iha ihb iht ihe =>
    rw [booleanLocalOperands?.eq_11] at parsed
    simp only [same, ite_true] at parsed
    rw [bodies] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    obtain ⟨trueType, falseType, yesShape, noShape⟩ := booleanProofBodies_sound bodies
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanProofBranch.expr]
    rw [trueType, falseType, yesShape, noShape, decision, iha ha, ihb hb, iht ht, ihe he]
    rfl
  | case17 left right evidence tn td yesBody ti fn fd noBody fi different =>
    rw [booleanLocalOperands?.eq_11] at parsed
    simp only [different] at parsed
    contradiction
  | case18 condition evidence tn td yesBody ti fn fd noBody fi excludedEqual excludedUnequal bodies =>
    rw [booleanLocalOperands?] at parsed
    · rw [bodies] at parsed
      contradiction
    · exact excludedEqual
    · exact excludedUnequal
  | case19 condition evidence tn td yesBody ti fn fd noBody fi excludedEqual excludedUnequal yes no bodies iht ihe =>
    rw [booleanLocalOperands?] at parsed
    · rw [bodies] at parsed
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨g, hg, t, ht, e, he, rfl⟩ := parsed
      have guard := propositionGuard_sound hg
      obtain ⟨trueType, falseType, yesShape, noShape⟩ := booleanProofBodies_sound bodies
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanProofBranch.expr]
      rw [trueType, falseType, yesShape, noShape, guard.1, guard.2, iht ht, ihe he]
    · exact excludedEqual
    · exact excludedUnequal
  | case20 left right evidence same ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [same, ite_true, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanRelationDecisionExpr]
    rw [decision, ihl ha, ihr hb]
    rfl
  | case21 left right evidence different => simp [booleanLocalOperands?, different] at parsed
  | case22 left right evidence same ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [same, ite_true, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanRelationDecisionExpr]
    rw [decision, ihl ha, ihr hb]
    rfl
  | case23 left right evidence different => simp [booleanLocalOperands?, different] at parsed
  | case24 condition evidence excludedEqual excludedUnequal =>
    rw [booleanLocalOperands?] at parsed
    · obtain ⟨g, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      obtain ⟨hc, he⟩ := propositionGuard_sound found
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, DecidedGuard.decisionExpr, hc, he]
    · exact excludedEqual
    · exact excludedUnequal
  | case25 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanEqualityExpr, ihl ha, ihr hb]
  | case26 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanEqualityExpr, ihl ha, ihr hb]
  | case27 name type value body nondep application named annotation found ihb =>
    rw [booleanLocalOperands?] at parsed
    split at parsed
    · rename_i candidate accepted
      have same : candidate = application := Option.some.inj (accepted.symm.trans named)
      subst candidate
      simp only [found, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨b, hb, rfl⟩ := parsed
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr]
      rw [← scalarResultType_sound found, ← ihb hb]
      exact booleanFunctionApplication_sound named
    · rename_i rejected
      have impossible := rejected.symm.trans named
      cases impossible
  | case28 name type value body nondep application named noWord ihv ihb =>
    rw [booleanLocalOperands?] at parsed
    split at parsed
    · rename_i candidate accepted
      have same : candidate = application := Option.some.inj (accepted.symm.trans named)
      subst candidate
      simp only [noWord, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨annotation, ht, v, hv, b, hb, rfl⟩ := parsed
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr]
      rw [← booleanType_sound ht, ← ihv hv, ← ihb hb]
      exact booleanFunctionApplication_sound named
    · rename_i rejected
      have impossible := rejected.symm.trans named
      cases impossible
  | case29 name type value body form noNamed annotation found ihb =>
    rw [booleanLocalOperands?, noNamed, found] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨b, hb, rfl⟩ := parsed
    have typeShape := scalarResultType_sound found
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr, typeShape, ihb hb]
  | case30 name type value body form noNamed noWord ihv ihb =>
    rw [booleanLocalOperands?, noNamed, noWord] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨annotation, ht, v, hv, b, hb, rfl⟩ := parsed
    have typeShape := booleanType_sound ht
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr, typeShape, ihv hv, ihb hb]
  | case31 type body ih =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
    obtain ⟨annotation, ht, value, hv, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanWrapper.expr,
      BooleanIdentity.run, booleanType_sound ht, ih hv]
  | case32 type body ih =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
    obtain ⟨annotation, ht, value, hv, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanWrapper.expr,
      BooleanIdentity.pure, booleanType_sound ht, ih hv]
  | case33 data body ih =>
    rw [booleanLocalOperands?] at parsed
    obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanWrapper.expr, ih found]
  | case34 name type body binder value annotation found ihb =>
    rw [booleanLocalOperands?, found] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr,
      scalarResultType_sound found, ihb hb]
  | case35 name type body binder value noWord ihv ihb =>
    rw [booleanLocalOperands?, noWord] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨annotation, ht, v, hv, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, BooleanBindingForm.expr,
      booleanType_sound ht, ihv hv, ihb hb]
  | case36 index argument =>
    simp only [booleanLocalOperands?, Option.some.injEq] at parsed
    subst guard
    rfl
  | case37 expression excludedAnd excludedOr excludedNot excludedTrue excludedFalse excludedVar excludedChoiceEq excludedChoiceNe excludedProposition excludedDependentEq excludedDependentNe excludedDependentProp excludedDecisionEq excludedDecisionNe excludedDecision excludedEq excludedNe excludedBinding excludedRun excludedPure excludedMetadata excludedApplication excludedPredicate =>
    rw [booleanLocalOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact booleanComparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot
    · exact excludedTrue
    · exact excludedFalse
    · exact excludedVar
    · exact excludedChoiceEq
    · exact excludedChoiceNe
    · exact excludedProposition
    · exact excludedDependentEq
    · exact excludedDependentNe
    · exact excludedDependentProp
    · exact excludedDecisionEq
    · exact excludedDecisionNe
    · exact excludedDecision
    · exact excludedEq
    · exact excludedNe
    · exact excludedBinding
    · exact excludedRun
    · exact excludedPure
    · exact excludedMetadata
    · exact excludedApplication
    · exact excludedPredicate

theorem booleanLocalOperands_size {expression : Lean.Expr} {value : BooleanLocal}
    (parsed : booleanLocalOperands? expression = some value) {operand : Lean.Expr}
    (member : operand ∈ value.operands) : sizeOf operand < sizeOf expression := by
  rw [booleanLocalOperands_sound parsed]
  exact value.operands_size member

theorem booleanGuardOperands_variable (n index : Nat) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (.bvar index)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanChoice_not_guard (n : Nat) (unequal : Bool) (a b t e : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (booleanChoiceExpr unequal a b t e)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanChoice_not_comparison (n : Nat) (unequal : Bool) (a b t e : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (booleanChoiceExpr unequal a b t e)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem propositionChoice_not_guard (n : Nat) (guard : PropositionGuard) (t e : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (guard.branch t e)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem propositionChoice_not_comparison (n : Nat) (guard : PropositionGuard) (t e : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (guard.branch t e)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanProofBranch_not_guard (n : Nat) (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (shape.expr condition evidence yes no)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanProofBranch_not_comparison (n : Nat) (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (shape.expr condition evidence yes no)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem decision_not_guard (n : Nat) (guard : DecidedGuard) :
    booleanGuardOperands? (BooleanGuardNegation.expr n guard.decisionExpr) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem decision_not_comparison (n : Nat) (guard : DecidedGuard) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n guard.decisionExpr) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem relationDecision_not_guard (n : Nat) (unequal : Bool) (left right : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (booleanRelationDecisionExpr unequal left right)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem relationDecision_not_comparison (n : Nat) (unequal : Bool) (left right : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (booleanRelationDecisionExpr unequal left right)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanEquality_not_guard (n : Nat) (unequal : Bool) (a b : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (booleanEqualityExpr unequal a b)) = none := by
  induction n with
  | zero => cases unequal <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanEquality_not_comparison (n : Nat) (unequal : Bool) (a b : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (booleanEqualityExpr unequal a b)) = none := by
  induction n with
  | zero => cases unequal <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanLet_not_guard (n : Nat) (name : Lean.Name) (form : BooleanBindingForm) (value body : Lean.Expr)
    (type : BooleanType) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (form.expr name type.expr value body)) = none := by
  induction n with
  | zero => cases form <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanLet_not_comparison (n : Nat) (name : Lean.Name) (form : BooleanBindingForm) (value body : Lean.Expr)
    (type : BooleanType) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (form.expr name type.expr value body)) = none := by
  induction n with
  | zero => cases form <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanWordLet_not_guard (n : Nat) (name : Lean.Name) (form : BooleanBindingForm) (value body : Lean.Expr)
    (type : ResultType) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (form.expr name type.expr value body)) = none := by
  induction n with
  | zero => cases form <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanWordLet_not_comparison (n : Nat) (name : Lean.Name) (form : BooleanBindingForm) (value body : Lean.Expr)
    (type : ResultType) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (form.expr name type.expr value body)) = none := by
  induction n with
  | zero => cases form <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanWrapper_not_guard (n : Nat) (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (wrapper.expr body)) = none := by
  induction n with
  | zero => cases wrapper <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanWrapper_not_comparison (n : Nat) (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (wrapper.expr body)) = none := by
  induction n with
  | zero => cases wrapper <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanPredicate_not_guard (n index : Nat) (argument : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (.app (.bvar index) argument)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanPredicate_not_comparison (n index : Nat) (argument : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (.app (.bvar index) argument)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanGuardOperands_local_closed (value : BooleanLocal) {guard : BooleanGuard}
    (parsed : booleanGuardOperands? value.expr = some guard) : value.extended = false := by
  induction value generalizing guard with
  | var n index => simp [BooleanLocal.expr, booleanGuardOperands_variable] at parsed
  | predicate n index argument => simp [BooleanLocal.expr, booleanPredicate_not_guard] at parsed
  | literal | compare => rfl
  | choice n unequal a b t e => simp [BooleanLocal.expr, booleanChoice_not_guard] at parsed
  | proposition n g t e => simp [BooleanLocal.expr, propositionChoice_not_guard] at parsed
  | dependentChoice n shape unequal a b t e => simp [BooleanLocal.expr, booleanProofBranch_not_guard] at parsed
  | dependentProposition n shape g t e => simp [BooleanLocal.expr, booleanProofBranch_not_guard] at parsed
  | binding n name form value body type => simp [BooleanLocal.expr, booleanLet_not_guard] at parsed
  | wordBinding n name form value body type => simp [BooleanLocal.expr, booleanWordLet_not_guard] at parsed
  | wrapped n wrapper body => simp [BooleanLocal.expr, booleanWrapper_not_guard] at parsed
  | decision n g => simp [BooleanLocal.expr, decision_not_guard] at parsed
  | equality n unequal a b => simp [BooleanLocal.expr, booleanEquality_not_guard] at parsed
  | relationDecision n unequal a b => simp [BooleanLocal.expr, relationDecision_not_guard] at parsed
  | junction n op a b iha ihb =>
    induction n generalizing guard with
    | zero =>
      cases op <;> simp only [BooleanLocal.expr, BooleanGuardNegation.expr,
        Junction.booleanExpr, booleanGuardOperands?, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at parsed
      all_goals
        obtain ⟨left, hl, right, hr, _⟩ := parsed
        simp [BooleanLocal.extended, iha hl, ihb hr]
    | succ n ih =>
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanGuardOperands?] at parsed
      obtain ⟨inner, found, _⟩ := Option.map_eq_some_iff.mp parsed
      exact ih found

theorem booleanGuardOperands_local_none (value : BooleanLocal) (expanded : value.extended = true) :
    booleanGuardOperands? value.expr = none := by
  cases parsed : booleanGuardOperands? value.expr with
  | none => rfl
  | some guard =>
    have closed := booleanGuardOperands_local_closed value parsed
    simp [expanded] at closed

theorem booleanComparisonOperands_variable (n index : Nat) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (.bvar index)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanLocal_not_comparison (value : BooleanLocal) (expanded : value.extended = true) :
    comparisonOperands? value.condition = none := by
  cases value with
  | literal | compare => simp [BooleanLocal.extended] at expanded
  | var n index =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanComparisonOperands_variable]
  | predicate n index argument =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanPredicate_not_comparison]
  | junction n op a b =>
    cases n with
    | zero => cases op <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanJunction_not_comparison]
  | choice n unequal a b t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanChoice_not_comparison]
  | proposition n g t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, propositionChoice_not_comparison]
  | dependentChoice n shape unequal a b t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanProofBranch_not_comparison]
  | dependentProposition n shape g t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanProofBranch_not_comparison]
  | binding n name form value body type =>
    cases n with
    | zero => cases form <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanLet_not_comparison]
  | wordBinding n name form value body type =>
    cases n with
    | zero => cases form <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanWordLet_not_comparison]
  | wrapped n wrapper body =>
    cases n with
    | zero => cases wrapper <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanWrapper_not_comparison]
  | decision n g =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, decision_not_comparison]

  | equality n unequal a b =>
    cases n with
    | zero => cases unequal <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanEquality_not_comparison]
  | relationDecision n unequal a b =>
    cases n with
    | zero => cases unequal <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, relationDecision_not_comparison]

theorem booleanLocal_not_guard (guard : BooleanLocalGuard) :
    guardOperands? guard.condition = none := by
  obtain ⟨value, expanded, form⟩ := guard
  cases form with
  | truth value =>
    have noComparison := booleanLocal_not_comparison value expanded
    have noClosed := booleanGuardOperands_local_none value expanded
    simp only [BooleanLocal.condition] at noComparison
    change guardOperands? value.condition = none
    rw [guardOperands?]
    · simp [noComparison, booleanGuardCondition?, BooleanLocal.condition, noClosed]
    all_goals simp [BooleanLocal.condition]
  | equal left right nontrue => exact booleanRelationEqual_not_guard left.expr right.expr nontrue
  | unequal left right => exact booleanRelationUnequal_not_guard left.expr right.expr

theorem booleanLocal_not_compound (guard : BooleanLocalGuard) :
    compoundGuard? guard.condition guard.evidence = none :=
  compoundGuard_none_of_no_guard (booleanLocal_not_guard guard)

def booleanLocalGuard? (condition evidence : Lean.Expr) : Option BooleanLocalGuard :=
  match condition with
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) expression) (.const ``Bool.true []) => do
    let value ← booleanLocalOperands? expression
    if expanded : value.extended = true then
      if LeanExe.Source.ExprEquality.same evidence value.evidence then some ⟨value, expanded, .truth value⟩ else none
    else none
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right => do
    let a ← booleanLocalOperands? left
    let b ← booleanLocalOperands? right
    if nontrue : b.expr ≠ .const ``Bool.true [] then
      let guard : BooleanLocalGuard := ⟨.equality 0 false a b, rfl, .equal a b nontrue⟩
      if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none
    else none
  | .app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right => do
    let a ← booleanLocalOperands? left
    let b ← booleanLocalOperands? right
    let guard : BooleanLocalGuard := ⟨.equality 0 true a b, rfl, .unequal a b⟩
    if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none
  | _ => none

@[simp] theorem booleanLocalGuard_accepts (guard : BooleanLocalGuard) :
    booleanLocalGuard? guard.condition guard.evidence = some guard := by
  obtain ⟨value, expanded, form⟩ := guard
  cases form with
  | truth value =>
    simp [booleanLocalGuard?, BooleanLocalGuard.condition, BooleanConditionForm.condition,
      BooleanLocal.condition, BooleanLocalGuard.evidence, BooleanConditionForm.evidence, expanded]
  | equal left right nontrue =>
    simp [booleanLocalGuard?, BooleanLocalGuard.condition, BooleanConditionForm.condition,
      booleanRelationCondition, BooleanLocalGuard.evidence, BooleanConditionForm.evidence, nontrue]
  | unequal left right =>
    simp [booleanLocalGuard?, BooleanLocalGuard.condition, BooleanConditionForm.condition,
      booleanRelationCondition, BooleanLocalGuard.evidence, BooleanConditionForm.evidence]

theorem booleanLocalGuard_sound {condition evidence : Lean.Expr} {guard : BooleanLocalGuard}
    (parsed : booleanLocalGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  unfold booleanLocalGuard? at parsed
  split at parsed
  · rename_i expression
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨value, matched, accepted⟩ := parsed
    split at accepted
    · split at accepted
      · rename_i same
        cases accepted
        exact ⟨by rw [booleanLocalOperands_sound matched]; rfl,
          LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
      · contradiction
    · contradiction
  · rename_i left right excluded
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨a, ha, b, hb, accepted⟩ := parsed
    split at accepted
    · split at accepted
      · rename_i same
        cases accepted
        exact ⟨by rw [booleanLocalOperands_sound ha, booleanLocalOperands_sound hb]; rfl,
          LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
      · contradiction
    · contradiction
  · rename_i left right
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨a, ha, b, hb, accepted⟩ := parsed
    split at accepted
    · rename_i same
      cases accepted
      exact ⟨by rw [booleanLocalOperands_sound ha, booleanLocalOperands_sound hb]; rfl,
        LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
    · contradiction
  · contradiction

theorem booleanLocalGuard_not_comparison (guard : BooleanLocalGuard) :
    comparison? guard.condition guard.evidence = none := by
  have absent : comparisonOperands? guard.condition = none := by
    obtain ⟨value, expanded, form⟩ := guard
    cases form with
    | truth value => exact booleanLocal_not_comparison value expanded
    | equal left right nontrue => exact booleanRelationEqual_not_comparison left.expr right.expr nontrue
    | unequal left right => exact booleanRelationUnequal_not_comparison left.expr right.expr
  simp [comparison?, absent]

theorem booleanLocalGuard_size {condition evidence : Lean.Expr} {guard : BooleanLocalGuard}
    (parsed : booleanLocalGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.value.operands) : sizeOf operand < sizeOf condition := by
  rw [(booleanLocalGuard_sound parsed).1]
  exact guard.operands_size member

end LeanExe.Extract.Core
