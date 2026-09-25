import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Extract.ScalarPropositionGuard
import LeanExe.Extract.ScalarBooleanRelation
import LeanExe.Extract.ScalarDecisionGuard

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

def booleanLocalOperands? : Lean.Expr → Option BooleanLocal
  | .app (.app (.const ``Bool.and []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .conjunction a b)
  | .app (.app (.const ``Bool.or []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .disjunction a b)
  | .app (.const ``Bool.not []) inner => (booleanLocalOperands? inner).map BooleanLocal.negate
  | .const ``Bool.true [] => some (.literal 0 true)
  | .const ``Bool.false [] => some (.literal 0 false)
  | .bvar index => some (.var 0 index)
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) condition) (.const ``Bool.true []))) evidence) yes) no =>
      if LeanExe.Source.ExprEquality.same evidence
          (.app (.app (.const ``instDecidableEqBool []) condition) (.const ``Bool.true [])) then do
        let c ← booleanLocalOperands? condition
        let t ← booleanLocalOperands? yes
        let e ← booleanLocalOperands? no
        pure (.choice 0 c t e)
      else none
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool [])) condition) evidence) yes) no => do
      let guard ← propositionGuard? condition evidence
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.proposition 0 guard t e)
  | .app (.app (.const ``Decidable.decide []) condition) evidence =>
      (decisionGuard? condition evidence).map (.decision 0)
  | .app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.equality 0 false a b)
  | .app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.equality 0 true a b)
  | expression => (booleanComparisonOperands? expression).map fun (op, a, b) => .compare op a b

@[simp] theorem booleanLocalOperands_compare (op : BooleanComparison) (a b : Lean.Expr) :
    booleanLocalOperands? (op.expr a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [BooleanComparison.expr, booleanLocalOperands?, ih, BooleanLocal.negate]
  | _ => rfl

@[simp] theorem booleanLocalOperands_proposition (guard : PropositionGuard) (yes no : Lean.Expr) :
    booleanLocalOperands? (guard.branch yes no) = (do
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.proposition 0 guard t e)) := by
  rw [PropositionGuard.branch, booleanLocalOperands?]
  · rw [propositionGuard_accepts]
    rfl
  · exact guard.not_boolean_condition

@[simp] theorem booleanLocalOperands_expr (guard : BooleanLocal) :
    booleanLocalOperands? guard.expr = some guard := by
  induction guard with
  | var n index =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | literal n value =>
    induction n with
    | zero => cases value <;> rfl
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
  | choice n c t e ihc iht ihe =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanChoiceExpr,
        booleanLocalOperands?, ihc, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | proposition n g t e iht ihe =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, iht, ihe]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | decision n g =>
    induction n with
    | zero => simp [BooleanLocal.expr, BooleanGuardNegation.expr, Guard.decisionExpr, booleanLocalOperands?]
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
  | case4 | case5 => cases parsed; rfl
  | case6 index => cases parsed; rfl
  | case7 condition evidence yes no same ihc iht ihe =>
    rw [booleanLocalOperands?] at parsed
    simp only [same, ite_true, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨c, hc, t, ht, e, he, rfl⟩ := parsed
    have decision := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanChoiceExpr]
    rw [decision, ihc hc, iht ht, ihe he]
  | case8 condition evidence yes no different =>
    simp [booleanLocalOperands?, different] at parsed
  | case9 condition evidence yes no excludedBoolean iht ihe =>
    rw [booleanLocalOperands?] at parsed
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨g, hg, t, ht, e, he, rfl⟩ := parsed
      have guard := propositionGuard_sound hg
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, PropositionGuard.branch]
      rw [guard.1, guard.2, iht ht, ihe he]
    · exact excludedBoolean
  | case10 condition evidence =>
    rw [booleanLocalOperands?] at parsed
    obtain ⟨g, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    obtain ⟨hc, he⟩ := decisionGuard_sound found
    simp only [BooleanLocal.expr, BooleanGuardNegation.expr, Guard.decisionExpr, hc, he]
  | case11 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanEqualityExpr, ihl ha, ihr hb]
  | case12 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanEqualityExpr, ihl ha, ihr hb]
  | case13 expression excludedAnd excludedOr excludedNot excludedTrue excludedFalse excludedVar excludedChoice excludedProposition excludedDecision excludedEq excludedNe =>
    rw [booleanLocalOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact booleanComparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot
    · exact excludedTrue
    · exact excludedFalse
    · exact excludedVar
    · exact excludedChoice
    · exact excludedProposition
    · exact excludedDecision
    · exact excludedEq
    · exact excludedNe

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

theorem booleanChoice_not_guard (n : Nat) (c t e : Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (booleanChoiceExpr c t e)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanChoice_not_comparison (n : Nat) (c t e : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (booleanChoiceExpr c t e)) = none := by
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

theorem decision_not_guard (n : Nat) (guard : Guard) :
    booleanGuardOperands? (BooleanGuardNegation.expr n guard.decisionExpr) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem decision_not_comparison (n : Nat) (guard : Guard) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n guard.decisionExpr) = none := by
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

theorem booleanGuardOperands_local_closed (value : BooleanLocal) {guard : BooleanGuard}
    (parsed : booleanGuardOperands? value.expr = some guard) : value.extended = false := by
  induction value generalizing guard with
  | var n index => simp [BooleanLocal.expr, booleanGuardOperands_variable] at parsed
  | literal | compare => rfl
  | choice n c t e => simp [BooleanLocal.expr, booleanChoice_not_guard] at parsed
  | proposition n g t e => simp [BooleanLocal.expr, propositionChoice_not_guard] at parsed
  | decision n g => simp [BooleanLocal.expr, decision_not_guard] at parsed
  | equality n unequal a b => simp [BooleanLocal.expr, booleanEquality_not_guard] at parsed
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
  | junction n op a b =>
    cases n with
    | zero => cases op <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanJunction_not_comparison]
  | choice n c t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanChoice_not_comparison]
  | proposition n g t e =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, propositionChoice_not_comparison]
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
    compoundGuard? guard.condition guard.evidence = none := by
  simp [compoundGuard?, compoundGuardShape?, booleanLocal_not_guard]

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
