import LeanExe.Source.ScalarCompoundGuard
import LeanExe.Extract.ScalarBooleanGuardSyntax
import LeanExe.Extract.ScalarGuardDecision
import LeanExe.Extract.ScalarBooleanPropositionLeaf
import LeanExe.Extract.ScalarGuardLet

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

/-- Saved Boolean leaves are admitted under propositional junctions. -/
def guardJunctionOperands? (op : Junction) (left right : Lean.Expr)
    (a b : Option Guard) : Option Guard :=
  match a, b with
  | some a, some b => some (.junction 0 op a b)
  | none, some b => (booleanPropositionLeaf? left).map fun a => .savedLeft 0 op a b
  | some a, none => (booleanPropositionLeaf? right).map fun b => .savedRight 0 op a b
  | none, none => do
      let a ← booleanPropositionLeaf? left
      let b ← booleanPropositionLeaf? right
      some (.savedBoth 0 op a b)

theorem guardJunctionOperands_sound (op : Junction) (left right : Lean.Expr)
    (a b : Option Guard)
    (leftMeaning : ∀ guard, a = some guard → left = guard.condition)
    (rightMeaning : ∀ guard, b = some guard → right = guard.condition)
    {guard : Guard} (parsed : guardJunctionOperands? op left right a b = some guard) :
    op.condition left right = guard.condition := by
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [guardJunctionOperands?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨a, ha, b, hb, rfl⟩ := parsed
      simp [Guard.condition, GuardNegation.condition, booleanPropositionLeaf_sound ha, booleanPropositionLeaf_sound hb]
    | some b =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp parsed
      simp [Guard.condition, GuardNegation.condition, booleanPropositionLeaf_sound ha, rightMeaning b rfl]
  | some a =>
    cases b with
    | none =>
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp parsed
      simp [Guard.condition, GuardNegation.condition, leftMeaning a rfl, booleanPropositionLeaf_sound hb]
    | some b =>
      cases parsed
      simp [Guard.condition, GuardNegation.condition, leftMeaning a rfl, rightMeaning b rfl]

def guardLetOperands? (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool)
    (parsedBody : Option Guard) : Option Guard := do
  let type ← guardLetType? type
  let binding : GuardLet := ⟨name, type, value, nondep⟩
  match parsedBody with
  | some body => some (.letGuard 0 binding body)
  | none => (savedBooleanGuard? body).map fun body => .letSaved 0 binding body

theorem guardLetOperands_sound (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool)
    (parsedBody : Option Guard)
    (bodyMeaning : ∀ guard, parsedBody = some guard → body = guard.condition)
    {guard : Guard} (parsed : guardLetOperands? name type value body nondep parsedBody = some guard) :
    Lean.Expr.letE name type value body nondep = guard.condition := by
  simp only [guardLetOperands?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨bindingType, typeFound, accepted⟩ := parsed
  have typeSame := guardLetType_sound typeFound
  subst type
  cases parsedBody with
  | none =>
    obtain ⟨bodyGuard, bodyFound, rfl⟩ := Option.map_eq_some_iff.mp accepted
    simp [Guard.condition, GuardLet.wrap, GuardNegation.condition, savedBooleanGuard_sound bodyFound]
  | some bodyGuard =>
    cases accepted
    simp [Guard.condition, GuardLet.wrap, GuardNegation.condition, bodyMeaning bodyGuard rfl]

def guardNegateOperands? (inner : Lean.Expr) (parsedInner : Option Guard) : Option Guard :=
  match parsedInner with
  | some guard => some guard.negate
  | none => (booleanPropositionLeaf? inner).map fun value => .localNegation 0 value

theorem guardNegateOperands_sound (inner : Lean.Expr) (parsedInner : Option Guard)
    (innerMeaning : ∀ guard, parsedInner = some guard → inner = guard.condition)
    {guard : Guard} (parsed : guardNegateOperands? inner parsedInner = some guard) :
    Lean.Expr.app (.const ``Not []) inner = guard.condition := by
  cases parsedInner with
  | some value =>
    cases parsed
    rw [Guard.negate_condition, innerMeaning value rfl]
  | none =>
    obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [booleanPropositionLeaf_sound found]
    rfl

def guardOperands? : Lean.Expr → Option Guard
  | .letE name type value body nondep =>
      guardLetOperands? name type value body nondep (guardOperands? body)
  | .app (.app (.const ``And []) left) right =>
      guardJunctionOperands? .conjunction left right (guardOperands? left) (guardOperands? right)
  | .app (.app (.const ``Or []) left) right =>
      guardJunctionOperands? .disjunction left right (guardOperands? left) (guardOperands? right)
  | .app (.const ``Not []) inner => guardNegateOperands? inner (guardOperands? inner)
  | .const ``True [] => some (.literal (.proposition 0 true))
  | .const ``False [] => some (.literal (.proposition 0 false))
  | expression =>
      match comparisonOperands? expression with
      | some (op, a, b) => some (.compare op a b)
      | none => do
          let tree ← booleanGuardCondition? expression
          match tree with
          | .literal n value => some (.literal (.boolean 0 n value))
          | .junction n op a b => some (.boolean 0 n op a b)
          | .compare .. => none

theorem guardOperands_negate {inner : Lean.Expr} {guard : Guard}
    (parsed : guardOperands? inner = some guard) :
    guardOperands? (.app (.const ``Not []) inner) = some guard.negate := by
  simp [guardOperands?, guardNegateOperands?, parsed]

@[simp] theorem savedBooleanGuard_not_guard (guard : SavedBooleanGuard) :
    guardOperands? guard.condition = none := by
  obtain ⟨value, extended⟩ := guard
  have noClosed := savedBooleanValue_not_closed ⟨value, extended⟩
  change booleanGuardOperands? value = none at noClosed
  change guardOperands? (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value)
    (.const ``Bool.true [])) = none
  rw [guardOperands?]
  · simp [booleanTruth_not_comparison_of_not_closed value extended, booleanGuardCondition?, noClosed]
  all_goals simp

@[simp] theorem booleanPropositionLeaf_not_guard (value : BooleanPropositionLeaf) :
    guardOperands? value.condition = none := by
  cases value with
  | truth value => exact savedBooleanGuard_not_guard value
  | relation unequal left right nontruth =>
    cases unequal with
    | true => rfl
    | false =>
      have absent : comparisonOperands?
          (BooleanPropositionLeaf.relation false left right nontruth).condition = none := by
        simp [BooleanPropositionLeaf.condition, comparisonOperands?, scalarResultType?, nontruth rfl]
      rw [guardOperands?]
      · rw [absent]
        simp only [booleanGuardCondition?, BooleanPropositionLeaf.condition]
        split <;> simp_all
      all_goals simp [BooleanPropositionLeaf.condition]

@[simp] theorem guardOperands_compare (op : Comparison) (a b : Lean.Expr) :
    guardOperands? (op.condition a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [Comparison.condition, guardOperands?, guardNegateOperands?, ih, Guard.negate]
  | eq type => cases type <;>
      simp [Comparison.condition, guardOperands?, comparisonOperands?, ResultType.expr, scalarResultType?]
  | _ => simp [Comparison.condition, Comparison.boolExpr, guardOperands?, comparisonOperands?]

@[simp] theorem guardOperands_condition (guard : Guard) :
    guardOperands? guard.condition = some guard := by
  induction guard with
  | literal literal =>
    cases literal with
    | proposition m value =>
      induction m with
      | zero => cases value <;> rfl
      | succ m ih =>
        simpa only [Guard.condition, GuardLiteral.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?,
          Option.map_some, Guard.negate, GuardLiteral.negate] using guardOperands_negate ih
    | boolean m n value =>
      induction m with
      | zero =>
        change guardOperands? (BooleanGuard.literal n value).condition = _
        rw [guardOperands?]
        · rw [booleanLiteral_condition_not_comparison, booleanGuardCondition_accepts]
          rfl
        all_goals simp [BooleanGuard.condition]
      | succ m ih =>
        simpa only [Guard.condition, GuardLiteral.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?,
          Option.map_some, Guard.negate, GuardLiteral.negate] using guardOperands_negate ih
  | compare op a b => exact guardOperands_compare op a b
  | junction n op a b iha ihb =>
    induction n with
    | zero => cases op <;> simp [Guard.condition, GuardNegation.condition, Junction.condition, guardOperands?, guardJunctionOperands?, iha, ihb]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih
  | boolean m n op a b =>
    induction m with
    | zero =>
      change guardOperands? (BooleanGuard.junction n op a b).condition = _
      rw [guardOperands?]
      · rw [booleanJunction_condition_not_comparison, booleanGuardCondition_accepts]
        rfl
      all_goals simp [BooleanGuard.condition]
    | succ m ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih

  | savedLeft n op a b ihb =>
    induction n with
    | zero => cases op <;> simp [Guard.condition, GuardNegation.condition, Junction.condition,
        guardOperands?, guardJunctionOperands?, ihb]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih
  | savedRight n op a b iha =>
    induction n with
    | zero => cases op <;> simp [Guard.condition, GuardNegation.condition, Junction.condition,
        guardOperands?, guardJunctionOperands?, iha]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih
  | savedBoth n op a b =>
    induction n with
    | zero => cases op <;> simp [Guard.condition, GuardNegation.condition, Junction.condition,
        guardOperands?, guardJunctionOperands?]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih

  | letGuard n binding body ihb =>
    induction n with
    | zero =>
      simp [Guard.condition, GuardNegation.condition, GuardLet.wrap, guardOperands?, guardLetOperands?, ihb]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih
  | letSaved n binding body =>
    induction n with
    | zero =>
      simp [Guard.condition, GuardNegation.condition, GuardLet.wrap, guardOperands?, guardLetOperands?]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?, Option.map_some, Guard.negate] using guardOperands_negate ih
  | localNegation n value =>
    induction n with
    | zero => simp [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, guardNegateOperands?,
        Guard.negate] using guardOperands_negate ih


theorem guardOperands_sound {expression : Lean.Expr} {guard : Guard}
    (parsed : guardOperands? expression = some guard) : expression = guard.condition := by
  induction expression using guardOperands?.induct generalizing guard with
  | case1 name type value body nondep ih =>
    exact guardLetOperands_sound name type value body nondep _ (fun guard => ih) parsed
  | case2 left right ihl ihr =>
    exact guardJunctionOperands_sound .conjunction left right _ _ (fun guard => ihl) (fun guard => ihr) parsed
  | case3 left right ihl ihr =>
    exact guardJunctionOperands_sound .disjunction left right _ _ (fun guard => ihl) (fun guard => ihr) parsed
  | case4 inner ih =>
    exact guardNegateOperands_sound inner _ (fun guard => ih) parsed
  | case5 | case6 => cases parsed; rfl
  | case7 expression excludedLet excludedAnd excludedOr excludedNot excludedTrue excludedFalse =>
    rw [guardOperands?] at parsed
    · split at parsed
      · rename_i op a b found
        cases parsed
        exact comparisonOperands_sound found
      · simp only [bind, Option.bind_eq_some_iff] at parsed
        obtain ⟨tree, found, accepted⟩ := parsed
        cases tree with
        | literal n value => cases accepted; exact booleanGuardCondition_sound found
        | compare => contradiction
        | junction n op a b =>
          cases accepted
          exact booleanGuardCondition_sound found
    · exact excludedLet
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot
    · exact excludedTrue
    · exact excludedFalse
  | case8 expression excludedLet excludedAnd excludedOr excludedNot excludedTrue excludedFalse absent =>
    rw [guardOperands?] at parsed
    · rw [absent] at parsed
      simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨tree, found, accepted⟩ := parsed
      cases tree with
      | literal n value => cases accepted; exact booleanGuardCondition_sound found
      | compare => contradiction
      | junction n op a b =>
        cases accepted
        exact booleanGuardCondition_sound found
    · exact excludedLet
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot
    · exact excludedTrue
    · exact excludedFalse

theorem junction_not_comparison (n : Nat) (op : Junction) (a b : Lean.Expr) :
    comparisonOperands? (GuardNegation.condition n (op.condition a b)) = none := by
  induction n with
  | zero => cases op <;> rfl
  | succ n ih => simp [GuardNegation.condition, comparisonOperands?, ih]

def reannotatedGuard? (condition evidence : Lean.Expr) : Option ReannotatedGuard := do
  let tree ← guardOperands? condition
  if different : evidence ≠ tree.evidence then
    if accepted : guardDecision? tree evidence = true then
      some ⟨tree, evidence, guardDecision_sound accepted, different⟩
    else none
  else none

@[simp] theorem reannotatedGuard_accepts (guard : ReannotatedGuard) :
    reannotatedGuard? guard.condition guard.evidence = some guard := by
  cases guard with
  | mk tree evidence meaning different =>
    simp [reannotatedGuard?, ReannotatedGuard.condition, different, guardDecision_accepts meaning]

@[simp] theorem reannotatedGuard_canonical_none (guard : Guard) :
    reannotatedGuard? guard.condition guard.evidence = none := by
  simp [reannotatedGuard?]

theorem reannotatedGuard_sound {condition evidence : Lean.Expr} {guard : ReannotatedGuard}
    (found : reannotatedGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [reannotatedGuard?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨tree, parsed, accepted⟩ := found
  split at accepted
  · split at accepted
    · cases accepted
      exact ⟨guardOperands_sound parsed, rfl⟩
    · contradiction
  · contradiction

def compoundGuardShape? (condition : Lean.Expr) : Option CompoundGuard := do
  let tree ← guardOperands? condition
  match tree with
  | .literal value => some (.literal value)
  | .junction n op a b => some (.proposition op a b n)
  | .boolean m n op a b => some (.boolean op a b n m)
  | .savedLeft n op a b => some (.savedLeft op a b n)
  | .savedRight n op a b => some (.savedRight op a b n)
  | .savedBoth n op a b => some (.savedBoth op a b n)
  | .letGuard n binding body => some (.letGuard binding body n)
  | .letSaved n binding body => some (.letSaved binding body n)
  | .localNegation n value => some (.localNegation value n)
  | .compare .. => none

@[simp] theorem compoundGuardShape_condition (tree : Guard) :
    compoundGuardShape? tree.condition = (match tree with
      | .literal value => some (.literal value)
      | .junction n op a b => some (.proposition op a b n)
      | .boolean m n op a b => some (.boolean op a b n m)
      | .savedLeft n op a b => some (.savedLeft op a b n)
      | .savedRight n op a b => some (.savedRight op a b n)
      | .savedBoth n op a b => some (.savedBoth op a b n)
      | .letGuard n binding body => some (.letGuard binding body n)
      | .letSaved n binding body => some (.letSaved binding body n)
      | .localNegation n value => some (.localNegation value n)
      | .compare .. => none) := by
  simp [compoundGuardShape?]

theorem compoundGuardShape_sound {condition : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuardShape? condition = some guard) : condition = guard.condition := by
  simp only [compoundGuardShape?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨tree, found, accepted⟩ := parsed
  cases tree with
  | literal value => cases accepted; exact guardOperands_sound found
  | compare => contradiction
  | junction n op a b => cases accepted; exact guardOperands_sound found
  | boolean m n op a b => cases accepted; exact guardOperands_sound found

  | savedLeft n op a b => cases accepted; exact guardOperands_sound found
  | savedRight n op a b => cases accepted; exact guardOperands_sound found
  | savedBoth n op a b => cases accepted; exact guardOperands_sound found
  | letGuard n binding body => cases accepted; exact guardOperands_sound found
  | letSaved n binding body => cases accepted; exact guardOperands_sound found
  | localNegation n value => cases accepted; exact guardOperands_sound found

private def canonicalCompoundGuard? (condition evidence : Lean.Expr) : Option CompoundGuard := do
  let guard ← compoundGuardShape? condition
  if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none

/-- Check the entire decision expression for every admitted guard form. -/
def compoundGuard? (condition evidence : Lean.Expr) : Option CompoundGuard :=
  (canonicalCompoundGuard? condition evidence).orElse fun _ =>
    (reannotatedGuard? condition evidence).map CompoundGuard.reannotated

theorem compoundGuard_none_of_no_guard {condition evidence : Lean.Expr}
    (absent : guardOperands? condition = none) : compoundGuard? condition evidence = none := by
  simp [compoundGuard?, canonicalCompoundGuard?, compoundGuardShape?, reannotatedGuard?, absent]

@[simp] theorem compoundGuard_accepts (guard : CompoundGuard) :
    compoundGuard? guard.condition guard.evidence = some guard := by
  cases guard with
  | reannotated guard =>
    have absent : canonicalCompoundGuard? guard.condition guard.evidence = none := by
      rcases guard with ⟨tree, evidence, meaning, different⟩
      have distinct := different
      cases tree <;> simp only [Guard.evidence] at distinct
      all_goals simp [canonicalCompoundGuard?, ReannotatedGuard.condition,
        CompoundGuard.evidence, CompoundGuard.tree, Guard.evidence, distinct]
    simpa [compoundGuard?, CompoundGuard.condition, CompoundGuard.tree,
      CompoundGuard.evidence, absent] using reannotatedGuard_accepts guard
  | _ => simp [compoundGuard?, canonicalCompoundGuard?, CompoundGuard.condition,
      CompoundGuard.tree, CompoundGuard.evidence]

theorem compoundGuard_sound {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  unfold compoundGuard? at parsed
  cases found : canonicalCompoundGuard? condition evidence with
  | none =>
    rw [found] at parsed
    obtain ⟨guard, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact reannotatedGuard_sound found
  | some shape =>
    rw [found] at parsed
    cases parsed
    simp only [canonicalCompoundGuard?, bind, Option.bind_eq_some_iff] at found
    obtain ⟨shape, parsedShape, accepted⟩ := found
    split at accepted
    · cases accepted
      exact ⟨compoundGuardShape_sound parsedShape, LeanExe.Source.ExprEquality.same_eq_true.mp (by assumption)⟩
    · contradiction

theorem compoundGuard_size {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition + guardOperandOverhead := by
  rw [(compoundGuard_sound parsed).1]
  exact guard.operands_size member

theorem negated_not_comparison (n : Nat) (condition : Lean.Expr)
    (absent : comparisonOperands? condition = none) :
    comparisonOperands? (GuardNegation.condition n condition) = none := by
  induction n with
  | zero => exact absent
  | succ n ih => simp [GuardNegation.condition, comparisonOperands?, ih]

theorem guardLiteral_not_comparison (literal : GuardLiteral) :
    comparisonOperands? literal.condition = none := by
  cases literal with
  | proposition m value =>
    apply negated_not_comparison
    cases value <;> rfl
  | boolean m n value =>
    exact negated_not_comparison m _ (booleanLiteral_condition_not_comparison n value)

theorem booleanPropositionLeaf_not_comparison (value : LeanExe.Source.Scalar.BooleanPropositionLeaf) :
    comparisonOperands? value.condition = none := by
  cases value with
  | truth value =>
    exact booleanTruth_not_comparison_of_not_closed value.value value.extended
  | relation unequal left right nontruth =>
    cases unequal with
    | false => simp [LeanExe.Source.Scalar.BooleanPropositionLeaf.condition,
        comparisonOperands?, scalarResultType?, nontruth rfl]
    | true => rfl

@[simp] theorem compoundGuard_not_comparison (guard : CompoundGuard) :
    comparison? guard.condition guard.evidence = none := by
  cases guard with
  | reannotated guard =>
    rcases guard with ⟨tree, evidence, meaning, different⟩
    cases tree with
    | compare op a b =>
      have distinct : evidence ≠ op.evidence a b := different
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree,
        CompoundGuard.evidence, Guard.condition, distinct]
    | literal value =>
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition,
        guardLiteral_not_comparison]
    | junction n op a b =>
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition,
        junction_not_comparison]
    | boolean m n op a b =>
      have absent := negated_not_comparison m _ (booleanJunction_condition_not_comparison n op a b)
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
    | savedLeft n op a b =>
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition,
        junction_not_comparison]
    | savedRight n op a b =>
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition,
        junction_not_comparison]
    | savedBoth n op a b =>
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition,
        junction_not_comparison]
    | localNegation n value =>
      have absent := negated_not_comparison (n + 1) value.condition
        (booleanPropositionLeaf_not_comparison value)
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
    | letGuard n binding body =>
      have absent := negated_not_comparison n (binding.wrap body.condition) (by rfl)
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
    | letSaved n binding body =>
      have absent := negated_not_comparison n (binding.wrap body.condition) (by rfl)
      simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
  | literal value =>
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, guardLiteral_not_comparison]
  | proposition op a b n =>
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, junction_not_comparison]
  | boolean op a b n m =>
    have absent := negated_not_comparison m _ (booleanJunction_condition_not_comparison n op a b)
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]

  | savedLeft op a b n =>
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, junction_not_comparison]
  | savedRight op a b n =>
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, junction_not_comparison]
  | savedBoth op a b n =>
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, junction_not_comparison]

  | localNegation value n =>
    have absent := negated_not_comparison (n + 1) value.condition
      (booleanPropositionLeaf_not_comparison value)
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
  | letGuard binding body n =>
    have absent := negated_not_comparison n (binding.wrap body.condition) (by rfl)
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]
  | letSaved binding body n =>
    have absent := negated_not_comparison n (binding.wrap body.condition) (by rfl)
    simp [comparison?, CompoundGuard.condition, CompoundGuard.tree, Guard.condition, absent]

end LeanExe.Extract.Core
