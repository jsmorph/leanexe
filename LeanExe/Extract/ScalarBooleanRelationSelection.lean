import LeanExe.Source.ScalarBooleanRelationSelection
import LeanExe.Extract.ScalarBooleanGuardedSelection
import LeanExe.Extract.ScalarBooleanRelation
import LeanExe.Extract.ScalarBooleanProofBodies

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanRelationGuard? (condition evidence : Lean.Expr) : Option BooleanRelationGuard := do
  match ← booleanPropositionLeaf? condition with
  | .truth _ => none
  | .relation unequal left right nontruth =>
    let guard : BooleanRelationGuard := ⟨unequal, left, right, nontruth⟩
    if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none

@[simp] theorem booleanRelationGuard_accepts (guard : BooleanRelationGuard) :
    booleanRelationGuard? guard.condition guard.evidence = some guard := by
  rcases guard with ⟨unequal, left, right, nontruth⟩
  simp [booleanRelationGuard?, BooleanRelationGuard.condition, BooleanRelationGuard.leaf]

theorem booleanRelationGuard_sound {condition evidence : Lean.Expr} {guard : BooleanRelationGuard}
    (parsed : booleanRelationGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [booleanRelationGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨leaf, found, accepted⟩ := parsed
  cases leaf with
  | truth value => contradiction
  | relation unequal left right nontruth =>
    dsimp only at accepted
    split at accepted <;> try contradiction
    rename_i same
    cases accepted
    exact ⟨booleanPropositionLeaf_sound found, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩

@[simp] theorem booleanRelationGuard_not_proposition (relation : BooleanRelationGuard) :
    propositionGuard? relation.condition relation.evidence = none := by
  cases parsed : propositionGuard? relation.condition relation.evidence with
  | none => rfl
  | some guard =>
    have same := (propositionGuard_sound parsed).1
    rcases relation with ⟨unequal, left, right, nontruth⟩
    cases unequal with
    | false => exact False.elim (propositionGuard_not_boolean_equal guard left right same.symm)
    | true => exact False.elim (propositionGuard_not_boolean_unequal guard left right same.symm)

/-- Parse the proposition and its exact standard evidence before both branches. -/
def booleanRelationSelectionSyntax? : Lean.Expr → Option BooleanRelationSelectionSyntax
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) annotation) condition) evidence) yes) no => do
      let type ← booleanType? annotation
      let guard ← booleanRelationGuard? condition evidence
      pure ⟨type, none, guard, yes, no⟩
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) annotation) condition) evidence)
      (.lam tn td yes ti)) (.lam fn fd no fi) => do
      let type ← booleanType? annotation
      let guard ← booleanRelationGuard? condition evidence
      let (t, e) ← booleanProofBodies? condition td yes fd no
      pure ⟨type, some ⟨tn, fn, ti, fi⟩, guard, t, e⟩
  | _ => none

@[simp] theorem booleanRelationSelectionSyntax_accepts (value : BooleanRelationSelectionSyntax) :
    booleanRelationSelectionSyntax? value.expr = some value := by
  rcases value with ⟨type, proof, guard, yes, no⟩
  cases proof <;> simp [booleanRelationSelectionSyntax?, BooleanRelationSelectionSyntax.expr]

theorem booleanRelationSelectionSyntax_sound {source : Lean.Expr} {value : BooleanRelationSelectionSyntax}
    (parsed : booleanRelationSelectionSyntax? source = some value) : source = value.expr := by
  unfold booleanRelationSelectionSyntax? at parsed
  split at parsed
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, found, guard, guardFound, rfl⟩ := parsed
    obtain ⟨hc, he⟩ := booleanRelationGuard_sound guardFound
    rw [booleanType_sound found, hc, he]
    rfl
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, found, guard, guardFound, ⟨t, e⟩, bodies, rfl⟩ := parsed
    obtain ⟨hc, he⟩ := booleanRelationGuard_sound guardFound
    obtain ⟨htd, hfd, ht, hn⟩ := booleanProofBodies_sound bodies
    rw [booleanType_sound found, htd, hfd, ht, hn, hc, he]
    rfl
  · contradiction

private def choiceCondition : Lean.Expr → Lean.Expr
  | .app (.app (.app (.app (.app _ _) condition) _) _) _ => condition
  | other => other

theorem booleanRelationSelectionSyntax_not_boolean (value : BooleanRelationSelectionSyntax)
    (other : BooleanSelectionSyntax) : value.expr ≠ other.expr := by
  intro equal
  have projected := congrArg choiceCondition equal
  rcases value with ⟨type, proof, guard, yes, no⟩
  rcases other with ⟨otherType, otherProof, condition, otherYes, otherNo⟩
  cases proof <;> cases otherProof
  all_goals
    change guard.condition = booleanRelationCondition false condition (booleanLiteralExpr true) at projected
    exact guard.not_boolean_condition condition projected

@[simp] theorem booleanRelationSelectionSyntax_not_selected (value : BooleanRelationSelectionSyntax) :
    booleanSelectionSyntax? value.expr = none := by
  cases parsed : booleanSelectionSyntax? value.expr with
  | none => rfl
  | some other =>
    exact False.elim (booleanRelationSelectionSyntax_not_boolean value other (booleanSelectionSyntax_sound parsed))

@[simp] theorem booleanRelationSelectionSyntax_not_guarded (value : BooleanRelationSelectionSyntax) :
    booleanGuardedSelectionSyntax? value.expr = none := by
  rcases value with ⟨type, proof, guard, yes, no⟩
  cases proof <;> simp [booleanGuardedSelectionSyntax?, BooleanRelationSelectionSyntax.expr]

@[simp] theorem booleanRelationSelection_not_local (value : BooleanRelationSelection) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanRelationSelection? (source : Lean.Expr) : Option BooleanRelationSelection :=
  if absent : booleanLocalOperands? source = none then
    match parsed : booleanRelationSelectionSyntax? source with
    | some selection => some ⟨selection,
        fun expression same => booleanLocal_excluded absent expression ((booleanRelationSelectionSyntax_sound parsed).trans same)⟩
    | none => none
  else none

@[simp] theorem booleanRelationSelection_accepts (value : BooleanRelationSelection) :
    booleanRelationSelection? value.expr = some value := by
  have absent := booleanRelationSelection_not_local value
  rcases value with ⟨selection, extended⟩
  simp only [booleanRelationSelection?, dite_eq_left absent]
  split
  · rename_i actual found
    have same := Option.some.inj ((booleanRelationSelectionSyntax_accepts selection).symm.trans found)
    cases same
    rfl
  · rename_i found
    rw [booleanRelationSelectionSyntax_accepts] at found
    contradiction

theorem booleanRelationSelection_sound {source : Lean.Expr} {value : BooleanRelationSelection}
    (parsed : booleanRelationSelection? source = some value) : source = value.expr := by
  unfold booleanRelationSelection? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i selection found
  cases parsed
  exact booleanRelationSelectionSyntax_sound found

@[simp] theorem booleanRelationSelection_not_helper (value : BooleanRelationSelection) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanRelationSelection_not_wrapped (value : BooleanRelationSelection) :
    booleanWrapped? value.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanRelationSelection_not_negated (value : BooleanRelationSelection) :
    booleanNegated? value.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanRelationSelection_not_joined (value : BooleanRelationSelection) :
    booleanJoined? value.expr = none := by
  unfold booleanJoined?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanRelationSelection_not_related (value : BooleanRelationSelection) :
    booleanRelated? value.expr = none := by
  unfold booleanRelated?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanRelationSelection_not_selected (value : BooleanRelationSelection) :
    booleanSelected? value.expr = none := by
  unfold booleanSelected?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  split
  · rename_i selection found
    rw [booleanRelationSelectionSyntax_not_selected] at found
    contradiction
  · rfl

@[simp] theorem booleanRelationSelection_not_guarded (value : BooleanRelationSelection) :
    booleanGuardedSelection? value.expr = none := by
  unfold booleanGuardedSelection?
  rw [dite_eq_left (booleanRelationSelection_not_local value)]
  split
  · rename_i selection found
    rw [booleanRelationSelectionSyntax_not_guarded] at found
    contradiction
  · rfl

theorem booleanRelationSelection_sizes {source : Lean.Expr} {value : BooleanRelationSelection}
    (parsed : booleanRelationSelection? source = some value) :
    sizeOf value.selection.guard.left < sizeOf source ∧ sizeOf value.selection.guard.right < sizeOf source ∧
      sizeOf value.selection.yes < sizeOf source ∧ sizeOf value.selection.no < sizeOf source := by
  rw [booleanRelationSelection_sound parsed]
  exact value.selection.children_size

end LeanExe.Extract.Core
