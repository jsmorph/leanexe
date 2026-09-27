import LeanExe.Source.ScalarBooleanRelated
import LeanExe.Extract.ScalarBooleanJoined

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Check the exact standard comparison or decision, preserving both operands. -/
def booleanRelationSyntax? : Lean.Expr → Option BooleanRelationSyntax
  | .app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right =>
      some ⟨.equality, false, left, right⟩
  | .app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``Bool []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
        (.const ``instDecidableEqBool []))) left) right =>
      some ⟨.equality, true, left, right⟩
  | .app (.app (.const ``Decidable.decide [])
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right)) evidence =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false left right) then
        some ⟨.decision, false, left, right⟩
      else none
  | .app (.app (.const ``Decidable.decide [])
      (.app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right)) evidence =>
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence true left right) then
        some ⟨.decision, true, left, right⟩
      else none
  | _ => none

@[simp] theorem booleanRelationSyntax_accepts (value : BooleanRelationSyntax) :
    booleanRelationSyntax? value.expr = some value := by
  rcases value with ⟨form, unequal, left, right⟩
  cases form <;> cases unequal <;>
    simp [booleanRelationSyntax?, BooleanRelationSyntax.expr, booleanEqualityExpr,
      booleanRelationDecisionExpr, booleanRelationCondition]

theorem booleanRelationSyntax_sound {source : Lean.Expr} {value : BooleanRelationSyntax}
    (parsed : booleanRelationSyntax? source = some value) : source = value.expr := by
  unfold booleanRelationSyntax? at parsed
  split at parsed
  · cases parsed; rfl
  · cases parsed; rfl
  · split at parsed <;> try contradiction
    rename_i evidence same
    have equal := LeanExe.Source.ExprEquality.same_eq_true.mp same
    subst evidence
    cases parsed
    rfl
  · split at parsed <;> try contradiction
    rename_i evidence same
    have equal := LeanExe.Source.ExprEquality.same_eq_true.mp same
    subst evidence
    cases parsed
    rfl
  · contradiction

@[simp] theorem booleanRelated_not_local (value : BooleanRelated) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanRelated? (source : Lean.Expr) : Option BooleanRelated :=
  if absent : booleanLocalOperands? source = none then
    match parsed : booleanRelationSyntax? source with
    | some relation => some ⟨relation,
        fun expression same => booleanLocal_excluded absent expression ((booleanRelationSyntax_sound parsed).trans same)⟩
    | none => none
  else none

@[simp] theorem booleanRelated_accepts (value : BooleanRelated) :
    booleanRelated? value.expr = some value := by
  have absent := booleanRelated_not_local value
  rcases value with ⟨relation, extended⟩
  simp only [booleanRelated?, dite_eq_left absent]
  split
  · rename_i actual found
    have same := Option.some.inj ((booleanRelationSyntax_accepts relation).symm.trans found)
    cases same
    rfl
  · rename_i found
    rw [booleanRelationSyntax_accepts] at found
    contradiction

theorem booleanRelated_sound {source : Lean.Expr} {value : BooleanRelated}
    (parsed : booleanRelated? source = some value) : source = value.expr := by
  unfold booleanRelated? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i relation found
  cases parsed
  exact booleanRelationSyntax_sound found

@[simp] theorem booleanRelated_not_helper (value : BooleanRelated) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanRelated_not_local value)]
  rcases value with ⟨⟨form, unequal, left, right⟩, extended⟩
  cases form <;> cases unequal <;> rfl

@[simp] theorem booleanRelated_not_wrapped (value : BooleanRelated) :
    booleanWrapped? value.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanRelated_not_local value)]
  rcases value with ⟨⟨form, unequal, left, right⟩, extended⟩
  cases form <;> cases unequal <;> rfl

@[simp] theorem booleanRelated_not_negated (value : BooleanRelated) :
    booleanNegated? value.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanRelated_not_local value)]
  rcases value with ⟨⟨form, unequal, left, right⟩, extended⟩
  cases form <;> cases unequal <;> rfl

@[simp] theorem booleanRelated_not_joined (value : BooleanRelated) :
    booleanJoined? value.expr = none := by
  unfold booleanJoined?
  rw [dite_eq_left (booleanRelated_not_local value)]
  rcases value with ⟨⟨form, unequal, left, right⟩, extended⟩
  cases form <;> cases unequal <;> rfl

theorem booleanRelated_sizes {source : Lean.Expr} {value : BooleanRelated}
    (parsed : booleanRelated? source = some value) :
    sizeOf value.relation.left < sizeOf source ∧ sizeOf value.relation.right < sizeOf source := by
  rw [booleanRelated_sound parsed]
  exact value.relation.children_size

end LeanExe.Extract.Core
