import LeanExe.Source.ScalarBooleanSelected
import LeanExe.Extract.ScalarBooleanRelated
import LeanExe.Extract.ScalarBooleanProofBodies

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Preserve the exact Boolean truth condition and standard decision evidence. -/
def booleanSelectionSyntax? : Lean.Expr → Option BooleanSelectionSyntax
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) annotation)
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) condition) (.const ``Bool.true []))) evidence) yes) no => do
      let type ← booleanType? annotation
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false condition (booleanLiteralExpr true)) then
        pure ⟨type, none, condition, yes, no⟩
      else none
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) annotation)
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) condition) (.const ``Bool.true []))) evidence)
      (.lam tn td yes ti)) (.lam fn fd no fi) => do
      let type ← booleanType? annotation
      if LeanExe.Source.ExprEquality.same evidence (booleanRelationEvidence false condition (booleanLiteralExpr true)) then do
        let (t, e) ← booleanProofBodies? (booleanRelationCondition false condition (booleanLiteralExpr true)) td yes fd no
        pure ⟨type, some ⟨tn, fn, ti, fi⟩, condition, t, e⟩
      else none
  | _ => none

@[simp] theorem booleanSelectionSyntax_accepts (value : BooleanSelectionSyntax) :
    booleanSelectionSyntax? value.expr = some value := by
  rcases value with ⟨type, proof, condition, yes, no⟩
  cases proof <;>
    simp [booleanSelectionSyntax?, BooleanSelectionSyntax.expr, BooleanSelectionSyntax.proposition,
      BooleanSelectionSyntax.evidence, booleanRelationCondition, booleanLiteralExpr]

theorem booleanSelectionSyntax_sound {source : Lean.Expr} {value : BooleanSelectionSyntax}
    (parsed : booleanSelectionSyntax? source = some value) : source = value.expr := by
  unfold booleanSelectionSyntax? at parsed
  split at parsed
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨type, found, accepted⟩ := parsed
    split at accepted <;> try contradiction
    rename_i same
    have he := LeanExe.Source.ExprEquality.same_eq_true.mp same
    cases accepted
    rw [booleanType_sound found, he]
    rfl
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨type, found, accepted⟩ := parsed
    split at accepted <;> try contradiction
    rename_i same
    have he := LeanExe.Source.ExprEquality.same_eq_true.mp same
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
    obtain ⟨⟨t, e⟩, bodies, rfl⟩ := accepted
    obtain ⟨htd, hfd, ht, hn⟩ := booleanProofBodies_sound bodies
    rw [booleanType_sound found, he, htd, hfd, ht, hn]
    rfl
  · contradiction

@[simp] theorem booleanSelected_not_local (value : BooleanSelected) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanSelected? (source : Lean.Expr) : Option BooleanSelected :=
  if absent : booleanLocalOperands? source = none then
    match parsed : booleanSelectionSyntax? source with
    | some selection => some ⟨selection,
        fun expression same => booleanLocal_excluded absent expression ((booleanSelectionSyntax_sound parsed).trans same)⟩
    | none => none
  else none

@[simp] theorem booleanSelected_accepts (value : BooleanSelected) :
    booleanSelected? value.expr = some value := by
  have absent := booleanSelected_not_local value
  rcases value with ⟨selection, extended⟩
  simp only [booleanSelected?, dite_eq_left absent]
  split
  · rename_i actual found
    have same := Option.some.inj ((booleanSelectionSyntax_accepts selection).symm.trans found)
    cases same
    rfl
  · rename_i found
    rw [booleanSelectionSyntax_accepts] at found
    contradiction

theorem booleanSelected_sound {source : Lean.Expr} {value : BooleanSelected}
    (parsed : booleanSelected? source = some value) : source = value.expr := by
  unfold booleanSelected? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i selection found
  cases parsed
  exact booleanSelectionSyntax_sound found

@[simp] theorem booleanSelected_not_helper (value : BooleanSelected) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanSelected_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanSelected_not_wrapped (value : BooleanSelected) :
    booleanWrapped? value.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanSelected_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanSelected_not_negated (value : BooleanSelected) :
    booleanNegated? value.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanSelected_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanSelected_not_joined (value : BooleanSelected) :
    booleanJoined? value.expr = none := by
  unfold booleanJoined?
  rw [dite_eq_left (booleanSelected_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

@[simp] theorem booleanSelected_not_related (value : BooleanSelected) :
    booleanRelated? value.expr = none := by
  unfold booleanRelated?
  rw [dite_eq_left (booleanSelected_not_local value)]
  rcases value with ⟨⟨type, proof, condition, yes, no⟩, extended⟩
  cases proof <;> rfl

theorem booleanSelected_sizes {source : Lean.Expr} {value : BooleanSelected}
    (parsed : booleanSelected? source = some value) :
    sizeOf value.selection.condition < sizeOf source ∧
      sizeOf value.selection.yes < sizeOf source ∧ sizeOf value.selection.no < sizeOf source := by
  rw [booleanSelected_sound parsed]
  exact value.selection.children_size

end LeanExe.Extract.Core
