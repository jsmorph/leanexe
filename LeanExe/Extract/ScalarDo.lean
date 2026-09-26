import LeanExe.Source.ScalarDo
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (ResultType)

def scalarResultType? : Lean.Expr → Option ResultType
  | .const ``UInt64 [] => some .word
  | .app (.const ``Id [.zero]) inner => (scalarResultType? inner).map ResultType.identity
  | _ => none

@[simp] theorem scalarResultType_accepts (type : ResultType) :
    scalarResultType? type.expr = some type := by
  induction type with
  | word => rfl
  | identity inner ih => simp [ResultType.expr, scalarResultType?, ih]

theorem scalarResultType_sound {source : Lean.Expr} {type : ResultType}
    (matched : scalarResultType? source = some type) : source = type.expr := by
  induction source using scalarResultType?.induct generalizing type with
  | case1 => cases matched; rfl
  | case2 inner ih =>
    rw [scalarResultType?] at matched
    obtain ⟨type, found, rfl⟩ := Option.map_eq_some_iff.mp matched
    simp [ResultType.expr, ih found]
  | case3 source h1 h2 => rw [scalarResultType?] at matched <;> first | assumption | contradiction

/-- Bind annotations must be scalar Id types, with the exact input binder type. -/
def scalarBindTypes? (input domain output : Lean.Expr) : Option (ResultType × ResultType) := do
  let first ← scalarResultType? input
  let last ← scalarResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem scalarBindTypes_accepts (input output : ResultType) :
    scalarBindTypes? input.expr input.expr output.expr = some (input, output) := by
  simp [scalarBindTypes?]

theorem scalarBindTypes_sound {input domain output : Lean.Expr} {first last : ResultType}
    (parsed : scalarBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = last.expr := by
  simp only [scalarBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨scalarResultType_sound ha, same ▸ scalarResultType_sound ha, scalarResultType_sound hb⟩
  · contradiction

end LeanExe.Extract.Core
