import LeanExe.Extract.ScalarBooleanLetTypes
import LeanExe.Source.ScalarGuardLet

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def guardLetType? (type : Lean.Expr) : Option GuardLetType :=
  match scalarResultType? type with
  | some result => some (.word result)
  | none =>
      match booleanType? type with
      | some result => some (.boolean result)
      | none =>
          match type with
          | .forallE name (.const ``UInt64 []) result info =>
              (booleanType? result).map (.predicate false name info)
          | .forallE name (.const ``Bool []) result info =>
              (booleanType? result).map (.predicate true name info)
          | .forallE name (.app (.const ``Id [.zero]) domain) result info =>
              match parsed : PublicArgument.ofType? domain with
              | some kind => (booleanType? result).map
                  (.predicateId kind domain (PublicArgument.ofType_sound parsed) name info)
              | none => none
          | _ => none

@[simp] theorem guardLetType_accepts (type : GuardLetType) :
    guardLetType? type.expr = some type := by
  cases type with
  | word type => simp [guardLetType?, GuardLetType.expr]
  | boolean type => simp [guardLetType?, GuardLetType.expr, scalarResultType_boolean]
  | predicate booleanInput inputName info result =>
    cases booleanInput <;> simp [guardLetType?, GuardLetType.expr, scalarResultType?, booleanType?]
  | predicateId kind domain input inputName info result =>
    simp [guardLetType?, GuardLetType.expr, scalarResultType?, booleanType?]
    have parsed := PublicArgument.ofType_accepts input
    split <;> simp_all

theorem guardLetType_sound {type : Lean.Expr} {result : GuardLetType}
    (found : guardLetType? type = some result) : type = result.expr := by
  unfold guardLetType? at found
  split at found
  · rename_i result parsed
    cases found
    exact scalarResultType_sound parsed
  · split at found
    · rename_i result parsed
      cases found
      exact booleanType_sound parsed
    · split at found
      · obtain ⟨annotation, parsed, rfl⟩ := Option.map_eq_some_iff.mp found
        rw [booleanType_sound parsed]
        rfl
      · obtain ⟨annotation, parsed, rfl⟩ := Option.map_eq_some_iff.mp found
        rw [booleanType_sound parsed]
        rfl
      · split at found
        · obtain ⟨annotation, parsed, rfl⟩ := Option.map_eq_some_iff.mp found
          rw [booleanType_sound parsed]
          rfl
        · contradiction
      · contradiction

end LeanExe.Extract.Core
