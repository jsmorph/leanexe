import LeanExe.Source.ScalarRangeCount
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar.Range.Exit

/-- Exact standard UInt64.toNat or a bounded standard Nat literal. -/
def scalarRangeCount? : Lean.Expr → Option Count
  | .app (.const ``UInt64.toNat []) source => some (.word source)
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal number)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal instanceNumber))) =>
      if checked : number = instanceNumber ∧ number < UInt64.size then
        some (.literal number checked.2)
      else none
  | _ => none

theorem scalarRangeCount_accepts (count : Count) : scalarRangeCount? count.source = some count := by
  cases count with
  | word source => rfl
  | literal number fits => simp [Count.source, LeanExe.Source.Scalar.Range.natLiteral, scalarRangeCount?, fits]

theorem scalarRangeCount_sound {source : Lean.Expr} {count : Count}
    (matched : scalarRangeCount? source = some count) : source = count.source := by
  unfold scalarRangeCount? at matched
  split at matched
  · cases matched; rfl
  · split at matched
    · rename_i checked
      obtain ⟨rfl, fits⟩ := checked
      cases matched
      rfl
    · contradiction
  · contradiction

/-- First indices are bounded standard literals in this increment. -/
def scalarRangeFirst? (source : Lean.Expr) : Option First :=
  match scalarRangeCount? source with
  | some (.literal number fits) => some ⟨number, fits⟩
  | _ => none

theorem scalarRangeFirst_accepts (first : First) :
    scalarRangeFirst? first.source = some first := by
  have accepted := scalarRangeCount_accepts (.literal first.number first.fits)
  simp only [Count.source] at accepted
  simp [scalarRangeFirst?, First.source, accepted]

theorem scalarRangeFirst_sound {source : Lean.Expr} {first : First}
    (matched : scalarRangeFirst? source = some first) : source = first.source := by
  unfold scalarRangeFirst? at matched
  split at matched
  · rename_i number fits recognized
    cases matched
    exact scalarRangeCount_sound recognized
  · contradiction

end LeanExe.Extract.Core
