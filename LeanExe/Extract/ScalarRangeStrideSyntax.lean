import LeanExe.Source.ScalarRangeStrideSyntax
import LeanExe.Extract.ScalarRangeCount

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar.Range.Exit

def scalarRangeStride? (source evidence : Lean.Expr) : Option Stride :=
  match scalarRangeCount? source with
  | some (.literal number fits) =>
      if positive : 0 < number then some ⟨number, positive, fits, evidence⟩ else none
  | _ => none

theorem scalarRangeStride_accepts (stride : Stride) :
    scalarRangeStride? stride.source stride.evidence = some stride := by
  have recognized := scalarRangeCount_accepts (.literal stride.number stride.fits)
  simp only [Count.source] at recognized
  simp [scalarRangeStride?, Stride.source, recognized, stride.positive]

theorem scalarRangeStride_sound {source evidence : Lean.Expr} {stride : Stride}
    (matched : scalarRangeStride? source evidence = some stride) :
    source = stride.source ∧ evidence = stride.evidence := by
  unfold scalarRangeStride? at matched
  split at matched
  · rename_i number fits recognized
    split at matched
    · cases matched
      exact ⟨scalarRangeCount_sound recognized, rfl⟩
    · contradiction
  · contradiction

end LeanExe.Extract.Core
