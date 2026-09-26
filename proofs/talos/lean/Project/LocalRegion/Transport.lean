import Project.LocalRegion.Exec
import Project.LocalRegion.Calls
import Project.FunctionRegion.Exec
import Project.ProofKit.Sequence

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

theorem wp_calls
    (shift : Shift sourceModule targetModule callRename typeRename calls)
    (hPortable : PortableProgram calls program)
    (hSource : wp sourceModule program P st frame env) :
    wp targetModule (FunctionRegion.renameProgram callRename program) P st frame env := by
  unfold wp at hSource ⊢
  obtain ⟨minimumFuel, hFuel⟩ := hSource
  refine ⟨minimumFuel, fun fuel hMinimum => ?_⟩
  rw [FunctionRegion.exec_eq shift hPortable]
  exact hFuel fuel hMinimum

theorem wp_renamed
    (mapping : FrameMap localRename locals Related)
    (shift : Shift sourceModule targetModule callRename typeRename calls)
    (hRelated : Related source target)
    (hPortable : PortableProgram calls program)
    (hAllowed : AllowsProgram locals program)
    (hPost : ∀ sourceResult targetResult, ContinuationRel Related sourceResult targetResult →
      P sourceResult → Q targetResult)
    (hSource : wp sourceModule program P st source env) :
    wp targetModule
      (renameProgram localRename (FunctionRegion.renameProgram callRename program))
      Q st target env :=
  wp_transport mapping hRelated (portableProgram_calls program hPortable)
    (allowsProgram_calls program hAllowed) hPost (wp_calls shift hPortable hSource)

theorem wp_fallthrough
    (mapping : FrameMap localRename locals Related)
    (shift : Shift sourceModule targetModule callRename typeRename calls)
    (hRelated : Related source target)
    (hPortable : PortableProgram calls program)
    (hAllowed : AllowsProgram locals program)
    (hSource : wp sourceModule program (ProofKit.Sequence.Fallthrough P) st source env)
    (hNext : ∀ nextStore nextSource nextTarget, P nextStore nextSource →
      Related nextSource nextTarget → wp targetModule rest Q nextStore nextTarget env) :
    wp targetModule
      (renameProgram localRename (FunctionRegion.renameProgram callRename program) ++ rest)
      Q st target env := by
  apply ProofKit.Sequence.wp_append
    (P := fun nextStore nextTarget => ∃ nextSource,
      Related nextSource nextTarget ∧ P nextStore nextSource)
  · apply wp_renamed mapping shift hRelated hPortable hAllowed (hSource := hSource)
    intro sourceResult targetResult hResult hPost
    cases hResult <;> simp only [ProofKit.Sequence.Fallthrough] at hPost ⊢
    case fallthrough h => exact ⟨_, h, hPost⟩
  · rintro nextStore nextTarget ⟨nextSource, hRelated, hPost⟩
    exact hNext nextStore nextSource nextTarget hPost hRelated

#print axioms wp_fallthrough
end Project.LocalRegion
