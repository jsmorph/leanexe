import Project.Smalltalk.Memory

namespace Project.Smalltalk.BootGuard
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def rejected (p s : Array UInt64) : Bool := !programValid p || read s 2 != 0 || read s 0 != 0

theorem accepted {p s : Array UInt64} (good : rejected p s = false) :
    programValid p = true ∧ read s 2 = 0 ∧ read s 0 = 0 := by
  have program : programValid p = true := by
    cases eq : programValid p
    · simp only [rejected, eq, Bool.not_false, Bool.true_or] at good
      contradiction
    · rfl
  have current : read s 2 = 0 := by
    apply Classical.byContradiction
    intro nonzero
    have bad := bne_iff_ne.mpr nonzero
    simp only [rejected, bad, Bool.or_true, Bool.true_or] at good
    contradiction
  have phase : read s 0 = 0 := by
    apply Classical.byContradiction
    intro nonzero
    have bad := bne_iff_ne.mpr nonzero
    simp only [rejected, bad, Bool.or_true] at good
    contradiction
  exact ⟨program, current, phase⟩

end Project.Smalltalk.BootGuard
