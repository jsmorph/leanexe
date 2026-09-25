import Project.RunningSum.SourceExecution

namespace Project.RunningSum.Source

open LeanExe.Examples.RunningSum (Decimal render)

local instance : LawfulMonad BaseIO := LawfulMonad.mk' BaseIO
  (by intros; rfl) (by intros; rfl) (by intros; rfl)

theorem newline_correct (total : Decimal) (pending : ByteArray)
    (hc : Canonical total.digits) (hv : ValidLine pending) :
    ∃ next, Canonical next.digits ∧
      integer next = integer total + lineInteger pending ∧
      DecimalOutput (integer total + lineInteger pending) (render next) ∧
      byteStep 10 (none, total, pending) = (do
        let status ← LeanExe.ByteIO.write (render next) 18446744073709551615
        if status != 0 then pure (.done (some status, total, pending))
        else pure (.yield (none, next, ByteArray.empty))) := by
  obtain ⟨value, hp, hn, hs, hout⟩ := line_add_correct total hc pending hv
  refine ⟨LeanExe.Examples.RunningSum.add total value, hn, hs, hout, ?_⟩
  simp only [byteStep, beq_self_eq_true, ↓reduceIte, LeanExe.Examples.RunningSum.emitSum,
    hp, bind_assoc]
  congr 1
  funext status
  split <;> simp only [pure_bind]

#print axioms newline_correct

end Project.RunningSum.Source
