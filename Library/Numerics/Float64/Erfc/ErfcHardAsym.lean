import Library.Numerics.Float64.Erfc.ErfcHardRows
import Library.Numerics.Float64.Erfc.ErfcHardAsym0
import Library.Numerics.Float64.Erfc.ErfcHardAsym1

/-!
The 22 hard cases of `Erfc` for `x > 0x1.b59ffb450828cp+0` (the table at offset 0 of
`excTable`, rows in `ErfcHardAsym0` and `ErfcHardAsym1`).  `table` gives one step for
`Erfc.hardCase` on this table when the fallback is within one step.
-/

namespace Library.Numerics.Float64.Erfc.ErfcHardAsym

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcHardBase ErfcHardRows RealErf

set_option exponentiation.threshold 4096

theorem table (x f : Float) (hx : ff x)
    (hf : F64SignedRounding.WithinSteps 1 (erfc (fv x)) f.toBits) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.hardCase Erfc.excTable 0 22 x f).toBits := by
  rcases hardCase_cases Erfc.excTable 0 22 x f with h | ⟨k, hk, heq, h⟩
  · rw [h]; exact hf
  · rw [h]
    have hk' : k < 22 := hk
    interval_cases k
    · exact ErfcHardAsym0.within0 x hx heq
    · exact ErfcHardAsym0.within1 x hx heq
    · exact ErfcHardAsym0.within2 x hx heq
    · exact ErfcHardAsym0.within3 x hx heq
    · exact ErfcHardAsym0.within4 x hx heq
    · exact ErfcHardAsym0.within5 x hx heq
    · exact ErfcHardAsym0.within6 x hx heq
    · exact ErfcHardAsym0.within7 x hx heq
    · exact ErfcHardAsym0.within8 x hx heq
    · exact ErfcHardAsym0.within9 x hx heq
    · exact ErfcHardAsym0.within10 x hx heq
    · exact ErfcHardAsym1.within11 x hx heq
    · exact ErfcHardAsym1.within12 x hx heq
    · exact ErfcHardAsym1.within13 x hx heq
    · exact ErfcHardAsym1.within14 x hx heq
    · exact ErfcHardAsym1.within15 x hx heq
    · exact ErfcHardAsym1.within16 x hx heq
    · exact ErfcHardAsym1.within17 x hx heq
    · exact ErfcHardAsym1.within18 x hx heq
    · exact ErfcHardAsym1.within19 x hx heq
    · exact ErfcHardAsym1.within20 x hx heq
    · exact ErfcHardAsym1.within21 x hx heq

#print axioms table

end Library.Numerics.Float64.Erfc.ErfcHardAsym
