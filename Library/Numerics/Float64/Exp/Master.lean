import Library.Numerics.Float64.Exp.ExpTheorem
import Verified.Master

namespace Library.Numerics.Float64.Exp

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `exp`, called on a finite float `x`, returns a float within one representable step
of the nearest-even rounding of `Real.exp x`. -/
theorem exp_master :
    Verified.Master compiled.module compiled.tables "exp" compiled.exp.bound
      (fun x : Float => Finite x.toBits)
      (fun x (y : Float) => F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits)) y.toBits) :=
  .of_trapFree compiled.exp.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)
    ExpTheorem.exp_export (fun _ _ _ _ h => by first | exact h | trivial)
    (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hx => by
      obtain ⟨h1, h2, h3⟩ := ExpTheorem.exp_one_step x hx
      exact F64SignedRounding.within_of_nonneg 1 _ (Real.exp_pos _).le _ h1 h2 h3

#print axioms exp_master

end Library.Numerics.Float64.Exp
