import Library.Numerics.Arithmetic.Fma.Compiled
import Library.Numerics.Arithmetic.Fma.FmaTheorem
import Verified.Master

namespace Library.Numerics.Arithmetic.Fma

theorem fma_export :
    ({ name := "fma", funcIdx := 15 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `fma`, called on three floats `a`, `b`, and `c`, returns the float whose bits are
IEEE 754 fusedMultiplyAdd(`a`, `b`, `c`) with roundTiesToEven, with the canonical NaN for every
NaN result. -/
theorem fma_master :
    Verified.Master compiled.module compiled.tables "fma" compiled.fma.bound (fun _ => True)
      (fun (x : Float × Float × Float) (y : Float) =>
        y.toBits = FmaTheorem.fmaReference x.1.toBits x.2.1.toBits x.2.2.toBits) :=
  .of_trapFree (.ofA compiled.fma.trapFree) nofun fma_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => FmaTheorem.fma_toBits x.1 x.2.1 x.2.2

#print axioms fma_master

end Library.Numerics.Arithmetic.Fma
