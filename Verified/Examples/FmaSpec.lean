import Verified.Examples.Fma
import LeanExe.ProofKit.F64SignedRounding

/-!
The property of `Fma.fma` that the proof of `Erfc.erfc` uses, as a proposition.  For finite
operands whose exact `a b + c` lies within `2 ^ 1023` in magnitude, the result is finite and a
nearest double to `a b + c`: no finite double lies closer.  The proof of `erfc` takes `FmaNearest`
as a hypothesis until the correctness proof of `Fma.fma` proves it, so that its axiom report stays
the permitted one.
-/

namespace Verified.Examples.FmaSpec

open CodeLib.IEEE64

/-- `Fma.fma a b c` is finite and nearest to `a b + c` when the operands are finite and
`|a b + c| ≤ 2 ^ 1023`. -/
def FmaNearest : Prop :=
  ∀ a b c : Float, Finite a.toBits → Finite b.toBits → Finite c.toBits →
    |value a.toBits * value b.toBits + value c.toBits| ≤ 2 ^ 1023 →
    Finite (Fma.fma a b c).toBits ∧
      ∀ v : UInt64, Finite v →
        |value (Fma.fma a b c).toBits - (value a.toBits * value b.toBits + value c.toBits)| ≤
          |value v - (value a.toBits * value b.toBits + value c.toBits)|

end Verified.Examples.FmaSpec
