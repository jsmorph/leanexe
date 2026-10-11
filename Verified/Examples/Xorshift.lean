import Verified.Reflect.Command
import Examples.Xorshift.Period

/-! The thirty-fourth program of the verified compiler: Marsaglia's xorshift64 of
`Examples/Xorshift/Program.lean`, compiled unchanged.  Neither `step`
nor `advance` allocates, so the compiler's theorem states that the module computes each of them
without a trap.  `xorshift_advance` adds the theorem of `Examples/Xorshift/Period.lean` that a
nonzero state never becomes 0. -/

namespace Verified.Examples.Xorshift

open _root_.Examples.Xorshift

verified_compile compiled := [step, advance]

/-- The module's bytes decode to the module, whose function 3 computes `advance` without a trap,
and `advance n x` is nonzero for every nonzero `x`. -/
theorem xorshift_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 3
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ n x : UInt64, x ≠ 0 → advance n x ≠ 0 := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, fun n _ hx => advance_ne_zero hx n⟩

end Verified.Examples.Xorshift
