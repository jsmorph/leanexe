import Verified.Reflect.Command
import Examples.Lcg.Period

/-! The thirty-second program of the verified compiler: the linear congruential generator of
`Examples/Lcg/Program.lean`, compiled unchanged.  None of
`affine`, `step`, and `advance` allocates, so the compiler's theorem states that the module computes
each of them without a trap.  `lcg_advance` adds the theorem of `Examples/Lcg/Period.lean` that
from every word each word occurs at exactly one count. -/

namespace Verified.Examples.Lcg

open _root_.Examples.Lcg

verified_compile compiled := [affine, step, advance]

/-- The module's bytes decode to the module, whose function 4 computes `advance` without a trap,
and for all words `x` and `y` exactly one count `n` gives `advance n x = y`. -/
theorem lcg_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ x y : UInt64, ∃! n : UInt64, advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, advance_existsUnique⟩

end Verified.Examples.Lcg
