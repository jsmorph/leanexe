import Verified.Reflect.Command
import Examples.ParkMiller.Period

/-! The thirty-third program of the verified compiler: Park and Miller's generator of
`Examples/ParkMiller/Program.lean`, compiled unchanged.  None of `step`, `advance`, and `seed`
allocates, so the compiler's theorem states that the module computes each of them without a trap.
`parkMiller_advance` adds the theorems of `Examples/ParkMiller/Period.lean` that every seed gives a
state in `[1, 2^31 - 2]` and that from such a state each state of the range occurs at exactly one
count below the period `2^31 - 2`. -/

namespace Verified.Examples.ParkMiller

open _root_.Examples.ParkMiller

verified_compile compiled := [step, advance, seed]

/-- The module's bytes decode to the module, whose functions 3 and 4 compute `advance` and `seed`
without a trap, every seed gives a state in `[1, 2^31 - 2]`, and from that state each state in the
range occurs at exactly one count below `2^31 - 2`. -/
theorem parkMiller_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 3
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4 seed
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    (∀ s : UInt64, 0 < seed s ∧ seed s < 2147483647) ∧
    ∀ s y : UInt64, 0 < y ∧ y < 2147483647 →
      ∃! n : UInt64, n < 2147483646 ∧ advance n (seed s) = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, compiled.seed.implements, seed_mem,
    fun s _ hy => advance_existsUnique (seed_mem s) hy⟩

end Verified.Examples.ParkMiller
