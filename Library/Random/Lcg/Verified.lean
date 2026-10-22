import Verified.Reflect.Command
import Library.Random.Lcg.Jump

/-! The thirty-second program of the verified compiler: the linear congruential generator of
`Examples/Lcg/Program.lean`, compiled unchanged.  None of its functions allocates, so the compiler's
theorem states that the module computes each of them without a trap.  `lcg_advance` adds the
theorem of `Examples/Lcg/Period.lean` that from every word each word occurs at exactly one count,
and `lcg_jump` the theorem of `Examples/Lcg/Jump.lean` that `jump` computes `advance`. -/

namespace Library.Random.Lcg

open _root_.Library.Random.Lcg

verified_compile compiled := [affine, step, advance, jumpPass, jump]

/-- The module's bytes decode to the module, whose function 4 computes `advance` without a trap,
and for all words `x` and `y` exactly one count `n` gives `advance n x = y`. -/
theorem lcg_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ x y : UInt64, ∃! n : UInt64, advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, advance_existsUnique⟩

/-- The module's bytes decode to the module, whose function 6, `jump`, computes `advance` without a
trap by one squaring of the affine map per bit of the count. -/
theorem lcg_jump : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 6
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  have h := compiled.jump.implements
  rw [show (fun x : UInt64 × UInt64 => jump x.1 x.2) = fun x => advance x.1 x.2 from
    funext fun x => jump_eq x.1 x.2] at h
  exact ⟨bytes, success, decoded, h⟩

#print axioms minimalPeriod_affine_iff
#print axioms step_minimalPeriod
#print axioms step_bijective
#print axioms advance_existsUnique
#print axioms advance_ne_self
#print axioms periodic_testBit_iff
#print axioms step_periodic_testBit_iff

end Library.Random.Lcg
