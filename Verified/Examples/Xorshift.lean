import Verified.Reflect.Command
import Examples.Xorshift.Jump

/-! The thirty-fourth program of the verified compiler: Marsaglia's xorshift64 of
`Examples/Xorshift/Program.lean`, compiled unchanged.  `step`, `advance`, and `applyCols` do not
allocate, so the compiler's theorem states that the module computes them without a trap.  `square`,
`jumpPass`, and `jump` allocate, and `jump_bound` states that the compiler's bound on the growth of
`top` during `jump` is 36,920 bytes: 568 bytes for each of the 65 blocks that it builds.
`xorshift_advance` adds the theorems of `Examples/Xorshift/Period.lean` that a nonzero state never
becomes 0 and that from every nonzero state each nonzero state occurs at exactly one count below the
period `2^64 - 1`, and `xorshift_jump` the theorem of `Examples/Xorshift/Jump.lean` that `jump`
computes `advance`. -/

namespace Verified.Examples.Xorshift

open _root_.Examples.Xorshift

verified_compile compiled := [step, advance, applyCols, square, jumpPass, jump]

/-- The module's bytes decode to the module, whose function 3 computes `advance` without a trap,
`advance n x` is nonzero for every nonzero `x`, and from every nonzero `x` each nonzero `y` occurs
at exactly one count below `2^64 - 1`. -/
theorem xorshift_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 3
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    (∀ n x : UInt64, x ≠ 0 → advance n x ≠ 0) ∧
    ∀ x y : UInt64, x ≠ 0 → y ≠ 0 →
      ∃! n : UInt64, n < 18446744073709551615 ∧ advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, fun n _ hx => advance_ne_zero hx n,
    fun _ _ hx hy => advance_existsUnique hx hy⟩

/-- The compiler's bound on the growth of `top` during `jump` is 36,920 bytes: 568 bytes, the 64
words, the length word, and a block's header of 48 bytes, for each of 65 blocks, the first columns
and one square per pass. -/
theorem jump_bound (x : UInt64 × UInt64) : compiled.jump.bound x = 36920 := by
  obtain ⟨n, y⟩ := x
  have hp : ∀ a b, compiled.jumpPass.bound (n, a, b) = blockCost (UInt64.toNat 64) := fun a b => by
    rw [compiled.jumpPass.bound_eq, compiled.square.bound_eq]
  rw [compiled.jump.bound_eq]
  simp only [hp, loopCost_const]
  rfl

/-- The module's bytes decode to the module, whose function 7, `jump`, computes `advance` without a
trap when `top` can rise by 36,920 bytes within the memory's cap, and raises `top` by at most that
much. -/
theorem xorshift_jump : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 7
      (fun x : UInt64 × UInt64 => advance x.1 x.2)
      (fun _ heap store => heap.Within store compiled.module 36920)
      (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 36920) := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  have h := compiled.jump.trapFree.mono (fun x _ _ hw => by rw [jump_bound]; exact hw)
    fun x _ _ _ _ _ hle => by rw [jump_bound] at hle; exact hle
  rw [show (fun x : UInt64 × UInt64 => jump x.1 x.2) = fun x => advance x.1 x.2 from
    funext fun x => jump_eq x.1 x.2] at h
  exact ⟨bytes, success, decoded, h⟩

#print axioms step_xor
#print axioms step_bijective
#print axioms iterate_ne_zero
#print axioms advance_ne_zero

end Verified.Examples.Xorshift
