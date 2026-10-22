import Library.Random.Lcg.Period

/-! `jump` of `Examples/Lcg/Program.lean` computes `advance`: after `k` passes its state holds the
coefficients of the steps of the low `k` bits of `n` and the coefficients `doubled a c k` of `2^k`
steps. -/

namespace Library.Random.Lcg

open Function
open scoped UInt64.CommRing

/-- The state of `jump`'s loop after `k` passes. -/
def jumpPasses (n : UInt64) (k : Nat) : UInt64 × UInt64 × UInt64 × UInt64 :=
  Nat.fold k (fun i _ s => jumpPass n (UInt64.ofNat i) s)
    (1, 0, multiplier, increment)

theorem jump_eq_passes (n x : UInt64) :
    jump n x = (jumpPasses n 64).1 * x + (jumpPasses n 64).2.1 := rfl

theorem jumpPasses_succ (n : UInt64) (k : Nat) :
    jumpPasses n (k + 1) = jumpPass n (UInt64.ofNat k) (jumpPasses n k) := by
  unfold jumpPasses
  rw [Nat.fold_succ]

/-- After `k` passes, the loop holds the coefficients of the steps of the low `k` bits of `n` and
of `2^k` steps. -/
theorem jumpPasses_spec (n x : UInt64) : ∀ k ≤ 64,
    (jumpPasses n k).2.2 = doubled multiplier increment k ∧
      step^[n.toNat % 2 ^ k] x = (jumpPasses n k).1 * x + (jumpPasses n k).2.1 := by
  intro k hk
  induction k with
  | zero => simp [jumpPasses, doubled, Nat.mod_one]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [jumpPasses_succ, jumpPass, Orbit.shift_and_one_ne_zero n (by omega),
      Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
    have hstep : ∀ m, step^[m] = (affine multiplier increment)^[m] :=
      fun _ => rfl
    rcases Nat.mod_two_eq_zero_or_one (n.toNat / 2 ^ k) with hb | hb
    · simp only [hb, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero,
        Nat.add_zero]
      exact ⟨by rw [doubled, ← h1], h2⟩
    · simp only [hb, decide_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [doubled, ← h1]
      · rw [Nat.mul_one, Nat.add_comm, iterate_add_apply, h2, hstep, iterate_two_pow, ← h1]
        ring

/-- `jump` computes `advance`. -/
theorem jump_eq (n x : UInt64) : jump n x = advance n x := by
  rw [jump_eq_passes, advance_eq_iterate, ← (jumpPasses_spec n x 64 le_rfl).2,
    Nat.mod_eq_of_lt n.toNat_lt]

end Library.Random.Lcg
