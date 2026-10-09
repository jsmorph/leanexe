import Verified.Examples.Orbit
import Mathlib.Data.Fintype.Card

/-! Marsaglia's xorshift64 generator with the shifts 13, 7, and 17: each step replaces the state
`x` with `x ^^^ (x <<< 13)`, then with `x ^^^ (x >>> 7)`, and then with `x ^^^ (x <<< 17)`.  Each
of the three operations distributes over xor and is injective, so the step is a bijection on words
that maps 0 to 0, and a nonzero state never becomes 0.  The proofs work with the bit vectors of
the words.  The programs are `step` and `advance`. -/

namespace Verified.Examples.Xorshift

/-- One step of xorshift64: `x ^^^ (x <<< 13)`, then `x ^^^ (x >>> 7)`, then `x ^^^ (x <<< 17)`. -/
def step (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

open Function

theorem advance_eq_iterate (n x : UInt64) : advance n x = step^[n.toNat] x :=
  Orbit.loop_eq_iterate step n x

/-- `v ^^^ (v <<< a)`. -/
def shl (a : ℕ) (v : BitVec 64) : BitVec 64 := v ^^^ (v <<< a)

/-- `v ^^^ (v >>> a)`. -/
def shr (a : ℕ) (v : BitVec 64) : BitVec 64 := v ^^^ (v >>> a)

theorem toBitVec_step (x : UInt64) : (step x).toBitVec = shl 17 (shr 7 (shl 13 x.toBitVec)) :=
  rfl

theorem shl_xor (a : ℕ) (v w : BitVec 64) : shl a (v ^^^ w) = shl a v ^^^ shl a w := by
  simp only [shl, BitVec.shiftLeft_xor_distrib]
  ac_rfl

theorem shr_xor (a : ℕ) (v w : BitVec 64) : shr a (v ^^^ w) = shr a v ^^^ shr a w := by
  simp only [shr, BitVec.ushiftRight_xor_distrib]
  ac_rfl

theorem eq_zero_of_shl_eq_zero {a : ℕ} (ha : 0 < a) {v : BitVec 64} (h : shl a v = 0) : v = 0 := by
  have hv : v = v <<< a := BitVec.xor_eq_zero_iff.mp h
  have key : ∀ m i, i ≤ m → v.getLsbD i = false := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [hv, BitVec.getLsbD_shiftLeft]
      simp [show i < a by omega]
    | succ m ih =>
      intro i hi
      rw [hv, BitVec.getLsbD_shiftLeft]
      by_cases hia : i < a
      · simp [hia]
      · simp [ih (i - a) (by omega)]
  exact BitVec.eq_of_getLsbD_eq fun i _ => by simp [key i i le_rfl]

theorem eq_zero_of_shr_eq_zero {a : ℕ} (ha : 0 < a) {v : BitVec 64} (h : shr a v = 0) : v = 0 := by
  have hv : v = v >>> a := BitVec.xor_eq_zero_iff.mp h
  have key : ∀ m i, 64 - i ≤ m → v.getLsbD i = false := by
    intro m
    induction m with
    | zero =>
      intro i hi
      exact BitVec.getLsbD_of_ge v i (by omega)
    | succ m ih =>
      intro i hi
      rw [hv, BitVec.getLsbD_ushiftRight]
      exact ih (a + i) (by omega)
  exact BitVec.eq_of_getLsbD_eq fun i _ => by simp [key 64 i (by omega)]

theorem shl_injective {a : ℕ} (ha : 0 < a) : Injective (shl a) := fun v w h =>
  BitVec.xor_eq_zero_iff.mp (eq_zero_of_shl_eq_zero ha (by rw [shl_xor, h, BitVec.xor_self]; rfl))

theorem shr_injective {a : ℕ} (ha : 0 < a) : Injective (shr a) := fun v w h =>
  BitVec.xor_eq_zero_iff.mp (eq_zero_of_shr_eq_zero ha (by rw [shr_xor, h, BitVec.xor_self]; rfl))

/-- The step distributes over xor. -/
theorem step_xor (x y : UInt64) : step (x ^^^ y) = step x ^^^ step y := by
  apply UInt64.toBitVec_inj.mp
  simp only [toBitVec_step, UInt64.toBitVec_xor, shl_xor, shr_xor]

theorem step_zero : step 0 = 0 := rfl

theorem step_injective : Injective step := fun x y h => by
  have h' := congrArg UInt64.toBitVec h
  rw [toBitVec_step, toBitVec_step] at h'
  exact UInt64.toBitVec_inj.mp
    (shl_injective (a := 13) (by omega)
      (shr_injective (a := 7) (by omega) (shl_injective (a := 17) (by omega) h')))

/-- The step is a bijection on words. -/
theorem step_bijective : Bijective step := Finite.injective_iff_bijective.mp step_injective

/-- A nonzero state never becomes 0. -/
theorem iterate_ne_zero {x : UInt64} (hx : x ≠ 0) (n : ℕ) : step^[n] x ≠ 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [iterate_succ_apply']
    exact fun h => ih (step_injective (h.trans step_zero.symm))

theorem advance_ne_zero {x : UInt64} (hx : x ≠ 0) (n : UInt64) : advance n x ≠ 0 := by
  rw [advance_eq_iterate]
  exact iterate_ne_zero hx _

end Verified.Examples.Xorshift
