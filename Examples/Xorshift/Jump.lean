import Examples.Xorshift.Period
import LeanExe.IR.Combinators

/-! `jump` of `Examples/Xorshift/Program.lean` computes `advance`.  A map on words that distributes
over xor is the xor of its columns, the images of `2^i`, at the set bits of its argument, which the
decomposition of a word into its bits gives, so `applyCols` of the columns of such a map computes
it and `square` gives the columns of its square.  After `k` passes, `jump`'s state holds
`step^[n % 2^k] x` and the columns of `step^[2^k]`. -/

namespace Examples.Xorshift

open Function

/-- The columns of a map on words: its images of `2^i` for `i < 64`. -/
def columns (g : UInt64 → UInt64) : Array UInt64 :=
  LeanExe.build 64 fun i => g ((1 : UInt64) <<< i)

/-- The first `k` passes of `applyCols c x`. -/
def applyPasses (c : Array UInt64) (x : UInt64) (k : Nat) : UInt64 :=
  Nat.fold k (fun i _ acc =>
    (fun i acc => if (x >>> i) &&& 1 != 0 then acc ^^^ c[i.toNat]! else acc) (UInt64.ofNat i) acc) 0

theorem applyCols_eq (c : Array UInt64) (x : UInt64) :
    applyCols c x = applyPasses c x 64 := rfl

theorem applyPasses_succ (c : Array UInt64) (x : UInt64) (k : Nat) :
    applyPasses c x (k + 1) = if (x >>> UInt64.ofNat k) &&& 1 != 0 then
      applyPasses c x k ^^^ c[(UInt64.ofNat k).toNat]! else applyPasses c x k := by
  unfold applyPasses
  rw [Nat.fold_succ]

theorem columns_get (g : UInt64 → UInt64) {k : Nat} (hk : k < 64) :
    (columns g)[(UInt64.ofNat k).toNat]! = g ((1 : UInt64) <<< UInt64.ofNat k) := by
  have hk' : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [hk', columns, LeanExe.IR.build_get (by simpa using hk)]

/-- The unit columns give the bits of `x` below `k`. -/
theorem testBit_applyPasses_unit (x : UInt64) (j : Nat) : ∀ k ≤ 64,
    (applyPasses (columns id) x k).toNat.testBit j = (decide (j < k) && x.toNat.testBit j) := by
  intro k hk
  induction k with
  | zero => simp [applyPasses]
  | succ k ih =>
    rw [applyPasses_succ, Orbit.shift_and_one_ne_zero x (by omega)]
    split <;> rename_i hb
    · rw [UInt64.toNat_xor, Nat.testBit_xor, ih (by omega), columns_get _ (by omega), id,
        Orbit.toNat_one_shiftLeft (by omega), Nat.testBit_two_pow]
      by_cases hjk : j = k
      · subst hjk; simp [hb]
      · by_cases hlt : j < k <;> simp [hlt, Ne.symm hjk] <;> omega
    · rw [ih (by omega)]
      by_cases hjk : j = k
      · subst hjk; simp_all
      · by_cases hlt : j < k <;> simp [hlt] <;> omega

theorem applyCols_unit (x : UInt64) : applyCols (columns id) x = x := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  rw [applyCols_eq, testBit_applyPasses_unit x j 64 le_rfl]
  by_cases hj : j < 64
  · simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le x.toNat_lt
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem Linear.map_zero_word {g : UInt64 → UInt64} (h : Linear g) : g 0 = 0 := by
  have := h 0 0
  simpa using this

theorem applyPasses_linear {g : UInt64 → UInt64} (hg : Linear g) (x : UInt64) :
    ∀ k ≤ 64, applyPasses (columns g) x k = g (applyPasses (columns id) x k) := by
  intro k hk
  induction k with
  | zero => simp [applyPasses, hg.map_zero_word]
  | succ k ih =>
    rw [applyPasses_succ, applyPasses_succ, ih (by omega)]
    split
    · rw [columns_get _ (by omega), columns_get _ (by omega), hg, id]
    · rfl

/-- The columns of a map that distributes over xor give its image of every word. -/
theorem applyCols_columns {g : UInt64 → UInt64} (hg : Linear g) (x : UInt64) :
    applyCols (columns g) x = g x := by
  rw [applyCols_eq, applyPasses_linear hg x 64 le_rfl, ← applyCols_eq, applyCols_unit]

theorem square_columns {g : UInt64 → UInt64} (hg : Linear g) :
    square (columns g) = columns (g ∘ g) := by
  unfold square columns
  apply LeanExe.IR.build_congr
  intro i hi
  rw [show (LeanExe.build 64 fun i => g ((1 : UInt64) <<< i)) = columns g from rfl,
    show (columns g)[i.toNat]! = g ((1 : UInt64) <<< i) by
      rw [columns, LeanExe.IR.build_get hi, UInt64.ofNat_toNat], applyCols_columns hg]
  rfl

theorem step_linear : Linear step := step_xor

/-- The state of `jump`'s loop after `k` passes. -/
def jumpPasses (n x : UInt64) (k : Nat) : UInt64 × Array UInt64 :=
  Nat.fold k (fun i _ s => jumpPass n (UInt64.ofNat i) s) (x, columns step)

theorem jump_eq_passes (n x : UInt64) : jump n x = (jumpPasses n x 64).1 := rfl

theorem jumpPasses_spec (n x : UInt64) : ∀ k ≤ 64,
    (jumpPasses n x k).1 = step^[n.toNat % 2 ^ k] x ∧
      (jumpPasses n x k).2 = columns step^[2 ^ k] := by
  intro k hk
  induction k with
  | zero => simp [jumpPasses, Nat.mod_one]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    unfold jumpPasses
    rw [Nat.fold_succ]
    show (jumpPass n (UInt64.ofNat k) (jumpPasses n x k)).1 = _ ∧
      (jumpPass n (UInt64.ofNat k) (jumpPasses n x k)).2 = _
    simp only [jumpPass]
    rw [Orbit.shift_and_one_ne_zero n (by omega), Nat.testBit_eq_decide_div_mod_eq,
      Nat.mod_pow_succ, h2, square_columns (step_linear.iterate _), ← iterate_add, pow_succ,
      Nat.mul_two]
    refine ⟨?_, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one (n.toNat / 2 ^ k) with hb | hb
    · simp [hb, h1]
    · simp only [hb, decide_true, ↓reduceIte, Nat.mul_one]
      rw [applyCols_columns (step_linear.iterate _), h1, ← iterate_add_apply, Nat.add_comm]

/-- `jump` computes `advance`. -/
theorem jump_eq (n x : UInt64) : jump n x = advance n x := by
  rw [jump_eq_passes, (jumpPasses_spec n x 64 le_rfl).1, advance_eq_iterate,
    Nat.mod_eq_of_lt n.toNat_lt]

end Examples.Xorshift
