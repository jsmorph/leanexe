import Library.Numerics.Decimal.PrintFloat.PrintFloatPick

/-!
The length of the search of `PrintFloat.shortest`.  The search returns `steps = jstart - top`
(`search_spec`).  Above the top exponent the interval is narrower than `10 ^ (top + 1)`
(`width_le`), and it is at least `3 · 2 ^ (E - 1) / 2 ^ (nu + 2)` wide, while `jstart` grows with
the bits of `4 Q + 2`.  So `steps ≥ N + 1` would make `10 ^ (jstart - N)` at least the width,
which an exact check of every binade refutes: at most 27 steps for a binary64 word (`steps_le`),
and at most 10 for a binary32 word (`steps_le_binary32`).
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatSteps
open PrintFloat PrintFloatQuot PrintFloatSearch PrintFloatPick

/-- `jstart` for a significand whose `4 Q + 2` has `s` bits. -/
def jfor (nu E s : ℕ) : ℤ :=
  if nu + 2 ≤ s + (E - 1) then ((31 * (s + (E - 1) - (nu + 2)) + 99) / 100 : ℕ)
  else -((3 * (nu + 2 - (s + (E - 1))) / 10 : ℕ) : ℤ)

theorem jstart_eq (Q E nu : ℕ) : jstart Q E nu = jfor nu E (Nat.size (4 * Q + 2)) := rfl

theorem jfor_mono (nu E : ℕ) {s t : ℕ} (le : s ≤ t) : jfor nu E s ≤ jfor nu E t := by
  unfold jfor
  split_ifs <;> omega

/-- Whether `10 ^ (jfor nu E s - N)` lies below `3 · 2 ^ (E - 1) / 2 ^ (nu + 2)`, in natural
numbers. -/
def wide (nu s N E : ℕ) : Bool :=
  let j := jfor nu E s - N
  if 0 ≤ j then decide (10 ^ j.toNat * 2 ^ (nu + 2) < 3 * 2 ^ (E - 1))
  else decide (2 ^ (nu + 2) < 3 * 2 ^ (E - 1) * 10 ^ (-j).toNat)

theorem wide_spec {nu s N E : ℕ} (holds : wide nu s N E = true) :
    (10 : ℝ) ^ (jfor nu E s - N) < 3 * 2 ^ (E - 1) / 2 ^ (nu + 2) := by
  unfold wide at holds
  dsimp only at holds
  have hp : (0 : ℝ) < 2 ^ (nu + 2) := by positivity
  split at holds
  · rename_i nonneg
    have nat := of_decide_eq_true holds
    have real : (10 : ℝ) ^ (jfor nu E s - N).toNat * 2 ^ (nu + 2) < 3 * 2 ^ (E - 1) := by
      exact_mod_cast nat
    rw [show jfor nu E s - (N : ℤ) = ((jfor nu E s - N).toNat : ℤ) by omega, zpow_natCast,
      lt_div_iff₀ hp]
    exact real
  · rename_i neg
    have nat := of_decide_eq_true holds
    have real : (2 : ℝ) ^ (nu + 2) < 3 * 2 ^ (E - 1) * 10 ^ (-(jfor nu E s - N)).toNat := by
      exact_mod_cast nat
    have hq : (0 : ℝ) < 10 ^ (-(jfor nu E s - N)).toNat := by positivity
    rw [show jfor nu E s - (N : ℤ) = -((-(jfor nu E s - N)).toNat : ℤ) by omega, zpow_neg,
      zpow_natCast, lt_div_iff₀ hp, inv_mul_lt_iff₀ hq]
    linarith

theorem wide_binary64 : ∀ E, E < 2049 → 1 ≤ E → wide 1074 55 27 E = true := by
  decide +kernel

theorem wide_binary32 : ∀ E, E < 256 → 1 ≤ E → wide 149 26 10 E = true := by
  decide +kernel

/-- At most `N` steps when the check holds at the word's binade for `s` bits or more. -/
theorem steps_le_of_wide {Q E nu : ℕ} {low : Bool} (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu)
    {s N : ℕ} (bits : Nat.size (4 * Q + 2) ≤ s) (holds : wide nu s N E = true) :
    steps Q E nu low hQ hE hnu ≤ N := by
  by_contra more
  have bound := width_le (low := low) hQ hE hnu
  rw [width_eq hQ] at bound
  have below := wide_spec holds
  have start : jstart Q E nu ≤ jfor nu E s := by
    rw [jstart_eq]
    exact jfor_mono nu E bits
  have topEq : top Q E nu low hQ hE hnu = jstart Q E nu - steps Q E nu low hQ hE hnu := rfl
  have power : (10 : ℝ) ^ (top Q E nu low hQ hE hnu + 1) ≤ 10 ^ (jfor nu E s - N) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have narrow : (3 : ℝ) * 2 ^ (E - 1) / 2 ^ (nu + 2) ≤ rv (if low then 3 else 4) (E - 1) (nu + 2) := by
    unfold rv
    have three : (3 : ℝ) ≤ ((if low then 3 else 4 : ℕ) : ℝ) := by split_ifs <;> norm_num
    have hp : (0 : ℝ) < 2 ^ (E - 1) := by positivity
    gcongr
  linarith

variable {Q E nu : ℕ} {low : Bool}

/-- The search of a binary64 word takes at most 27 steps. -/
theorem steps_le (hb : WordBounds Q E 1074) :
    steps Q E 1074 low hb.hQ hb.hE (by have := hb.hnu; omega) ≤ 27 := by
  have bits : Nat.size (4 * Q + 2) ≤ 55 := by
    rw [Nat.size_le]
    have := hb.hQ53
    omega
  exact steps_le_of_wide hb.hQ hb.hE _ bits
    (wide_binary64 E (by have := hb.hE2; omega) hb.hE)

/-- The search of a binary32 word takes at most 10 steps. -/
theorem steps_le_binary32 (hb : WordBounds Q E 149) (hQ24 : Q < 2 ^ 24) (hE : E < 256) :
    steps Q E 149 low hb.hQ hb.hE (by have := hb.hnu; omega) ≤ 10 := by
  have bits : Nat.size (4 * Q + 2) ≤ 26 := by
    rw [Nat.size_le]
    omega
  exact steps_le_of_wide hb.hQ hb.hE _ bits (wide_binary32 E hE hb.hE)

/-- The code's search of a binary64 word ends after at most 27 steps. -/
theorem search_le (hb : WordBounds Q E 1074) :
    (LeanExe.repeatWhile 2000 0 (fun i => i < 2000 &&
        !found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat 1074 + 2)
          (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat 1074 + 2) - i)
          ((UInt64.ofNat Q &&& 1) == 0)) (fun i => i + 1)).toNat ≤ 27 := by
  rw [search_spec hb]
  exact steps_le hb

/-- The code's search of a binary32 word ends after at most 10 steps. -/
theorem search_le_binary32 (hb : WordBounds Q E 149) (hQ24 : Q < 2 ^ 24) (hE : E < 256) :
    (LeanExe.repeatWhile 2000 0 (fun i => i < 2000 &&
        !found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat 149 + 2)
          (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat 149 + 2) - i)
          ((UInt64.ofNat Q &&& 1) == 0)) (fun i => i + 1)).toNat ≤ 10 := by
  rw [search_spec hb]
  exact steps_le_binary32 hb hQ24 hE

end Library.Numerics.Decimal.PrintFloat.PrintFloatSteps
