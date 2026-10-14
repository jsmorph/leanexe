import Verified.Examples.LgammaApprox

/-!
The piece index of `Lgamma.piece`.  For the top bits `au` of a double from 0.5 to 8.29541, the code
estimates the piece by a quadratic in `au - tab[0]` (`jf`) and corrects the estimate by one
comparison with the border `tab[j]`.  `jf` increases on the range (`jf_mono`), and the kernel checks
`k ≤ jf` at the first and `jf ≤ k + 1` at the last value of each piece `k` (`border_ok`), so the
comparison returns the piece `k` with `tab[k] ≤ au < tab[k + 1]` (`piece_spec`).
-/

namespace Verified.Examples.LgammaPieceIdx

/-- The border `k` of the pieces as a natural number. -/
def tw (k : ℕ) : ℕ := (Lgamma.mainTable[k]!).toNat

/-- The code's estimate of the piece, on natural numbers. -/
def jf (ou : ℕ) : ℕ := ((0x157ced865 - ou * 0x150d) * ou + 0x128000000000) / 2 ^ 45

theorem tw_ends : tw 0 = 0x1FF0000 ∧ tw 19 = 0x20104BA := by decide +kernel

theorem tab0 : Lgamma.mainTable[(0 : UInt64).toNat]! = 0x1FF0000 := by decide +kernel

theorem border_ok : ∀ k < 19, k ≤ jf (tw k - 0x1FF0000) ∧ jf (tw (k + 1) - 1 - 0x1FF0000) ≤ k + 1 ∧
    tw k < tw (k + 1) ∧ tw (k + 1) ≤ 0x20104BA := by
  decide +kernel

/-- `jf` increases below `132282`, the width of the range of `au`. -/
theorem jf_mono {a b : ℕ} (hab : a ≤ b) (hb : b < 132282) : jf a ≤ jf b := by
  unfold jf
  apply Nat.div_le_div_right
  apply Nat.add_le_add_right
  have hs : (0 : ℤ) ≤ 0x157ced865 - 0x150d * ((a : ℤ) + b) := by omega
  have h2 : b * 0x150d ≤ 0x157ced865 :=
    le_trans (Nat.mul_le_mul_right _ hb.le) (by norm_num)
  have h1 : a * 0x150d ≤ 0x157ced865 := le_trans (Nat.mul_le_mul_right _ hab) h2
  zify [h1, h2]
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') hs]

/-- The `UInt64` estimate of the code equals `jf`. -/
theorem est_toNat (au : UInt64) (h0 : 0x1FF0000 ≤ au.toNat) (h1 : au.toNat < 0x20104BA) :
    ((((0x157ced865 : UInt64) - (au - 0x1FF0000) * 0x150d) * (au - 0x1FF0000) + 0x128000000000) >>>
      (45 : UInt64)).toNat = jf (au.toNat - 0x1FF0000) := by
  have hou : (au - 0x1FF0000).toNat = au.toNat - 0x1FF0000 :=
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact h0)
  have hxb : au.toNat - 0x1FF0000 < 132282 := by omega
  have hm : ((au - 0x1FF0000) * 0x150d).toNat = (au.toNat - 0x1FF0000) * 0x150d := by
    rw [UInt64.toNat_mul, hou, show (0x150d : UInt64).toNat = 0x150d from rfl]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_right _ hxb.le) (by norm_num))
  have hle : (au.toNat - 0x1FF0000) * 0x150d ≤ 0x157ced865 :=
    le_trans (Nat.mul_le_mul_right _ hxb.le) (by norm_num)
  have hs : ((0x157ced865 : UInt64) - (au - 0x1FF0000) * 0x150d).toNat =
      0x157ced865 - (au.toNat - 0x1FF0000) * 0x150d := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; exact hle), hm]
    rfl
  have hp : (0x157ced865 - (au.toNat - 0x1FF0000) * 0x150d) * (au.toNat - 0x1FF0000) ≤
      0x157ced865 * 132282 :=
    Nat.mul_le_mul (Nat.sub_le _ _) hxb.le
  have hmul : (((0x157ced865 : UInt64) - (au - 0x1FF0000) * 0x150d) * (au - 0x1FF0000)).toNat =
      (0x157ced865 - (au.toNat - 0x1FF0000) * 0x150d) * (au.toNat - 0x1FF0000) := by
    rw [UInt64.toNat_mul, hs, hou]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hp (by norm_num))
  have hadd : (((0x157ced865 : UInt64) - (au - 0x1FF0000) * 0x150d) * (au - 0x1FF0000) +
      0x128000000000).toNat =
      (0x157ced865 - (au.toNat - 0x1FF0000) * 0x150d) * (au.toNat - 0x1FF0000) + 0x128000000000 := by
    rw [UInt64.toNat_add, hmul, show (0x128000000000 : UInt64).toNat = 0x128000000000 from rfl]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.add_le_add_right hp _) (by norm_num))
  rw [UInt64.toNat_shiftRight, hadd, show (45 : UInt64).toNat % 64 = 45 from rfl,
    Nat.shiftRight_eq_div_pow]
  rfl

/-- Every value of the range lies in one piece. -/
theorem exists_piece (n : ℕ) (h0 : tw 0 ≤ n) (h1 : n < tw 19) :
    ∃ k < 19, tw k ≤ n ∧ n < tw (k + 1) := by
  by_contra hne
  push Not at hne
  have : ∀ k ≤ 19, tw k ≤ n := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact hne k (by omega) (ih (by omega))
  exact absurd (this 19 le_rfl) (not_le.mpr h1)

/-- **The piece of `au`**: `Lgamma.piece` returns the `k < 19` with `tab[k] ≤ au < tab[k + 1]`. -/
theorem piece_spec (au : UInt64) (h0 : 0x1FF0000 ≤ au.toNat) (h1 : au.toNat < 0x20104BA) :
    ∃ k < 19, (Lgamma.piece Lgamma.mainTable au).toNat = k ∧ tw k ≤ au.toNat ∧
      au.toNat < tw (k + 1) := by
  obtain ⟨k, hk, hk0, hk1⟩ := exists_piece au.toNat (by rw [tw_ends.1]; exact h0)
    (by rw [tw_ends.2]; exact h1)
  have hb := border_ok k hk
  have hlo : k ≤ jf (au.toNat - 0x1FF0000) := hb.1.trans (jf_mono (by omega) (by omega))
  have hhi : jf (au.toNat - 0x1FF0000) ≤ k + 1 := (jf_mono (by omega) (by omega)).trans hb.2.1
  have hE := est_toNat au h0 h1
  refine ⟨k, hk, ?_, hk0, hk1⟩
  simp only [Lgamma.piece, tab0]
  generalize ((((0x157ced865 : UInt64) - (au - 0x1FF0000) * 0x150d) * (au - 0x1FF0000) +
    0x128000000000) >>> (45 : UInt64)) = e at hE ⊢
  rcases (show jf (au.toNat - 0x1FF0000) = k ∨ jf (au.toNat - 0x1FF0000) = k + 1 by omega)
    with h | h
  · have hne : ¬ au < Lgamma.mainTable[e.toNat]! := by
      rw [UInt64.lt_iff_toNat_lt, hE, h]
      unfold tw at hk0
      omega
    simp only [hne, ↓reduceIte]
    rw [hE, h]
  · have hlt : au < Lgamma.mainTable[e.toNat]! := by
      rw [UInt64.lt_iff_toNat_lt, hE, h]
      unfold tw at hk1
      exact hk1
    have h1e : (1 : UInt64) ≤ e := by
      rw [UInt64.le_iff_toNat_le, hE, h]
      exact Nat.le_add_left 1 k
    simp only [hlt, ↓reduceIte]
    rw [UInt64.toNat_sub_of_le _ _ h1e, hE, h]
    rfl

#print axioms piece_spec

end Verified.Examples.LgammaPieceIdx
