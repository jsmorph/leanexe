import Library.Random.Sampling.Program
import Mathlib.Data.FinEnum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The index of step P3: `scale u m` is `⌊u·m / 2^64⌋` when `m < 2^32` (`scale_toNat`), it lies
below `m` (`scale_lt`), and each value `i < m` comes from `⌊2^64 / m⌋` or `⌈2^64 / m⌉` words
(`scale_card`).  The count of the words that give `i` is the length of the interval of words `u`
with `i·2^64 ≤ u·m < (i + 1)·2^64`, from `⌈i·2^64 / m⌉` to `⌈(i + 1)·2^64 / m⌉`. -/

namespace Library.Random.Sampling

theorem word_toNat {x : Nat} (h : x < 2 ^ 64) : (UInt64.ofNat x).toNat = x :=
  UInt64.toNat_ofNat_of_lt' h

theorem land_32 (x : Nat) : x &&& 4294967295 = x % 4294967296 :=
  Nat.and_two_pow_sub_one_eq_mod x 32

theorem scale_toNat (u m : UInt64) (hm : m.toNat < 2 ^ 32) :
    (scale u m).toNat = u.toNat * m.toNat / 2 ^ 64 := by
  have hu := u.toNat_lt
  simp only [scale, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_and, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, land_32]
  generalize u.toNat = U at *
  generalize m.toNat = M at *
  have h1 : U / 4294967296 * M ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h0 : U % 4294967296 * M ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : U * M = U / 4294967296 * M * 4294967296 + U % 4294967296 * M := by
    conv_lhs => rw [← Nat.div_add_mod U 4294967296]
    ring
  omega

/-- `scale u m < m` for every `m ≥ 1`: exactly when `m < 2^32`, and because the result is below
`2^32` otherwise. -/
theorem scale_lt (u m : UInt64) (h0 : 0 < m.toNat) : (scale u m).toNat < m.toNat := by
  by_cases hm : m.toNat < 2 ^ 32
  · rw [scale_toNat u m hm, Nat.div_lt_iff_lt_mul (by norm_num), Nat.mul_comm m.toNat]
    exact Nat.mul_lt_mul_of_pos_right u.toNat_lt h0
  · have h32 : (scale u m).toNat < 2 ^ 32 := by
      unfold scale
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      generalize ((u >>> 32) * m + (((u &&& 0xFFFFFFFF) * m) >>> 32)) = x
      have := x.toNat_lt
      simp only [UInt64.reduceToNat, Nat.reduceMod]
      omega
    omega

/-- `⌈y / m⌉ ≤ x` exactly when `y ≤ x·m`. -/
theorem ceil_le_iff {y m x : Nat} (hm : 0 < m) : (y + m - 1) / m ≤ x ↔ y ≤ x * m := by
  rw [Nat.div_le_iff_le_mul_add_pred hm, Nat.mul_comm m x]
  omega

theorem le_ceil_mul (y : Nat) {m : Nat} (hm : 0 < m) : y ≤ (y + m - 1) / m * m :=
  (ceil_le_iff hm).mp le_rfl

/-- The words `u < 2^64` with `⌊u·m / 2^64⌋ = i` are those from `⌈i·2^64 / m⌉` to
`⌈(i + 1)·2^64 / m⌉`. -/
theorem div_eq_iff_mem {x m i : Nat} (hm : 0 < m) :
    x * m / 2 ^ 64 = i ↔
      (i * 2 ^ 64 + m - 1) / m ≤ x ∧ x < ((i + 1) * 2 ^ 64 + m - 1) / m := by
  have h1 := Nat.le_div_iff_mul_le (k := 2 ^ 64) (x := i) (y := x * m) (by norm_num)
  have h2 := Nat.div_lt_iff_lt_mul (k := 2 ^ 64) (x := x * m) (y := i + 1) (by norm_num)
  have h3 := ceil_le_iff (y := i * 2 ^ 64) (x := x) hm
  have h4 := ceil_le_iff (y := (i + 1) * 2 ^ 64) (x := x) hm
  constructor
  · intro h
    exact ⟨h3.mpr (h1.mp (by omega)), lt_of_not_ge fun h' => by
      have := h4.mp h'; have := h2.mp (by omega); omega⟩
  · rintro ⟨ha, hb⟩
    have := h1.mpr (h3.mp ha)
    have := h2.mpr (lt_of_not_ge fun h' => absurd (h4.mpr h') (by omega))
    omega

/-- `⌈(y + d) / m⌉ - ⌈y / m⌉` lies between `⌊d / m⌋` and `⌈d / m⌉`. -/
theorem ceil_add_bounds (y d : Nat) {m : Nat} (hm : 0 < m) :
    (y + m - 1) / m + d / m ≤ (y + d + m - 1) / m ∧
      (y + d + m - 1) / m ≤ (y + m - 1) / m + (d + m - 1) / m := by
  have hzm := le_ceil_mul (y + d) hm
  have hy := le_ceil_mul y hm
  have hd := le_ceil_mul d hm
  have hq := Nat.div_mul_le_self d m
  constructor
  · generalize (y + d + m - 1) / m = z at hzm ⊢
    generalize d / m = q at hq ⊢
    have hqz : q ≤ z := Nat.le_of_mul_le_mul_right (by omega : q * m ≤ z * m) hm
    have : (y + m - 1) / m ≤ z - q := by
      rw [ceil_le_iff hm, Nat.sub_mul]; omega
    omega
  · rw [ceil_le_iff hm, Nat.add_mul]
    omega

/-- The words that `scale` maps to `i` correspond to the natural numbers below `2^64` in the
interval of `div_eq_iff_mem`. -/
theorem scale_card_eq (m i : Nat) (hm0 : 0 < m) (hm : m < 2 ^ 32) (hi : i < m) :
    (Finset.univ.filter fun u : UInt64 => (scale u (UInt64.ofNat m)).toNat = i).card =
      ((i + 1) * 2 ^ 64 + m - 1) / m - (i * 2 ^ 64 + m - 1) / m := by
  have hmm : (UInt64.ofNat m).toNat = m := UInt64.toNat_ofNat_of_lt' (show m < 2 ^ 64 by omega)
  have hb : ((i + 1) * 2 ^ 64 + m - 1) / m ≤ 2 ^ 64 := by
    rw [ceil_le_iff hm0, Nat.mul_comm (2 ^ 64) m]; exact Nat.mul_le_mul_right _ hi
  rw [← Nat.card_Ico]
  apply Finset.card_bij (fun u _ => u.toNat)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [scale_toNat _ _ (by omega), hmm] at hu
    exact Finset.mem_Ico.mpr ((div_eq_iff_mem hm0).mp hu)
  · intro a _ b _ h
    exact UInt64.toNat_inj.mp h
  · intro x hx
    have hx' := Finset.mem_Ico.mp hx
    have hx64 : x < 2 ^ 64 := by omega
    refine ⟨UInt64.ofNat x, ?_, UInt64.toNat_ofNat_of_lt' hx64⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [scale_toNat _ _ (by omega), hmm, UInt64.toNat_ofNat_of_lt' hx64]
    exact (div_eq_iff_mem hm0).mpr hx'

/-- With `a = ⌈i·A / m⌉` and `b = ⌈(i + 1)·A / m⌉`, the difference `b - a` lies between `⌊A / m⌋`
and `⌈A / m⌉`. -/
theorem ceil_diff_bounds (A i : Nat) {m : Nat} (hm : 0 < m) :
    A / m ≤ ((i + 1) * A + m - 1) / m - (i * A + m - 1) / m ∧
      ((i + 1) * A + m - 1) / m - (i * A + m - 1) / m ≤ (A + m - 1) / m := by
  have h := ceil_add_bounds (i * A) A hm
  rw [show i * A + A = (i + 1) * A by ring] at h
  generalize (i * A + m - 1) / m = a at h ⊢
  generalize ((i + 1) * A + m - 1) / m = b at h ⊢
  generalize A / m = q at h ⊢
  generalize (A + m - 1) / m = c at h ⊢
  omega

/-- Each value `i < m` of `scale u m` comes from `⌊2^64 / m⌋` or `⌈2^64 / m⌉` words. -/
theorem scale_card (m i : Nat) (hm0 : 0 < m) (hm : m < 2 ^ 32) (hi : i < m) :
    2 ^ 64 / m ≤ (Finset.univ.filter fun u : UInt64 => (scale u (UInt64.ofNat m)).toNat = i).card ∧
      (Finset.univ.filter fun u : UInt64 => (scale u (UInt64.ofNat m)).toNat = i).card ≤
        (2 ^ 64 + m - 1) / m := by
  rw [scale_card_eq m i hm0 hm hi]
  exact ceil_diff_bounds (2 ^ 64) i hm0

end Library.Random.Sampling
