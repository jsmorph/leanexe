import Mathlib.Tactic

namespace Verified.Examples.FFTIndex

def lower (h i : Nat) : Nat := 2 * h * (i / h) + i % h

def upper (h i : Nat) : Nat := lower h i + h

theorem lower_group (h i : Nat) (hh : 0 < h) : lower h i / (2 * h) = i / h := by
  have hr : i % h < 2 * h := by have := Nat.mod_lt i hh; omega
  unfold lower
  rw [Nat.mul_add_div (by omega : 0 < 2 * h), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem upper_group (h i : Nat) (hh : 0 < h) : upper h i / (2 * h) = i / h := by
  have hr : i % h + h < 2 * h := by have := Nat.mod_lt i hh; omega
  unfold upper lower
  rw [Nat.add_assoc, Nat.mul_add_div (by omega : 0 < 2 * h), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem lower_injective (h : Nat) (hh : 0 < h) (i j : Nat) (heq : lower h i = lower h j) :
    i = j := by
  have hgroup : i / h = j / h := by
    simpa only [lower_group h i hh, lower_group h j hh] using
      congrArg (fun k => k / (2 * h)) heq
  have hrem : i % h = j % h := by
    unfold lower at heq
    rw [hgroup] at heq
    omega
  have hi := Nat.mod_add_div i h
  have hj := Nat.mod_add_div j h
  rw [hgroup, hrem] at hi
  omega

theorem upper_injective (h : Nat) (hh : 0 < h) (i j : Nat) (heq : upper h i = upper h j) :
    i = j := by
  apply lower_injective h hh i j
  unfold upper at heq
  omega

theorem lower_ne_upper (h i j : Nat) (hh : 0 < h) : lower h i ≠ upper h j := by
  intro heq
  have hgroup : i / h = j / h := by
    simpa only [lower_group h i hh, upper_group h j hh] using
      congrArg (fun k => k / (2 * h)) heq
  unfold upper lower at heq
  rw [hgroup] at heq
  have := Nat.mod_lt i hh
  omega

theorem lower_lt_upper (h i : Nat) (hh : 0 < h) : lower h i < upper h i := by
  unfold upper
  omega

theorem lower_flattened (h b j : Nat) (hh : 0 < h) (hj : j < h) :
    lower h (b * h + j) = b * (2 * h) + j := by
  unfold lower
  rw [Nat.mul_comm b h, Nat.mul_add_div hh, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [Nat.mul_comm (2 * h) b]

theorem upper_flattened (h b j : Nat) (hh : 0 < h) (hj : j < h) :
    upper h (b * h + j) = b * (2 * h) + j + h := by
  unfold upper
  rw [lower_flattened h b j hh hj]

theorem upper_lt (h blocks i : Nat) (hh : 0 < h) (hi : i < h * blocks) :
    upper h i < 2 * h * blocks := by
  have hgroup : i / h < blocks :=
    (Nat.div_lt_iff_lt_mul hh).mpr (by simpa only [Nat.mul_comm] using hi)
  have hmul := Nat.mul_le_mul_left (2 * h) (show i / h + 1 ≤ blocks by omega)
  have hrem := Nat.mod_lt i hh
  unfold upper lower
  nlinarith only [hmul, hrem]

theorem lower_lt (h blocks i : Nat) (hh : 0 < h) (hi : i < h * blocks) :
    lower h i < 2 * h * blocks :=
  (lower_lt_upper h i hh).trans (upper_lt h blocks i hh hi)

theorem disjoint (h i j : Nat) (hh : 0 < h) (hij : i ≠ j) :
    lower h i ≠ lower h j ∧ lower h i ≠ upper h j ∧
      upper h i ≠ lower h j ∧ upper h i ≠ upper h j := by
  refine ⟨fun heq => hij (lower_injective h hh i j heq), lower_ne_upper h i j hh,
    (lower_ne_upper h j i hh).symm, fun heq => hij (upper_injective h hh i j heq)⟩

theorem exists_index (h blocks k : Nat) (hh : 0 < h) (hk : k < 2 * h * blocks) :
    ∃ i < h * blocks, lower h i = k ∨ upper h i = k := by
  let b := k / (2 * h)
  let r := k % (2 * h)
  have hb : b < blocks :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * h)).mpr
      (by simpa only [Nat.mul_comm] using hk)
  have hr : r < 2 * h := Nat.mod_lt _ (by omega)
  have hdecomp : r + 2 * h * b = k := Nat.mod_add_div k (2 * h)
  have hmul := Nat.mul_le_mul_left h (show b + 1 ≤ blocks by omega)
  by_cases hrh : r < h
  · refine ⟨h * b + r, by nlinarith only [hmul, hrh], Or.inl ?_⟩
    unfold lower
    rw [Nat.mul_add_div hh, Nat.div_eq_of_lt hrh, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hrh]
    omega
  · have hrh' : r - h < h := by omega
    refine ⟨h * b + (r - h), by nlinarith only [hmul, hrh'], Or.inr ?_⟩
    unfold upper lower
    rw [Nat.mul_add_div hh, Nat.div_eq_of_lt hrh', Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hrh']
    omega

theorem twiddleIndex_lt (h blocks i : Nat) (hh : 0 < h) (hi : i < h * blocks) :
    (i % h) * blocks < h * blocks := by
  have hb : 0 < blocks := by
    by_contra hb
    have hzero : blocks = 0 := by omega
    rw [hzero, Nat.mul_zero] at hi
    exact Nat.not_lt_zero _ hi
  exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt i hh) hb

def lowerWord (width i : UInt64) : UInt64 := (i / (width / 2)) * width + i % (width / 2)

def upperWord (width i : UInt64) : UInt64 := lowerWord width i + width / 2

def twiddleWord (n width i : UInt64) : UInt64 := (i % (width / 2)) * (n / width)

theorem word_indices (n width i : UInt64) (h blocks : Nat) (hh : 0 < h)
    (hn : n.toNat = 2 * h * blocks) (hwidth : width.toNat = 2 * h)
    (hnmax : n.toNat ≤ 2 ^ 32) (hi : i.toNat < h * blocks) :
    (lowerWord width i).toNat = lower h i.toNat ∧
      (upperWord width i).toNat = upper h i.toNat ∧
      (twiddleWord n width i).toNat = (i.toNat % h) * blocks := by
  have hhalf : (width / 2).toNat = h := by
    rw [UInt64.toNat_div, hwidth]
    simp only [UInt64.reduceToNat]
    exact Nat.mul_div_cancel_left h (by omega)
  have hblocks : (n / width).toNat = blocks := by
    rw [UInt64.toNat_div, hn, hwidth]
    exact Nat.mul_div_cancel_left blocks (by omega)
  have hcap : (2 : Nat) ^ 32 < UInt64.size := by norm_num [UInt64.size]
  have hlo : lower h i.toNat < UInt64.size :=
    (lower_lt h blocks i.toNat hh hi).trans_le (by rw [← hn]; exact hnmax) |>.trans hcap
  have hhi : upper h i.toNat < UInt64.size :=
    (upper_lt h blocks i.toNat hh hi).trans_le (by rw [← hn]; exact hnmax) |>.trans hcap
  have hmul : (i.toNat / h) * (2 * h) < UInt64.size := by
    unfold lower at hlo
    rw [Nat.mul_comm (i.toNat / h) (2 * h)]
    omega
  have hloEq : (lowerWord width i).toNat = lower h i.toNat := by
    unfold lowerWord lower
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
      hhalf, hwidth, Nat.mod_eq_of_lt hmul]
    rw [Nat.mul_comm (i.toNat / h) (2 * h)]
    exact Nat.mod_eq_of_lt hlo
  have hhiEq : (upperWord width i).toNat = upper h i.toNat := by
    unfold upperWord upper
    rw [UInt64.toNat_add, hloEq, hhalf]
    exact Nat.mod_eq_of_lt hhi
  have hfactor : (i.toNat % h) * blocks < UInt64.size := by
    have hlt := twiddleIndex_lt h blocks i.toNat hh hi
    have hle : h * blocks ≤ n.toNat := by rw [hn, Nat.mul_assoc]; omega
    exact (hlt.trans_le hle).trans_le hnmax |>.trans hcap
  refine ⟨hloEq, hhiEq, ?_⟩
  unfold twiddleWord
  rw [UInt64.toNat_mul, UInt64.toNat_mod, hhalf, hblocks]
  exact Nat.mod_eq_of_lt hfactor

#print axioms disjoint
#print axioms exists_index
#print axioms upper_lt
#print axioms word_indices

end Verified.Examples.FFTIndex
