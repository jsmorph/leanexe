import Mathlib.Tactic

/-!
The alignment of the two addends of `Fma.fmaBits`.  Both are normalized to `[2 ^ 125, 2 ^ 126)`
with bits 0 to 19 clear, `X · 2 ^ d ≥ Y`, and `Y` is shifted right by `d` with the lost bits ORed
into bit 0 (`stickyShift`, as `Fma.sticky128` computes it).  When no set bit is lost, the sum
`Z = X ± Y'` times `2 ^ d` is the exact sum `T = X · 2 ^ d ± Y`.  When a set bit is lost, `d` is at
least 21, `Z` is odd and at least `2 ^ 124`, and `Z · 2 ^ d` lies within `2 ^ d` of `T`.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaAlign

/-- `Y` shifted right by `d`, with bit 0 set when a set bit is lost. -/
def stickyShift (Y d : ℕ) : ℕ := if Y % 2 ^ d ≠ 0 then Y / 2 ^ d / 2 * 2 + 1 else Y / 2 ^ d

/-- The shifted addend: at most `X` and below `2 ^ 126`, exact when no set bit is lost, and
otherwise odd, at most `2 ^ 105`, and within one unit of `Y / 2 ^ d`. -/
theorem sticky_facts (X Y d : ℕ) (hY2 : Y < 2 ^ 126) (hY20 : Y % 2 ^ 20 = 0)
    (hord : Y ≤ X * 2 ^ d) :
    stickyShift Y d ≤ X ∧ stickyShift Y d < 2 ^ 126 ∧
      (Y % 2 ^ d = 0 → stickyShift Y d * 2 ^ d = Y) ∧
      (Y % 2 ^ d ≠ 0 → stickyShift Y d % 2 = 1 ∧ stickyShift Y d ≤ 2 ^ 105 ∧
        stickyShift Y d * 2 ^ d < Y + 2 ^ d ∧ Y < stickyShift Y d * 2 ^ d + 2 ^ d) := by
  set D := 2 ^ d with hD
  have hDp : 0 < D := by positivity
  set q := Y / D with hq
  set r := Y % D with hr
  have hYqr : Y = q * D + r := by rw [hq, hr, Nat.mul_comm]; exact (Nat.div_add_mod Y D).symm
  have hrD : r < D := Nat.mod_lt _ hDp
  have hqY : q ≤ Y := by rw [hq]; exact Nat.div_le_self _ _
  have h105 : (2 : ℕ) ^ 105 < 2 ^ 126 := by norm_num
  unfold stickyShift
  rw [← hD, ← hq, ← hr]
  by_cases hr0 : r = 0
  · rw [ite_eq_right (by simpa using hr0)]
    have hqX : q ≤ X := by
      apply Nat.le_of_mul_le_mul_right _ hDp
      omega
    exact ⟨hqX, by omega, fun _ => by omega, fun h => absurd hr0 h⟩
  · rw [ite_eq_left hr0]
    -- `d` is at least 21, since bits 0 to 19 of `Y` are clear
    have hd : 21 ≤ d := by
      by_contra hc
      have h1 : D ∣ 2 ^ 20 := by rw [hD]; exact Nat.pow_dvd_pow 2 (by omega)
      have h2 : 2 ^ 20 ∣ Y := Nat.dvd_of_mod_eq_zero hY20
      exact hr0 (Nat.mod_eq_zero_of_dvd (h1.trans h2))
    have hqX : q < X := by
      by_contra hc
      push Not at hc
      have := Nat.mul_le_mul_right D hc
      omega
    have hq105 : q < 2 ^ 105 := by
      have h1 : 2 ^ 21 ≤ D := by rw [hD]; exact Nat.pow_le_pow_right (by norm_num) hd
      have h2 : q * 2 ^ 21 ≤ Y := by
        calc q * 2 ^ 21 ≤ q * D := Nat.mul_le_mul_left _ h1
          _ ≤ Y := by omega
      by_contra hc
      push Not at hc
      have h3 : 2 ^ 105 * 2 ^ 21 ≤ q * 2 ^ 21 := Nat.mul_le_mul_right _ hc
      have h4 : (2 : ℕ) ^ 105 * 2 ^ 21 = 2 ^ 126 := by norm_num
      omega
    have hsplit : q / 2 * 2 + 1 = q ∨ q / 2 * 2 + 1 = q + 1 := by omega
    refine ⟨by omega, by omega, fun h => absurd h hr0, fun _ => ⟨by omega, by omega, ?_, ?_⟩⟩
    · rcases hsplit with h | h <;> rw [h]
      · omega
      · rw [Nat.add_mul, one_mul]; omega
    · rcases hsplit with h | h <;> rw [h]
      · omega
      · rw [Nat.add_mul, one_mul]; omega

/-- The sum of addends of equal signs. -/
theorem sum_same (X Y d : ℕ) (hX2 : X < 2 ^ 126) (hX1 : 2 ^ 125 ≤ X) (hY2 : Y < 2 ^ 126)
    (hX20 : X % 2 ^ 20 = 0) (hY20 : Y % 2 ^ 20 = 0) (hord : Y ≤ X * 2 ^ d) :
    X + stickyShift Y d < 2 ^ 127 ∧
      (Y % 2 ^ d = 0 → (X + stickyShift Y d) * 2 ^ d = X * 2 ^ d + Y) ∧
      (Y % 2 ^ d ≠ 0 → (X + stickyShift Y d) % 2 = 1 ∧ 2 ^ 124 ≤ X + stickyShift Y d ∧
        (X + stickyShift Y d) * 2 ^ d < X * 2 ^ d + Y + 2 ^ d ∧
        X * 2 ^ d + Y < (X + stickyShift Y d) * 2 ^ d + 2 ^ d) := by
  obtain ⟨f1, f2, f3, f4⟩ := sticky_facts X Y d hY2 hY20 hord
  have hXe : X % 2 = 0 := by
    have h := hX20
    simp only [Nat.reducePow] at h
    omega
  have h127 : (2 : ℕ) ^ 127 = 2 ^ 126 + 2 ^ 126 := by norm_num
  have h124 : (2 : ℕ) ^ 124 ≤ 2 ^ 125 := by norm_num
  rw [Nat.add_mul]
  refine ⟨by omega, fun h => by rw [f3 h], fun h => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := f4 h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The difference of addends of opposite signs. -/
theorem sum_diff (X Y d : ℕ) (hX2 : X < 2 ^ 126) (hX1 : 2 ^ 125 ≤ X) (hY2 : Y < 2 ^ 126)
    (hX20 : X % 2 ^ 20 = 0) (hY20 : Y % 2 ^ 20 = 0) (hord : Y ≤ X * 2 ^ d) :
    stickyShift Y d ≤ X ∧ X - stickyShift Y d < 2 ^ 127 ∧
      (Y % 2 ^ d = 0 → (X - stickyShift Y d) * 2 ^ d = X * 2 ^ d - Y) ∧
      (Y % 2 ^ d ≠ 0 → (X - stickyShift Y d) % 2 = 1 ∧ 2 ^ 124 ≤ X - stickyShift Y d ∧
        (X - stickyShift Y d) * 2 ^ d < X * 2 ^ d - Y + 2 ^ d ∧
        X * 2 ^ d - Y < (X - stickyShift Y d) * 2 ^ d + 2 ^ d) := by
  obtain ⟨f1, f2, f3, f4⟩ := sticky_facts X Y d hY2 hY20 hord
  have hXe : X % 2 = 0 := by
    have h := hX20
    simp only [Nat.reducePow] at h
    omega
  have h127 : (2 : ℕ) ^ 126 < 2 ^ 127 := by norm_num
  have h124 : (2 : ℕ) ^ 125 = 2 ^ 124 + 2 ^ 124 := by norm_num
  have h105 : (2 : ℕ) ^ 105 ≤ 2 ^ 124 := by norm_num
  have hle : stickyShift Y d * 2 ^ d ≤ X * 2 ^ d := Nat.mul_le_mul_right _ f1
  rw [Nat.sub_mul]
  refine ⟨f1, by omega, fun h => by rw [f3 h], fun h => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := f4 h
  exact ⟨by omega, by omega, by omega, by omega⟩

#print axioms sticky_facts
#print axioms sum_same
#print axioms sum_diff

end Library.Numerics.Arithmetic.Fma.FmaAlign
