import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.F64PositiveOrder

/-!
The grid of binary64 values in units of `2 ^ -2400`, for the rounding of `Fma.roundPack`.  The
doubles of biased exponent `E ≥ 1` are spaced `2 ^ (E + 1325)` units apart (`spacing E`), the
subnormal ones with `E = 1`.  `RoundsTo Y E Q` states that `Y` lies in binade `E` and that `Q` is the
integer nearest to `Y / spacing E`, the even one at a tie, and `packWord` assembles the word
`(E - 1) · 2 ^ 52 + Q` as `roundPack` does.  A double at or above the start of binade `E` is a
multiple of the spacing, and one below it lies at least half a spacing below the start
(`grid_or_below`).  `roundsTo_transfer` moves `RoundsTo` from `Y1` to any `Y2` closer than `2 ^ w`
when `Y1` is an odd multiple of `2 ^ w` and the spacing is a multiple of `2 ^ (w + 2)`: every bound
in `RoundsTo` is then a multiple of `2 ^ (w + 1)`, and none lies between `Y1` and `Y2`.  This is the
sticky-bit argument of `Fma`.
-/

namespace Verified.Examples.FmaGrid
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative

set_option exponentiation.threshold 4096

/-- The spacing of the doubles of biased exponent `E`, subnormal for `E = 1`, in units of
`2 ^ -2400`. -/
def spacing (E : ℕ) : ℕ := 2 ^ (E + 1325)

attribute [irreducible] spacing

/-- `Y` lies in binade `E`, and `Q` is the integer nearest to `Y / spacing E`, even at a tie. -/
def RoundsTo (Y E Q : ℕ) : Prop :=
  1 ≤ E ∧ Y < 2 ^ 53 * spacing E ∧ (E = 1 ∨ 2 ^ 52 * spacing E ≤ Y) ∧
    2 * Y ≤ (2 * Q + 1) * spacing E ∧ 2 * Q * spacing E ≤ 2 * Y + spacing E ∧
    (2 * Y = (2 * Q + 1) * spacing E ∨ 2 * Y + spacing E = 2 * Q * spacing E → Q % 2 = 0)

/-- The word of sign `s` (0 or 1), biased exponent `E`, and significand `Q`, as `Fma.roundPack`
assembles it, with infinity from the exponent field 2047 on. -/
def packWord (s : UInt64) (E Q : ℕ) : UInt64 :=
  if 2047 ≤ E then (s <<< 63) ||| 0x7FF0000000000000
  else if 0x7FF0000000000000 ≤ (E - 1) * 2 ^ 52 + Q then (s <<< 63) ||| 0x7FF0000000000000
  else (s <<< 63) ||| UInt64.ofNat ((E - 1) * 2 ^ 52 + Q)

theorem spacing_pos (E : ℕ) : 0 < spacing E := by unfold spacing; positivity

theorem spacing_real (E : ℕ) : ((spacing E : ℕ) : ℝ) = (2 : ℝ) ^ (E + 1325) := by
  unfold spacing; rw [Nat.cast_pow, Nat.cast_ofNat]

/-- The significand of a rounding lies between `2 ^ 52` (for a normal binade) and `2 ^ 53`. -/
theorem significand_bounds (Y E Q : ℕ) (h : RoundsTo Y E Q) :
    Q ≤ 2 ^ 53 ∧ (E = 1 ∨ 2 ^ 52 ≤ Q) := by
  obtain ⟨_, hY53, hY52, hr1, hr2, _⟩ := h
  have hS := spacing_pos E
  simp only [Nat.reducePow] at *
  constructor
  · have h1 : 2 * Q * spacing E < 18014398509481985 * spacing E := by
      calc 2 * Q * spacing E ≤ 2 * Y + spacing E := hr2
        _ < 2 * (9007199254740992 * spacing E) + spacing E := by omega
        _ = 18014398509481985 * spacing E := by ring
    have := Nat.lt_of_mul_lt_mul_right h1
    omega
  · rcases hY52 with h1 | h1
    · exact Or.inl h1
    · right
      have h2 : 9007199254740992 * spacing E ≤ (2 * Q + 1) * spacing E := by
        calc 9007199254740992 * spacing E = 2 * (4503599627370496 * spacing E) := by ring
          _ ≤ 2 * Y := by omega
          _ ≤ _ := hr1
      have := Nat.le_of_mul_le_mul_right h2 hS
      omega

/-- The word `(E - 1) · 2 ^ 52 + Q` of a significand in range, and its value. -/
theorem word_value (E Q : ℕ) (hE : 1 ≤ E) (hQ : Q ≤ 2 ^ 53) (hQ52 : E = 1 ∨ 2 ^ 52 ≤ Q)
    (hW : (E - 1) * 2 ^ 52 + Q < 0x7FF0000000000000) :
    (UInt64.ofNat ((E - 1) * 2 ^ 52 + Q)).toNat = (E - 1) * 2 ^ 52 + Q ∧
      Wasm.IEEE64.sign (UInt64.ofNat ((E - 1) * 2 ^ 52 + Q)) = false ∧
      value (UInt64.ofNat ((E - 1) * 2 ^ 52 + Q)) = (Q : ℝ) * ((spacing E : ℕ) : ℝ) / 2 ^ 2400 := by
  set W := (E - 1) * 2 ^ 52 + Q with hWdef
  have hWn : (UInt64.ofNat W).toNat = W :=
    UInt64.toNat_ofNat_of_lt' (hW.trans (by decide))
  have hs : Wasm.IEEE64.sign (UInt64.ofNat W) = false := by
    simp only [Wasm.IEEE64.sign, hWn, decide_eq_false_iff_not, not_le]
    simp only [Nat.reducePow] at *
    omega
  have hmag : Wasm.IEEE64.scaledMagnitude (UInt64.ofNat W) = Q * 2 ^ (E - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, hWn]
    simp only [Nat.reducePow] at *
    rcases lt_or_ge Q 4503599627370496 with h1 | h1
    · have hE1 : E = 1 := by omega
      subst hE1
      have he : W / 4503599627370496 % 2048 = 0 := by omega
      have hf : W % 4503599627370496 = Q := by omega
      simp [he, hf]
    rcases lt_or_ge Q 9007199254740992 with h2 | h2
    · have he : W / 4503599627370496 % 2048 = E := by omega
      have hf : W % 4503599627370496 = Q - 4503599627370496 := by omega
      have hE0 : (E == 0) = false := by simp; omega
      simp only [he, hf, hE0, Bool.false_eq_true, ite_false]
      rw [show 4503599627370496 + (Q - 4503599627370496) = Q by omega]
    · have hQe : Q = 9007199254740992 := by omega
      have he : W / 4503599627370496 % 2048 = E + 1 := by omega
      have hf : W % 4503599627370496 = 0 := by omega
      have hE0 : (E + 1 == 0) = false := by simp
      simp only [he, hf, hE0, Bool.false_eq_true, ite_false, add_zero, Nat.add_sub_cancel, hQe]
      rw [show E = (E - 1) + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
  refine ⟨hWn, hs, ?_⟩
  rw [F64Exact.value_of_sign _ hs, hmag, spacing_real, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    show E + 1325 = (E - 1) + 1326 by omega, pow_add,
    show (2400 : ℕ) = 1074 + 1326 by norm_num, pow_add, ← mul_assoc,
    mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ 1326 ≠ 0)]

/-- A nonnegative finite word lies on the grid of binade `E`, or below its start by at least half a
spacing. -/
theorem grid_or_below (v : UInt64) (E : ℕ) (hE : 1 ≤ E) :
    (∃ j : ℕ, Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326 = j * spacing E) ∨
      (2 ≤ E ∧ 2 * (Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326) + spacing E ≤
        2 ^ 53 * spacing E) := by
  have hsp : spacing E = 2 ^ (E - 1) * 2 ^ 1326 := by
    unfold spacing; rw [← pow_add]; congr 1; omega
  by_cases hE1 : E = 1
  · left
    refine ⟨Wasm.IEEE64.scaledMagnitude v, ?_⟩
    rw [hsp, hE1]
    simp
  by_cases hm : 2 ^ (52 + (E - 1)) ≤ Wasm.IEEE64.scaledMagnitude v
  · left
    obtain ⟨j, hj⟩ := F64NearestSum.magnitude_dvd v (E - 1) hm
    refine ⟨j, ?_⟩
    rw [hj, hsp]
    ring
  · right
    push Not at hm
    have hb := F64RoundNearest.magnitude_below v (E - 1) (by omega) hm
    refine ⟨by omega, ?_⟩
    have h1 : 2 ^ (E - 1 - 1) * 2 = 2 ^ (E - 1) := by
      rw [← pow_succ, show E - 1 - 1 + 1 = E - 1 by omega]
    have h2 : (2 : ℕ) ^ (52 + (E - 1)) * 2 = 2 ^ 53 * 2 ^ (E - 1) := by
      rw [← pow_succ, ← pow_add, show 52 + (E - 1) + 1 = 53 + (E - 1) by omega]
    rw [hsp]
    have h3 : (Wasm.IEEE64.scaledMagnitude v + 2 ^ (E - 1 - 1)) * 2 * 2 ^ 1326 ≤
        2 ^ (52 + (E - 1)) * 2 * 2 ^ 1326 := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact hb
    rw [h2] at h3
    calc 2 * (Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326) + 2 ^ (E - 1) * 2 ^ 1326
        = (Wasm.IEEE64.scaledMagnitude v + 2 ^ (E - 1 - 1)) * 2 * 2 ^ 1326 := by
          rw [← h1]; ring
      _ ≤ 2 ^ 53 * 2 ^ (E - 1) * 2 ^ 1326 := h3
      _ = 2 ^ 53 * (2 ^ (E - 1) * 2 ^ 1326) := by ring

/-- The value of a nonnegative word in units of `2 ^ -2400`. -/
theorem nonneg_value (v : UInt64) (hv : v.toNat < limit) :
    value v = ((Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326 : ℕ) : ℝ) / 2 ^ 2400 := by
  have hs : Wasm.IEEE64.sign v = false := (nearest_finite (value v) v ⟨hv, fun _ _ => by simp⟩).2
  rw [F64Exact.value_of_sign _ hs, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    show (2400 : ℕ) = 1074 + 1326 by norm_num, pow_add,
    mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ 1326 ≠ 0)]

/-- The nearest multiple of a spacing is at least as close as any other multiple. -/
theorem step_below (s : ℝ) (j Q : ℕ) (hs : 0 < s) (hj : j < Q) : (j : ℝ) * s + s ≤ Q * s := by
  have h := mul_le_mul_of_nonneg_right (show (j : ℝ) + 1 ≤ Q by exact_mod_cast hj) hs.le
  linarith [add_mul (j : ℝ) 1 s, one_mul s]

theorem grid_near (y s : ℝ) (Q j : ℕ) (hs : 0 < s) (h1 : 2 * y ≤ (2 * Q + 1) * s)
    (h2 : 2 * Q * s ≤ 2 * y + s) : |(Q : ℝ) * s - y| ≤ |(j : ℝ) * s - y| := by
  have e1 : (2 * (Q : ℝ) + 1) * s = 2 * (Q * s) + s := by ring
  have e2 : 2 * (Q : ℝ) * s = 2 * (Q * s) := by ring
  rw [e1] at h1
  rw [e2] at h2
  rcases lt_trichotomy j Q with hj | hj | hj
  · have hj' := step_below s j Q hs hj
    rw [abs_of_neg (show (j : ℝ) * s - y < 0 by linarith), abs_le]
    constructor <;> linarith
  · rw [hj]
  · have hj' := step_below s Q j hs hj
    rw [abs_of_pos (show 0 < (j : ℝ) * s - y by linarith), abs_le]
    constructor <;> linarith

/-- Away from a tie, a multiple of the spacing as close as the nearest one is the nearest one. -/
theorem grid_unique (y s : ℝ) (Q j : ℕ) (hs : 0 < s) (h1 : 2 * y < (2 * Q + 1) * s)
    (h2 : 2 * Q * s < 2 * y + s) (hj : |(j : ℝ) * s - y| ≤ |(Q : ℝ) * s - y|) : j = Q := by
  have e1 : (2 * (Q : ℝ) + 1) * s = 2 * (Q * s) + s := by ring
  have e2 : 2 * (Q : ℝ) * s = 2 * (Q * s) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hq : |(Q : ℝ) * s - y| < s / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hj' := step_below s j Q hs hlt
    rw [abs_of_neg (show (j : ℝ) * s - y < 0 by linarith)] at hj
    linarith
  · have hj' := step_below s Q j hs hlt
    rw [abs_of_pos (show 0 < (j : ℝ) * s - y by linarith)] at hj
    linarith

/-- A word below the start of the binade is no closer than the nearest multiple. -/
theorem below_far (y s b v q : ℝ) (hs : 0 < s) (hv : 2 * v + s ≤ 2 * b) (hb : b ≤ y)
    (hq : b ≤ q) (h2 : 2 * q ≤ 2 * y + s) : |q - y| ≤ |v - y| ∧ s / 2 ≤ |v - y| := by
  rw [abs_of_neg (by linarith : v - y < 0)]
  refine ⟨?_, by linarith⟩
  rw [abs_le]
  constructor <;> linarith

theorem dist_div (a b c : ℝ) (hc : 0 < c) : |a / c - b / c| = |a - b| / c := by
  rw [← sub_div, abs_div, abs_of_pos hc]

theorem or_sign (w : UInt64) (hw : w.toNat < 2 ^ 63) :
    (((1 : UInt64) <<< 63) ||| w).toNat = 2 ^ 63 + w.toNat := by
  rw [UInt64.toNat_or]
  have h1 : ((1 : UInt64) <<< 63).toNat = 2 ^ 63 := by decide +kernel
  rw [h1]
  have := Nat.two_pow_add_eq_or_of_lt hw 1
  rw [mul_one] at this
  rw [← this]

/-- Two bounds of a separation argument: an odd multiple of `U` and a number within `U` of it lie
on the same side of every multiple of `2 U`. -/
theorem odd_side (Z U Y2 B K : ℕ) (hZ : Z % 2 = 1) (hU : 0 < U) (h1 : Z * U < Y2 + U)
    (h2 : Y2 < Z * U + U) (hB : B = 2 * K * U) :
    (Z * U ≤ B → Y2 < B) ∧ (B ≤ Z * U → B < Y2) := by
  subst hB
  constructor
  · intro h
    have h3 : Z ≤ 2 * K := Nat.le_of_mul_le_mul_right h hU
    have h4 : Z + 1 ≤ 2 * K := by omega
    have h5 : (Z + 1) * U ≤ 2 * K * U := Nat.mul_le_mul_right _ h4
    rw [Nat.add_mul, one_mul] at h5
    omega
  · intro h
    have h3 : 2 * K ≤ Z := Nat.le_of_mul_le_mul_right h hU
    have h4 : 2 * K + 1 ≤ Z := by omega
    have h5 : (2 * K + 1) * U ≤ Z * U := Nat.mul_le_mul_right _ h4
    rw [Nat.add_mul, one_mul] at h5
    omega

/-- `RoundsTo` moves from an odd multiple `Y1` of `2 ^ w` to any `Y2` within `2 ^ w` of it when
the spacing is a multiple of `2 ^ (w + 2)`, and `Y2` is then no tie. -/
theorem roundsTo_transfer (Y1 Y2 E Q Z w : ℕ) (h : RoundsTo Y1 E Q) (hY1 : Y1 = Z * 2 ^ w)
    (hZ : Z % 2 = 1) (hw : w + 2 ≤ E + 1325) (h1 : Y1 < Y2 + 2 ^ w) (h2 : Y2 < Y1 + 2 ^ w) :
    RoundsTo Y2 E Q := by
  obtain ⟨hE, hY53, hY52, hr1, hr2, _⟩ := h
  set U := 2 ^ w with hUdef
  have hU : 0 < U := by positivity
  set G := 2 ^ (E + 1325 - w - 2) with hG
  have hS : spacing E = 4 * G * U := by
    unfold spacing
    rw [hG, hUdef, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hY1] at h1 h2 hY53 hY52 hr1 hr2
  have side := fun B K (hB : B = 2 * K * U) => odd_side Z U Y2 B K hZ hU h1 h2 hB
  -- the upper end of the binade
  have a53 := (side (2 ^ 53 * spacing E) (2 ^ 54 * G) (by rw [hS]; ring)).1 hY53.le
  -- the lower end of a normal binade
  have a52 : E = 1 ∨ 2 ^ 52 * spacing E ≤ Y2 := by
    rcases hY52 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ((side (2 ^ 52 * spacing E) (2 ^ 53 * G) (by rw [hS]; ring)).2 h').le
  -- below the midpoint above `Q`
  have e1 : (2 * Q + 1) * spacing E = 2 * ((2 * Q + 1) * 2 * G * U) := by rw [hS]; ring
  have a1 := (side ((2 * Q + 1) * 2 * G * U) ((2 * Q + 1) * G) (by ring)).1 (by omega)
  have s1 : 2 * Y2 < (2 * Q + 1) * spacing E := by omega
  -- above the midpoint below `Q`
  have s2 : 2 * Q * spacing E < 2 * Y2 + spacing E := by
    rcases Nat.eq_zero_or_pos Q with hQ | hQ
    · rw [hQ, mul_zero, zero_mul]; have := spacing_pos E; omega
    · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      have e2 : 2 * (Q' + 1) * spacing E = 2 * ((2 * Q' + 1) * 2 * G * U) + spacing E := by
        rw [hS]; ring
      have a2 := (side ((2 * Q' + 1) * 2 * G * U) ((2 * Q' + 1) * G) (by ring)).2 (by omega)
      omega
  unfold RoundsTo
  exact ⟨hE, a53, a52, s1.le, s2.le, fun ht => by omega⟩

#print axioms significand_bounds
#print axioms word_value
#print axioms grid_or_below
#print axioms nonneg_value
#print axioms grid_near
#print axioms grid_unique
#print axioms below_far
#print axioms or_sign
#print axioms roundsTo_transfer

end Verified.Examples.FmaGrid
