import Verified.Examples.StrconvGrid

/-!
The rounding interval of a finite positive encoding.  The encoding `pack f E Q` of a canonical
significand `Q` in binade `E` (`Canonical`) is the reference of exactly the reals `y ≥ 0`, in units
of the least subnormal, that lie between `lower f E Q` and `upper E Q`, the ends included when
`Q` is even (`interval_iff`).  The upper end is the midpoint `(2 Q + 1) · 2 ^ (E - 1) / 2` to the
next value.  The lower end is the midpoint to the previous value: `(2 Q - 1) · 2 ^ (E - 1) / 2`,
except at the start of a normal binade, `Q = 2 ^ (p - 1)` with `E ≥ 2`, where the previous value
lies in the binade below at half the spacing and the lower end is
`(4 Q - 1) · 2 ^ (E - 1) / 4`.  The printers decide membership in this interval with integers.
-/

namespace Verified.Examples.StrconvInterval
open StrconvGrid

set_option exponentiation.threshold 4096

variable (f : Fmt)

/-- A canonical nonzero significand of binade `E`. -/
def Canonical (E Q : ℕ) : Prop := 1 ≤ E ∧ 0 < Q ∧ Q < 2 * half f ∧ (E = 1 ∨ half f ≤ Q)

/-- The lower end of the rounding interval of `pack f E Q`, in units. -/
noncomputable def lower (E Q : ℕ) : ℝ :=
  if 2 ≤ E ∧ Q = half f then (4 * Q - 1 : ℝ) * 2 ^ (E - 1) / 4
  else (2 * Q - 1 : ℝ) * 2 ^ (E - 1) / 2

/-- The upper end of the rounding interval of `pack f E Q`, in units. -/
noncomputable def upper (E Q : ℕ) : ℝ := (2 * Q + 1 : ℝ) * 2 ^ (E - 1) / 2

/-- `y` lies in the rounding interval of `pack f E Q`, with its ends when `Q` is even. -/
def InInterval (E Q : ℕ) (y : ℝ) : Prop :=
  if Q % 2 = 0 then lower f E Q ≤ y ∧ y ≤ upper E Q else lower f E Q < y ∧ y < upper E Q

/-- Two encodings of significands are equal only for the same significand, or for the carry of
`2 ^ p` in the binade below into `2 ^ (p - 1)`. -/
theorem pack_eq (E Q E' Q' : ℕ) (hc : Canonical f E Q) (hE' : 1 ≤ E') (hQ' : Q' ≤ 2 * half f)
    (hQ1' : E' = 1 ∨ half f ≤ Q') (h : pack f E Q = pack f E' Q') :
    (E = E' ∧ Q = Q') ∨ (E = E' + 1 ∧ Q' = 2 * half f ∧ Q = half f) := by
  obtain ⟨hE, hQ0, hQ2, hQ1⟩ := hc
  have hB := half_pos f
  obtain ⟨k, rfl⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', E' = k' + 1 := ⟨E' - 1, by omega⟩
  unfold pack at h
  simp only [Nat.add_sub_cancel] at h hQ1 hQ1' ⊢
  by_cases ha : Q < half f
  · have hk : k = 0 := by
      rcases hQ1 with h1 | h1
      · omega
      · omega
    subst hk
    simp only [zero_mul, zero_add] at h
    by_cases hb : Q' < half f
    · have hk' : k' = 0 := by
        rcases hQ1' with h1 | h1
        · omega
        · omega
      subst hk'
      left; simp at h; omega
    · exfalso
      have : half f ≤ k' * half f + Q' := by omega
      omega
  · push Not at ha
    have hn : k * half f + Q = (Q - half f) + (k + 1) * half f := by rw [Nat.add_mul, one_mul]; omega
    have hd : (k * half f + Q) / half f = k + 1 := by
      rw [hn, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), zero_add]
    have hm : (k * half f + Q) % half f = Q - half f := by
      rw [hn, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    by_cases hb : Q' < half f
    · exfalso
      have hk' : k' = 0 := by rcases hQ1' with h1 | h1 <;> omega
      subst hk'
      simp at h
      omega
    · push Not at hb
      by_cases hc' : Q' < 2 * half f
      · have hn' : k' * half f + Q' = (Q' - half f) + (k' + 1) * half f := by
          rw [Nat.add_mul, one_mul]; omega
        have hd' : (k' * half f + Q') / half f = k' + 1 := by
          rw [hn', Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), zero_add]
        have hm' : (k' * half f + Q') % half f = Q' - half f := by
          rw [hn', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        left
        rw [h] at hd hm
        rw [hd] at hd'
        constructor <;> omega
      · have hQe : Q' = 2 * half f := by omega
        subst hQe
        have hn' : k' * half f + 2 * half f = (k' + 2) * half f := by ring
        rw [h, hn', Nat.mul_div_cancel _ hB] at hd
        rw [h, hn', Nat.mul_mod_left] at hm
        right
        refine ⟨by omega, rfl, by omega⟩

theorem pack_lt_F (E Q : ℕ) (hc : Canonical f E Q) (hL : pack f E Q < limit f) : E < f.F := by
  obtain ⟨hE, _, _, hQ1⟩ := hc
  have hB := half_pos f
  unfold pack limit at hL
  by_contra h
  push Not at h
  rcases hQ1 with h1 | h1
  · have := f.hF; omega
  · have : f.F * half f ≤ (E - 1) * half f + half f := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem packInf_of (E Q : ℕ) (hE : E < f.F) (hL : pack f E Q < limit f) :
    packInf f E Q = pack f E Q := by
  unfold packInf; rw [if_neg (by omega)]

/-- The rounding interval: `pack f E Q` is the reference of exactly the reals in its interval. -/
theorem interval_iff (E Q : ℕ) (hc : Canonical f E Q) (hL : pack f E Q < limit f) (y : ℝ)
    (hy : 0 ≤ y) : refPos f y = pack f E Q ↔ InInterval f E Q y := by
  have hc' := hc
  obtain ⟨hE, hQ0, hQ2, hQ1⟩ := hc'
  have hB := half_pos f
  have hBe := half_even f
  have hEF := pack_lt_F f E Q hc hL
  set S : ℝ := (2 : ℝ) ^ (E - 1) with hS
  have hS0 : 0 < S := by positivity
  have hp : (2 : ℝ) ^ f.p = 2 * half f := by exact_mod_cast (two_half f).symm
  have hph : (2 : ℝ) ^ (f.p - 1) = half f := by unfold half; push_cast; ring
  have hBr : (1 : ℝ) ≤ half f := by exact_mod_cast hB
  have hQr : (Q : ℝ) + 1 ≤ 2 * half f := by exact_mod_cast hQ2
  have hlow : ∀ (h2 : ¬ (2 ≤ E ∧ Q = half f)), lower f E Q = (2 * Q - 1 : ℝ) * S / 2 :=
    fun h2 => by unfold lower; rw [if_neg h2]
  constructor
  · intro href
    obtain ⟨E', Q', hR⟩ := exists_roundsTo f y hy
    obtain ⟨hQ', hQ1'⟩ := significand_bounds f y E' Q' hR
    have href' := positive_reference f y E' Q' hR
    rw [href] at href'
    have hF' : ¬ (f.F ≤ E' ∨ limit f ≤ pack f E' Q') := by
      intro hc2
      unfold packInf at href'; rw [if_pos hc2] at href'; omega
    rw [packInf, if_neg hF'] at href'
    obtain ⟨hE', hb1, hb2, hr1, hr2, htie⟩ := hR
    rcases pack_eq f E Q E' Q' hc hE' hQ' hQ1' href' with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hQB⟩
    · unfold InInterval
      have hup : y ≤ upper E Q := by unfold upper; linarith
      have hlo : lower f E Q ≤ y := by
        unfold lower
        split_ifs with hst
        · rcases hb2 with h1 | h1
          · omega
          · rw [hph] at h1
            have : (4 * Q - 1 : ℝ) * S / 4 ≤ half f * S := by
              rw [hst.2]; nlinarith
            linarith
        · linarith
      split_ifs with hpar
      · exact ⟨hlo, hup⟩
      · have hnt1 : 2 * y ≠ (2 * Q + 1) * S := fun h => hpar (htie (Or.inl h))
        have hnt2 : 2 * y + S ≠ 2 * Q * S := fun h => hpar (htie (Or.inr h))
        have hst : ¬ (2 ≤ E ∧ Q = half f) := by
          rintro ⟨_, h⟩; rw [h] at hpar; exact hpar hBe
        constructor
        · rw [hlow hst]
          rcases lt_or_eq_of_le hr2 with h | h
          · linarith
          · exact absurd h.symm hnt2
        · unfold upper
          rcases lt_or_eq_of_le hr1 with h | h
          · linarith
          · exact absurd h hnt1
    · -- the carry from the binade below
      unfold InInterval
      rw [if_pos (by rw [hQB]; exact hBe)]
      have hS2 : (2 : ℝ) ^ (E' + 1 - 1) = 2 * (2 : ℝ) ^ (E' - 1) := by
        rw [show E' + 1 - 1 = (E' - 1) + 1 by omega, pow_succ]; ring
      constructor
      · unfold lower
        rw [if_pos ⟨by omega, hQB⟩, hQB, hS2]
        push_cast at hr2
        nlinarith
      · unfold upper
        rw [hQB, hS2]
        rw [hp] at hb1
        nlinarith
  · intro hin
    have hup : y ≤ upper E Q := by
      unfold InInterval at hin; split_ifs at hin <;> linarith [hin.2]
    have hlo : lower f E Q ≤ y := by
      unfold InInterval at hin; split_ifs at hin <;> linarith [hin.1]
    by_cases hcase : E = 1 ∨ (half f : ℝ) * S ≤ y
    · have hR : RoundsTo f y E Q := by
        refine ⟨hE, ?_, ?_, ?_, ?_, ?_⟩
        · unfold upper at hup; rw [hp]; nlinarith
        · rcases hcase with h | h
          · exact Or.inl h
          · right; rw [hph]; exact h
        · unfold upper at hup; linarith
        · by_cases hst : 2 ≤ E ∧ Q = half f
          · rcases hcase with h | h
            · omega
            · rw [hst.2]; nlinarith
          · rw [hlow hst] at hlo; linarith
        · intro ht
          by_contra hpar
          unfold InInterval at hin
          rw [if_neg hpar] at hin
          have hst : ¬ (2 ≤ E ∧ Q = half f) := by
            rintro ⟨_, h⟩; rw [h] at hpar; exact hpar hBe
          rcases ht with ht | ht
          · unfold upper at hin; linarith [hin.2]
          · rw [hlow hst] at hin; linarith [hin.1]
      rw [positive_reference f y E Q hR, packInf_of f E Q hEF hL]
    · push Not at hcase
      obtain ⟨hE1, hyB⟩ := hcase
      have hQB : Q = half f := by
        by_contra hne
        have hst : ¬ (2 ≤ E ∧ Q = half f) := fun h => hne h.2
        rw [hlow hst] at hlo
        have : half f + 1 ≤ Q := by rcases hQ1 with h | h <;> omega
        have : ((half f : ℕ) : ℝ) + 1 ≤ Q := by exact_mod_cast this
        nlinarith
      have hE2 : 2 ≤ E := by omega
      have hS2 : (2 : ℝ) ^ (E - 1) = 2 * (2 : ℝ) ^ (E - 1 - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hlo' : (4 * (half f : ℝ) - 1) * (2 * (2 : ℝ) ^ (E - 1 - 1)) / 4 ≤ y := by
        unfold lower at hlo; rw [if_pos ⟨hE2, hQB⟩, hQB, hS2] at hlo; exact_mod_cast hlo
      have hyB' : y < (half f : ℝ) * (2 * (2 : ℝ) ^ (E - 1 - 1)) := by
        rw [← hS2]; exact hyB
      have hR : RoundsTo f y (E - 1) (2 * half f) := by
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hp]; nlinarith
        · right; rw [hph]; nlinarith
        · push_cast; nlinarith
        · push_cast; nlinarith
        · intro _; omega
      have hpk : pack f (E - 1) (2 * half f) = pack f E Q := by
        unfold pack; rw [hQB]
        obtain ⟨k, rfl⟩ : ∃ k, E = k + 2 := ⟨E - 2, by omega⟩
        rw [show k + 2 - 1 - 1 = k by omega, show k + 2 - 1 = k + 1 by omega]
        ring
      rw [positive_reference f y _ _ hR, packInf_of f _ _ (by omega) (by rw [hpk]; exact hL), hpk]

#print axioms pack_eq
#print axioms interval_iff

end Verified.Examples.StrconvInterval
