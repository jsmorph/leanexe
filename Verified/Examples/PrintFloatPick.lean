import Verified.Examples.PrintFloatSearch

/-!
The code of `PrintFloat.shortest` against `PrintFloatSearch`: the words of the interval's
numerators and scales (`words_spec`), the start of the search (`startExp_spec`), `found` as the
decision of `Ex` from `top - 1` on (`found_iff`), and the search, which returns the number of
steps from the start to the top exponent (`search_spec`).
-/

namespace Verified.Examples.PrintFloatPick
open PrintFloat Uscale UscaleTheorem ParseFloatRound PrintFloatShort PrintFloatQuot PrintFloatSearch
open scoped Classical

set_option exponentiation.threshold 4096

section
variable (Q E nu : ℕ) (low : Bool)

/-- The bounds on a word's significand, binade, and format. -/
structure WordBounds : Prop where
  hQ : 1 ≤ Q
  hQ53 : Q < 2 ^ 53
  hE : 1 ≤ E
  hE2 : E ≤ 2 ^ 11
  hnu : 7 ≤ nu
  hnu2 : nu ≤ 1100

end

variable {Q E nu : ℕ} {low : Bool}

theorem words_spec (hb : WordBounds Q E nu) :
    (4 * UInt64.ofNat Q).toNat = 4 * Q ∧ (4 * UInt64.ofNat Q + 2).toNat = 4 * Q + 2 ∧
      (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2).toNat = nl Q low ∧
      (UInt64.ofNat E - 1).toNat = E - 1 ∧ (UInt64.ofNat nu + 2).toNat = nu + 2 ∧
      ((UInt64.ofNat Q &&& 1) == 0) = cl Q := by
  obtain ⟨hQ, hQ53, hE, hE2, hnu, hnu2⟩ := hb
  have q : (UInt64.ofNat Q).toNat = Q := ofNat_toNat _ (by omega)
  have e : (UInt64.ofNat E).toNat = E := ofNat_toNat _ (by omega)
  have n : (UInt64.ofNat nu).toNat = nu := ofNat_toNat _ (by omega)
  have h4 : (4 * UInt64.ofNat Q).toNat = 4 * Q := by
    rw [toNat_mul' _ _ (by rw [q]; simp; omega), q]; rfl
  refine ⟨h4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toNat_add' _ _ (by rw [h4]; simp; omega), h4]; rfl
  · unfold nl
    cases low
    · simp only [Bool.false_eq_true, ite_false]
      rw [toNat_sub' _ _ (by rw [h4]; simp; omega), h4]; rfl
    · simp only [ite_true]
      rw [toNat_sub' _ _ (by rw [h4]; simp; omega), h4]; rfl
  · rw [toNat_sub' _ _ (by rw [e]; simp; omega), e]; rfl
  · rw [toNat_add' _ _ (by rw [n]; simp; omega), n]; rfl
  · unfold cl
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_and, q, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simpa using this
    · intro h
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_and, q, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      simpa using h

theorem jstart_le (hb : WordBounds Q E nu) : jstart Q E nu ≤ 700 ∧ -400 ≤ jstart Q E nu := by
  obtain ⟨hQ, hQ53, hE, hE2, hnu, hnu2⟩ := hb
  have hs : Nat.size (4 * Q + 2) ≤ 56 := by
    rw [Nat.size_le]; omega
  unfold jstart
  split_ifs with h <;> constructor <;> omega

theorem startExp_spec (hb : WordBounds Q E nu) :
    ((startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2)).toNat : ℤ) =
      2 ^ 62 + jstart Q E nu := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words_spec (low := false) hb
  have hb' := hb
  obtain ⟨hQ, hQ53, hE, hE2, hnu, hnu2⟩ := hb'
  have hs : Nat.size (4 * Q + 2) ≤ 56 := by rw [Nat.size_le]; omega
  have hwb : (wordBits (4 * UInt64.ofNat Q + 2)).toNat = Nat.size (4 * Q + 2) := by
    rw [wordBits_spec, w2]
  have hbsum : (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1)).toNat =
      Nat.size (4 * Q + 2) + (E - 1) := by
    rw [toNat_add' _ _ (by rw [hwb, w4]; omega), hwb, w4]
  unfold startExp jstart
  dsimp only
  by_cases h : nu + 2 ≤ Nat.size (4 * Q + 2) + (E - 1)
  · have hc : (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1)) ≥ UInt64.ofNat nu + 2 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hbsum, w5]; exact h
    rw [ite_eq_left hc, ite_eq_left h]
    have hd : (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1) - (UInt64.ofNat nu + 2)).toNat =
        Nat.size (4 * Q + 2) + (E - 1) - (nu + 2) := by
      rw [toNat_sub' _ _ (by rw [hbsum, w5]; exact h), hbsum, w5]
    have hm : ((wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1) - (UInt64.ofNat nu + 2)) * 31
        + 99).toNat = (Nat.size (4 * Q + 2) + (E - 1) - (nu + 2)) * 31 + 99 := by
      rw [toNat_add' _ _ (by rw [toNat_mul' _ _ (by rw [hd]; simp; omega), hd]; simp; omega),
        toNat_mul' _ _ (by rw [hd]; simp; omega), hd]; rfl
    have hq : (((wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1) - (UInt64.ofNat nu + 2)) * 31
        + 99) / 100).toNat = ((Nat.size (4 * Q + 2) + (E - 1) - (nu + 2)) * 31 + 99) / 100 := by
      rw [UInt64.toNat_div, hm]; rfl
    rw [toNat_add' _ _ (by rw [bias_toNat, hq]; omega), bias_toNat, hq]
    push_cast
    congr 2
    ring_nf
  · have hc : ¬ (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1)) ≥ UInt64.ofNat nu + 2 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hbsum, w5]; exact h
    rw [ite_eq_right hc, ite_eq_right h]
    have hd : (UInt64.ofNat nu + 2 - (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1))).toNat =
        nu + 2 - (Nat.size (4 * Q + 2) + (E - 1)) := by
      rw [toNat_sub' _ _ (by rw [hbsum, w5]; omega), hbsum, w5]
    have hq : ((UInt64.ofNat nu + 2 - (wordBits (4 * UInt64.ofNat Q + 2) + (UInt64.ofNat E - 1))) * 3
        / 10).toNat = 3 * (nu + 2 - (Nat.size (4 * Q + 2) + (E - 1))) / 10 := by
      rw [UInt64.toNat_div, toNat_mul' _ _ (by rw [hd]; simp; omega), hd]
      simp only [show (3 : UInt64).toNat = 3 from rfl, show (10 : UInt64).toNat = 10 from rfl]
      rw [Nat.mul_comm]
    rw [toNat_sub' _ _ (by rw [bias_toNat, hq]; omega), bias_toNat, hq]
    omega

/-- `found` decides whether a multiple of `10 ^ j` lies in the interval, from `top - 1` on. -/
theorem found_iff (hb : WordBounds Q E nu) (jb : UInt64)
    (hj1 : 2 ^ 62 - 2 ^ 19 ≤ jb.toNat) (hj2 : jb.toNat ≤ 2 ^ 62 + 2 ^ 19)
    (hj : top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) - 1 ≤ (jb.toNat : ℤ) - 2 ^ 62) :
    found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
        (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb ((UInt64.ofNat Q &&& 1) == 0) =
      decide (Ex Q E nu low ((jb.toNat : ℤ) - 2 ^ 62)) := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words_spec (low := low) hb
  set j : ℤ := (jb.toNat : ℤ) - 2 ^ 62 with hjdef
  have hsn : (UInt64.ofNat E - 1).toNat < 2 ^ 30 := by rw [w4]; have := hb.hE2; omega
  have hsd : (UInt64.ofNat nu + 2).toNat < 2 ^ 30 := by rw [w5]; have := hb.hnu2; omega
  obtain ⟨r1, r2⟩ := range_spec ((UInt64.ofNat Q &&& 1) == 0)
    (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
    (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb hsn hsd hj1 hj2
    (by rw [w3, w4, w5, ← hjdef]
        exact quot_bound hb.hQ hb.hE _ hb.hQ53 _ (by unfold nl; split_ifs <;> omega) j hj)
    (by rw [w2, w4, w5, ← hjdef]
        exact quot_bound hb.hQ hb.hE _ hb.hQ53 _ (by omega) j hj)
  rw [w3, w4, w5, w6, ← hjdef] at r1
  rw [w2, w4, w5, w6, ← hjdef] at r2
  unfold found
  dsimp only
  rw [w6, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.lt_iff_toNat_lt, r1, r2]
  unfold Ex
  constructor
  · intro h
    refine ⟨ceilOf (cl Q) (num (nl Q low) (E - 1) j) (den (nu + 2) j), ?_⟩
    unfold lo hi
    rw [inside_iff]
    exact ⟨le_rfl, h⟩
  · rintro ⟨m, hm⟩
    unfold lo hi at hm
    rw [inside_iff] at hm
    omega

/-- The search returns the number of steps from the start to the top exponent. -/
theorem search_spec (hb : WordBounds Q E nu) :
    (LeanExe.repeatWhile 2000 0 (fun i => i < 2000 &&
        !found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2)
          (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) - i)
          ((UInt64.ofNat Q &&& 1) == 0)) (fun i => i + 1)).toNat =
      steps Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) := by
  have hnu1 : 1 ≤ nu := by have := hb.hnu; omega
  have hst := startExp_spec hb
  obtain ⟨hj1, hj2⟩ := jstart_le hb
  have hge := top_ge (low := low) hb.hQ hb.hE hnu1
  have hlt := top_lt_start (low := low) hb.hQ hb.hE hnu1
  set S := steps Q E nu low hb.hQ hb.hE hnu1 with hS
  have htop : top Q E nu low hb.hQ hb.hE hnu1 = jstart Q E nu - S := rfl
  have hS2 : S ≤ 1800 := by have := hb.hnu2; omega
  -- the exponent of step `z`
  have hstep : ∀ z : ℕ, z ≤ S →
      ((startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) -
        UInt64.ofNat z).toNat : ℤ) = 2 ^ 62 + (jstart Q E nu - z) := by
    intro z hz
    rw [toNat_sub' _ _ (by rw [ofNat_toNat _ (by omega)]; omega), ofNat_toNat _ (by omega)]
    push_cast [show z ≤ (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1)
      (UInt64.ofNat nu + 2)).toNat by omega]
    omega
  apply ParseFloatDigits.repeat_first 2000 (by norm_num) 2000 (by decide)
    (fun z => !found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2)
      (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2)
      (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) - z)
      ((UInt64.ofNat Q &&& 1) == 0)) S (by omega)
  · intro z hz
    have h := hstep z hz.le
    rw [found_iff hb _ (by omega) (by omega) (by rw [h]; omega), h]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    have := Nat.find_min (ex_some (low := low) hb.hQ hb.hE hnu1) hz
    rwa [show (2 : ℤ) ^ 62 + (jstart Q E nu - z) - 2 ^ 62 = jstart Q E nu - z by ring]
  · intro _
    have h := hstep S le_rfl
    rw [found_iff hb _ (by omega) (by omega) (by rw [h]; omega), h]
    simp only [Bool.not_eq_false', decide_eq_true_eq]
    rw [show (2 : ℤ) ^ 62 + (jstart Q E nu - S) - 2 ^ 62 = top Q E nu low hb.hQ hb.hE hnu1 by
      rw [htop]; ring]
    exact ex_top hb.hQ hb.hE hnu1

#print axioms startExp_spec
#print axioms found_iff
#print axioms search_spec

end Verified.Examples.PrintFloatPick
