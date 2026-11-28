module

public import Library.Numerics.Bignum.NatProof

@[expose] public section

/-!
The integer functions equal their specifications.  An integer `z` is `signed (decide (z < 0))
|z|`, where `signed s A` is `-A` when `s` holds and `A` otherwise (`signed_natAbs`), and the
canonical form of `signed s A` has the magnitude `limbsOf A` and the sign `s ∧ A ≠ 0`
(`ofInt_signed`).  `addCore_eq` proves the sum of two signed magnitudes once, for `intAdd` and for
`intSub`, which flips the second sign.  The truncated division of signed magnitudes is the natural
division with the signs of Lean's `Int.tdiv` and `Int.tmod` (`tdiv_signed`, `tmod_signed`), and
the Euclidean division follows from Lean's `Int.tdiv_eq_ediv` and `Int.tmod_eq_emod`, which
differ from the truncated ones exactly when the dividend is negative and the divisor does not
divide it.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-! ## Signed magnitudes -/

/-- The integer of a sign and a magnitude. -/
def signed (s : Bool) (A : ℕ) : ℤ := if s then -(A : ℤ) else A

theorem signed_natAbs (z : ℤ) : signed (decide (z < 0)) z.natAbs = z := by
  unfold signed
  by_cases h : z < 0
  · rw [decide_eq_true h, ite_eq_left rfl]; omega
  · rw [decide_eq_false h, ite_eq_right (by decide)]; omega

theorem natAbs_signed (s : Bool) (A : ℕ) : (signed s A).natAbs = A := by
  unfold signed; cases s <;> simp

theorem decide_signed (s : Bool) (A : ℕ) : decide (signed s A < 0) = (s && decide (A ≠ 0)) := by
  unfold signed
  cases s
  · simp
  · rw [ite_eq_left rfl, Bool.true_and]
    exact decide_eq_decide.mpr (by omega)

/-- The canonical form of a signed magnitude. -/
theorem ofInt_signed (s : Bool) (A : ℕ) :
    BigInt.ofInt (signed s A) = ⟨s && decide (A ≠ 0), limbsOf A⟩ := by
  unfold BigInt.ofInt
  rw [decide_signed, natAbs_signed]

/-- The two cases of `|z|`.  `omega` reads the cast of `z.natAbs` as an atom that it does not
relate to `z`, so a proof splits on these cases and passes the equation. -/
theorem natAbs_cases (z : ℤ) :
    (z < 0 ∧ (z.natAbs : ℤ) = -z) ∨ (0 ≤ z ∧ (z.natAbs : ℤ) = z) := by
  by_cases h : z < 0
  · exact Or.inl ⟨h, Int.ofNat_natAbs_of_nonpos h.le⟩
  · exact Or.inr ⟨not_lt.mp h, Int.natAbs_of_nonneg (not_lt.mp h)⟩

theorem ofInt_eq_signed (z : ℤ) : BigInt.ofInt z = ⟨decide (z < 0), limbsOf z.natAbs⟩ := rfl

/-! ## Sizes -/

theorem size_limbsOf_le_iff (n k : ℕ) : (limbsOf n).size ≤ k ↔ n < base ^ k := by
  rw [size_limbsOf]
  exact Nat.digits_length_le_iff one_lt_base n

theorem size_limbsOf_mono {m n : ℕ} (h : m ≤ n) : (limbsOf m).size ≤ (limbsOf n).size := by
  rw [size_limbsOf, size_limbsOf]
  exact Nat.le_length_digits_le _ _ _ h

theorem size_limbsOf_mul (m n : ℕ) :
    (limbsOf (m * n)).size ≤ (limbsOf m).size + (limbsOf n).size := by
  rw [size_limbsOf_le_iff, pow_add]
  have h1 := (size_limbsOf_le_iff m (limbsOf m).size).mp le_rfl
  have h2 := (size_limbsOf_le_iff n (limbsOf n).size).mp le_rfl
  exact Nat.mul_lt_mul'' h1 h2

theorem toUInt64_bne_zero {u : Array UInt64} (hs : u.size < 2 ^ 64) :
    (u.size.toUInt64 != 0) = decide (u.size ≠ 0) := by
  rw [bne, size_toUInt64_beq_zero hs]
  by_cases h : u.size = 0 <;> simp [h]

theorem limbsOf_bne_zero {n : ℕ} (hs : (limbsOf n).size < 2 ^ 64) :
    ((limbsOf n).size.toUInt64 != 0) = decide (n ≠ 0) := by
  rw [toUInt64_bne_zero hs]
  exact decide_eq_decide.mpr (not_congr (size_limbsOf_eq_zero n))

theorem limbsOf_beq_zero {n : ℕ} (hs : (limbsOf n).size < 2 ^ 64) :
    ((limbsOf n).size.toUInt64 == 0) = decide (n = 0) := by
  rw [size_toUInt64_beq_zero hs]
  exact decide_eq_decide.mpr (size_limbsOf_eq_zero n)

theorem limbsOf_one : limbsOf 1 = #[1] := by
  simp [limbsOf, Nat.digits_of_lt base 1 one_ne_zero one_lt_base]

/-! ## Negation and comparison -/

theorem intNeg_eq {a : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32) :
    intNeg (.ofInt a) = .ofInt (-a) := by
  unfold intNeg
  simp only [BigInt.ofInt] at ha ⊢
  rw [limbsOf_bne_zero (by omega), natTrim_canonical (canonical_limbsOf _) (by omega),
    Int.natAbs_neg]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    ne_eq]
  omega

theorem intCmp_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intCmp (.ofInt a) (.ofInt b) = cmpSpec a b := by
  unfold intCmp
  simp only [BigInt.ofInt] at ha hb ⊢
  have hA := (canonical_limbsOf a.natAbs).1
  have hB := (canonical_limbsOf b.natAbs).1
  rcases natAbs_cases a with ⟨h1, ea⟩ | ⟨h1, ea⟩ <;>
    rcases natAbs_cases b with ⟨h2, eb⟩ | ⟨h2, eb⟩
  · simp only [decide_eq_true h1, decide_eq_true h2, ite_true]
    rw [natCmp_eq hB hA hb ha, value_limbsOf, value_limbsOf]
    unfold cmpSpec
    split_ifs <;> first | rfl | omega
  · simp only [decide_eq_true h1, decide_eq_false (not_lt.mpr h2), ite_true, Bool.false_eq_true,
      ite_false]
    unfold cmpSpec; split_ifs <;> first | rfl | omega
  · simp only [decide_eq_false (not_lt.mpr h1), decide_eq_true h2, ite_true, Bool.false_eq_true,
      ite_false]
    unfold cmpSpec; split_ifs <;> first | rfl | omega
  · simp only [decide_eq_false (not_lt.mpr h1), decide_eq_false (not_lt.mpr h2),
      Bool.false_eq_true, ite_false]
    rw [natCmp_eq hA hB ha hb, value_limbsOf, value_limbsOf]
    unfold cmpSpec
    split_ifs <;> first | rfl | omega

/-! ## Sums and products -/

/-- The sum of two signed magnitudes, for a first sign that is negative only with a nonzero
magnitude. -/
theorem addCore_eq {xs ys : Bool} {A B : ℕ} (hA : (limbsOf A).size < 2 ^ 32)
    (hB : (limbsOf B).size < 2 ^ 32) (hx : xs = true → A ≠ 0) :
    addCore xs (limbsOf A) ys (limbsOf B) = .ofInt (signed xs A + signed ys B) := by
  have cA := (canonical_limbsOf A).1
  have cB := (canonical_limbsOf B).1
  unfold addCore
  by_cases hxy : xs = ys
  · subst hxy
    rw [ite_eq_left (by simp), natAdd_eq cA cB hA hB, value_limbsOf, value_limbsOf]
    have : signed xs A + signed xs B = signed xs (A + B) := by
      unfold signed; cases xs <;> simp; omega
    rw [this, ofInt_signed]
    congr 1
    cases xs <;> simp
    have := hx rfl
    omega
  · rw [ite_eq_right (by cases xs <;> cases ys <;> simp_all)]
    dsimp only
    rw [natSub_eq cA cB hA hB, value_limbsOf, value_limbsOf, natSubSpec]
    dsimp only
    have hd : (limbsOf ((A : ℤ) - B).natAbs).size < 2 ^ 64 := by
      have := size_limbsOf_mono (show ((A : ℤ) - B).natAbs ≤ A + B by omega)
      have := size_limbsOf_mono (show A + B ≤ 2 * max A B by omega)
      have h3 : (limbsOf (2 * max A B)).size ≤ (limbsOf 2).size + (limbsOf (max A B)).size :=
        size_limbsOf_mul 2 (max A B)
      have h4 : (limbsOf 2).size ≤ 1 := (size_limbsOf_le_iff 2 1).mpr (by rw [base_eq]; norm_num)
      have h5 : (limbsOf (max A B)).size < 2 ^ 32 := by
        rcases le_total A B with h | h
        · rw [max_eq_right h]; exact hB
        · rw [max_eq_left h]; exact hA
      omega
    rw [limbsOf_bne_zero hd]
    rw [ofInt_eq_signed]
    cases xs <;> cases ys
    · exact absurd rfl hxy
    · simp only [signed, Bool.false_eq_true, ite_false, ite_true]
      rw [show (A : ℤ) + -(B : ℤ) = (A : ℤ) - B by ring]
      congr 1
      simp only [ne_eq, Int.natAbs_eq_zero]
      rcases Nat.lt_or_ge A B with h | h
      · rw [decide_eq_true h, ite_eq_left rfl, Bool.true_and]
        exact decide_eq_decide.mpr (by omega)
      · rw [decide_eq_false (not_lt.mpr h), ite_eq_right (by decide), Bool.false_and]
        exact (decide_eq_false (by omega)).symm
    · simp only [signed, Bool.false_eq_true, ite_false, ite_true]
      rw [show -(A : ℤ) + (B : ℤ) = -((A : ℤ) - B) by ring, Int.natAbs_neg]
      congr 1
      simp only [ne_eq, Int.natAbs_eq_zero]
      rcases Nat.lt_or_ge A B with h | h
      · rw [decide_eq_true h, ite_eq_left rfl, Bool.false_and]
        exact (decide_eq_false (by omega)).symm
      · rw [decide_eq_false (not_lt.mpr h), ite_eq_right (by decide), Bool.true_and]
        exact decide_eq_decide.mpr (by omega)
    · exact absurd rfl hxy

theorem intAdd_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intAdd (.ofInt a) (.ofInt b) = .ofInt (a + b) := by
  unfold intAdd
  simp only [BigInt.ofInt] at ha hb
  rw [show (BigInt.ofInt a).neg = decide (a < 0) from rfl,
    show (BigInt.ofInt a).mag = limbsOf a.natAbs from rfl,
    show (BigInt.ofInt b).neg = decide (b < 0) from rfl,
    show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl,
    addCore_eq ha hb (fun h => by simp at h; omega), signed_natAbs, signed_natAbs]

theorem intSub_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intSub (.ofInt a) (.ofInt b) = .ofInt (a - b) := by
  unfold intSub
  simp only [BigInt.ofInt] at ha hb
  rw [show (BigInt.ofInt a).neg = decide (a < 0) from rfl,
    show (BigInt.ofInt a).mag = limbsOf a.natAbs from rfl,
    show (BigInt.ofInt b).neg = decide (b < 0) from rfl,
    show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl,
    addCore_eq ha hb (fun h => by simp at h; omega), signed_natAbs]
  congr 1
  unfold signed
  by_cases h : b < 0
  · rw [decide_eq_true h, Bool.not_true, ite_eq_right (by decide)]; omega
  · rw [decide_eq_false h, Bool.not_false, ite_eq_left rfl]; omega

theorem intMul_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intMul (.ofInt a) (.ofInt b) = .ofInt (a * b) := by
  unfold intMul
  simp only [BigInt.ofInt] at ha hb ⊢
  rw [natMul_eq (canonical_limbsOf _).1 (canonical_limbsOf _).1 ha hb, value_limbsOf,
    value_limbsOf, limbsOf_bne_zero (by
      have := size_limbsOf_mul a.natAbs b.natAbs
      omega), Int.natAbs_mul]
  congr 1
  rcases lt_trichotomy a 0 with h1 | h1 | h1 <;> rcases lt_trichotomy b 0 with h2 | h2 | h2
  · simp [h1, h2, show ¬ a * b < 0 by nlinarith]
  · subst h2; simp
  · simp [h1, h2.ne', not_lt.mpr h2.le, mul_neg_of_neg_of_pos h1 h2]; omega
  · subst h1; simp
  · subst h1; simp
  · subst h1; simp
  · simp [h2, not_lt.mpr h1.le, mul_neg_of_pos_of_neg h1 h2]; omega
  · subst h2; simp
  · simp [not_lt.mpr h1.le, not_lt.mpr h2.le, show ¬ a * b < 0 by nlinarith]

/-! ## Division -/

theorem tdiv_signed (s t : Bool) (A B : ℕ) :
    (signed s A).tdiv (signed t B) = signed (s != t) (A / B) := by
  unfold signed
  cases s <;> cases t <;>
    simp [Int.neg_tdiv, Int.tdiv_neg]

theorem tmod_signed (s t : Bool) (A B : ℕ) :
    (signed s A).tmod (signed t B) = signed s (A % B) := by
  unfold signed
  cases s <;> cases t <;>
    simp [Int.neg_tmod, Int.tmod_neg, ← Int.ofNat_tmod]

theorem intTDivMod_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intTDivMod (.ofInt a) (.ofInt b) = intTDivModSpec a b := by
  unfold intTDivMod intTDivModSpec
  simp only [BigInt.ofInt] at ha hb ⊢
  rw [natDivMod_eq (canonical_limbsOf _) (canonical_limbsOf _) ha hb, natDivModSpec,
    value_limbsOf, value_limbsOf]
  dsimp only
  rw [limbsOf_bne_zero (lt_of_le_of_lt (size_limbsOf_mono (Nat.div_le_self _ _)) (by omega)),
    limbsOf_bne_zero (lt_of_le_of_lt (size_limbsOf_mono (Nat.mod_le _ _)) (by omega))]
  conv_rhs => rw [← signed_natAbs a, ← signed_natAbs b, tdiv_signed, tmod_signed]
  rw [← ofInt_signed, ← ofInt_signed]
  rfl

theorem sign_eq (b : ℤ) (hb : b ≠ 0) : b.sign = if b < 0 then -1 else 1 := by
  by_cases h : b < 0
  · rw [ite_eq_left h, Int.sign_eq_neg_one_of_neg h]
  · rw [ite_eq_right h, Int.sign_eq_one_of_pos (by omega)]

theorem intEDivMod_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intEDivMod (.ofInt a) (.ofInt b) = intEDivModSpec a b := by
  simp only [intEDivMod, intTDivMod_eq ha hb, intTDivModSpec, intEDivModSpec]
  have hbs : (BigInt.ofInt b).mag.size < 2 ^ 64 := by omega
  simp only [BigInt.ofInt] at hbs
  rw [show (BigInt.ofInt (a.tmod b)).neg = decide (a.tmod b < 0) from rfl,
    show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl, limbsOf_bne_zero hbs]
  have hm := Int.natAbs_tmod a b
  by_cases hc : a.tmod b < 0 ∧ b.natAbs ≠ 0
  · obtain ⟨hneg, hb0⟩ := hc
    rw [ite_eq_left (by simp [hneg, hb0])]
    have hnd : ¬ (0 ≤ a ∨ b ∣ a) := by
      rintro (h | h)
      · have := tmod_signed (decide (a < 0)) (decide (b < 0)) a.natAbs b.natAbs
        rw [signed_natAbs, signed_natAbs, decide_eq_false (not_lt.mpr h)] at this
        rw [this] at hneg
        unfold signed at hneg
        rw [ite_eq_right (by decide)] at hneg
        omega
      · rw [Int.tmod_eq_zero_of_dvd h] at hneg
        exact lt_irrefl 0 hneg
    have hq := @Int.tdiv_eq_ediv a b
    have hr := @Int.tmod_eq_emod a b
    rw [ite_eq_right hnd] at hq hr
    rw [sign_eq b (by omega)] at hq
    have hRlt : (a.tmod b).natAbs < b.natAbs := by
      rw [hm]; exact Nat.mod_lt _ (by omega)
    have hcA := canonical_limbsOf (a.tdiv b).natAbs
    have hsQ : (limbsOf (a.tdiv b).natAbs).size < 2 ^ 32 := by
      simp only [BigInt.ofInt] at ha
      exact lt_of_le_of_lt (size_limbsOf_mono (by rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _))
        ha
    have hs1 : (limbsOf 1).size < 2 ^ 32 := by rw [limbsOf_one]; simp
    have hsR : (limbsOf (a.tmod b).natAbs).size < 2 ^ 32 :=
      lt_of_le_of_lt (size_limbsOf_mono hRlt.le) (by simp only [BigInt.ofInt] at hb; exact hb)
    simp only [BigInt.ofInt] at hb
    rw [show (BigInt.ofInt (a.tdiv b)).mag = limbsOf (a.tdiv b).natAbs from rfl,
      show (BigInt.ofInt (a.tmod b)).mag = limbsOf (a.tmod b).natAbs from rfl,
      show (BigInt.ofInt b).neg = decide (b < 0) from rfl, ← limbsOf_one,
      natAdd_eq hcA.1 (canonical_limbsOf 1).1 hsQ hs1, value_limbsOf, value_limbsOf,
      natSub_eq (canonical_limbsOf _).1 (canonical_limbsOf _).1 hb hsR, value_limbsOf,
      value_limbsOf, natSubSpec]
    dsimp only
    have hneg' := Int.ofNat_natAbs_of_nonpos hneg.le
    have ha0 : a < 0 := by
      by_contra h
      exact hnd (Or.inl (not_lt.mp h))
    have hemod := Int.emod_nonneg a (show b ≠ 0 by omega)
    have htd := tdiv_signed (decide (a < 0)) (decide (b < 0)) a.natAbs b.natAbs
    rw [signed_natAbs, signed_natAbs, decide_eq_true ha0] at htd
    unfold BigInt.ofInt
    refine Prod.ext ?_ ?_ <;> dsimp only <;> rw [BigInt.mk.injEq]
    · by_cases hbn : b < 0
      · rw [ite_eq_left hbn] at hq
        rw [decide_eq_true hbn] at htd
        have h0 : 0 ≤ a.tdiv b := by
          rw [htd]; unfold signed
          rw [ite_eq_right (by decide)]; exact Int.natCast_nonneg _
        have e1 := Int.natAbs_of_nonneg h0
        have e2 := Int.natAbs_of_nonneg (show 0 ≤ a / b by omega)
        refine ⟨by rw [decide_eq_true hbn]; exact (decide_eq_false (by omega)).symm, ?_⟩
        congr 1; omega
      · rw [ite_eq_right hbn] at hq
        rw [decide_eq_false hbn] at htd
        have h0 : a.tdiv b ≤ 0 := by
          rw [htd]; unfold signed
          rw [ite_eq_left (by decide)]; exact neg_nonpos.mpr (Int.natCast_nonneg _)
        have e1 := Int.ofNat_natAbs_of_nonpos h0
        have e2 := Int.ofNat_natAbs_of_nonpos (show a / b ≤ 0 by omega)
        refine ⟨by rw [decide_eq_false hbn]; exact (decide_eq_true (by omega)).symm, ?_⟩
        congr 1; omega
    · refine ⟨(decide_eq_false (not_lt.mpr hemod)).symm, ?_⟩
      have e2 := Int.natAbs_of_nonneg hemod
      have e3 := natAbs_cases b
      congr 1; omega
  · rw [ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact hc)]
    by_cases hb0 : b = 0
    · subst hb0
      rw [Int.tdiv_zero, Int.tmod_zero, Int.ediv_zero, Int.emod_zero]
    · have hnn : 0 ≤ a.tmod b := by
        by_contra h
        exact hc ⟨by omega, by omega⟩
      have hd : 0 ≤ a ∨ b ∣ a := by
        by_contra h
        push Not at h
        obtain ⟨ha0, hndvd⟩ := h
        have := tmod_signed (decide (a < 0)) (decide (b < 0)) a.natAbs b.natAbs
        rw [signed_natAbs, signed_natAbs] at this
        have hr0 : a.natAbs % b.natAbs ≠ 0 := by
          intro h0
          apply hndvd
          exact Int.dvd_iff_tmod_eq_zero.mpr (by rw [this, h0]; unfold signed; simp)
        rw [this] at hnn
        unfold signed at hnn
        rw [decide_eq_true ha0, ite_eq_left rfl] at hnn
        have : (0 : ℤ) < ((a.natAbs % b.natAbs : ℕ) : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
        linarith
      rw [@Int.tdiv_eq_ediv a b, @Int.tmod_eq_emod a b, ite_eq_left hd, ite_eq_left hd,
        Int.add_zero, Nat.cast_zero, Int.sub_zero]

theorem intTDivModChecked_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intTDivModChecked (.ofInt a) (.ofInt b) = intTDivModCheckedSpec a b := by
  unfold intTDivModChecked intTDivModCheckedSpec
  rw [show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl,
    limbsOf_beq_zero (by simp only [BigInt.ofInt] at hb; omega)]
  by_cases h0 : b = 0
  · simp [h0, BigInt.ofInt, limbsOf_zero]
  · rw [ite_eq_right (by simp [h0]), ite_eq_right h0]
    dsimp only
    rw [intTDivMod_eq ha hb]
    rfl

theorem intEDivModChecked_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intEDivModChecked (.ofInt a) (.ofInt b) = intEDivModCheckedSpec a b := by
  unfold intEDivModChecked intEDivModCheckedSpec
  rw [show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl,
    limbsOf_beq_zero (by simp only [BigInt.ofInt] at hb; omega)]
  by_cases h0 : b = 0
  · simp [h0, BigInt.ofInt, limbsOf_zero]
  · rw [ite_eq_right (by simp [h0]), ite_eq_right h0]
    dsimp only
    rw [intEDivMod_eq ha hb]
    rfl

end Library.Numerics.Bignum
