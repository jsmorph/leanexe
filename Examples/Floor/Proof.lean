import Examples.Floor.Program
import Examples.Floor.Spec

/-! The programs meet their specifications.  `floorDiv_spec` follows from Lean's truncating
quotient and remainder (`Int64.toInt_div_of_ne_left`, `Int64.toInt_mod`) and `Int.fdiv_eq_tdiv`,
which corrects the truncating quotient by one exactly when the divisor does not divide the dividend
and their signs differ.  The corrected quotient does not wrap, since a divisor that does not divide
has magnitude at least 2.  `average_spec` follows from `add_eq_xor_add_and`, `u + v = (u ^^^ v) +
2 (u &&& v)` on the words' natural numbers, and a case split on the operands' sign bits, which
give the sign bits of the conjunction and the exclusive or.  `clamp_spec` follows from `toInt_min`
and `toInt_max`, which hold because `Int64`'s order is the order of the integers. -/

namespace Examples.Floor

/-- A sum of two numbers is their exclusive or plus twice their conjunction. -/
theorem add_eq_xor_add_and (u v : Nat) : u + v = (u ^^^ v) + 2 * (u &&& v) := by
  induction u using Nat.strongRecOn generalizing v with
  | _ u ih =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · simp
    · have h := ih (u / 2) (by omega) (v / 2)
      rw [← Nat.xor_div_two, ← Nat.and_div_two] at h
      have hx := Nat.div_add_mod (u ^^^ v) 2
      have ha := Nat.div_add_mod (u &&& v) 2
      have hu2 := Nat.div_add_mod u 2
      have hv2 := Nat.div_add_mod v 2
      have hxm := @Nat.xor_mod_two_eq_one u v
      have ham := @Nat.and_mod_two_eq_one u v
      rcases Nat.mod_two_eq_zero_or_one u with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;>
        rcases Nat.mod_two_eq_zero_or_one (u ^^^ v) with h3 | h3 <;>
        rcases Nat.mod_two_eq_zero_or_one (u &&& v) with h4 | h4 <;>
        simp_all <;> omega

/-- `average` computes the floor of the mean on every pair. -/
theorem average_spec (a b : Int64) : (average a b).toInt = expectedAverage a b := by
  rw [expectedAverage, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have h1 : ((1 : Int64).toBitVec.smod 64).toNat = 1 := by decide
  show ((a.toBitVec &&& b.toBitVec) + (a.toBitVec ^^^ b.toBitVec).sshiftRight'
    ((1 : Int64).toBitVec.smod 64)).toInt = (a.toBitVec.toInt + b.toBitVec.toInt) / 2
  rw [BitVec.sshiftRight_eq', h1]
  generalize a.toBitVec = x
  generalize b.toBitVec = y
  have hu := x.isLt
  have hv := y.isLt
  have hsum := add_eq_xor_add_and x.toNat y.toNat
  have hk : (x &&& y).toNat = x.toNat &&& y.toNat := BitVec.toNat_and x y
  have hw : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := BitVec.toNat_xor x y
  have hkl := (x &&& y).isLt
  have hwl := (x ^^^ y).isLt
  have mk : (x &&& y).msb = (x.msb && y.msb) := BitVec.msb_and
  have mw : (x ^^^ y).msb = (x.msb ^^ y.msb) := BitVec.msb_xor
  rw [BitVec.toInt_add, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow,
    BitVec.toInt_eq_msb_cond x, BitVec.toInt_eq_msb_cond y, BitVec.toInt_eq_msb_cond (x &&& y),
    BitVec.toInt_eq_msb_cond (x ^^^ y), mk, mw, hk, hw]
  rw [hk] at hkl
  rw [hw] at hwl
  have ck := BitVec.msb_eq_decide (x &&& y)
  have cw := BitVec.msb_eq_decide (x ^^^ y)
  rw [mk, hk] at ck
  rw [mw, hw] at cw
  cases hx : x.msb <;> cases hy : y.msb <;>
    simp only [hx, hy, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false,
      Bool.not_true, ite_true, ite_false, Bool.false_eq_true] at ck cw ⊢ <;>
    have px := BitVec.msb_eq_decide x <;> have py := BitVec.msb_eq_decide y <;>
    simp only [hx, hy] at px py <;>
    simp only [Nat.add_one_sub_one, Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not,
      Nat.not_le, eq_comm (a := true), eq_comm (a := false)] at px py ck cw <;>
    rw [Int.bmod_eq_of_le (by simp only [Nat.reducePow, Nat.reduceDiv]; omega)
      (by simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceAdd]; omega)] <;>
    omega

/-- `floorDiv` computes the floor quotient for every nonzero divisor, except `minValue` by -1,
whose floor quotient `2 ^ 63` lies outside `Int64`. -/
theorem floorDiv_spec (a b : Int64) (hb : b ≠ 0) (ho : ¬(a = Int64.minValue ∧ b = -1)) :
    (floorDiv a b).toInt = expectedDiv a b := by
  have hA1 := a.toInt_lt
  have hA2 := a.le_toInt
  have hB1 := b.toInt_lt
  have hB2 := b.le_toInt
  have hB : b.toInt ≠ 0 := fun h => hb (Int64.toInt_inj.mp (by rw [h]; rfl))
  have hq : (a / b).toInt = a.toInt.tdiv b.toInt := by
    by_cases ha : a = Int64.minValue
    · exact Int64.toInt_div_of_ne_right a b (fun h => ho ⟨ha, h⟩)
    · exact Int64.toInt_div_of_ne_left a b ha
  have hr : (a % b).toInt = a.toInt.tmod b.toInt := Int64.toInt_mod a b
  have hz : ((a % b != 0) = true) ↔ ¬ (b.toInt ∣ a.toInt) := by
    rw [Int.dvd_iff_tmod_eq_zero, ← hr, bne_iff_ne, ne_eq, ← Int64.toInt_inj, Int64.toInt_zero]
  have hla : (decide (a < 0) = true) ↔ a.toInt < 0 := by
    simp [Int64.lt_iff_toInt_lt, Int64.toInt_zero]
  have hlb : (decide (b < 0) = true) ↔ b.toInt < 0 := by
    simp [Int64.lt_iff_toInt_lt, Int64.toInt_zero]
  have hnat := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
  rw [expectedDiv, Int.fdiv_eq_tdiv, ← hq]
  unfold floorDiv
  simp only []
  by_cases hd : b.toInt ∣ a.toInt
  · have hc : (a % b != 0) = false := by
      cases h : (a % b != 0) with
      | false => rfl
      | true => exact absurd hd (hz.mp h)
    simp [hc, hd]
  · have hc : (a % b != 0) = true := by
      cases h : (a % b != 0) with
      | false => exact absurd (hz.mpr hd) (by rw [h]; decide)
      | true => rfl
    have h2 : 2 ≤ b.toInt.natAbs := by
      rcases Nat.lt_or_ge b.toInt.natAbs 2 with h | h
      · exfalso
        apply hd
        have : b.toInt.natAbs = 1 := by omega
        rcases Int.natAbs_eq b.toInt with e | e <;> rw [this] at e <;> rw [e] <;> simp
      · exact h
    have hdl : a.toInt.natAbs / b.toInt.natAbs ≤ a.toInt.natAbs / 2 :=
      Nat.div_le_div_left h2 (by decide)
    have hqa : (a / b).toInt.natAbs = a.toInt.natAbs / b.toInt.natAbs := by
      rw [hq]; exact Int.natAbs_tdiv a.toInt b.toInt
    have hqb1 := (a / b).toInt_lt
    have hqb2 := (a / b).le_toInt
    have hqne : -2 ^ 63 < (a / b).toInt := by
      rcases Int.natAbs_eq (a / b).toInt with e | e <;> omega
    have hs : ((a / b) - 1).toInt = (a / b).toInt - 1 := by
      rw [Int64.toInt_sub, Int64.toInt_one]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    by_cases hsa : a.toInt < 0 <;> by_cases hsb : b.toInt < 0
    · have hla' : decide (a < 0) = true := by simpa using hla.mpr hsa
      have hlb' : decide (b < 0) = true := by simpa using hlb.mpr hsb
      simp [hc, hla', hlb', hd, Int.sign_eq_neg_one_of_neg hsb]
      omega
    · have hla' : decide (a < 0) = true := by simpa using hla.mpr hsa
      have hlb' : decide (b < 0) = false := by
        cases h : decide (b < 0) with
        | false => rfl
        | true => exact absurd (hlb.mp h) hsb
      simp [hc, hla', hlb', hd, hs, Int.sign_eq_one_of_pos (by omega : 0 < b.toInt)]
      omega
    · have hla' : decide (a < 0) = false := by
        cases h : decide (a < 0) with
        | false => rfl
        | true => exact absurd (hla.mp h) hsa
      have hlb' : decide (b < 0) = true := by simpa using hlb.mpr hsb
      simp [hc, hla', hlb', hd, hs]
      omega
    · have hla' : decide (a < 0) = false := by
        cases h : decide (a < 0) with
        | false => rfl
        | true => exact absurd (hla.mp h) hsa
      have hlb' : decide (b < 0) = false := by
        cases h : decide (b < 0) with
        | false => rfl
        | true => exact absurd (hlb.mp h) hsb
      simp [hc, hla', hlb', hd]
      omega

theorem toInt_min (a b : Int64) : (min a b).toInt = min a.toInt b.toInt := by
  show (if a ≤ b then a else b).toInt = _
  by_cases h : a ≤ b
  · have h' := Int64.le_iff_toInt_le.mp h
    simp only [h, ↓reduceIte]
    omega
  · have h' : ¬a.toInt ≤ b.toInt := fun h'' => h (Int64.le_iff_toInt_le.mpr h'')
    simp only [h, ↓reduceIte]
    omega

theorem toInt_max (a b : Int64) : (max a b).toInt = max a.toInt b.toInt := by
  show (if a ≤ b then b else a).toInt = _
  by_cases h : a ≤ b
  · have h' := Int64.le_iff_toInt_le.mp h
    simp only [h, ↓reduceIte]
    omega
  · have h' : ¬a.toInt ≤ b.toInt := fun h'' => h (Int64.le_iff_toInt_le.mpr h'')
    simp only [h, ↓reduceIte]
    omega

/-- `clamp` bounds the value by the interval on every triple. -/
theorem clamp_spec (x lo hi : Int64) : (clamp x lo hi).toInt = expectedClamp x lo hi := by
  rw [clamp, expectedClamp, toInt_max, toInt_min]

end Examples.Floor
