import Verified.Examples.TanTrunc
import Verified.Examples.TanStep
import Verified.Examples.Sinpi

/-!
`Sinpi.toSingle` on words.  For a positive normal word, the low 29 bits of the fraction are
rounded away, ties to even, with a carry into the exponent field when the fraction overflows.  The
result is a finite word whose magnitude has at most 24 significant bits, within `2 ^ -24` of the
word relative to its value.
-/

namespace Verified.Examples.SinpiSingle

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanStep

/-- `Sinpi.toSingle` on words. -/
def singleW (b : UInt64) : UInt64 :=
  let low := b &&& 0x1FFFFFFF
  let base := b - low
  if low > 0x10000000 || (low == 0x10000000 && base &&& 0x20000000 != 0) then
    base + 0x20000000
  else base

theorem toSingle_bits (x : Float) : (Sinpi.toSingle x).toBits = canon (singleW x.toBits) := by
  unfold Sinpi.toSingle singleW canon
  simp only [toBits_ite, F64Bits.toBits_ofBits]
  split_ifs <;> rfl

theorem low_mask (n : Nat) : n &&& 0x1FFFFFFF = n % 2 ^ 29 :=
  Nat.and_two_pow_sub_one_eq_mod n 29

/-- The rounding of a positive normal word: the result is `e 2 ^ 52 + j` with `j` a multiple of
`2 ^ 29` within `2 ^ 28` of the fraction `f`. -/
theorem single_toNat (b : UInt64) (hs : b.toNat < 2 ^ 63) :
    ∃ j : Nat, (singleW b).toNat = Wasm.IEEE64.exponent b * 2 ^ 52 + j ∧ j % 2 ^ 29 = 0 ∧
      j ≤ 2 ^ 52 ∧ j ≤ Wasm.IEEE64.fraction b + 2 ^ 28 ∧ Wasm.IEEE64.fraction b ≤ j + 2 ^ 28 := by
  have hb : b.toNat = Wasm.IEEE64.exponent b * 2 ^ 52 + Wasm.IEEE64.fraction b := by
    unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
    omega
  have hf : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  set f := Wasm.IEEE64.fraction b with hfdef
  set e := Wasm.IEEE64.exponent b with hedef
  have hlow : (b &&& 0x1FFFFFFF).toNat = f % 2 ^ 29 := by
    rw [UInt64.toNat_and, show (0x1FFFFFFF : UInt64).toNat = 0x1FFFFFFF from rfl, low_mask, hb]
    omega
  have hbase : (b - (b &&& 0x1FFFFFFF)).toNat = e * 2 ^ 52 + (f - f % 2 ^ 29) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hlow]; omega), hlow, hb]
    omega
  have hm := Nat.mod_lt f (show 0 < 2 ^ 29 by positivity)
  have hdiv : (f - f % 2 ^ 29) % 2 ^ 29 = 0 := by omega
  unfold singleW
  dsimp only
  split_ifs with hc
  · refine ⟨f - f % 2 ^ 29 + 2 ^ 29, ?_, by omega, by omega, ?_, by omega⟩
    · rw [UInt64.toNat_add, hbase, show (0x20000000 : UInt64).toNat = 2 ^ 29 from rfl,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
        ne_eq, UInt64.lt_iff_toNat_lt, hlow, show (0x10000000 : UInt64).toNat = 2 ^ 28 from rfl]
        at hc
      rcases hc with hc | ⟨hc, -⟩
      · omega
      · have : f % 2 ^ 29 = 2 ^ 28 := by
          have := congrArg UInt64.toNat hc
          rw [hlow] at this
          exact this
        omega
  · refine ⟨f - f % 2 ^ 29, hbase, hdiv, by omega, by omega, ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq, UInt64.lt_iff_toNat_lt, hlow, show (0x10000000 : UInt64).toNat = 2 ^ 28 from rfl,
      not_or, not_lt] at hc
    omega

theorem word_of (b : UInt64) (hs : b.toNat < 2 ^ 63) :
    b = UInt64.ofNat (Wasm.IEEE64.exponent b * 2 ^ 52 + Wasm.IEEE64.fraction b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
    omega)]
  unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  omega

/-- The rounded word: finite, positive, within `2 ^ -24` of the word relative to its value, and
with a magnitude of at most 24 significant bits. -/
theorem single_spec (b : UInt64) (hs : b.toNat < 2 ^ 63) (he1 : 1 ≤ Wasm.IEEE64.exponent b)
    (he2 : Wasm.IEEE64.exponent b ≤ 2044) :
    Finite (singleW b) ∧ (singleW b).toNat < 2 ^ 63 ∧
      |value (singleW b) - value b| ≤ value b / 2 ^ 24 ∧
      ∃ m : Nat, Wasm.IEEE64.scaledMagnitude (singleW b) =
        m * 2 ^ (Wasm.IEEE64.exponent b - 1 + 29) ∧ m ≤ 2 ^ 24 := by
  obtain ⟨j, hj, hj29, hj52, hj1, hj2⟩ := single_toNat b hs
  have hwb := word_of b hs
  have hf : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  generalize hsw : singleW b = w at *
  generalize he : Wasm.IEEE64.exponent b = e at *
  generalize hfd : Wasm.IEEE64.fraction b = f at *
  have hw : w = UInt64.ofNat (e * 2 ^ 52 + j) := by
    apply UInt64.toNat_inj.mp
    rw [hj, UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
  obtain ⟨hv, hfin, h63⟩ := word_value e j he1 (by omega) hj52
  obtain ⟨hvb, -, -⟩ := word_value e f he1 (by omega) hf.le
  rw [← hwb] at hvb
  rw [← hw] at hv hfin h63
  refine ⟨hfin, h63, ?_, ?_⟩
  · rw [hv, hvb]
    have hS := S_pos e
    have hB : B e = 2 ^ 52 * S e := B_eq e he1
    have hd : |(j : ℝ) - f| ≤ 2 ^ 28 := by
      rw [abs_le]
      constructor
      · have : (f : ℝ) ≤ j + 2 ^ 28 := by exact_mod_cast hj2
        linarith
      · have : (j : ℝ) ≤ f + 2 ^ 28 := by exact_mod_cast hj1
        linarith
    have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
    rw [show B e + j * S e - (B e + f * S e) = ((j : ℝ) - f) * S e by ring, abs_mul,
      abs_of_pos hS]
    have : |(j : ℝ) - f| * S e ≤ 2 ^ 28 * S e := mul_le_mul_of_nonneg_right hd hS.le
    have : f * S e ≥ 0 := mul_nonneg hf0 hS.le
    rw [hB]
    linarith
  · by_cases hj' : j < 2 ^ 52
    · refine ⟨2 ^ 23 + j / 2 ^ 29, ?_, by omega⟩
      have hex : Wasm.IEEE64.exponent w = e := by
        unfold Wasm.IEEE64.exponent; rw [hj]; omega
      have hfr : Wasm.IEEE64.fraction w = j := by
        unfold Wasm.IEEE64.fraction; rw [hj]; omega
      simp only [Wasm.IEEE64.scaledMagnitude, hex, hfr, show (e == 0) = false by
        simp; omega, Bool.false_eq_true, ite_false]
      rw [pow_add, mul_comm (2 ^ (e - 1)) (2 ^ 29), ← mul_assoc]
      congr 1
      omega
    · refine ⟨2 ^ 24, ?_, le_refl _⟩
      have hj52' : j = 2 ^ 52 := by omega
      have hex : Wasm.IEEE64.exponent w = e + 1 := by
        unfold Wasm.IEEE64.exponent; rw [hj]; omega
      have hfr : Wasm.IEEE64.fraction w = 0 := by
        unfold Wasm.IEEE64.fraction; rw [hj]; omega
      simp only [Wasm.IEEE64.scaledMagnitude, hex, hfr, show (e + 1 == 0) = false by
        simp, Bool.false_eq_true, ite_false, add_zero]
      rw [show e + 1 - 1 = e by omega, ← pow_add, ← pow_add]
      congr 1
      omega

#print axioms single_spec

end Verified.Examples.SinpiSingle
