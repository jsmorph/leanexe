import Library.Numerics.Float64.Tgamma.TgammaRefl3

/-!
The word operations of the path of `tgammaWith` below `-170`.  `and_high` and `and_low` compute the
masks `0xFFF0000000000000` and `0x800FFFFFFFFFFFFF` on natural numbers bit by bit.  `field_eq` reads
the exponent field as the code does, `nonPositive_sub` decides `re - e ≤ 0`, `scale_down` subtracts
`E` from the exponent field of a normal word of either sign, `th_value` builds `±2 ^ (E - 1022)`
with the sign of `rh`, and `mask_value` gives the value of a word in the binade of `2 ^ (E - 1022)`
with its exponent field cleared: `(ub - th)/2 ^ E`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaBits
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

theorem and_high (a : ℕ) (ha : a < 2 ^ 64) : a &&& 0xFFF0000000000000 = a / 2 ^ 52 * 2 ^ 52 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (0xFFF0000000000000 : ℕ) = (2 ^ 12 - 1) * 2 ^ 52 by norm_num,
    Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : 52 ≤ i
  · simp only [h1, decide_true, Bool.true_and]
    rw [show i - 52 + 52 = i by omega]
    by_cases h2 : i - 52 < 12
    · simp [h2]
    · simp only [h2, decide_false, Bool.and_false]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
        (by omega)))).symm
  · simp [h1]

theorem and_low (a : ℕ) (ha : a < 2 ^ 64) :
    a &&& 0x800FFFFFFFFFFFFF = 2 ^ 63 * (a / 2 ^ 63) + a % 2 ^ 52 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hr : a % 2 ^ 52 < 2 ^ 63 := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hr,
    show (0x800FFFFFFFFFFFFF : ℕ) = 2 ^ 63 * 1 + (2 ^ 52 - 1) by norm_num,
    Nat.testBit_two_pow_mul_add _ (by norm_num : (2 : ℕ) ^ 52 - 1 < 2 ^ 63),
    Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h1 : i < 63
  · simp only [h1, ite_true]
    by_cases h2 : i < 52
    · simp [h2]
    · simp [h2]
  · simp only [h1, ite_false]
    rw [show i - 63 + 63 = i by omega]
    by_cases h3 : i = 63
    · subst h3; simp
    · have h4 : a.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [h4]
      simp

theorem field_eq (w : UInt64) :
    (w >>> 52) &&& 0x7ff = UInt64.ofNat (Wasm.IEEE64.exponent w) := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hlt : Wasm.IEEE64.exponent w < 2048 := Nat.mod_lt _ (by norm_num)
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' (by omega)]
  show w.toNat >>> (52 % 64) &&& 2047 = Wasm.IEEE64.exponent w
  rw [show 52 % 64 = 52 from rfl, Nat.shiftRight_eq_div_pow, show (2047 : ℕ) = 2 ^ 11 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- `nonPositive (a - b)` for small `a` and `b` is `a ≤ b`. -/
theorem nonPositive_sub (a b : ℕ) (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) :
    nonPositive (UInt64.ofNat a - UInt64.ofNat b) = decide (a ≤ b) := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hta : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (by omega)
  have htb : (UInt64.ofNat b).toNat = b := UInt64.toNat_ofNat_of_lt' (by omega)
  have hsub : (UInt64.ofNat a - UInt64.ofNat b).toNat = (2 ^ 64 - b + a) % 2 ^ 64 := by
    rw [UInt64.toNat_sub, hta, htb]
  unfold nonPositive
  by_cases h : a ≤ b
  · rw [decide_eq_true h]
    rcases h.lt_or_eq with hlt | heq
    · have h63 : ((UInt64.ofNat a - UInt64.ofNat b) >>> 63 == 1) = true := by
        rw [beq_iff_eq]
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftRight, hsub]
        show ((2 ^ 64 - b + a) % 2 ^ 64) >>> (63 % 64) = 1
        rw [show 63 % 64 = 63 from rfl, Nat.shiftRight_eq_div_pow]
        omega
      rw [h63, Bool.or_true]
    · subst heq
      simp
  · rw [decide_eq_false h]
    have h0 : (UInt64.ofNat a - UInt64.ofNat b == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      have := congrArg UInt64.toNat he
      rw [hsub] at this
      simp only [UInt64.toNat_zero] at this
      omega
    have h63 : ((UInt64.ofNat a - UInt64.ofNat b) >>> 63 == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      have := congrArg UInt64.toNat he
      rw [UInt64.toNat_shiftRight, hsub] at this
      change ((2 ^ 64 - b + a) % 2 ^ 64) >>> (63 % 64) = 1 at this
      rw [show 63 % 64 = 63 from rfl, Nat.shiftRight_eq_div_pow] at this
      omega
    rw [h0, h63]
    rfl

/-- The value of a normal word from its fields. -/
theorem value_normal (w : UInt64) (h1 : 1 ≤ Wasm.IEEE64.exponent w) :
    value w = (if Wasm.IEEE64.sign w then -1 else 1) *
      ((2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) / 2 ^ 1074 : ℝ) := by
  rw [TgammaTop.value_sign]
  simp only [Wasm.IEEE64.scaledMagnitude]
  have h2 : (Wasm.IEEE64.exponent w == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  rw [h2]
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> push_cast <;> ring

/-- The value of a word with a zero exponent field. -/
theorem value_sub (w : UInt64) (h0 : Wasm.IEEE64.exponent w = 0) :
    value w = (if Wasm.IEEE64.sign w then -1 else 1) * ((Wasm.IEEE64.fraction w : ℝ) / 2 ^ 1074) := by
  rw [TgammaTop.value_sign]
  simp only [Wasm.IEEE64.scaledMagnitude, h0, beq_self_eq_true, ite_true]
  split_ifs <;> ring

/-- **Subtracting `E` from the exponent field** of a normal word divides its value by `2 ^ E`. -/
theorem scale_down (w : UInt64) (E : ℕ) (hf : Finite w) (hE : E + 1 ≤ Wasm.IEEE64.exponent w) :
    Finite (w - (UInt64.ofNat E <<< 52)) ∧
      value (w - (UInt64.ofNat E <<< 52)) * 2 ^ E = value w := by
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hw := w.toNat_lt
  have hexp : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  have hfin : Wasm.IEEE64.exponent w ≠ 2047 := by
    have h := hf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    exact h
  have hshift : (UInt64.ofNat E <<< 52).toNat = E * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (by omega)]
    have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [h52, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hle : E * 2 ^ 52 ≤ w.toNat := by omega
  have hsub : (w - (UInt64.ofNat E <<< 52)).toNat = w.toNat - E * 2 ^ 52 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hshift]; exact hle), hshift]
  have hex : Wasm.IEEE64.exponent (w - (UInt64.ofNat E <<< 52)) =
      Wasm.IEEE64.exponent w - E := by
    unfold Wasm.IEEE64.exponent
    rw [hsub]
    omega
  have hfr : Wasm.IEEE64.fraction (w - (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.fraction w := by
    unfold Wasm.IEEE64.fraction
    rw [hsub]
    omega
  have hsg : Wasm.IEEE64.sign (w - (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.sign w := by
    unfold Wasm.IEEE64.sign
    rw [hsub]
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  refine ⟨?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hex]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [value_normal _ (by rw [hex]; omega), value_normal _ (by omega), hex, hfr, hsg,
      show Wasm.IEEE64.exponent w - 1 = (Wasm.IEEE64.exponent w - E - 1) + E by omega, pow_add]
    ring

/-- **`th`** from the word `w` of `rh` with exponent field `re ≤ E`: the sign of `w`, the exponent
field `E + 1`, and a zero fraction. -/
theorem th_fields (w : UInt64) (E : ℕ) (hre : Wasm.IEEE64.exponent w ≤ E) (hE : E ≤ 2045) :
    Wasm.IEEE64.sign ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
        0xFFF0000000000000) = Wasm.IEEE64.sign w ∧
      Wasm.IEEE64.exponent ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<<
        52)) &&& 0xFFF0000000000000) = E + 1 ∧
      Wasm.IEEE64.fraction ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<<
        52)) &&& 0xFFF0000000000000) = 0 := by
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hw := w.toNat_lt
  have hexp : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  have hk : (UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1).toNat =
      E - Wasm.IEEE64.exponent w + 1 := by
    have ha : (UInt64.ofNat E).toNat = E := UInt64.toNat_ofNat_of_lt' (by omega)
    have hb : (UInt64.ofNat (Wasm.IEEE64.exponent w)).toNat = Wasm.IEEE64.exponent w :=
      UInt64.toNat_ofNat_of_lt' (by omega)
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, ha, hb]; omega),
      ha, hb]
    show (E - Wasm.IEEE64.exponent w + 1) % 2 ^ 64 = E - Wasm.IEEE64.exponent w + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hshift : ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52).toNat =
      (E - Wasm.IEEE64.exponent w + 1) * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, hk]
    have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [h52, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)).toNat =
      w.toNat + (E - Wasm.IEEE64.exponent w + 1) * 2 ^ 52 := by
    rw [UInt64.toNat_add, hshift]
    exact Nat.mod_eq_of_lt (by omega)
  have hmask : ((w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
      0xFFF0000000000000).toNat =
      (w.toNat + (E - Wasm.IEEE64.exponent w + 1) * 2 ^ 52) / 2 ^ 52 * 2 ^ 52 := by
    rw [UInt64.toNat_and, hsum]
    exact and_high _ (by omega)
  generalize (w + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
    0xFFF0000000000000 = T at hmask ⊢
  refine ⟨?_, ?_, ?_⟩
  · unfold Wasm.IEEE64.sign
    rw [hmask]
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  · unfold Wasm.IEEE64.exponent
    rw [hmask]
    omega
  · unfold Wasm.IEEE64.fraction
    rw [hmask]
    omega

/-- The fields of a word with its exponent field cleared. -/
theorem mask_fields (w : UInt64) :
    Wasm.IEEE64.sign (w &&& 0x800FFFFFFFFFFFFF) = Wasm.IEEE64.sign w ∧
      Wasm.IEEE64.exponent (w &&& 0x800FFFFFFFFFFFFF) = 0 ∧
      Wasm.IEEE64.fraction (w &&& 0x800FFFFFFFFFFFFF) = Wasm.IEEE64.fraction w := by
  have hw := w.toNat_lt
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hmask : (w &&& 0x800FFFFFFFFFFFFF).toNat = 2 ^ 63 * (w.toNat / 2 ^ 63) + w.toNat % 2 ^ 52 := by
    rw [UInt64.toNat_and]
    exact and_low _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold Wasm.IEEE64.sign
    rw [hmask]
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  · unfold Wasm.IEEE64.exponent
    rw [hmask]
    omega
  · unfold Wasm.IEEE64.fraction
    rw [hmask]
    omega

#print axioms and_high
#print axioms and_low
#print axioms nonPositive_sub
#print axioms scale_down
#print axioms th_fields
#print axioms mask_fields

end Library.Numerics.Float64.Tgamma.TgammaBits
