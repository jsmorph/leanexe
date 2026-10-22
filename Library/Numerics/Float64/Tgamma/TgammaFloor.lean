import Library.Numerics.Float64.Tgamma.Compiled
import LeanExe.ProofKit.F64TwoSum
import LeanExe.ProofKit.F64UpperWord
import LeanExe.ProofKit.F64Sign
import LeanExe.ProofKit.F64Magnitude

/-!
`Tgamma.roundEven` on finite inputs, and `Tgamma.floorF` on finite inputs below `2 ^ 52` in magnitude.  Below
`2 ^ 52`, `|x| + 2 ^ 52` rounds to an integer within `1/2` of the sum, because the doubles of
`[2 ^ 52, 2 ^ 53]` are the integers there, and subtracting `2 ^ 52` is exact.  From `2 ^ 52` on, `x`
is an integer.  So `roundEven x` is an integer within `1/2` of `x` (`roundEven_spec`), and
`floorF x` is `⌊x⌋` (`floorF_spec`), since the subtraction of 1 that corrects a result above `x`
is exact.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaFloor
open CodeLib.IEEE64 LeanExe.ProofKit F64RoundNearest F64TwoSum Tgamma

set_option exponentiation.threshold 4096

theorem neg_float (y : Float) (hy : Finite y.toBits) :
    Finite (-y).toBits ∧ value (-y).toBits = -value y.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite hy]
  exact F64Magnitude.negate_value _ hy

theorem abs_float (y : Float) (hy : Finite y.toBits) :
    Finite y.abs.toBits ∧ value y.abs.toBits = |value y.toBits| := by
  rw [F64Bits.toBits_abs]
  refine ⟨?_, F64UpperWord.value_abs _⟩
  obtain ⟨he, -, -⟩ := F64Sign.fields_abs y.toBits
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hy ⊢
  rw [he]
  exact hy

/-- A word for each integer of at most 53 bits. -/
theorem int_word (K : ℤ) (hK : K.natAbs ≤ 2 ^ 53) : ∃ v : UInt64, Finite v ∧ value v = K := by
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact K 1074 hK (by norm_num)
  refine ⟨_, hf, ?_⟩
  rw [value, hv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
    div_self (pow_ne_zero _ two_ne_zero), mul_one]

/-- A word of magnitude at least `2 ^ 52` is an integer. -/
theorem int_of_large (w : UInt64) (hw : Finite w) (h : 2 ^ 52 ≤ |value w|) :
    ∃ N : ℤ, value w = N := by
  have hd := rounded_dvd w (value w) (rounded_self w hw) 1073 (by norm_num)
    (by rw [show (2 : ℝ) ^ (53 + 1073) / 2 ^ 1074 = 2 ^ 52 by norm_num]; exact h)
  obtain ⟨N, hN⟩ := hd
  refine ⟨N, ?_⟩
  rw [value, hN, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, show 1073 + 1 = 1074 from rfl,
    mul_comm, mul_div_assoc, div_self (pow_ne_zero _ two_ne_zero), mul_one]

/-- The difference of two integer words of at most 53 bits is exact. -/
theorem sub_int_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (A B : ℤ)
    (hA : value a = A) (hB : value b = B) (hAB : (A - B).natAbs ≤ 2 ^ 53) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = A - B := by
  have hsa : Wasm.IEEE64.scaledValue a = A * 2 ^ 1074 := by
    have : (Wasm.IEEE64.scaledValue a : ℝ) = (A * 2 ^ 1074 : ℤ) := by
      rw [value] at hA
      push_cast
      field_simp at hA
      linarith
    exact_mod_cast this
  have hsb : Wasm.IEEE64.scaledValue b = B * 2 ^ 1074 := by
    have : (Wasm.IEEE64.scaledValue b : ℝ) = (B * 2 ^ 1074 : ℤ) := by
      rw [value] at hB
      push_cast
      field_simp at hB
      linarith
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a b ha hb (A - B) 1074
    (by rw [hsa, hsb]; ring) hAB (by norm_num)
  refine ⟨hf, ?_⟩
  rw [value, hv, hsa, hsb]
  push_cast
  field_simp
  ring

theorem two52_value : value (Float.ofBits 0x4330000000000000).toBits = 2 ^ 52 := by
  rw [F64Bits.toBits_ofBits]
  have h : Wasm.IEEE64.isNaN 0x4330000000000000 = false := by decide
  rw [h]
  show value (0x4330000000000000 : UInt64) = 2 ^ 52
  rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x4330000000000000 = 2 ^ 52 by
    decide +kernel]
  norm_num

theorem two52_finite : Finite (Float.ofBits 0x4330000000000000).toBits := by
  rw [F64Bits.toBits_ofBits]
  have h : Wasm.IEEE64.isNaN 0x4330000000000000 = false := by decide
  rw [h]
  unfold CodeLib.IEEE64.Finite
  decide

/-- `(a + 2 ^ 52) - 2 ^ 52` rounds a nonnegative `a < 2 ^ 52` to an integer within `1/2`. -/
theorem round_small (a : Float) (ha : Finite a.toBits) (h0 : 0 ≤ value a.toBits)
    (h52 : value a.toBits < 2 ^ 52) :
    let big := Float.ofBits 0x4330000000000000
    Finite ((a + big) - big).toBits ∧ (∃ R : ℤ, value ((a + big) - big).toBits = R) ∧
      |value ((a + big) - big).toBits - value a.toBits| ≤ 1 / 2 ∧
      0 ≤ value ((a + big) - big).toBits ∧ value ((a + big) - big).toBits ≤ 2 ^ 52 := by
  intro big
  have hbf := two52_finite
  have hbv := two52_value
  set S := value a.toBits + 2 ^ 52 with hS
  have hc := add_rounded a.toBits big.toBits ha hbf (by rw [hbv]; exact ne_of_gt (by positivity))
    (by rw [hbv, abs_of_pos (by positivity)]; linarith [(by norm_num : (2 : ℝ) ^ 52 + 2 ^ 52 < 2 ^ 1023)])
  rw [hbv] at hc
  set c := Wasm.IEEE64.add a.toBits big.toBits with hcdef
  have hcf : Finite c := hc.1
  -- `c` is an integer
  obtain ⟨N, hN⟩ := int_of_large c hcf (by
    have h1 := rounded_le hc (Float.ofBits 0x4330000000000000).toBits
    rw [hbv, show (2 : ℝ) ^ 52 - (value a.toBits + 2 ^ 52) = -value a.toBits by ring, abs_neg,
      abs_of_nonneg h0] at h1
    have h2 := neg_abs_le (value c - (value a.toBits + 2 ^ 52))
    have h3 := le_abs_self (value c)
    linarith)
  -- `c` lies within `1/2` of the sum
  have hhalf : |value c - S| ≤ 1 / 2 := by
    set K := ⌊S + 1 / 2⌋ with hK
    have hK1 : (K : ℝ) ≤ S + 1 / 2 := Int.floor_le _
    have hK2 : S + 1 / 2 < K + 1 := Int.lt_floor_add_one _
    have hKb : K.natAbs ≤ 2 ^ 53 := by
      have hlo : (0 : ℝ) ≤ K := by
        have : (0 : ℝ) < K + 1 := by linarith
        have : (0 : ℤ) < K + 1 := by exact_mod_cast this
        exact_mod_cast (show (0 : ℤ) ≤ K by omega)
      have hhi : (K : ℝ) < ((2 ^ 53 + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h1 : (0 : ℤ) ≤ K := by exact_mod_cast hlo
      have h2 : K < 2 ^ 53 + 1 := by exact_mod_cast hhi
      omega
    obtain ⟨v, -, hv⟩ := int_word K hKb
    have h := rounded_le hc v
    rw [hv] at h
    have : |(K : ℝ) - S| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hNr : value c = N := hN
  -- the subtraction of `2 ^ 52` is exact
  have hNb : (N - 2 ^ 52 : ℤ).natAbs ≤ 2 ^ 53 := by
    have h1 : (N : ℝ) ≤ 2 ^ 53 + 1 := by rw [← hNr]; rw [abs_le] at hhalf; linarith
    have h2 : (2 : ℝ) ^ 52 - 1 ≤ N := by rw [← hNr]; rw [abs_le] at hhalf; linarith
    have h1' : N ≤ 2 ^ 53 + 1 := by exact_mod_cast h1
    have h2' : 2 ^ 52 - 1 ≤ N := by exact_mod_cast h2
    omega
  obtain ⟨hrf, hrv⟩ := sub_int_exact c big.toBits hcf hbf N (2 ^ 52) hNr
    (by rw [hbv]; norm_num) hNb
  rw [show ((a + big) - big).toBits = Wasm.IEEE64.sub c big.toBits by
    rw [F64Bits.toBits_sub, F64Bits.toBits_add]]
  refine ⟨hrf, ⟨N - 2 ^ 52, by rw [hrv]; push_cast; ring⟩, ?_, ?_, ?_⟩
  · rw [hrv, Int.cast_pow, Int.cast_ofNat, ← hNr,
      show value c - 2 ^ 52 - value a.toBits = value c - S by rw [hS]; ring]
    exact hhalf
  · rw [hrv]
    push_cast
    rw [← hNr]
    rw [abs_le] at hhalf
    -- `N` is an integer above `2 ^ 52 - 1/2`
    have : (2 : ℝ) ^ 52 - 1 / 2 ≤ value c := by linarith
    have h3 : (2 : ℤ) ^ 52 ≤ N := by
      have h4 : (2 : ℝ) ^ 52 - 1 < N := by rw [← hNr]; linarith
      have h5 : (2 : ℤ) ^ 52 - 1 < N := by exact_mod_cast h4
      omega
    have h6 : ((2 : ℤ) ^ 52 : ℝ) ≤ N := by exact_mod_cast h3
    push_cast at h6
    rw [hNr]
    linarith
  · rw [hrv]
    push_cast
    rw [← hNr]
    rw [abs_le] at hhalf
    have h3 : N ≤ (2 : ℤ) ^ 53 := by
      have h4 : (N : ℝ) < 2 ^ 53 + 1 := by rw [← hNr]; linarith
      have h5 : N < (2 : ℤ) ^ 53 + 1 := by exact_mod_cast h4
      omega
    have h6 : (N : ℝ) ≤ ((2 : ℤ) ^ 53 : ℝ) := by exact_mod_cast h3
    push_cast at h6
    rw [hNr]
    linarith

/-- **`roundEven`** of a finite `x` is an integer within `1/2` of `x`. -/
theorem roundEven_spec (x : Float) (hx : Finite x.toBits) :
    Finite (roundEven x).toBits ∧ (∃ R : ℤ, value (roundEven x).toBits = R) ∧
      |value (roundEven x).toBits - value x.toBits| ≤ 1 / 2 ∧
      |value (roundEven x).toBits| ≤ |value x.toBits| + 1 / 2 := by
  obtain ⟨haf, hav⟩ := abs_float x hx
  -- the rounded magnitude
  have hr : Finite (if x.abs < Float.ofBits 0x4330000000000000 then
        (x.abs + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000
      else x.abs).toBits ∧
      (∃ R : ℤ, value (if x.abs < Float.ofBits 0x4330000000000000 then
        (x.abs + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000
      else x.abs).toBits = R) ∧
      abs (value (if x.abs < Float.ofBits 0x4330000000000000 then
        (x.abs + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000
      else x.abs).toBits - |value x.toBits|) ≤ 1 / 2 ∧
      0 ≤ value (if x.abs < Float.ofBits 0x4330000000000000 then
        (x.abs + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000
      else x.abs).toBits := by
    by_cases hlt : x.abs < Float.ofBits 0x4330000000000000
    · rw [ite_eq_left hlt]
      have hlt' := (F64UpperWord.float_lt_iff _ _ haf two52_finite).mp hlt
      rw [hav, two52_value] at hlt'
      obtain ⟨h1, h2, h3, h4, -⟩ := round_small x.abs haf (by rw [hav]; exact abs_nonneg _)
        (by rw [hav]; exact hlt')
      rw [hav] at h3
      exact ⟨h1, h2, h3, h4⟩
    · rw [ite_eq_right hlt]
      have hge : 2 ^ 52 ≤ |value x.toBits| := by
        have := (not_congr (F64UpperWord.float_lt_iff _ _ haf two52_finite)).mp hlt
        rw [hav, two52_value] at this
        linarith
      obtain ⟨N, hN⟩ := int_of_large x.abs.toBits haf (by rw [hav, abs_abs]; exact hge)
      exact ⟨haf, ⟨N, hN⟩, by rw [hav]; simp, by rw [hav]; exact abs_nonneg _⟩
  obtain ⟨hrf, ⟨R, hR⟩, hrd, hr0⟩ := hr
  unfold roundEven
  simp only []
  by_cases hs : x.toBits >>> 63 == 1
  · rw [ite_eq_left hs]
    obtain ⟨hnf, hnv⟩ := neg_float _ hrf
    have hneg : value x.toBits ≤ 0 := by
      have hsign : Wasm.IEEE64.sign x.toBits = true := by
        simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
        have := x.toBits.toNat_lt
        rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight] at hs
        simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hs
        omega
      exact value_nonpos_of_sign _ hsign
    refine ⟨hnf, ⟨-R, by rw [hnv, hR]; push_cast; ring⟩, ?_, ?_⟩
    · rw [abs_of_nonpos hneg] at hrd
      rw [hnv]
      rw [show ∀ u v : ℝ, -u - v = -(u - -v) from fun u v => by ring, abs_neg]
      exact hrd
    · rw [hnv, abs_neg, abs_of_nonneg hr0]
      rw [abs_le] at hrd
      linarith [abs_nonneg (value x.toBits)]
  · rw [ite_eq_right hs]
    have hpos : 0 ≤ value x.toBits := by
      have hsign : Wasm.IEEE64.sign x.toBits = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
        have := x.toBits.toNat_lt
        rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight] at hs
        simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hs
        omega
      exact value_nonneg_of_sign _ hsign
    rw [abs_of_nonneg hpos] at hrd ⊢
    refine ⟨hrf, ⟨R, hR⟩, hrd, ?_⟩
    rw [abs_of_nonneg hr0]
    rw [abs_le] at hrd
    linarith

/-- **`floorF`** of a finite `x` below `2 ^ 52` is `⌊x⌋`. -/
theorem floorF_spec (x : Float) (hx : Finite x.toBits) (hlim : |value x.toBits| < 2 ^ 52) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = ⌊value x.toBits⌋ := by
  obtain ⟨hrf, ⟨R, hR⟩, hrd, hrb⟩ := roundEven_spec x hx
  unfold floorF
  simp only []
  have hone : value (1.0 : Float).toBits = 1 := by
    rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl, ← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]
    norm_num
  have honef : Finite (1.0 : Float).toBits := by
    rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
    unfold CodeLib.IEEE64.Finite
    decide
  by_cases hgt : roundEven x > x
  · rw [ite_eq_left hgt]
    have hgt' := (F64UpperWord.float_lt_iff _ _ hx hrf).mp hgt
    have hRb : (R - 1).natAbs ≤ 2 ^ 53 := by
      have h1 : (R : ℝ) ≤ 2 ^ 52 + 1 := by
        rw [← hR]; linarith [le_abs_self (value (roundEven x).toBits)]
      have h2 : -(2 : ℝ) ^ 52 - 1 ≤ R := by
        rw [← hR]; linarith [neg_abs_le (value (roundEven x).toBits)]
      have h1' : R ≤ 2 ^ 52 + 1 := by exact_mod_cast h1
      have h2' : -2 ^ 52 - 1 ≤ R := by exact_mod_cast h2
      omega
    obtain ⟨hf, hv⟩ := sub_int_exact _ _ hrf honef R 1 hR (by rw [hone]; norm_num) hRb
    rw [F64Bits.toBits_sub]
    refine ⟨hf, ?_⟩
    have : ⌊value x.toBits⌋ = R - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      rw [← hR]
      rw [abs_le] at hrd
      constructor <;> linarith
    rw [hv, this]
    push_cast
    ring
  · rw [ite_eq_right hgt]
    have hle : value (roundEven x).toBits ≤ value x.toBits := by
      have := (not_congr (F64UpperWord.float_lt_iff _ _ hx hrf)).mp hgt
      linarith
    refine ⟨hrf, ?_⟩
    rw [hR]
    have : ⌊value x.toBits⌋ = R := by
      rw [Int.floor_eq_iff]
      rw [← hR]
      rw [abs_le] at hrd
      constructor <;> linarith
    rw [this]

#print axioms roundEven_spec
#print axioms floorF_spec

end Library.Numerics.Float64.Tgamma.TgammaFloor
