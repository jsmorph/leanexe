import Verified.Examples.Expm1PathsEdge
import Verified.Examples.Expm1Branches
import LeanExe.ProofKit.F64RoundScaled

/-!
`Tanh.expm1` lies within one step of `exp x - 1` on every finite input, with overflow to positive
infinity included, and gives the exceptional results of fdlibm on zeros, infinities, and NaNs.
The proof selects the branch with `Expm1Branches`, converts the Float operations of the branch to
words, and applies the path theorems of `Expm1PathsReduced` and `Expm1PathsEdge`.
-/

namespace Verified.Examples.Expm1Theorem
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1ReduceConst Expm1PathsReduced
  Expm1PathsEdge

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem word_ge (a : ℚ) (w : UInt64) (h : a ≤ PolyBound.ratOfWord w) : (a : ℝ) ≤ value w := by
  rw [← PolyBound.ratOfWord_cast]; exact_mod_cast h

theorem word_le (a : ℚ) (w : UInt64) (h : PolyBound.ratOfWord w ≤ a) : value w ≤ (a : ℝ) := by
  rw [← PolyBound.ratOfWord_cast]; exact_mod_cast h

theorem high_ge (w : UInt64) (C : Nat) (hC : C < 0x7ff00000) (h : C ≤ (highWord w).toNat) :
    value (UInt64.ofNat (C * 2 ^ 32)) ≤ |value w| := by
  refine (high_le_iff w C hC).mp (UInt64.le_iff_toNat_le.mpr ?_)
  rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  exact h

theorem high_lt (w : UInt64) (C : Nat) (hC : C < 0x7ff00000) (h : (highWord w).toNat < C) :
    |value w| < value (UInt64.ofNat (C * 2 ^ 32)) := by
  refine lt_of_not_ge (fun h' => ?_)
  have := UInt64.le_iff_toNat_le.mp ((high_le_iff w C hC).mpr h')
  rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)] at this
  omega

/-- A lower bound on `abs(x)` from the high word, with the threshold as a rational. -/
theorem high_ge_real (w : UInt64) (C : Nat) (hC : C < 0x7ff00000) (r : ℝ) (a : ℚ)
    (hr : (a : ℝ) = r) (ha : a ≤ PolyBound.ratOfWord (UInt64.ofNat (C * 2 ^ 32)))
    (h : C ≤ (highWord w).toNat) : r ≤ |value w| := by
  rw [← hr]
  exact (word_ge a _ ha).trans (high_ge w C hC h)

/-- An upper bound on `abs(x)` from the high word, with the threshold as a rational. -/
theorem high_lt_real (w : UInt64) (C : Nat) (hC : C < 0x7ff00000) (r : ℝ) (a : ℚ)
    (hr : (a : ℝ) = r) (ha : PolyBound.ratOfWord (UInt64.ofNat (C * 2 ^ 32)) ≤ a)
    (h : (highWord w).toNat < C) : |value w| < r := by
  rw [← hr]
  exact (high_lt w C hC h).trans_le (word_le a _ ha)

theorem magnitude_pos (w : UInt64) (h : 0 < |value w|) : 0 < Wasm.IEEE64.scaledMagnitude w := by
  rw [abs_value] at h
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude w) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

theorem neg_of_sgn (w : UInt64) (hs : sgn w = true) (h : 0 < |value w|) : value w < 0 := by
  rw [sgn_iff] at hs
  exact (F64Magnitude.sign_value w (magnitude_pos w h)).mp hs

theorem pos_of_sgn (w : UInt64) (hs : sgn w = false) (h : 0 < |value w|) : 0 < value w := by
  rw [sgn_iff] at hs
  have h1 := F64Magnitude.sign_value w (magnitude_pos w h)
  rw [hs] at h1
  have h2 : ¬ value w < 0 := fun h' => absurd (h1.mpr h') (by decide)
  have h3 : value w ≠ 0 := fun h' => by rw [h', abs_zero] at h; exact lt_irrefl _ h
  exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h3)

theorem neg_bits (w : UInt64) (hw : Finite w) :
    Wasm.IEEE64.sub 0x8000000000000000 w = Wasm.IEEE64.negate w := by
  rw [F64Sign.sub_negZero, not_nan_of_finite hw]
  rfl

/-- Subtracting a finite word from itself gives positive zero. -/
theorem sub_self_finite (a : UInt64) (ha : Finite a) : Wasm.IEEE64.sub a a = 0 := by
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value a ha
  have hs := (F64Sign.fields_negate a).2.2
  have hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate a) = 0 := by
    have h := negate_spec a ha
    rw [h.2]
    ring
  simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hnf,
    not_infinite_of_finite ha, not_infinite_of_finite hnf, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, hsum, beq_self_eq_true, hs]
  cases Wasm.IEEE64.sign a <;> rfl

theorem lt_encode (e f : Nat) (he1 : 1 ≤ e) (he : e < 0x7FF) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.lt (Wasm.IEEE64.encodeFinite true e f) 0 = true := by
  have hfin := finite_encodeFinite true e f he hf
  have hsv := scaledValue_encodeFinite true e f (by omega) hf
  have h0n : Wasm.IEEE64.isNaN 0 = false := by decide
  have h0 : Wasm.IEEE64.scaledValue 0 = 0 := by decide
  have hne : e ≠ 0 := by omega
  simp only [hne, ite_false, ite_true] at hsv
  have hp : (0 : Int) < ((2 ^ 52 + f) * 2 ^ (e - 1) : Nat) := by positivity
  simp only [Wasm.IEEE64.lt, not_nan_of_finite hfin, h0n, Bool.or_self, Bool.false_eq_true,
    ite_false, hsv, h0, decide_eq_true_eq]
  omega

/-- A negative rounding of a magnitude of at least `2 ^ 53` compares below zero. -/
theorem round_neg_lt (n : Nat) (hn : 2 ^ 53 ≤ n) :
    Wasm.IEEE64.lt (Wasm.IEEE64.roundScaledMagnitude true n) 0 = true := by
  obtain ⟨hs0, hr1, hr2⟩ := F64RoundScaled.rounded_parameters n hn
  have h52 : ¬ n < 2 ^ 52 := by omega
  have h53 : ¬ n < 2 ^ 53 := by omega
  have hinf : Wasm.IEEE64.lt (Wasm.IEEE64.infinity true) 0 = true := by decide +kernel
  unfold Wasm.IEEE64.roundScaledMagnitude
  simp only [h52, h53, ite_false]
  by_cases hc : Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 2 ^ 53
  · simp only [hc, beq_self_eq_true, ite_true]
    split_ifs with h
    · exact hinf
    · exact lt_encode _ _ (by omega) (by omega) (by norm_num)
  · have hb : (Wasm.IEEE32.roundShift n (Nat.log2 n - 52) == 2 ^ 53) = false := by simpa using hc
    simp only [hb, Bool.false_eq_true, ite_false]
    split_ifs with h
    · exact hinf
    · exact lt_encode _ _ (by omega) (by omega) (by omega)

theorem add_neg_lt (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≤ -(2 ^ 53)) :
    Wasm.IEEE64.lt (Wasm.IEEE64.add a b) 0 = true := by
  have hne : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0 := by omega
  have hneg : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0 := by omega
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude true
      (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs := by
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, hne, hneg]
  rw [heq]
  refine round_neg_lt _ ?_
  have : ((2 ^ 53 : Nat) : Int) ≤
      ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs : Int) := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
    push_cast
    omega
  exact_mod_cast this

/-- `x + tiny < 0` from `x ≤ -38` on. -/
theorem add_tiny_neg (x : Float) (hxf : Finite x.toBits) (hX : value x.toBits ≤ -38) :
    x + Float.ofBits 118622047889322841 < 0.0 := by
  have hb : (Float.ofBits 118622047889322841).toBits = 118622047889322841 := by
    rw [F64Bits.toBits_ofBits]; decide +kernel
  have h0 : (0.0 : Float).toBits = 0 := rfl
  rw [F64Bits.lt_iff, F64Bits.toBits_add, hb, h0]
  have htf : Finite (118622047889322841 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have ht := word_le 1 (118622047889322841 : UInt64) (by decide +kernel)
  push_cast at ht
  refine add_neg_lt _ _ hxf htf ?_
  have hs := F64Magnitude.sum_scaled x.toBits 118622047889322841
  set K := (2 : ℝ) ^ 1074 with hK
  have hK0 : (0 : ℝ) < K := by positivity
  have hK53 : (2 : ℝ) ^ 53 ≤ K := by rw [hK]; norm_num
  have h1 : ((Wasm.IEEE64.scaledValue x.toBits + Wasm.IEEE64.scaledValue 118622047889322841 : Int)
      : ℝ) = (value x.toBits + value 118622047889322841) * K := by
    rw [hs]; field_simp
  have h2 : (value x.toBits + value 118622047889322841) * K ≤ -37 * K :=
    mul_le_mul_of_nonneg_right (by linarith) hK0.le
  have h3 : ((Wasm.IEEE64.scaledValue x.toBits + Wasm.IEEE64.scaledValue 118622047889322841 : Int)
      : ℝ) ≤ ((-(2 ^ 53) : Int) : ℝ) := by
    rw [h1]; push_cast; linarith
  exact_mod_cast h3

theorem gt_overflow (x : Float) (hxf : Finite x.toBits) :
    x > Float.ofBits 4649454530587146735 ↔ value overflowWord < value x.toBits := by
  have hb : (Float.ofBits 4649454530587146735).toBits = overflowWord := by
    rw [F64Bits.toBits_ofBits]; unfold overflowWord; decide +kernel
  have hof : Finite overflowWord := by
    unfold CodeLib.IEEE64.Finite overflowWord; decide +kernel
  rw [gt_iff_lt, F64Bits.lt_iff, hb, Expm1FormsOne.lt_value _ _ hof hxf, decide_eq_true_iff]

theorem quotient_half_finite (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 7098 / 10) :
    Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul invln2 x) Expm1Words.half) := by
  obtain ⟨hpf, hp⟩ := Expm1ReduceK.quotient_spec x hxf hx
  obtain ⟨hL1, hL2⟩ := Expm1ReduceK.log_two_bounds
  have hLpos : 0 < Real.log 2 := by linarith
  have hhalf : value Expm1Words.half = 1 / 2 := Expm1KernelInner.const_values.2.1
  have hhf := Expm1KernelInner.const_finite.2.1
  have hsmall : 1282 * u + η ≤ 1 := by
    rw [Expm1KernelInner.u_value, Expm1KernelInner.eta_value]; norm_num
  have hq : |value x / Real.log 2| ≤ 1100 := by
    rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
    nlinarith [abs_nonneg (value x)]
  have hb := abs_le.mp hp
  have hqb := abs_le.mp hq
  have hlt : |value (Wasm.IEEE64.mul invln2 x) - value Expm1Words.half| < 1102 := by
    rw [hhalf, abs_lt]; constructor <;> linarith
  exact (F64AddBounds.sub_real_relative _ _ hpf hhf (hlt.trans (by norm_num))).1

theorem ln2Hi_bits : Expm1Words.ofBitsWord 4604418534311723008 = ln2Hi := by
  unfold Expm1Words.ofBitsWord ln2Hi; decide +kernel

theorem ln2Lo_bits : Expm1Words.ofBitsWord 4461442080421002358 = ln2Lo := by
  unfold Expm1Words.ofBitsWord ln2Lo; decide +kernel

theorem invln2_bits : Expm1Words.ofBitsWord 4609176140021203710 = invln2 := by
  unfold Expm1Words.ofBitsWord invln2; decide +kernel

theorem huge_bits : Expm1Words.ofBitsWord 9094988921128908188 = 9094988921128908188 := by
  unfold Expm1Words.ofBitsWord; decide +kernel

theorem ln2Lo_neg : Wasm.IEEE64.sub 0x8000000000000000 ln2Lo = Wasm.IEEE64.negate ln2Lo :=
  neg_bits _ const_finite.2.1

theorem half_bits : (0.5 : Float).toBits = Expm1Words.half := rfl

theorem overflow_bits :
    (Float.ofBits 9094988921128908188 * Float.ofBits 9094988921128908188).toBits =
      0x7FF0000000000000 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

theorem saturated_bits : (Float.ofBits 118622047889322841 - 1.0).toBits = 0xBFF0000000000000 := by
  rw [F64Bits.toBits_sub, F64Bits.toBits_ofBits]
  decide +kernel

/-- The tiny path's zero, `(huge + x) - (huge + x)`. -/
theorem tiny_zero (x : UInt64) (hxf : Finite x) (hx : |value x| < 1) :
    Wasm.IEEE64.sub (Wasm.IEEE64.add 9094988921128908188 x)
      (Wasm.IEEE64.add 9094988921128908188 x) = 0 := by
  have hhf : Finite (9094988921128908188 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh := word_le (10 ^ 301) (9094988921128908188 : UInt64) (by decide +kernel)
  have hh0 := word_ge 0 (9094988921128908188 : UInt64) (by decide +kernel)
  push_cast at hh hh0
  have hxb := abs_lt.mp hx
  have hs : |value 9094988921128908188 + value x| < 10 ^ 302 := by
    rw [abs_lt]; constructor <;> linarith
  have ha := F64AddBounds.add_real_relative _ _ hhf hxf (hs.trans (by norm_num))
  exact sub_self_finite _ ha.1

/-- `Tanh.expm1` lies within one step of `exp x - 1` on every finite input. -/
theorem expm1_within_one (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits) - 1) (Tanh.expm1 x).toBits := by
  have h1 := high_finite x.toBits hxf
  by_cases h2 : highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735
  · rw [select_overflow x h1 h2, overflow_bits]
    exact path_overflow x.toBits ((gt_overflow x hxf).mp h2.2)
  by_cases h3 : highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0
  · rw [select_saturated x h1 h2 h3, saturated_bits]
    have hge := high_ge_real x.toBits 1078159482 (by norm_num) 38 38 (by norm_num)
      (by decide +kernel) (UInt64.le_iff_toNat_le.mp h3.1)
    have hneg := neg_of_sgn x.toBits h3.2.1 (by linarith)
    rw [abs_of_neg hneg] at hge
    exact path_saturated _ (by linarith)
  by_cases h4 : highWord x.toBits > 1071001154
  · have h4n : 1071001155 ≤ (highWord x.toBits).toNat := UInt64.lt_iff_toNat_lt.mp h4
    have hlo := high_ge_real x.toBits 1071001155 (by norm_num) (34657359 / 10 ^ 8)
      (34657359 / 10 ^ 8) (by norm_num) (by decide +kernel) h4n
    have hX0 : 0 < |value x.toBits| := by linarith
    by_cases h5 : highWord x.toBits < 1072734898
    · have h5n : (highWord x.toBits).toNat < 1072734898 := UInt64.lt_iff_toNat_lt.mp h5
      have hhi := high_lt_real x.toBits 1072734898 (by norm_num) (10397206 / 10 ^ 7)
        (10397206 / 10 ^ 7) (by norm_num) (by decide +kernel) h5n
      rw [select_reduced_one x h1 h2 h3 h4 h5]
      cases hs : sgn x.toBits
      · have hpos := pos_of_sgn x.toBits hs hX0
        rw [abs_of_pos hpos] at hlo hhi
        simp only [Bool.false_eq_true, ite_false]
        rw [Expm1Words.kernel_bits]
        simp only [F64Bits.toBits_sub, Expm1Words.float_ofBits, ln2Hi_bits, ln2Lo_bits]
        exact path_one_pos x.toBits hxf (by linarith) (by linarith)
      · have hneg := neg_of_sgn x.toBits hs hX0
        rw [abs_of_neg hneg] at hlo hhi
        simp only [ite_true]
        rw [Expm1Words.kernel_bits]
        simp only [F64Bits.toBits_sub, F64Bits.toBits_add, F64Bits.toBits_neg,
          Expm1Words.float_ofBits, ln2Hi_bits, ln2Lo_bits, ln2Lo_neg]
        exact path_one_neg x.toBits hxf (by linarith) (by linarith)
    · have h5n : 1072734898 ≤ (highWord x.toBits).toNat := by
        have : ¬ (highWord x.toBits).toNat < 1072734898 :=
          fun h => h5 (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have hlo2 := high_ge_real x.toBits 1072734898 (by norm_num) (10397205 / 10 ^ 7)
        (10397205 / 10 ^ 7) (by norm_num) (by decide +kernel) h5n
      cases hs : sgn x.toBits
      · have hpos := pos_of_sgn x.toBits hs hX0
        rw [abs_of_pos hpos] at hlo2
        have hhi : value x.toBits ≤ value overflowWord := by
          by_cases hge : highWord x.toBits ≥ 1082535490
          · have : ¬ x > Float.ofBits 4649454530587146735 := fun h => h2 ⟨hge, h⟩
            rw [gt_overflow x hxf] at this
            exact not_lt.mp this
          · have hn : (highWord x.toBits).toNat < 1082535490 := by
              have : ¬ 1082535490 ≤ (highWord x.toBits).toNat :=
                fun h => hge (UInt64.le_iff_toNat_le.mpr h)
              omega
            have h := high_lt_real x.toBits 1082535490 (by norm_num) (709782227 / 10 ^ 6)
              (709782227 / 10 ^ 6) (by norm_num) (by decide +kernel) hn
            have hw : (709782227 / 10 ^ 6 : ℚ) ≤ PolyBound.ratOfWord overflowWord := by
              unfold overflowWord; decide +kernel
            have hw' := word_ge _ _ hw
            push_cast at hw'
            rw [abs_of_pos hpos] at h
            linarith
        rw [select_reduced_pos x h1 h2 h3 h4 h5 hs, Expm1Words.kernel_bits]
        simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add,
          F64Convert.toUInt64_eq, F64Convert.toBits_toFloat, Expm1Words.float_ofBits, ln2Hi_bits,
          ln2Lo_bits, invln2_bits, half_bits, hs]
        exact path_k_pos x.toBits hxf hlo2 hhi
      · have hneg := neg_of_sgn x.toBits hs hX0
        have hlt : (highWord x.toBits).toNat < 1078159482 := by
          by_contra hc
          have hc' : 1078159482 ≤ (highWord x.toBits).toNat := by omega
          have hge : highWord x.toBits ≥ 1078159482 := UInt64.le_iff_toNat_le.mpr hc'
          have hX := high_ge_real x.toBits 1078159482 (by norm_num) 38 38 (by norm_num)
            (by decide +kernel) hc'
          rw [abs_of_neg hneg] at hX
          exact h3 ⟨hge, hs, add_tiny_neg x hxf (by linarith)⟩
        have hhi := high_lt_real x.toBits 1078159482 (by norm_num) (38817 / 1000) (38817 / 1000)
          (by norm_num) (by decide +kernel) hlt
        rw [abs_of_neg hneg] at hlo2 hhi
        rw [select_reduced_neg x h1 h2 h3 h4 h5 hs, Expm1Words.kernel_bits]
        simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_neg,
          F64Convert.toUInt64_eq, F64Convert.toBits_toFloat, Expm1Words.float_ofBits, ln2Hi_bits,
          ln2Lo_bits, invln2_bits, half_bits]
        rw [neg_bits _ (quotient_half_finite x.toBits hxf (by rw [abs_of_neg hneg]; linarith))]
        obtain ⟨-, hm2, -⟩ := Expm1ReduceK.reduce_k_neg x.toBits hxf (by linarith) (by linarith)
        obtain ⟨hcf, -, -⟩ := Expm1ReduceK.integer_word _ (lt_of_le_of_lt hm2 (by norm_num))
        rw [neg_bits _ hcf]
        exact path_k_neg x.toBits hxf (by linarith) (by linarith)
  · have h4n : (highWord x.toBits).toNat < 1071001155 := by
      have : ¬ 1071001154 < (highWord x.toBits).toNat :=
        fun h => h4 (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hhi := high_lt_real x.toBits 1071001155 (by norm_num) (3466 / 10000) (3466 / 10000)
      (by norm_num) (by decide +kernel) h4n
    by_cases h5 : highWord x.toBits < 1016070144
    · have hx := high_lt_real x.toBits 1016070144 (by norm_num) (1 / 2 ^ 54) (1 / 2 ^ 54)
        (by norm_num) (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp h5)
      rw [select_tiny x h1 h2 h3 h4 h5]
      simp only [F64Bits.toBits_sub, F64Bits.toBits_add, Expm1Words.float_ofBits, huge_bits]
      rw [tiny_zero x.toBits hxf (hx.trans (by norm_num))]
      by_cases hX0 : value x.toBits = 0
      · rw [hX0, Real.exp_zero, sub_self]
        have hm : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
          have h := abs_value x.toBits
          rw [hX0, abs_zero] at h
          have : (Wasm.IEEE64.scaledMagnitude x.toBits : ℝ) = 0 := by
            have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
            field_simp at h
            linarith
          exact_mod_cast this
        rw [F64Convert.zero_encoding _ hm]
        cases Wasm.IEEE64.sign x.toBits
        · exact zero_within _ (Or.inl (by decide +kernel))
        · exact zero_within _ (Or.inr (by decide +kernel))
      · exact path_tiny x.toBits 0 hxf (by unfold CodeLib.IEEE64.Finite; decide)
          F64Magnitude.value_zero hX0 hx
    · have h5n : 1016070144 ≤ (highWord x.toBits).toNat := by
        have : ¬ (highWord x.toBits).toNat < 1016070144 :=
          fun h => h5 (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have hlo := high_ge_real x.toBits 1016070144 (by norm_num) (1 / 2 ^ 54) (1 / 2 ^ 54)
        (by norm_num) (by decide +kernel) h5n
      rw [select_middle x h1 h2 h3 h4 h5, Expm1Words.kernel_bits]
      exact path_middle x.toBits _ hxf hlo hhi.le

#print axioms expm1_within_one

end Verified.Examples.Expm1Theorem
