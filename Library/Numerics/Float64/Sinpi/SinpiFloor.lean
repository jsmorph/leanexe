import Library.Numerics.Float64.Sinpi.SinpiBits
import LeanExe.ProofKit.F64GridExact

/-!
The integer part of `Sinpi`: for a positive word `b` from 1 below `2 ^ 52`, the word with the bits
below the units bit cleared has the value `N = ⌊b⌋`, the fraction `b - N` lies in `[0, 1)` and is
0 or at least `2 ^ -52`, and `toUInt64` gives `N`, so `Sinpi.oddPart` gives the parity of `N`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiFloor

open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tan.TanStep Library.Numerics.Float64.Tan.TanBigWords SinpiBits SinpiSingle

set_option exponentiation.threshold 1200

/-- The cleared word is the integer part. -/
theorem floor_spec (b fl : UInt64) (hb : b.toNat < 2 ^ 63)
    (he1 : 1023 ≤ Wasm.IEEE64.exponent b) (he2 : Wasm.IEEE64.exponent b ≤ 1074)
    (hfl : fl.toNat = b.toNat / 2 ^ (1075 - Wasm.IEEE64.exponent b) *
      2 ^ (1075 - Wasm.IEEE64.exponent b)) :
    Finite fl ∧ fl.toNat < 2 ^ 63 ∧ ∃ N : Nat, value fl = N ∧ 1 ≤ N ∧ N < 2 ^ 52 ∧
      (N : ℝ) ≤ value b ∧ value b < N + 1 ∧ (value b = N ∨ N + 1 / 2 ^ 52 ≤ value b) := by
  have hwb := word_of b hb
  have hf : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hbn : b.toNat = Wasm.IEEE64.exponent b * 2 ^ 52 + Wasm.IEEE64.fraction b := by
    unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction; omega
  generalize he : Wasm.IEEE64.exponent b = e at *
  generalize hfd : Wasm.IEEE64.fraction b = f at *
  obtain ⟨m, hm⟩ : ∃ m, 1075 - e = m := ⟨_, rfl⟩
  rw [hm] at hfl
  have hm1 : 1 ≤ m := by omega
  have hm52 : m ≤ 52 := by omega
  have hdiv : (2 : Nat) ^ 52 = 2 ^ (52 - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
  have hfl' : fl.toNat = e * 2 ^ 52 + f / 2 ^ m * 2 ^ m := by
    rw [hfl, hbn, hdiv, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.add_mul]
    ring
  have hj : f / 2 ^ m * 2 ^ m ≤ 2 ^ 52 := le_trans (Nat.div_mul_le_self _ _) hf.le
  have hw : fl = UInt64.ofNat (e * 2 ^ 52 + f / 2 ^ m * 2 ^ m) := by
    apply UInt64.toNat_inj.mp
    rw [hfl', UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
  obtain ⟨hv, hfin, h63⟩ := word_value e (f / 2 ^ m * 2 ^ m) (by omega) (by omega) hj
  obtain ⟨hvb, -, -⟩ := word_value e f (by omega) (by omega) hf.le
  rw [← hw] at hv hfin h63
  rw [← hwb] at hvb
  have hB : B e = 2 ^ (e - 1023) := by
    unfold B
    rw [show e + 51 = (e - 1023) + 1074 by omega, pow_add]
    field_simp
  have hS : S e = 1 / 2 ^ m := by
    unfold S
    rw [show (1074 : Nat) = (e - 1) + m by omega, pow_add]
    field_simp
  have hq : f / 2 ^ m < 2 ^ (e - 1023) := by
    have : f < 2 ^ (52 - m) * 2 ^ m := by rw [← hdiv]; exact hf
    have h2 : f / 2 ^ m < 2 ^ (52 - m) := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
    rwa [show 52 - m = e - 1023 by omega] at h2
  have hfq : (f : ℝ) = (f / 2 ^ m : Nat) * 2 ^ m + (f % 2 ^ m : Nat) := by
    exact_mod_cast (Nat.div_add_mod' f (2 ^ m)).symm
  have hr : (f % 2 ^ m : Nat) < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hr' : ((f % 2 ^ m : Nat) : ℝ) < 2 ^ m := by exact_mod_cast hr
  have hpm : (0 : ℝ) < 2 ^ m := by positivity
  have hvb' : value b = 2 ^ (e - 1023) + (f / 2 ^ m : Nat) + (f % 2 ^ m : Nat) / 2 ^ m := by
    rw [hvb, hB, hS, hfq, add_mul, mul_assoc, mul_one_div_cancel (ne_of_gt hpm), mul_one,
      mul_one_div]
    ring
  refine ⟨hfin, h63, 2 ^ (e - 1023) + f / 2 ^ m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, hB, hS]
    push_cast
    rw [mul_assoc, mul_one_div_cancel (ne_of_gt hpm), mul_one]
  · exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
  · have : 2 ^ (e - 1023) ≤ 2 ^ 51 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (e - 1023) + 2 ^ (e - 1023) ≤ 2 ^ 52 := by
      rw [show (2 : Nat) ^ 52 = 2 ^ 51 + 2 ^ 51 by norm_num]; omega
    omega
  · rw [hvb']
    push_cast
    have := div_nonneg (Nat.cast_nonneg (f % 2 ^ m)) hpm.le
    linarith
  · rw [hvb']
    push_cast
    have : ((f % 2 ^ m : Nat) : ℝ) / 2 ^ m < 1 := by rw [div_lt_one hpm]; exact hr'
    linarith
  · rcases Nat.eq_zero_or_pos (f % 2 ^ m) with h0 | h0
    · left
      rw [hvb', h0]
      push_cast
      ring
    · right
      rw [hvb']
      push_cast
      have h1 : (1 : ℝ) ≤ (f % 2 ^ m : Nat) := by exact_mod_cast h0
      have h2 : (1 : ℝ) / 2 ^ 52 ≤ 1 / 2 ^ m :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hm52)
      have h3 : (1 : ℝ) / 2 ^ m ≤ (f % 2 ^ m : Nat) / 2 ^ m :=
        div_le_div_of_nonneg_right h1 hpm.le
      linarith

/-- `toUInt64` of a float with a positive integer value. -/
theorem toUInt64_int (x : Float) (N : Nat) (hf : Finite x.toBits) (hv : value x.toBits = N)
    (h1 : 1 ≤ N) (h2 : N < 2 ^ 63) : x.toUInt64 = UInt64.ofNat N := by
  rw [F64Convert.toUInt64_eq]
  have hpos : 0 < value x.toBits := by rw [hv]; exact_mod_cast h1
  have hsg : Wasm.IEEE64.sign x.toBits = false := by
    rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x.toBits) with h | h
    · have := sign_true x.toBits h
      have := abs_nonneg (value x.toBits)
      linarith
    · exact h
  have hm : Wasm.IEEE64.scaledMagnitude x.toBits = N * 2 ^ 1074 := by
    have h := F64RoundNearest.abs_value x.toBits
    rw [abs_of_pos hpos, hv, eq_div_iff (by positivity)] at h
    exact_mod_cast h.symm
  have hfin : Wasm.IEEE64.isFinite x.toBits = true := hf
  have hnan : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hf
  have htr : Wasm.IEEE64.truncatedInt x.toBits = some (N : Int) := by
    unfold Wasm.IEEE64.truncatedInt
    simp only [hfin, ite_true, hm, hsg, Bool.false_eq_true, ite_false,
      Nat.mul_div_cancel _ (show 0 < 2 ^ 1074 by positivity)]
  unfold Wasm.IEEE64.truncSatI64U
  simp only [hnan, Bool.false_eq_true, ite_false, htr]
  rw [if_neg (by omega), if_neg (by omega)]
  unfold Wasm.IEEE64.intToUInt64
  rw [if_neg (by omega)]
  rfl

theorem parity (N : Nat) (h : N < 2 ^ 64) : (UInt64.ofNat N &&& 1 == 1) = decide (N % 2 = 1) := by
  have hn : (UInt64.ofNat N).toNat = N :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have h1 : (UInt64.ofNat N &&& 1).toNat = N % 2 := by
    rw [UInt64.toNat_and, hn]
    exact Nat.and_two_pow_sub_one_eq_mod N 1
  by_cases hc : N % 2 = 1
  · have : UInt64.ofNat N &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [h1, hc]; rfl)
    rw [this, decide_eq_true hc]
    rfl
  · have : UInt64.ofNat N &&& 1 ≠ 1 := fun h' => hc (by
      have := congrArg UInt64.toNat h'
      rw [h1] at this
      exact this)
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false hc]

/-- `Sinpi.oddPart` gives the parity of the integer part. -/
theorem oddPart_spec (fl : Float) (j0 : UInt64) (N : Nat) (hf : Finite fl.toBits)
    (hv : value fl.toBits = N) (h1 : 1 ≤ N) (h2 : N < 2 ^ 52)
    (hj : 30 < j0.toNat → 2 ^ 31 ≤ N) :
    Sinpi.oddPart fl j0 = decide (N % 2 = 1) := by
  unfold Sinpi.oddPart
  dsimp only
  split_ifs with hc
  · have hj0 : 30 < j0.toNat := by
      rw [GT.gt, UInt64.lt_iff_toNat_lt] at hc
      exact hc
    have hN := hj hj0
    have hc30 : (1073741824.0 : Float).toBits = 0x41D0000000000000 := by decide
    have hcf : Finite (0x41D0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
    have hcv : Wasm.IEEE64.scaledValue (0x41D0000000000000 : UInt64) = 2 ^ 30 * 2 ^ 1074 := by
      decide +kernel
    have hsv : Wasm.IEEE64.scaledValue fl.toBits = (N : Int) * 2 ^ 1074 := by
      have h := hv
      rw [Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, div_eq_iff (by positivity)] at h
      exact_mod_cast h
    have hz : ((N : Int) - 2 ^ 30) = ((N - 2 ^ 30 : Nat) : Int) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    obtain ⟨hdf, hdv⟩ := F64GridExact.sub_grid_exact fl.toBits _ hf hcf ((N : Int) - 2 ^ 30) 1074
      (by rw [hsv, hcv]; ring) (by rw [hz, Int.natAbs_natCast]; omega) (by norm_num)
    have hb : (fl - 1073741824.0).toBits = Wasm.IEEE64.sub fl.toBits 0x41D0000000000000 := by
      rw [F64Bits.toBits_sub, hc30]
    have hval : value (fl - 1073741824.0).toBits = ((N - 2 ^ 30 : Nat) : ℝ) := by
      rw [hb, Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, hdv, hsv, hcv, Nat.cast_sub (by omega),
        div_eq_iff (by positivity)]
      push_cast
      ring
    rw [toUInt64_int _ (N - 2 ^ 30) (by rw [hb]; exact hdf) hval (by omega) (by omega),
      parity _ (by omega)]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  · rw [toUInt64_int fl N hf hv h1 (by omega), parity _ (by omega)]

#print axioms floor_spec
#print axioms toUInt64_int
#print axioms oddPart_spec

end Library.Numerics.Float64.Sinpi.SinpiFloor
