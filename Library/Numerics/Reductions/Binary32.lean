import Library.Numerics.Reductions.SumError
import CodeLib.IEEE32.Roundoff
import CodeLib.IEEE32.Multiplication
import LeanExe.ProofKit.F32Bits
import LeanExe.ProofKit.F64DyadicBounds

/-!
Binary32 rounding errors and sums.  The binary32 operations of Talos, `Wasm.IEEE32.add` and
`Wasm.IEEE32.mul`, round to nearest, ties to even.  `add_relative` states that the error of a sum
below `2 ^ 127` is at most `2 ^ -24` of its magnitude, and `mul_mixed` that the error of a
product below `2 ^ 126` is at most `2 ^ -24` of its magnitude plus `2 ^ -150`, half the least
subnormal.  Both follow the binary64 proofs of `F64PackRelative` and `F64DyadicBounds`, with
24-bit significands and the scale `2 ^ -149`.  `f32` is the `SumError.Adder` of Lean's `Float32`,
and `dot_bound` the error of a left-to-right sum of `n` rounded products,
`γ_n Σ |x_i y_i| + n / 2 ^ 149` with `γ_k = k / (2 ^ 24 - k)`.
-/

namespace Library.Numerics.Reductions.Binary32

open CodeLib.IEEE32 LeanExe.ProofKit SumError

set_option exponentiation.threshold 4096

/-! ### Rounding a scaled magnitude -/

theorem roundedMagnitude_relative (n : Nat) :
    |(roundedMagnitude n : Int) - n| * (2 ^ 24 : Int) ≤ n := by
  by_cases hexact : n < 2 ^ 24
  · have hexactNum : n < 16777216 := by norm_num at hexact ⊢; exact hexact
    simp [roundedMagnitude, hexactNum]
  · have hmin : 2 ^ 24 ≤ n := by omega
    have hexactNum : ¬n < 16777216 := by norm_num at hexact ⊢; exact hexact
    have hn : n ≠ 0 := by omega
    have hlogLower : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    have hshift : 0 < shift := by simp only [shift]; omega
    have hpowLower : 2 ^ 23 * 2 ^ shift ≤ n := by
      rw [← pow_add]
      have heq : 23 + shift = Nat.log2 n := by simp only [shift]; omega
      rw [heq]
      exact Nat.log2_self_le hn
    have herrorCases := roundShift_error_cases n shift hshift
    have herrorHalf : |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ shift / 2 : Nat) :=
      abs_int_sub_le_of_error_cases _ _ _ herrorCases
    have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
      by_cases hcarry : rounded = 2 ^ 24
      · have hcarryNum : Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, shift] using hcarry
        simp [roundedMagnitude, hexactNum, rounded, shift, hcarryNum, pow_succ, Nat.mul_assoc,
          Nat.mul_comm]
        ring
      · have hcarryNum : ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, shift] using hcarry
        simp [roundedMagnitude, hexactNum, rounded, shift, hcarryNum]
    have hhalfScaled : ((2 ^ shift / 2 : Nat) : Int) * (2 ^ 24 : Int) =
        (2 ^ 23 * 2 ^ shift : Nat) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
      rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
      push_cast
      ring
    rw [hrounded]
    calc
      |((rounded * 2 ^ shift : Nat) : Int) - n| * (2 ^ 24 : Int) ≤
          ((2 ^ shift / 2 : Nat) : Int) * (2 ^ 24 : Int) :=
        mul_le_mul_of_nonneg_right herrorHalf (by positivity)
      _ = (2 ^ 23 * 2 ^ shift : Nat) := hhalfScaled
      _ ≤ n := by exact_mod_cast hpowLower

theorem rounding_parameters' {n : Nat} (hmin : 2 ^ 24 ≤ n) (hmax : n < 2 ^ 276) :
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ 252 ∧ 2 ^ 23 ≤ rounded ∧ rounded ≤ 2 ^ 24 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < 276 := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 23
  have hpowLower : 2 ^ 23 * 2 ^ shift ≤ n := by
    rw [← pow_add, show 23 + shift = Nat.log2 n by dsimp [shift]; omega]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2 ^ 24 * 2 ^ shift := by
    rw [← pow_add, show 24 + shift = Nat.log2 n + 1 by dsimp [shift]; omega]
    exact Nat.lt_log2_self
  have hquotLower : 2 ^ 23 ≤ n / 2 ^ shift := (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2 ^ shift < 2 ^ 24 := (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ 252 ∧
    2 ^ 23 ≤ Wasm.IEEE32.roundShift n shift ∧ Wasm.IEEE32.roundShift n shift ≤ 2 ^ 24
  dsimp only [shift] at *
  omega

/-- `roundScaledMagnitude` of a magnitude below `2 ^ 276`, a value below `2 ^ 127`, is finite,
with the magnitude `roundedMagnitude n` and the given sign. -/
theorem pack_spec (negative : Bool) (n : Nat) (hmax : n < 2 ^ 276) :
    Finite (Wasm.IEEE32.roundScaledMagnitude negative n) ∧
    Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundScaledMagnitude negative n) =
      roundedMagnitude n ∧
    Wasm.IEEE32.sign (Wasm.IEEE32.roundScaledMagnitude negative n) = negative := by
  by_cases hsmall : n < 2 ^ 151
  · have hs := roundScaledMagnitude_spec negative n hsmall
    exact ⟨hs.1, hs.2.1, sign_roundScaledMagnitude negative n hsmall⟩
  have hmin : 2 ^ 24 ≤ n := by omega
  have hsubnormalNum : ¬n < 8388608 := by omega
  have hexactNum : ¬n < 16777216 := by omega
  let shift := Nat.log2 n - 23
  let rounded := Wasm.IEEE32.roundShift n shift
  obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ := rounding_parameters' hmin hmax
  change 0 < shift at hshift
  change shift ≤ 252 at hshiftMax
  change 2 ^ 23 ≤ rounded at hroundedMin
  change rounded ≤ 2 ^ 24 at hroundedMax
  by_cases hcarry : rounded = 2 ^ 24
  · have hcarryNum : Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 2) 0 (by omega)
      (by norm_num)
    have hsign := sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift, hcarryNum,
        show ¬255 ≤ shift + 2 by omega, Nat.add_assoc]
    have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
      simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum, pow_succ, Nat.mul_assoc,
        Nat.mul_comm]
      ring
    rw [hactual, hrounded]
    refine ⟨hfinite, ?_, hsign⟩
    rw [hmagnitude]
    simp only [show shift + 2 ≠ 0 by omega, ↓reduceIte, Nat.add_zero]
    rw [show shift + 2 - 1 = shift + 1 by omega, pow_succ, hcarry]
    ring
  · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
    have hcarryNum : ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 1) (rounded - 2 ^ 23) (by omega)
      hfraction
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 1) (rounded - 2 ^ 23)
      (by omega) hfraction
    have hsign := sign_encodeFinite negative (shift + 1) (rounded - 2 ^ 23) (by omega) hfraction
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative (shift + 1) (rounded - 2 ^ 23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift, rounded,
        hcarryNum, show ¬255 ≤ shift + 1 by omega]
    have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
      simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
    rw [hactual, hrounded]
    refine ⟨hfinite, ?_, hsign⟩
    rw [hmagnitude, show shift + 1 - 1 = shift by omega,
      show 2 ^ 23 + (rounded - 2 ^ 23) = rounded by omega]
    simp

theorem roundedMagnitude_shifted_pos (rounded shift : Nat) (hlower : 2 ^ 23 ≤ rounded)
    (hupper : rounded ≤ 2 ^ 24) (hshiftPos : 0 < shift) :
    roundedMagnitude (rounded * 2 ^ shift) = rounded * 2 ^ shift := by
  have hroundedNe : rounded ≠ 0 := by omega
  have hlarge : ¬rounded * 2 ^ shift < 2 ^ 24 := by
    have hp : 2 ^ 23 * 2 ^ 1 ≤ rounded * 2 ^ shift :=
      Nat.mul_le_mul hlower (Nat.pow_le_pow_right (by omega) (by omega))
    norm_num [← pow_add] at hp ⊢
    exact hp
  by_cases hcarry : rounded = 2 ^ 24
  · subst rounded
    have hlog := F64DyadicBounds.log2_mul_two_pow (2 ^ 24) shift (by positivity)
    have hcandidate : 2 ^ 24 * 2 ^ shift = 2 ^ 23 * 2 ^ (shift + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hactualShift : Nat.log2 (2 ^ 24 * 2 ^ shift) - 23 = shift + 1 := by
      rw [hlog, Nat.log2_two_pow]
      omega
    simp only [roundedMagnitude, ite_eq_right hlarge]
    rw [hactualShift, hcandidate, F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega)]
    norm_num
  · have hroundedLt : rounded < 2 ^ 24 := by omega
    have hlogRounded : Nat.log2 rounded = 23 :=
      (Nat.log2_eq_iff hroundedNe).2 ⟨hlower, by simpa using hroundedLt⟩
    have hlog := F64DyadicBounds.log2_mul_two_pow rounded shift hroundedNe
    have hactualShift : Nat.log2 (rounded * 2 ^ shift) - 23 = shift := by
      rw [hlog, hlogRounded]
      omega
    simp only [roundedMagnitude, ite_eq_right hlarge]
    rw [hactualShift, F64DyadicBounds.roundShift_mul_two_pow _ _ hshiftPos]
    simp only [beq_iff_eq, ite_eq_right hcarry]

/-- A magnitude `rounded · 2 ^ shift` with `2 ^ 23 ≤ rounded ≤ 2 ^ 24` is representable. -/
theorem roundedMagnitude_shifted (rounded shift : Nat) (hlower : 2 ^ 23 ≤ rounded)
    (hupper : rounded ≤ 2 ^ 24) :
    roundedMagnitude (rounded * 2 ^ shift) = rounded * 2 ^ shift := by
  by_cases hshift : shift = 0
  · subst shift
    by_cases hr : rounded < 2 ^ 24
    · simp [roundedMagnitude, show rounded < 16777216 by omega]
    · have h24 : rounded * 2 ^ 0 = 2 ^ 23 * 2 ^ 1 := by
        rw [show rounded = 2 ^ 24 by omega]; norm_num
      rw [h24]
      exact roundedMagnitude_shifted_pos _ _ (by norm_num) (by norm_num) (by norm_num)
  · exact roundedMagnitude_shifted_pos _ _ hlower hupper (Nat.pos_of_ne_zero hshift)

theorem scaled_eq (v : UInt32) : (Wasm.IEEE32.scaledValue v : ℝ) = value v * 2 ^ 149 := by
  simp only [value]
  field_simp

theorem abs_scaled (v : UInt32) :
    |(Wasm.IEEE32.scaledValue v : ℝ)| = (Wasm.IEEE32.scaledMagnitude v : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
  norm_num

/-! ### Addition -/

/-- A rounded binary32 sum of finite words, below `2 ^ 127` in magnitude, is finite and within
`2 ^ -24` of its magnitude. -/
theorem add_relative (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a + value b| < 2 ^ 127) :
    Finite (Wasm.IEEE32.add a b) ∧
      |value (Wasm.IEEE32.add a b) - (value a + value b)| ≤ |value a + value b| / 2 ^ 24 := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  set z := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b with hz
  have hzr : (z : ℝ) = (value a + value b) * 2 ^ 149 := by
    rw [hz]; push_cast; rw [scaled_eq, scaled_eq]; ring
  by_cases hz0 : z = 0
  · have hv : value a + value b = 0 := by
      have : ((value a + value b) * 2 ^ 149 : ℝ) = 0 := by rw [← hzr, hz0]; simp
      simpa using this
    have hadd : Wasm.IEEE32.add a b =
        if Wasm.IEEE32.sign a && Wasm.IEEE32.sign b then 0x80000000 else 0 := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, ← hz, hz0]
    rw [hadd, hv]
    split
    · refine ⟨by unfold CodeLib.IEEE32.Finite; decide, ?_⟩
      have : value 0x80000000 = 0 := by simp [value]; decide
      rw [this]; simp
    · refine ⟨by unfold CodeLib.IEEE32.Finite; decide, ?_⟩
      have : value 0 = 0 := by simp [value]; decide
      rw [this]; simp
  · have hmax : z.natAbs < 2 ^ 276 := by
      have h1 : |(z : ℝ)| < 2 ^ 127 * 2 ^ 149 := by
        rw [hzr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
        exact mul_lt_mul_of_pos_right hbound (by positivity)
      have h2 : |z| < (2 ^ 276 : Int) := by
        have : (2 : ℝ) ^ 127 * 2 ^ 149 = 2 ^ 276 := by norm_num
        rw [this] at h1
        exact_mod_cast h1
      exact natAbs_lt_nat h2
    have hadd : Wasm.IEEE32.add a b = Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, ← hz, hz0]
    have hp := pack_spec (z < 0) z.natAbs hmax
    have herr := roundedMagnitude_relative z.natAbs
    rw [hadd]
    refine ⟨hp.1, ?_⟩
    have hsv : Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) =
        if z < 0 then -(roundedMagnitude z.natAbs : Int) else roundedMagnitude z.natAbs := by
      simp only [Wasm.IEEE32.scaledValue, hp.2.1, hp.2.2]
      by_cases h : z < 0 <;> simp [h]
    have hint : |Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) - z|
        * 2 ^ 24 ≤ |z| := by
      rw [hsv, Int.abs_eq_natAbs z]
      by_cases h : z < 0
      · rw [ite_eq_left h]
        have : -(roundedMagnitude z.natAbs : Int) - z = -((roundedMagnitude z.natAbs : Int) -
            z.natAbs) := by omega
        rw [this, abs_neg]; exact herr
      · rw [ite_eq_right h]
        have : (roundedMagnitude z.natAbs : Int) - z = (roundedMagnitude z.natAbs : Int) -
            z.natAbs := by omega
        rw [this]; exact herr
    have hreal : |(Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs)
        : ℝ) - z| * 2 ^ 24 ≤ |(z : ℝ)| := by exact_mod_cast hint
    rw [scaled_eq, hzr, ← sub_mul, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)] at hreal
    rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg (value (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) -
      (value a + value b))]

/-- Adding a finite word below `2 ^ 127` in magnitude to `+0` is exact. -/
theorem zero_add_exact (t : UInt32) (ht : Finite t) (hm : |value t| < 2 ^ 127) :
    Finite (Wasm.IEEE32.add 0 t) ∧ value (Wasm.IEEE32.add 0 t) = value t := by
  have h0 : CodeLib.IEEE32.Finite (0 : UInt32) := by unfold CodeLib.IEEE32.Finite; decide
  have hv0 : value 0 = 0 := by simp [value]; decide
  have h := add_relative 0 t h0 ht (by rw [hv0, zero_add]; exact hm)
  refine ⟨h.1, ?_⟩
  rw [hv0, zero_add] at h
  -- the sum is `t` itself: the exact sum is representable
  have hna := not_nan_of_finite ht
  have hia := not_infinite_of_finite ht
  have hsv0 : Wasm.IEEE32.scaledValue 0 = 0 := by decide
  by_cases hz : Wasm.IEEE32.scaledValue t = 0
  · have hvt : value t = 0 := by simp [value, hz]
    have hz' : Wasm.IEEE32.scaledValue 0 + Wasm.IEEE32.scaledValue t = 0 := by rw [hsv0, hz]; rfl
    have hadd : Wasm.IEEE32.add 0 t =
        if Wasm.IEEE32.sign 0 && Wasm.IEEE32.sign t then 0x80000000 else 0 := by
      simp [Wasm.IEEE32.add, hna, hia, hz', show Wasm.IEEE32.isNaN 0 = false by decide,
        show Wasm.IEEE32.isInfinite 0 = false by decide]
    rw [hadd, hvt]
    split
    · simp [value]; decide
    · simp [value]; decide
  · have hm0 : Wasm.IEEE32.scaledMagnitude t ≠ 0 := by
      intro h0'; apply hz; simp [Wasm.IEEE32.scaledValue, h0']
    have hadd : Wasm.IEEE32.add 0 t = Wasm.IEEE32.roundScaledMagnitude
        (Wasm.IEEE32.scaledValue t < 0) (Wasm.IEEE32.scaledMagnitude t) := by
      have hz' : Wasm.IEEE32.scaledValue 0 + Wasm.IEEE32.scaledValue t =
          Wasm.IEEE32.scaledValue t := by rw [hsv0]; simp
      simp [Wasm.IEEE32.add, hna, hia, hz', hz, show Wasm.IEEE32.isNaN 0 = false by decide,
        show Wasm.IEEE32.isInfinite 0 = false by decide, natAbs_scaledValue]
    have hmax : Wasm.IEEE32.scaledMagnitude t < 2 ^ 276 := by
      have h1 := abs_scaled t
      rw [scaled_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)] at h1
      have h2 : (Wasm.IEEE32.scaledMagnitude t : ℝ) < 2 ^ 276 := by
        rw [← h1]
        calc |value t| * 2 ^ 149 < 2 ^ 127 * 2 ^ 149 :=
              mul_lt_mul_of_pos_right hm (by positivity)
          _ = 2 ^ 276 := by norm_num
      exact_mod_cast h2
    have hp := pack_spec (Wasm.IEEE32.scaledValue t < 0) _ hmax
    have hrep : roundedMagnitude (Wasm.IEEE32.scaledMagnitude t) =
        Wasm.IEEE32.scaledMagnitude t := by
      have he : Wasm.IEEE32.exponent t < 256 := Nat.mod_lt _ (by norm_num)
      have hf : Wasm.IEEE32.fraction t < 2 ^ 23 := Nat.mod_lt _ (by norm_num)
      by_cases he0 : Wasm.IEEE32.exponent t = 0
      · have : Wasm.IEEE32.scaledMagnitude t = Wasm.IEEE32.fraction t := by
          simp [Wasm.IEEE32.scaledMagnitude, he0]
        rw [this]
        simp [roundedMagnitude, show Wasm.IEEE32.fraction t < 16777216 by omega]
      · have : Wasm.IEEE32.scaledMagnitude t =
            (2 ^ 23 + Wasm.IEEE32.fraction t) * 2 ^ (Wasm.IEEE32.exponent t - 1) := by
          simp [Wasm.IEEE32.scaledMagnitude, he0]
        rw [this]
        exact roundedMagnitude_shifted _ _ (by omega) (by omega)
    have hsgn : decide (Wasm.IEEE32.scaledValue t < 0) = Wasm.IEEE32.sign t := by
      unfold Wasm.IEEE32.scaledValue
      cases hs : Wasm.IEEE32.sign t
      · simp
      · simp only [↓reduceIte, decide_eq_true_eq]
        have : (0 : Int) < Wasm.IEEE32.scaledMagnitude t := by exact_mod_cast Nat.pos_of_ne_zero hm0
        omega
    rw [hadd]
    have hsv : Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude
        (Wasm.IEEE32.scaledValue t < 0) (Wasm.IEEE32.scaledMagnitude t)) =
        Wasm.IEEE32.scaledValue t := by
      have h1 : ∀ w : UInt32, Wasm.IEEE32.scaledValue w = if Wasm.IEEE32.sign w then
          -(Wasm.IEEE32.scaledMagnitude w : Int) else Wasm.IEEE32.scaledMagnitude w :=
        fun _ => rfl
      rw [h1, hp.2.1, hp.2.2, hrep, hsgn, ← h1]
    simp only [value, hsv]

/-! ### Multiplication -/

theorem value_mul_scaled (a b : UInt32) :
    value a * value b =
      ((Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b : Int) : ℝ) / 2 ^ 298 := by
  simp only [value]; push_cast; field_simp

/-- The dyadic rounder of a product magnitude `n` in units of `2 ^ -298`, below `2 ^ 424`, gives a
finite word with the given sign and a magnitude `M` with `|M 2 ^ 149 - n| 2 ^ 24 ≤ n + 2 ^ 172`. -/
theorem dyadic_mixed (negative : Bool) (n : Nat) (hmax : n < 2 ^ 424) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n 149) ∧
    (Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundDyadicMagnitude negative n 149) = 0 ∨
      Wasm.IEEE32.sign (Wasm.IEEE32.roundDyadicMagnitude negative n 149) = negative) ∧
    |((Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundDyadicMagnitude negative n 149) * 2 ^ 149
      : Nat) : Int) - n| * 2 ^ 24 ≤ n + 2 ^ 172 := by
  by_cases hn : n = 0
  · subst hn
    have h : Wasm.IEEE32.roundDyadicMagnitude negative 0 149 = Wasm.IEEE32.signMask negative := by
      simp [Wasm.IEEE32.roundDyadicMagnitude]
    rw [h]
    cases negative <;> refine ⟨by unfold CodeLib.IEEE32.Finite; decide, Or.inl (by decide), by decide⟩
  have hlogUpper : Nat.log2 n < 424 := (Nat.log2_lt hn).2 hmax
  by_cases hsmall : Nat.log2 n ≤ 172
  · -- one rounding to a multiple of `2 ^ 149`, then an exact packing
    have hlt : n < 2 ^ 173 := (Nat.log2_lt hn).1 (by omega)
    set r := Wasm.IEEE32.roundShift n 149 with hr
    have hrb := roundShift_bounds n 149
    have hr24 : r ≤ 2 ^ 24 := by
      have : n / 2 ^ 149 < 2 ^ 24 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by
        rw [← pow_add]; exact hlt)
      omega
    have hactual : Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
        Wasm.IEEE32.roundScaledMagnitude negative r := by
      simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_iff_eq, hn, ↓reduceIte,
        show Nat.log2 n - (149 + 23) = 0 by omega, show (149 : ℕ) ≠ 0 by norm_num]
      rfl
    have hp := roundScaledMagnitude_spec negative r (by omega)
    have hs := sign_roundScaledMagnitude negative r (by omega)
    have hrep : roundedMagnitude r = r := by
      by_cases hr' : r < 2 ^ 24
      · simp [roundedMagnitude, show r < 16777216 by omega]
      · have : r = 2 ^ 23 * 2 ^ 1 := by omega
        rw [this]; exact roundedMagnitude_shifted _ _ (by norm_num) (by norm_num)
    rw [hactual]
    refine ⟨hp.1, Or.inr hs, ?_⟩
    rw [hp.2.1, hrep]
    have herr := abs_int_sub_le_of_error_cases _ _ _ (roundShift_error_cases n 149 (by norm_num))
    rw [← hr] at herr
    have hhalf : (2 ^ 149 / 2 : ℕ) = 2 ^ 148 := by norm_num
    rw [hhalf] at herr
    calc |((r * 2 ^ 149 : ℕ) : Int) - n| * 2 ^ 24 ≤ ((2 ^ 148 : ℕ) : Int) * 2 ^ 24 :=
          mul_le_mul_of_nonneg_right herr (by positivity)
      _ = 2 ^ 172 := by norm_num
      _ ≤ n + 2 ^ 172 := by omega
  · -- one rounding to 24 bits and a direct packing
    set o := Nat.log2 n - 172 with ho
    have ho1 : 1 ≤ o := by omega
    have ho2 : o ≤ 251 := by omega
    set T := 149 + o with hT
    set rounded := Wasm.IEEE32.roundShift n T with hrounded
    have hpowLower : 2 ^ 23 * 2 ^ T ≤ n := by
      rw [← pow_add, show 23 + T = Nat.log2 n by omega]
      exact Nat.log2_self_le hn
    have hpowUpper : n < 2 ^ 24 * 2 ^ T := by
      rw [← pow_add, show 24 + T = Nat.log2 n + 1 by omega]
      exact Nat.lt_log2_self
    have hquotLower : 2 ^ 23 ≤ n / 2 ^ T := (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
    have hquotUpper : n / 2 ^ T < 2 ^ 24 := (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
    have hrb := roundShift_bounds n T
    have hrl : 2 ^ 23 ≤ rounded := by omega
    have hru : rounded ≤ 2 ^ 24 := by omega
    have herr := abs_int_sub_le_of_error_cases _ _ _ (roundShift_error_cases n T (by omega))
    rw [← hrounded] at herr
    have hhalf : ((2 ^ T / 2 : ℕ) : Int) * 2 ^ 24 = (2 ^ 23 * 2 ^ T : ℕ) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
      rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
      push_cast
      ring
    have hbound : |((rounded * 2 ^ T : ℕ) : Int) - n| * 2 ^ 24 ≤ n + 2 ^ 172 := by
      calc |((rounded * 2 ^ T : ℕ) : Int) - n| * 2 ^ 24 ≤ ((2 ^ T / 2 : ℕ) : Int) * 2 ^ 24 :=
            mul_le_mul_of_nonneg_right herr (by positivity)
        _ = (2 ^ 23 * 2 ^ T : ℕ) := hhalf
        _ ≤ n := by exact_mod_cast hpowLower
        _ ≤ n + 2 ^ 172 := by omega
    have hshift : Nat.log2 n - (149 + 23) = o := by omega
    by_cases hcarry : rounded = 2 ^ 24
    · have hactual : Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
          Wasm.IEEE32.encodeFinite negative (o + 2) 0 := by
        simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_iff_eq, hn, ↓reduceIte, hshift,
          show o ≠ 0 by omega]
        rw [show Wasm.IEEE32.roundShift n (149 + o) = rounded from rfl, hcarry]
        simp only [↓reduceIte, show ¬(255 ≤ o + 1 + 1) by omega]
      have hfin := finite_encodeFinite negative (o + 2) 0 (by omega) (by norm_num)
      have hmag := scaledMagnitude_encodeFinite negative (o + 2) 0 (by omega) (by norm_num)
      have hsgn := sign_encodeFinite negative (o + 2) 0 (by omega) (by norm_num)
      rw [hactual]
      refine ⟨hfin, Or.inr hsgn, ?_⟩
      rw [hmag]
      simp only [show o + 2 ≠ 0 by omega, ↓reduceIte, Nat.add_zero]
      have : 2 ^ 23 * 2 ^ (o + 2 - 1) * 2 ^ 149 = rounded * 2 ^ T := by
        rw [hcarry, hT, show o + 2 - 1 = o + 1 by omega]
        ring
      rw [this]; exact hbound
    · have hfr : rounded - 2 ^ 23 < 2 ^ 23 := by omega
      have hactual : Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
          Wasm.IEEE32.encodeFinite negative (o + 1) (rounded - 2 ^ 23) := by
        simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_iff_eq, hn, ↓reduceIte, hshift,
          show o ≠ 0 by omega]
        rw [show Wasm.IEEE32.roundShift n (149 + o) = rounded from rfl]
        simp only [hcarry, ↓reduceIte, show ¬(255 ≤ o + 1) by omega]
      have hfin := finite_encodeFinite negative (o + 1) (rounded - 2 ^ 23) (by omega) hfr
      have hmag := scaledMagnitude_encodeFinite negative (o + 1) (rounded - 2 ^ 23) (by omega) hfr
      have hsgn := sign_encodeFinite negative (o + 1) (rounded - 2 ^ 23) (by omega) hfr
      rw [hactual]
      refine ⟨hfin, Or.inr hsgn, ?_⟩
      rw [hmag]
      simp only [show o + 1 ≠ 0 by omega, ↓reduceIte]
      have : (2 ^ 23 + (rounded - 2 ^ 23)) * 2 ^ (o + 1 - 1) * 2 ^ 149 = rounded * 2 ^ T := by
        rw [show 2 ^ 23 + (rounded - 2 ^ 23) = rounded by omega, show o + 1 - 1 = o by omega,
          hT]
        ring
      rw [this]; exact hbound

/-- A rounded binary32 product of finite words, below `2 ^ 126` in magnitude, is finite and
within `2 ^ -24` of its magnitude plus `2 ^ -150`. -/
theorem mul_mixed (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < 2 ^ 126) :
    Finite (Wasm.IEEE32.mul a b) ∧
      |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
        |value a * value b| / 2 ^ 24 + 1 / 2 ^ 150 := by
  rw [mul_finite_rounder a b ha hb]
  set neg := Wasm.IEEE32.sign a != Wasm.IEEE32.sign b
  set n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b with hn
  have hprod : Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b =
      if neg then -(n : Int) else n := by
    simp only [Wasm.IEEE32.scaledValue, neg, hn]
    cases Wasm.IEEE32.sign a <;> cases Wasm.IEEE32.sign b <;> simp
  have hvab : value a * value b = (if neg then -(n : ℝ) else n) / 2 ^ 298 := by
    rw [value_mul_scaled, hprod]; split <;> simp
  have habs : |value a * value b| = n / 2 ^ 298 := by
    rw [hvab, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 298)]
    split <;> simp
  have hmax : n < 2 ^ 424 := by
    have h1 : (n : ℝ) < 2 ^ 424 := by
      rw [habs, div_lt_iff₀ (by positivity)] at hbound
      calc (n : ℝ) < 2 ^ 126 * 2 ^ 298 := hbound
        _ = 2 ^ 424 := by norm_num
    exact_mod_cast h1
  obtain ⟨hf, hs, he⟩ := dyadic_mixed neg n hmax
  refine ⟨hf, ?_⟩
  set w := Wasm.IEEE32.roundDyadicMagnitude neg n 149
  set M := Wasm.IEEE32.scaledMagnitude w
  have hsvw : Wasm.IEEE32.scaledValue w = if neg then -(M : Int) else M := by
    show (if Wasm.IEEE32.sign w then -(M : Int) else M) = _
    rcases hs with h0 | hsg
    · have hM : M = 0 := h0
      rw [hM]; simp
    · rw [hsg]
  have hvw : value w = (if neg then -(M : ℝ) else M) / 2 ^ 149 := by
    rw [value, hsvw]; split <;> simp
  have hreal : |(M : ℝ) * 2 ^ 149 - (n : ℝ)| * 2 ^ 24 ≤ (n : ℝ) + 2 ^ 172 := by
    have h' := (Int.cast_le (R := ℝ)).mpr he
    push_cast at h'
    norm_num
    linarith
  have hdiff : |value w - value a * value b| = |(M : ℝ) * 2 ^ 149 - n| / 2 ^ 298 := by
    rw [hvw, hvab]
    have e : ∀ s : ℝ, s / 2 ^ 149 - (n : ℝ) / 2 ^ 298 = (s * 2 ^ 149 - n) / 2 ^ 298 := by
      intro s; field_simp
    split
    · rw [show -(M : ℝ) / 2 ^ 149 - -(n : ℝ) / 2 ^ 298 = -((M * 2 ^ 149 - n) / 2 ^ 298) by
        field_simp; ring, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 298)]
    · rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 298)]
  rw [hdiff, habs, div_le_iff₀ (by positivity)]
  have : ((n : ℝ) / 2 ^ 298 / 2 ^ 24 + 1 / 2 ^ 150) * 2 ^ 298 = (n + 2 ^ 172) / 2 ^ 24 := by
    field_simp
  rw [this, le_div_iff₀ (by positivity)]
  exact hreal

/-! ### `Float32` sums -/

theorem zero_bits : (0.0 : Float32).toBits = 0 := rfl

/-- Lean's `Float32` as an `Adder`: unit roundoff `2 ^ -24`, exact sums below `2 ^ 127`. -/
noncomputable def f32 : Adder Float32 where
  val x := value x.toBits
  fin x := Finite x.toBits
  add a b := a + b
  zero := 0.0
  u := 1 / 2 ^ 24
  bound0 := 2 ^ 126
  bound := 2 ^ 127
  u_nonneg := by positivity
  zero_fin := by rw [zero_bits]; unfold CodeLib.IEEE32.Finite; decide
  zero_val := by rw [zero_bits]; simp [value]; decide
  zero_add t ht hm := by
    show Finite (0.0 + t).toBits ∧ value (0.0 + t).toBits = value t.toBits
    rw [F32Bits.toBits_add, zero_bits]
    exact zero_add_exact _ ht (lt_of_le_of_lt hm (by norm_num))
  add_rel a b ha hb h := by
    show Finite (a + b).toBits ∧ |value (a + b).toBits - (value a.toBits + value b.toBits)| ≤
      1 / 2 ^ 24 * |value a.toBits + value b.toBits|
    rw [F32Bits.toBits_add]
    obtain ⟨h1, h2⟩ := add_relative _ _ ha hb h
    exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

theorem f32_u : f32.u = 1 / 2 ^ 24 := rfl

/-- Every element of an array of finite floats, read with `xs[i]!`, is finite: a missing element
is `0.0`. -/
theorem finite_get (xs : Array Float32) (hf : ∀ x ∈ xs, Finite x.toBits) (i : ℕ) :
    Finite xs[i]!.toBits := by
  by_cases hi : i < xs.size
  · rw [getElem!_pos xs i hi]; exact hf _ (Array.getElem_mem hi)
  · rw [getElem!_neg xs i hi]
    show Finite (0.0 : Float32).toBits
    rw [zero_bits]; unfold CodeLib.IEEE32.Finite; decide

theorem mul_approx (a b : Float32) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h : |value a.toBits * value b.toBits| < 2 ^ 126) :
    f32.Approx (a * b) (f32.val a * f32.val b) (f32.u * |f32.val a * f32.val b| + 1 / 2 ^ 150) := by
  show Finite (a * b).toBits ∧ |value (a * b).toBits - value a.toBits * value b.toBits| ≤
    1 / 2 ^ 24 * |value a.toBits * value b.toBits| + 1 / 2 ^ 150
  rw [F32Bits.toBits_mul]
  obtain ⟨h1, h2⟩ := mul_mixed _ _ ha hb h
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

theorem range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- A left-to-right sum of `K < 2 ^ 22` rounded binary32 products of finite floats, whose exact
products' magnitudes sum to at most `2 ^ 125`, as `dot_approx` bounds it. -/
theorem dot_raw (K : ℕ) (x y : ℕ → Float32) (hx : ∀ c, Finite (x c).toBits)
    (hy : ∀ c, Finite (y c).toBits) (hK : K < 2 ^ 22)
    (hP : ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| ≤ 2 ^ 125) :
    f32.Approx ((List.range K).foldl (fun acc c => acc + x c * y c) 0.0)
      (∑ c ∈ Finset.range K, value (x c).toBits * value (y c).toBits)
      (((1 + 1 / 2 ^ 24 : ℝ) ^ K - 1) *
          ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| +
        (1 + 1 / 2 ^ 24 : ℝ) ^ (K - 1) * (K * (1 / 2 ^ 150))) := by
  set P := ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits|
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKr : (K : ℝ) ≤ 2 ^ 22 := by exact_mod_cast hK.le
  have h2 := pow_le_two 24 (K - 1) (by
    have : ((K - 1 : ℕ) : ℝ) ≤ 2 ^ 22 := by exact_mod_cast (Nat.sub_le _ _).trans hK.le
    linarith)
  have hmul : ∀ c ∈ List.range K, f32.Approx (x c * y c) (f32.val (x c) * f32.val (y c))
      (f32.u * |f32.val (x c) * f32.val (y c)| + 1 / 2 ^ 150) := fun c hc =>
    mul_approx _ _ (hx c) (hy c) (by
      have h1 : |value (x c).toBits * value (y c).toBits| ≤ P :=
        Finset.single_le_sum (f := fun c => |value (x c).toBits * value (y c).toBits|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (List.mem_range.mp hc))
      have : (2 : ℝ) ^ 125 < 2 ^ 126 := by norm_num
      linarith)
  have hinner : (1 + 1 / 2 ^ 24 : ℝ) * P + K * (1 / 2 ^ 150) ≤ 2 ^ 126 := by
    have h1 : (1 + 1 / 2 ^ 24 : ℝ) * P ≤ (1 + 1 / 2 ^ 24) * 2 ^ 125 :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    have h3 : (K : ℝ) * (1 / 2 ^ 150) ≤ 2 ^ 22 * (1 / 2 ^ 150) :=
      mul_le_mul_of_nonneg_right hKr (by positivity)
    have h4 : (1 + 1 / 2 ^ 24 : ℝ) * 2 ^ 125 + 2 ^ 22 * (1 / 2 ^ 150) ≤ 2 ^ 126 := by norm_num
    linarith
  have hsumP : ((List.range K).map fun c => |f32.val (x c) * f32.val (y c)|).sum = P :=
    range_sum K _
  have h := dot_approx f32 (List.range K) x y (· * ·) (1 / 2 ^ 150) hmul
    (by rw [hsumP, f32_u, List.length_range]; exact hinner) (by
      rw [hsumP, f32_u, List.length_range]
      show _ < (2 : ℝ) ^ 127
      have hp : 0 ≤ (1 + 1 / 2 ^ 24 : ℝ) ^ (K - 1) := by positivity
      calc (1 + 1 / 2 ^ 24 : ℝ) ^ (K - 1) * ((1 + 1 / 2 ^ 24) * P + K * (1 / 2 ^ 150)) ≤
            (1 + 1 / 2 ^ 24 : ℝ) ^ (K - 1) * 2 ^ 126 := mul_le_mul_of_nonneg_left hinner hp
        _ < 2 * 2 ^ 126 := by gcongr
        _ = 2 ^ 127 := by norm_num)
  rw [hsumP, f32_u, List.length_range, range_sum] at h
  exact h

/-- `dot_raw` in closed form: within `γ_K Σ |x_c y_c| + K / 2 ^ 149`. -/
theorem dot_bound (K : ℕ) (x y : ℕ → Float32) (hx : ∀ c, Finite (x c).toBits)
    (hy : ∀ c, Finite (y c).toBits) (hK : K < 2 ^ 22)
    (hP : ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| ≤ 2 ^ 125) :
    Finite ((List.range K).foldl (fun acc c => acc + x c * y c) 0.0).toBits ∧
      |value ((List.range K).foldl (fun acc c => acc + x c * y c) 0.0).toBits -
          ∑ c ∈ Finset.range K, value (x c).toBits * value (y c).toBits| ≤
        (K : ℝ) / (2 ^ 24 - K) * ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| +
          K / 2 ^ 149 := by
  have h := dot_raw K x y hx hy hK hP
  refine ⟨h.1, h.2.trans ?_⟩
  have hP0 : 0 ≤ ∑ c ∈ Finset.range K, |value (x c).toBits * value (y c).toBits| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKr : (K : ℝ) < 2 ^ 22 := by exact_mod_cast hK
  have hg := gamma_pow 24 K (by linarith)
  have h2 := pow_le_two 24 (K - 1) (by
    have : ((K - 1 : ℕ) : ℝ) ≤ 2 ^ 22 := by exact_mod_cast (Nat.sub_le _ _).trans hK.le
    linarith)
  have e1 := mul_le_mul_of_nonneg_right hg hP0
  have hn0 : 0 ≤ (K : ℝ) * (1 / 2 ^ 150) := by positivity
  have e2 : (1 + 1 / 2 ^ 24 : ℝ) ^ (K - 1) * (K * (1 / 2 ^ 150)) ≤ 2 * (K * (1 / 2 ^ 150)) :=
    mul_le_mul_of_nonneg_right h2.le hn0
  have e3 : 2 * ((K : ℝ) * (1 / 2 ^ 150)) = K / 2 ^ 149 := by ring
  linarith

/-- `γ_2 = 2 / (2 ^ 24 - 2)` bounds `2 u + u ^ 2` for `u = 2 ^ -24`. -/
theorem gamma_two : (2 : ℝ) / 2 ^ 24 + 1 / 2 ^ 48 ≤ 2 / (2 ^ 24 - 2) := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by norm_num)]
  norm_num

/-- A rounded binary32 product followed by a rounded sum with a third float lies within
`γ_2 (|p q| + |c|) + 2 ^ -149` of `p q + c` for finite floats with `|p q| + |c| ≤ 2 ^ 125`. -/
theorem mul_add_bound (p q c : Float32) (hp : Finite p.toBits) (hq : Finite q.toBits)
    (hc : Finite c.toBits)
    (hm : |value p.toBits * value q.toBits| + |value c.toBits| ≤ 2 ^ 125) :
    Finite (p * q + c).toBits ∧
      |value (p * q + c).toBits - (value p.toBits * value q.toBits + value c.toBits)| ≤
        2 / (2 ^ 24 - 2) * (|value p.toBits * value q.toBits| + |value c.toBits|) +
          1 / 2 ^ 149 := by
  set P := |value p.toBits * value q.toBits|
  set C := |value c.toBits|
  have hP : 0 ≤ P := abs_nonneg _
  have hC : 0 ≤ C := abs_nonneg _
  have hpq : P < 2 ^ 126 := by
    have : (2 : ℝ) ^ 125 < 2 ^ 126 := by norm_num
    linarith
  obtain ⟨hf1, he1⟩ := mul_mixed _ _ hp hq hpq
  rw [← F32Bits.toBits_mul] at hf1 he1
  set m := value (p * q).toBits
  have hm1 : |m| ≤ P + (P / 2 ^ 24 + 1 / 2 ^ 150) := by
    have := abs_sub_abs_le_abs_sub m (value p.toBits * value q.toBits)
    linarith
  have hs : |m + value c.toBits| < 2 ^ 127 := by
    have := abs_add_le m (value c.toBits)
    have : P / 2 ^ 24 ≤ 2 ^ 125 / 2 ^ 24 := div_le_div_of_nonneg_right (by linarith)
      (by positivity)
    have : (2 : ℝ) ^ 125 + 2 ^ 125 / 2 ^ 24 + 1 / 2 ^ 150 < 2 ^ 127 := by norm_num
    linarith
  obtain ⟨hf2, he2⟩ := add_relative _ _ hf1 hc hs
  rw [← F32Bits.toBits_add] at hf2 he2
  refine ⟨hf2, ?_⟩
  have htri : |value (p * q + c).toBits - (value p.toBits * value q.toBits + value c.toBits)| ≤
      |m + value c.toBits| / 2 ^ 24 + (P / 2 ^ 24 + 1 / 2 ^ 150) := by
    have : value (p * q + c).toBits - (value p.toBits * value q.toBits + value c.toBits) =
        (value (p * q + c).toBits - (m + value c.toBits)) +
          (m - value p.toBits * value q.toBits) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add he2 he1)
  have hmc : |m + value c.toBits| ≤ P + (P / 2 ^ 24 + 1 / 2 ^ 150) + C :=
    (abs_add_le _ _).trans (by linarith)
  have hg := mul_le_mul_of_nonneg_right gamma_two (add_nonneg hP hC)
  have e1 : (P + (P / 2 ^ 24 + 1 / 2 ^ 150) + C) / 2 ^ 24 + (P / 2 ^ 24 + 1 / 2 ^ 150) =
      (2 / 2 ^ 24 + 1 / 2 ^ 48) * P + C / 2 ^ 24 + (1 / 2 ^ 150 + 1 / 2 ^ 174) := by ring
  have e2 : (2 / 2 ^ 24 + 1 / 2 ^ 48 : ℝ) * (P + C) =
      (2 / 2 ^ 24 + 1 / 2 ^ 48) * P + C / 2 ^ 24 + C * (1 / 2 ^ 24 + 1 / 2 ^ 48) := by ring
  have e3 : 0 ≤ C * (1 / 2 ^ 24 + 1 / 2 ^ 48 : ℝ) := by positivity
  have e4 : (1 / 2 ^ 150 + 1 / 2 ^ 174 : ℝ) ≤ 1 / 2 ^ 149 := by norm_num
  have e5 : |m + value c.toBits| / 2 ^ 24 ≤ (P + (P / 2 ^ 24 + 1 / 2 ^ 150) + C) / 2 ^ 24 :=
    div_le_div_of_nonneg_right hmc (by positivity)
  linarith

end Library.Numerics.Reductions.Binary32
