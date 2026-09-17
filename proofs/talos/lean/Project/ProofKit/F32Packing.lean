import CodeLib.IEEE32.Roundoff

namespace Project.ProofKit.F32Packing
open CodeLib.IEEE32

set_option exponentiation.threshold 512

theorem rounding_parameters {n : Nat} (hmin : 2^24 ≤ n) (hmax : n < 2^276) :
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ 252 ∧ 2^23 ≤ rounded ∧ rounded ≤ 2^24 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < 276 := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 23
  have hpowLower : 2^23 * 2^shift ≤ n := by
    rw [← pow_add, show 23 + shift = Nat.log2 n by dsimp [shift]; omega]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2^24 * 2^shift := by
    rw [← pow_add, show 24 + shift = Nat.log2 n + 1 by dsimp [shift]; omega]
    exact Nat.lt_log2_self
  have hquotLower : 2^23 ≤ n / 2^shift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2^shift < 2^24 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := CodeLib.IEEE32.roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ 252 ∧
    2^23 ≤ Wasm.IEEE32.roundShift n shift ∧ Wasm.IEEE32.roundShift n shift ≤ 2^24
  dsimp only [shift] at *
  omega

theorem pack_spec (negative : Bool) (n : Nat) (hmax : n < 2^276) :
    Finite (Wasm.IEEE32.roundScaledMagnitude negative n) ∧
    Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundScaledMagnitude negative n) =
      roundedMagnitude n ∧
    Wasm.IEEE32.sign (Wasm.IEEE32.roundScaledMagnitude negative n) = negative := by
  by_cases hsmall : n < 2^151
  · have hs := CodeLib.IEEE32.roundScaledMagnitude_spec negative n hsmall
    exact ⟨hs.1, hs.2.1, CodeLib.IEEE32.sign_roundScaledMagnitude negative n hsmall⟩
  have hmin : 2^24 ≤ n := by omega
  have hsubnormalNum : ¬n < 8388608 := by omega
  have hexactNum : ¬n < 16777216 := by omega
  let shift := Nat.log2 n - 23
  let rounded := Wasm.IEEE32.roundShift n shift
  obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ := rounding_parameters hmin hmax
  change 0 < shift at hshift
  change shift ≤ 252 at hshiftMax
  change 2^23 ≤ rounded at hroundedMin
  change rounded ≤ 2^24 at hroundedMax
  by_cases hcarry : rounded = 2^24
  · have hcarryNum : Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 2) 0
      (by omega) (by norm_num)
    have hsign := sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
        shift, hcarryNum, show ¬255 ≤ shift + 2 by omega, Nat.add_assoc]
    have hrounded : roundedMagnitude n = rounded * 2^shift := by
      simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum, pow_succ,
        Nat.mul_assoc, Nat.mul_comm]
      ring
    rw [hactual, hrounded]
    refine ⟨hfinite, ?_, hsign⟩
    rw [hmagnitude]
    simp only [show shift + 2 ≠ 0 by omega, ↓reduceIte, Nat.add_zero]
    rw [show shift + 2 - 1 = shift + 1 by omega, pow_succ, hcarry]
    ring
  · have hfraction : rounded - 2^23 < 2^23 := by omega
    have hcarryNum : ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 1) (rounded - 2^23)
      (by omega) hfraction
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 1) (rounded - 2^23)
      (by omega) hfraction
    have hsign := sign_encodeFinite negative (shift + 1) (rounded - 2^23)
      (by omega) hfraction
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative (shift + 1) (rounded - 2^23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
        shift, rounded, hcarryNum, show ¬255 ≤ shift + 1 by omega]
    have hrounded : roundedMagnitude n = rounded * 2^shift := by
      simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
    rw [hactual, hrounded]
    refine ⟨hfinite, ?_, hsign⟩
    rw [hmagnitude, show shift + 1 - 1 = shift by omega,
      show 2^23 + (rounded - 2^23) = rounded by omega]
    simp

theorem scaledValue_pack (negative : Bool) (n : Nat) (hmax : n < 2^276) :
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hs := pack_spec negative n hmax
  simp [Wasm.IEEE32.scaledValue, hs.2.1, hs.2.2]

/-- Relative packing error, including carry into the next exponent. -/
theorem rounded_relative (n : Nat) :
    |(roundedMagnitude n : Int) - n| * (2^24 : Int) ≤ n := by
  by_cases hs : n < 2^24
  · have hsNum : n < 16777216 := by simpa using hs
    simp [roundedMagnitude, hsNum]
  have hn : n ≠ 0 := by omega
  have hl : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 (by omega)
  let shift := Nat.log2 n - 23
  have hshift : 0 < shift := by dsimp [shift]; omega
  have hp : 2^23 * 2^shift ≤ n := by
    rw [← pow_add, show 23 + shift = Nat.log2 n by dsimp [shift]; omega]
    exact Nat.log2_self_le hn
  have hm : roundedMagnitude n = Wasm.IEEE32.roundShift n shift * 2^shift := by
    simp only [roundedMagnitude, if_neg hs]
    change (if Wasm.IEEE32.roundShift n shift == 2^24 then
      2^23 * 2^(shift+1) else Wasm.IEEE32.roundShift n shift * 2^shift) = _
    split
    · next h =>
        have he : Wasm.IEEE32.roundShift n shift = 2^24 := by simpa using h
        rw [he, pow_succ]
        ring
    · rfl
  have he := abs_int_sub_le_of_error_cases _ _ _ (roundShift_error_cases n shift hshift)
  have hh : ((2^shift / 2 : Nat) : Int) * 2^24 = (2^23 * 2^shift : Nat) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
    rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
    push_cast
    ring
  rw [hm]
  calc
    _ ≤ ((2^shift / 2 : Nat) : Int) * 2^24 :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (2^23 * 2^shift : Nat) := hh
    _ ≤ n := by exact_mod_cast hp

theorem signed_pack_relative (z : Int) (hmax : z.natAbs < 2^276) :
    Finite (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) ∧
    |Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) - z| *
      (2^24 : Int) ≤ z.natAbs := by
  have hs := pack_spec (z < 0) z.natAbs hmax
  have hv := scaledValue_pack (z < 0) z.natAbs hmax
  have herr := rounded_relative z.natAbs
  refine ⟨hs.1, ?_⟩
  by_cases hz : z < 0
  · have hz' := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hz)
    rw [hv, if_pos (by simpa using hz)]
    rw [show -(roundedMagnitude z.natAbs : Int) - z =
      -((roundedMagnitude z.natAbs : Int) - z.natAbs) by omega, abs_neg]
    exact herr
  · have hz' := Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hz)
    rw [hv, if_neg (by simpa using hz)]
    rw [show (roundedMagnitude z.natAbs : Int) - z =
      (roundedMagnitude z.natAbs : Int) - z.natAbs by omega]
    exact herr

#print axioms rounding_parameters
#print axioms pack_spec
#print axioms rounded_relative
#print axioms signed_pack_relative
end Project.ProofKit.F32Packing
