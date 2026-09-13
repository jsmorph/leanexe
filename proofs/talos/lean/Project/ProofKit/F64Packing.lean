import CodeLib.IEEE64.Roundoff

namespace Project.ProofKit.F64Packing
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem rounding_parameters {n : Nat} (hmin : 2^53 ≤ n) (hmax : n < 2^2097) :
    let shift := Nat.log2 n - 52
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ 2044 ∧ 2^52 ≤ rounded ∧ rounded ≤ 2^53 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 53 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < 2097 := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 52
  have hpowLower : 2^52 * 2^shift ≤ n := by
    rw [← pow_add, show 52 + shift = Nat.log2 n by dsimp [shift]; omega]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2^53 * 2^shift := by
    rw [← pow_add, show 53 + shift = Nat.log2 n + 1 by dsimp [shift]; omega]
    exact Nat.lt_log2_self
  have hquotLower : 2^52 ≤ n / 2^shift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2^shift < 2^53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := CodeLib.IEEE32.roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ 2044 ∧
    2^52 ≤ Wasm.IEEE32.roundShift n shift ∧ Wasm.IEEE32.roundShift n shift ≤ 2^53
  dsimp only [shift] at *
  omega

theorem pack_spec (negative : Bool) (n : Nat) (hmax : n < 2^2097) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative n) ∧
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative n) =
      roundedMagnitude n ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude negative n) = negative := by
  by_cases hsmall : n < 2^1076
  · have hs := CodeLib.IEEE64.roundScaledMagnitude_spec negative n hsmall
    exact ⟨hs.1, hs.2.1, CodeLib.IEEE64.sign_roundScaledMagnitude negative n hsmall⟩
  have hmin : 2^53 ≤ n := by omega
  have hsubnormalNum : ¬n < 4503599627370496 := by omega
  have hexactNum : ¬n < 9007199254740992 := by omega
  let shift := Nat.log2 n - 52
  let rounded := Wasm.IEEE32.roundShift n shift
  obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ := rounding_parameters hmin hmax
  change 0 < shift at hshift
  change shift ≤ 2044 at hshiftMax
  change 2^52 ≤ rounded at hroundedMin
  change rounded ≤ 2^53 at hroundedMax
  by_cases hcarry : rounded = 2^53
  · have hcarryNum : Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 9007199254740992 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 2) 0
      (by omega) (by norm_num)
    have hsign := sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
        Wasm.IEEE64.encodeFinite negative (shift + 2) 0 := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
        shift, hcarryNum, show ¬2047 ≤ shift + 2 by omega, Nat.add_assoc]
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
  · have hfraction : rounded - 2^52 < 2^52 := by omega
    have hcarryNum : ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 9007199254740992 := by
      norm_num at hcarry ⊢
      simpa [rounded, shift] using hcarry
    have hfinite := finite_encodeFinite negative (shift + 1) (rounded - 2^52)
      (by omega) hfraction
    have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 1) (rounded - 2^52)
      (by omega) hfraction
    have hsign := sign_encodeFinite negative (shift + 1) (rounded - 2^52)
      (by omega) hfraction
    have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
        Wasm.IEEE64.encodeFinite negative (shift + 1) (rounded - 2^52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
        shift, rounded, hcarryNum, show ¬2047 ≤ shift + 1 by omega]
    have hrounded : roundedMagnitude n = rounded * 2^shift := by
      simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
    rw [hactual, hrounded]
    refine ⟨hfinite, ?_, hsign⟩
    rw [hmagnitude, show shift + 1 - 1 = shift by omega,
      show 2^52 + (rounded - 2^52) = rounded by omega]
    simp

theorem scaledValue_pack (negative : Bool) (n : Nat) (hmax : n < 2^2097) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hs := pack_spec negative n hmax
  simp [Wasm.IEEE64.scaledValue, hs.2.1, hs.2.2]

theorem signed_pack_relative (z : Int) (hmax : z.natAbs < 2^2097) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) - z| *
      (2^53 : Int) ≤ z.natAbs := by
  have hs := pack_spec (z < 0) z.natAbs hmax
  have hv := scaledValue_pack (z < 0) z.natAbs hmax
  have herr := roundedMagnitude_relative_error z.natAbs
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
#print axioms signed_pack_relative
end Project.ProofKit.F64Packing
