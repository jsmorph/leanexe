import CodeLib.IEEE32.Roundoff

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32RoundBounds
open Wasm CodeLib.IEEE32

theorem rounding_parameters {n bound : Nat} (hmin : 2 ^ 24 ≤ n)
    (hmax : n < 2 ^ bound) :
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ bound - 24 ∧
      2 ^ 23 ≤ rounded ∧ rounded ≤ 2 ^ 24 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < bound := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 23
  have hshift : 0 < shift := by simp only [shift]; omega
  have hshiftMax : shift ≤ bound - 24 := by simp only [shift]; omega
  have hpowLower : 2 ^ 23 * 2 ^ shift ≤ n := by
    rw [← pow_add]
    have heq : 23 + shift = Nat.log2 n := by simp only [shift]; omega
    rw [heq]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2 ^ 24 * 2 ^ shift := by
    rw [← pow_add]
    have heq : 24 + shift = Nat.log2 n + 1 := by simp only [shift]; omega
    rw [heq]
    exact Nat.lt_log2_self
  have hquotLower : 2 ^ 23 ≤ n / 2 ^ shift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2 ^ shift < 2 ^ 24 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ bound - 24 ∧
    2 ^ 23 ≤ Wasm.IEEE32.roundShift n shift ∧
      Wasm.IEEE32.roundShift n shift ≤ 2 ^ 24
  exact ⟨hshift, hshiftMax, by omega, by omega⟩

theorem roundScaledMagnitude_spec (negative : Bool) (n bound : Nat)
    (hBound : bound ≤ 276)
    (hmax : n < 2 ^ bound) :
    Finite (Wasm.IEEE32.roundScaledMagnitude negative n) ∧
      Wasm.IEEE32.scaledMagnitude
          (Wasm.IEEE32.roundScaledMagnitude negative n) = roundedMagnitude n ∧
      |(roundedMagnitude n : Int) - n| ≤ (2 ^ (bound - 25) : Nat) := by
  by_cases hsubnormal : n < 2 ^ 23
  · have hsubnormalNum : n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : n < 16777216 := by omega
    have hfinite := finite_encodeFinite negative 0 n (by norm_num) hsubnormal
    have hmagnitude :=
      scaledMagnitude_encodeFinite negative 0 n (by norm_num) hsubnormal
    simp [Wasm.IEEE32.roundScaledMagnitude, roundedMagnitude, hsubnormalNum,
      hexactNum] at hfinite hmagnitude ⊢
    exact ⟨hfinite, hmagnitude⟩
  by_cases hexact : n < 2 ^ 24
  · have hsubnormalNum : ¬n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : n < 16777216 := by norm_num at hexact ⊢; exact hexact
    have hlower : 2 ^ 23 ≤ n := by omega
    have hfraction : n - 2 ^ 23 < 2 ^ 23 := by omega
    have hfinite := finite_encodeFinite negative 1 (n - 2 ^ 23)
      (by norm_num) hfraction
    have hmagnitude :=
      scaledMagnitude_encodeFinite negative 1 (n - 2 ^ 23)
        (by norm_num) hfraction
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum]
    have hrounded : roundedMagnitude n = n := by
      simp [roundedMagnitude, hexactNum]
    have hmagnitude' :
        Wasm.IEEE32.scaledMagnitude
            (Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23)) = n := by
      rw [hmagnitude]
      norm_num
      omega
    rw [hactual, hrounded]
    exact ⟨hfinite, hmagnitude', by simp⟩
  · have hmin : 2 ^ 24 ≤ n := by omega
    have hsubnormalNum : ¬n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : ¬n < 16777216 := by norm_num at hexact ⊢; exact hexact
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change 0 < shift at hshift
    change shift ≤ bound - 24 at hshiftMax
    change 2 ^ 23 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 24 at hroundedMax
    have herrorCases := roundShift_error_cases n shift hshift
    have herrorHalf :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ shift / 2 : Nat) :=
      abs_int_sub_le_of_error_cases _ _ _ herrorCases
    have hhalf : 2 ^ shift / 2 ≤ 2 ^ (bound - 25) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
      rw [hk] at hshiftMax
      have hdiv : 2 ^ shift / 2 = 2 ^ k := by
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
      rw [hdiv]
      exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    have herror :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ (bound - 25) : Nat) :=
      herrorHalf.trans (by exact_mod_cast hhalf)
    by_cases hcarry : rounded = 2 ^ 24
    · have hcarry' :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
        simpa [rounded, shift] using hcarry
      have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry' ⊢
        exact hcarry'
      have hexponent : shift + 2 < 0xFF := by omega
      have hfinite := finite_encodeFinite negative (shift + 2) 0
        hexponent (by norm_num)
      have hmagnitude :=
        scaledMagnitude_encodeFinite negative (shift + 2) 0 (by omega)
          (by norm_num)
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, hcarryNum, show ¬253 ≤ shift by omega,
          Nat.add_assoc]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum, pow_succ,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        ring
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        simp only [if_neg (by omega : ¬shift + 2 = 0), Nat.add_zero]
        rw [show shift + 2 - 1 = shift + 1 by omega, pow_succ]
        rw [hcarry]
        ring_nf
      · exact herror
    · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
      have hcarry' :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
        simpa [rounded, shift] using hcarry
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry' ⊢
        exact hcarry'
      have hexponent : shift + 1 < 0xFF := by omega
      have hfinite := finite_encodeFinite negative (shift + 1)
        (rounded - 2 ^ 23) hexponent hfraction
      have hmagnitude :=
        scaledMagnitude_encodeFinite negative (shift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 23) := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, rounded, hcarryNum, show ¬254 ≤ shift by omega]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        rw [show shift + 1 - 1 = shift by omega]
        have hsum : 2 ^ 23 + (rounded - 2 ^ 23) = rounded := by omega
        rw [hsum]
        simp [show shift + 1 ≠ 0 by omega]
      · exact herror

theorem sign_roundScaledMagnitude (negative : Bool) (n bound : Nat)
    (hBound : bound ≤ 276)
    (hmax : n < 2 ^ bound) :
    Wasm.IEEE32.sign (Wasm.IEEE32.roundScaledMagnitude negative n) = negative := by
  by_cases hsubnormal : n < 2 ^ 23
  · have hsubnormalNum : n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 0 n := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum]
    rw [hactual]
    exact sign_encodeFinite negative 0 n (by norm_num) hsubnormal
  by_cases hexact : n < 2 ^ 24
  · have hsubnormalNum : ¬n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : n < 16777216 := by
      norm_num at hexact ⊢
      exact hexact
    have hfraction : n - 2 ^ 23 < 2 ^ 23 := by omega
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum]
    rw [hactual]
    exact sign_encodeFinite negative 1 (n - 2 ^ 23) (by norm_num) hfraction
  · have hmin : 2 ^ 24 ≤ n := by omega
    have hsubnormalNum : ¬n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : ¬n < 16777216 := by
      norm_num at hexact ⊢
      exact hexact
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨_hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change shift ≤ bound - 24 at hshiftMax
    change 2 ^ 23 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 24 at hroundedMax
    by_cases hcarry : rounded = 2 ^ 24
    · have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift,
          hcarryNum, show ¬253 ≤ shift by omega, Nat.add_assoc]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 23) := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift,
          rounded, hcarryNum, show ¬254 ≤ shift by omega]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 1) (rounded - 2 ^ 23)
        (by omega) hfraction


#print axioms roundScaledMagnitude_spec
#print axioms sign_roundScaledMagnitude
end Project.ProofKit.F32RoundBounds
