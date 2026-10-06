import Project.ProofKit.F64Bits

/-! The bits of the Euler solvers' float constants, and words that are not NaN patterns. -/

namespace Examples.Euler

open Project.ProofKit

theorem zero_toBits : (0 : Float).toBits = 0 := by decide +kernel
theorem half_toBits : (0.5 : Float).toBits = 0x3FE0000000000000 := by decide +kernel
theorem twoFifths_toBits : (0.4 : Float).toBits = 0x3FD999999999999A := by decide +kernel
theorem sevenFifths_toBits : (1.4 : Float).toBits = 0x3FF6666666666666 := by decide +kernel
theorem one_toBits : (1 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
theorem endTime_toBits : (0.8 : Float).toBits = 0x3FE999999999999A := by decide +kernel
theorem fifth_toBits : (0.2 : Float).toBits = 4596373779694328218 := by decide +kernel
theorem threeFifths_toBits : (0.6 : Float).toBits = 4603579539098121011 := by decide +kernel
theorem p029_toBits : (0.029 : Float).toBits = 4584015902316823577 := by decide +kernel
theorem p138_toBits : (0.138 : Float).toBits = 4594139994279152452 := by decide +kernel
theorem p1206_toBits : (1.206 : Float).toBits = 4608110160323255730 := by decide +kernel
theorem p3_toBits : (0.3 : Float).toBits = 4599075939470750515 := by decide +kernel
theorem p5323_toBits : (0.5323 : Float).toBits = 4602969751708575046 := by decide +kernel
theorem p15_toBits : (1.5 : Float).toBits = 4609434218613702656 := by decide +kernel

/-- A word whose exponent field is not all ones is not a NaN pattern. -/
theorem not_nan_of_exponent {w : UInt64} (h : ¬(w >>> 52) &&& 0x7FF = 0x7FF) :
    Wasm.IEEE64.isNaN w = false := by
  have hExp : Wasm.IEEE64.exponent w ≠ 0x7FF := by
    intro he
    apply h
    apply UInt64.toNat_inj.mp
    have hAnd : ((w >>> 52) &&& 0x7FF).toNat = w.toNat / 2 ^ 52 % 2 ^ 11 := by
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod _ 11
    rw [hAnd]
    simpa [Wasm.IEEE64.exponent] using he
  simp [Wasm.IEEE64.isNaN, hExp]

/-- A word below the infinities in magnitude is not a NaN pattern. -/
theorem not_nan_of_finite {w : UInt64} (h : w &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000) :
    Wasm.IEEE64.isNaN w = false := by
  refine not_nan_of_exponent fun he => ?_
  have hAbs : (w &&& 0x7FFFFFFFFFFFFFFF).toNat = w.toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have hExp : ((w >>> 52) &&& 0x7FF).toNat = w.toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 11
  have h1 := congrArg UInt64.toNat he
  rw [hExp] at h1
  have h2 := UInt64.lt_iff_toNat_lt.mp h
  rw [hAbs] at h2
  simp only [UInt64.reduceToNat] at h1 h2
  omega

theorem toBits_ofBits_of_finite {w : UInt64}
    (h : w &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000) : (Float.ofBits w).toBits = w := by
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  rfl

end Examples.Euler
