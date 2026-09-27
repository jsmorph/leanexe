import Project.ProofKit.F64OneSubtract

namespace Project.ProofKit.F64SubnormalScale
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem subtract_one_grid (a : UInt64)
    (hl : 0x3FF0000000000000 ≤ a) (hu : a ≤ 0x4000000000000000) :
    ∃ n : Nat, n ≤ 2^52 ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.sub a 0x3FF0000000000000) = n*2^1022 := by
  obtain ⟨ha, n, hn, hv⟩ := F64OneSubtract.one_interval_scaled a hl hu
  have hs := F64OneSubtract.subtract_one_exact a hl hu
  have he : value (Wasm.IEEE64.sub a 0x3FF0000000000000) =
      (n : ℝ)*2^1022/2^1074 := by
    rw [hs.2.1, value, hv]
    push_cast
    field_simp
    ring
  rw [value] at he
  have he' : (Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a 0x3FF0000000000000) : ℝ) =
      (n : ℝ)*2^1022 := (div_left_inj' (by positivity)).mp he
  have hei : Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a 0x3FF0000000000000) =
      (n : Int)*2^1022 := by exact_mod_cast he'
  have habs (word : UInt64) : (Wasm.IEEE64.scaledValue word).natAbs =
      Wasm.IEEE64.scaledMagnitude word := by
    simp only [Wasm.IEEE64.scaledValue]
    split <;> simp
  refine ⟨n, hn, ?_⟩
  rw [← habs, hei]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rfl

theorem scale_subtracted_one (a : UInt64)
    (hl : 0x3FF0000000000000 ≤ a) (hu : a ≤ 0x4000000000000000) :
    let r := Wasm.IEEE64.sub a 0x3FF0000000000000
    Finite (Wasm.IEEE64.mul 0x0010000000000000 r) ∧
    value (Wasm.IEEE64.mul 0x0010000000000000 r) = value r*(2 : ℝ)^(-1022 : Int) := by
  obtain ⟨n, hn, hmag⟩ := subtract_one_grid a hl hu
  have hs := F64OneSubtract.subtract_one_exact a hl hu
  have hmin : Wasm.IEEE64.scaledMagnitude 0x0010000000000000 = 2^52 := by decide
  have hp := F64ExactArithmetic.mul_exact_scaled 0x0010000000000000
    (Wasm.IEEE64.sub a 0x3FF0000000000000) (by rfl) hs.1 n 0 (by omega)
    (by rw [hmag, hmin]; ring)
    (by norm_num; omega)
  have hv : value 0x0010000000000000 = (2 : ℝ)^(-1022 : Int) := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  exact ⟨hp.1, by rw [hp.2, hv, mul_comm]⟩

#print axioms scale_subtracted_one
end Project.ProofKit.F64SubnormalScale
