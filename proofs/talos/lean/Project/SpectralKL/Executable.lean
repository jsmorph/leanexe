import Project.SpectralKL.Kernel40
import Project.SpectralKL.Operations
import Project.SpectralKL.Equal
import Project.SpectralKL.Kernel2
import Project.ProofKit.F64Order
import LeanExe.Examples.SpectralKL

namespace Project.SpectralKL
open CodeLib.IEEE64
namespace Executable

set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 4096

theorem kernel40_model (d : UInt64) :
    LeanExe.Examples.SpectralKL.kernel40Polynomial d = kernel40Bits d := by
  simp [LeanExe.Examples.SpectralKL.kernel40Polynomial,
    LeanExe.Examples.SpectralKL.coefficients40, kernel40Bits, hornerBits,
    Operations.add, Operations.mul]

/-- The error theorem names the executable function, not a parallel algorithm. -/
theorem kernel40Polynomial_error (d : UInt64) (hd : Finite d) (bd : |value d| ≤ 1/2) :
    Finite (LeanExe.Examples.SpectralKL.kernel40Polynomial d) ∧
      |value (LeanExe.Examples.SpectralKL.kernel40Polynomial d) - kernel (1+value d)| ≤
        1/100000000000000 := by
  rw [kernel40_model]
  exact kernel40_error d hd bd

theorem kernel2_model (d : UInt64) :
    LeanExe.Examples.SpectralKL.kernel2Polynomial d = kernel2Bits d := by
  simp only [LeanExe.Examples.SpectralKL.kernel2Polynomial, kernel2Bits,
    Operations.add, Operations.mul]

theorem guard_domain (d : UInt64)
    (h : d &&& 0x7FFFFFFFFFFFFFFF ≤ 0x3FE0000000000000) :
    Finite d ∧ |value d| ≤ 1/2 := by
  have hf : Project.ProofKit.F64Order.finiteBits d = true := by
    simp only [Project.ProofKit.F64Order.finiteBits, decide_eq_true_eq,
      Project.ProofKit.F64Order.absBits, UInt64.lt_iff_toNat_lt]
    exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp h) (by decide)
  have hhbits : Project.ProofKit.F64Order.absBits 0x3FE0000000000000 =
      0x3FE0000000000000 := by decide
  have hb := Project.ProofKit.F64Order.abs_value_mono d 0x3FE0000000000000
    (by rw [hhbits]; exact h)
  refine ⟨(Project.ProofKit.F64Order.finiteBits_iff d).mp hf, ?_⟩
  have hh : |value 0x3FE0000000000000| = 1/2 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  simpa only [hh] using hb

/-- Every successful executable result has the claimed numerical accuracy.
The input domain is derived from the executable's own guard. -/
theorem kernel40_accepted (d : UInt64)
    (h : (LeanExe.Examples.SpectralKL.kernel40 d).status = 0) :
    Finite (LeanExe.Examples.SpectralKL.kernel40 d).bits ∧
      |value (LeanExe.Examples.SpectralKL.kernel40 d).bits - kernel (1+value d)| ≤
        1/100000000000000 := by
  by_cases hg : d &&& 0x7FFFFFFFFFFFFFFF ≤ 0x3FE0000000000000
  · simpa only [LeanExe.Examples.SpectralKL.kernel40, if_pos hg] using
      kernel40Polynomial_error d (guard_domain d hg).1 (guard_domain d hg).2
  · simp [LeanExe.Examples.SpectralKL.kernel40, hg] at h

theorem equalMoments_accepted (d : UInt64)
    (h : (LeanExe.Examples.SpectralKL.equalMoments d).status = 0) :
    (LeanExe.Examples.SpectralKL.equalMoments d).bits = equalMomentsBits d := by
  unfold LeanExe.Examples.SpectralKL.equalMoments at h ⊢
  split <;> simp_all [equalMomentsBits, Operations.mul]

theorem kernel2_accepted (d : UInt64)
    (h : (LeanExe.Examples.SpectralKL.kernel2 d).status = 0) :
    Finite (LeanExe.Examples.SpectralKL.kernel2 d).bits ∧
      |value (LeanExe.Examples.SpectralKL.kernel2 d).bits - kernel (1+value d)| ≤
        |value d|^3/10 + 71*arithmeticEpsilon := by
  by_cases hg : d &&& 0x7FFFFFFFFFFFFFFF ≤ 0x3FE0000000000000
  · simpa only [LeanExe.Examples.SpectralKL.kernel2, if_pos hg, kernel2_model] using
      kernel2_error d (guard_domain d hg).1 (guard_domain d hg).2
  · simp [LeanExe.Examples.SpectralKL.kernel2, hg] at h

theorem equalMoments_accepted_error (d : UInt64)
    (h : (LeanExe.Examples.SpectralKL.equalMoments d).status = 0) :
    Finite (LeanExe.Examples.SpectralKL.equalMoments d).bits ∧
      |value (LeanExe.Examples.SpectralKL.equalMoments d).bits - value d^2/2| ≤
        2*arithmeticEpsilon := by
  have hg : d &&& 0x7FFFFFFFFFFFFFFF ≤ 0x3FF0000000000000 := by
    by_contra hn
    simp [LeanExe.Examples.SpectralKL.equalMoments, hn] at h
  have hf : Project.ProofKit.F64Order.finiteBits d = true := by
    simp only [Project.ProofKit.F64Order.finiteBits, decide_eq_true_eq,
      Project.ProofKit.F64Order.absBits, UInt64.lt_iff_toNat_lt]
    exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp hg) (by decide)
  have hhbits : Project.ProofKit.F64Order.absBits 0x3FF0000000000000 =
      0x3FF0000000000000 := by decide
  have hb := Project.ProofKit.F64Order.abs_value_mono d 0x3FF0000000000000
    (by rw [hhbits]; exact hg)
  have hv : |value 0x3FF0000000000000| = 1 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  rw [equalMoments_accepted d h]
  exact equalMoments_error d ((Project.ProofKit.F64Order.finiteBits_iff d).mp hf)
    (by simpa only [hv] using hb)

end Executable
#print axioms Executable.kernel40_model
#print axioms Executable.kernel40Polynomial_error
#print axioms Executable.kernel40_accepted
#print axioms Executable.kernel2_accepted
#print axioms Executable.equalMoments_accepted_error
end Project.SpectralKL
