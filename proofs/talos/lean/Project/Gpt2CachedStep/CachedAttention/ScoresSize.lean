import Project.Gpt2CachedStep.CachedAttention.ScoresLoop
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.ProofKit PackedFloatFrame

def scoresSizeFrame (frame : Locals) (position : Nat) : Locals :=
  { frame with
    locals := (((((((((frame.locals.set 101 (.i64 (UInt64.ofNat position))).set 102 (.i64 1)).set
      103 (.i64 (UInt64.ofNat (position + 1)))).set 0 (.i64 (UInt64.ofNat (position + 1)))).set
      103 (.i64 12)).set 104 (.i64 (UInt64.ofNat (position + 1)))).set
      101 (.i64 (UInt64.ofNat (12 * (position + 1))))).set 102 (.i64 4)).set
      1 (.i64 (UInt64.ofNat (4 * (12 * (position + 1)))))).set
      101 (.i64 (UInt64.ofNat (4 * (12 * (position + 1)))))
    values := [] }

set_option maxRecDepth 32768 in
theorem scoresSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (position : Nat)
    (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 114)
    (hValues : frame.values = []) (hPosition : frame.params[7]? = some (.i64 (UInt64.ofNat position)))
    (hBound : position < 128)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (scoresSizeFrame frame position) env) :
    wp «module» (func29.take 30 ++ rest) Q store frame env := by
  have hInc : UInt64.ofNat position + 1 = UInt64.ofNat (position + 1) := by simp
  have hSafeInc : ¬ UInt64.ofNat position + 1 < UInt64.ofNat position := by
    simpa only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using
      CheckedNatAdd.guard_of_fits position 1 (by change position + 1 < 18446744073709551616; omega)
  have hSafeInc' : ¬ UInt64.ofNat (position + 1) < UInt64.ofNat position := by
    simpa only [hInc] using hSafeInc
  have hNonzero : UInt64.ofNat (position + 1) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' (by change position + 1 < 18446744073709551616; omega)] at this
    change position + 1 = 0 at this
    omega
  have hMul : (12 : UInt64) * UInt64.ofNat (position + 1) = UInt64.ofNat (12 * (position + 1)) := by simp
  have hSafeMul : ¬ -1 / UInt64.ofNat (position + 1) < (12 : UInt64) :=
    CheckedNatMul.guard_of_nat_fits 12 (position + 1)
      (by change 12 * (position + 1) < 18446744073709551616; omega) hNonzero
  have hBytes : UInt64.ofNat (12 * (position + 1)) * 4 = UInt64.ofNat (4 * (12 * (position + 1))) := by
    rw [Nat.mul_comm 4 (12 * (position + 1))]
    simp
  have hSafeBytes : ¬ -1 / (4 : UInt64) < UInt64.ofNat (12 * (position + 1)) :=
    CheckedNatMul.guard_of_nat_fits (12 * (position + 1)) 4
      (by change 12 * (position + 1) * 4 < 18446744073709551616; omega) (by decide)
  simp only [func29, List.take, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hParams, hLocals, hValues, hPosition, hSafeInc', hInc, hNonzero,
        hSafeMul, hMul, hSafeBytes, hBytes]
    | (refine wp_iff_cons rfl ?_
       rw [ite_eq_right (by decide)])
  exact hNext

#print axioms scoresSize_spec

end Project.Gpt2CachedStep.CachedAttention
