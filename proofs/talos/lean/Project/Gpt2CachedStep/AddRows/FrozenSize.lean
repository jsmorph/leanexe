import Project.Gpt2CachedStep.AddRows.FrozenLoop
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame

namespace Project.Gpt2CachedStep.Frozen.AddRows
open Wasm Project.ProofKit PackedFloatFrame

def sizeFrame (frame : Locals) (input : ByteArray) : Locals :=
  { frame with
    locals := (((((frame.locals.set 16 (.i64 (UInt64.ofNat input.size))).set 17 (.i64 4)).set
      14 (.i64 (UInt64.ofNat (input.size / 4)))).set 15 (.i64 4)).set
      0 (.i64 (UInt64.ofNat (4 * (input.size / 4))))).set 14 (.i64 (UInt64.ofNat (4 * (input.size / 4))))
    values := [] }

set_option maxRecDepth 16384 in
theorem size_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (input : ByteArray)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 22)
    (hValues : frame.values = []) (hSize : frame.params[2]? = some (.i64 (UInt64.ofNat input.size)))
    (hBound : input.size ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (sizeFrame frame input) env) :
    wp «module» (func30.take 18 ++ rest) Q store frame env := by
  have hDiv : UInt64.ofNat input.size / 4 = UInt64.ofNat (input.size / 4) := by
    exact (UInt64.ofNat_div (by change input.size < 18446744073709551616; omega) (by decide)).symm
  have hMul : UInt64.ofNat (input.size / 4) * 4 = UInt64.ofNat (4 * (input.size / 4)) := by
    rw [Nat.mul_comm 4 (input.size / 4)]
    simp
  have hSafe : ¬ -1 / (4 : UInt64) < UInt64.ofNat (input.size / 4) :=
    CheckedNatMul.guard_of_nat_fits (input.size / 4) 4
      (by change input.size / 4 * 4 < 18446744073709551616; omega) (by decide)
  simp only [func30, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hSize]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLocals, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hSafe)]
  wp_packed_frame [hParams, hLocals, hMul]
  exact hNext

#print axioms size_spec

end Project.Gpt2CachedStep.Frozen.AddRows
