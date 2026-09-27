import Project.ExpArm.Program
import Project.ExpArm.Model
import Project.TalosCompat
import Project.ProofKit.FixedFrame
import Interpreter.Wasm.Wp.Call

namespace Project.ExpArm.Spec
open Wasm Project.ProofKit

set_option maxRecDepth 16384

theorem rescale_exact (env : HostEnv Unit) (initial : Store Unit)
    (tmp scaleBits kBits : UInt64) :
    TerminatesWith env Project.ExpArm.module 1 initial
      [.i64 kBits, .i64 scaleBits, .i64 tmp]
      (fun final values => final = initial ∧
        values = [.i64 (rescale tmp scaleBits kBits)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.ExpArm.module func1 _ initial
    (func1Def.toLocals [.i64 tmp, .i64 scaleBits, .i64 kBits]) env
  unfold func1
  by_cases hk : kBits &&& 0x80000000 = 0
  all_goals
    by_cases hy : IEEE64.add (scaleBits + ((1022 : UInt64) <<< 52))
        (IEEE64.mul (scaleBits + ((1022 : UInt64) <<< 52)) tmp) < 0x3FF0000000000000
  all_goals
    repeat
      first
      | wp_fixed_frame [func1Def, hk, hy, Wasm.f64Mul, Wasm.f64Add, Wasm.f64Sub, reduceIte]
      | (refine wp_iff_cons rfl ?_; simp)
  all_goals simp [rescale, hk, hy]

#print axioms rescale_exact
end Project.ExpArm.Spec
