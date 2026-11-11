import TestSupport.Bare.Theorems
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNDepth.DepthSpec

/-!
The statement `depth_terminates` of the instance that `clightn/check.sh` writes for the
bare-metal program of `recursive 1000` of `Verified/Examples/Fold.lean`, a recursion of depth
1,000: N's program judgment holds of the definitions and `main` of `clightgen`'s file either with
one volatile store to `lx_out` of each byte of the result and the result 0, or with no event and
the code of `unreachable`, which the recursion reaches at the depth limit.  The file's definitions
include the functions of the module on `double`, which `main` does not reach and which N does not
cover, and `progOk` checks the functions that `main` reaches.  `bare_n` carries the copy's theorem
`compiled.recursive.program` to the statement, and the kernel computes the bytes of the result
after `recursive_id`, since `recursive` recurses by well-founded recursion.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

theorem recursive_id : ∀ (k : Nat) (n : UInt64), n.toNat = k →
    Verified.Examples.Fold.recursive n = n
  | 0, n, h => by
      have hn : n = 0 := UInt64.toNat_inj.mp (by simpa using h)
      subst hn
      rw [Verified.Examples.Fold.recursive]
      rfl
  | k + 1, n, h => by
      have hn : n ≠ 0 := fun e => by simp [e] at h
      have hk : (n - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le n 1 (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
        simp [h]
      rw [Verified.Examples.Fold.recursive, ite_eq_right hn, recursive_id k (n - 1) hk]
      exact UInt64.sub_add_cancel n 1

set_option maxHeartbeats 4000000 in
theorem depth_terminates : stmt_depth_terminates := by
  refine (bare_n ?_ (Verified.Examples.Fold.compiled.recursive.program _ _)).imp_right And.right
  rw [recursive_id 1000 1000 rfl]
  inst_ok

end ClightN.Proof

run_cmd ClightN.Read.dump
