import Project.LebU32.Copy

/-!
# Byte-copy loop exit

The copy loop exits through `br 1` when its source and destination indices are
equal.  This lemma keeps that control-flow prefix independent of the block
continuation that follows it.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem copyExitPos (env : HostEnv Unit) (stC : Store Unit)
    (g0 v : UInt64) (k : Nat) (e : Nat → UInt64)
    (CPOST : Assertion Unit)
    (hB1 : CPOST (.Break 1 stC (cFramePos g0 v k k e))) :
    wp «module» copyBody CPOST stC (cFramePos g0 v k k e) env := by
  unfold copyBody
  simp only [cFramePos]
  wp_run
  simpa [cFramePos] using hB1

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem copyExitNeg (env : HostEnv Unit) (stC : Store Unit)
    (g0 v : UInt64) (k : Nat) (e : Nat → UInt64)
    (CPOST : Assertion Unit)
    (hB1 : CPOST (.Break 1 stC (cFrameNeg g0 v k k e))) :
    wp «module» copyBody CPOST stC (cFrameNeg g0 v k k e) env := by
  unfold copyBody
  simp only [cFrameNeg]
  wp_run
  simpa [cFrameNeg] using hB1

end Project.LebU32.Spec
