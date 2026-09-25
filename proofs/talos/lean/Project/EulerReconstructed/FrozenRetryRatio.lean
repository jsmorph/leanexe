import Project.EulerReconstructed.FrozenRetryGuard
import Project.EulerReconstructed.FrozenScalars

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.EulerRiemann.Frozen
open Project.ProofKit.F64Outward (Checked)
open Project.EulerOutwardSpeed.Execution (checkedValues)

def retryRatioFrame (frame : Locals) (n : Nat) (dt alpha : UInt64) (result : Checked) : Locals :=
  let locals := frame.locals.set 9 (.i64 (UInt64.ofNat n))
  let locals := locals.set 10 (.i64 dt)
  let locals := locals.set 11 (.i64 alpha)
  let locals := locals.set 13 (.i64 result.value)
  let locals := locals.set 12 (.i64 result.status)
  let locals := locals.set 14 (.i64 result.status)
  let locals := locals.set 15 (.i64 result.value)
  { frame with locals, values := [] }

theorem RetryFrameAt.ratio {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (result : Checked) :
    RetryFrameAt (retryRatioFrame frame n dt alpha result)
      fuel n trials time dt alpha source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryRatioFrame]

theorem RetryScratch.ratio {frame : Locals} (h : RetryScratch frame)
    (n : Nat) (dt alpha : UInt64) (result : Checked) :
    RetryScratch (retryRatioFrame frame n dt alpha result) := by
  unfold RetryScratch retryRatioFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem retry_ratio_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64)
    (done : Bool) (hn : n ≤ 800)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store
      (retryRatioFrame frame n dt alpha (OutwardCfl.gridRatioChecked n dt alpha)) env) :
    wp Project.EulerReconstructed.Frozen.«module» (retryTrial.take 16 ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  have hn64 : n < UInt64.size := by
    change n < 18446744073709551616
    omega
  have hWord := UInt64.toNat_ofNat_of_lt' hn64
  have hCall := gridRatioChecked_exact env store (UInt64.ofNat n) dt alpha
  simp only [hWord] at hCall
  unfold retryTrial retryLoop func125
  dsimp only
  reconstructed_retry_guard_peel
  refine wp_call_tw hCall ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  dsimp only [checkedValues]
  reconstructed_retry_guard_peel
  simpa [retryRatioFrame, hParams] using hNext

#print axioms RetryFrameAt.ratio
#print axioms RetryScratch.ratio
#print axioms retry_ratio_spec
end Project.EulerReconstructed.Frozen.Execution
