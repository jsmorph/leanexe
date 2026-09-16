import Project.EulerCertificate.RetryRatio

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann.Execution (boolWord)

def retryStepBody : Wasm.Program :=
  match (retryTrial[26]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryCflRejectBody : Wasm.Program :=
  match (retryTrial[26]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

theorem retry_ratio_branches_shape : retryTrial = retryTrial.take 26 ++
    [.iff 0 0 retryStepBody retryCflRejectBody] := rfl

def retryCflRejectedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source : UInt64) : Locals :=
  let half := IEEE64.mul 0x3FE0000000000000 dt
  let locals := frame.locals.set 64 (.i64 (UInt64.ofNat n))
  let locals := locals.set 65 (.i64 trials)
  let locals := locals.set 66 (.i64 time)
  let locals := locals.set 67 (.i64 half)
  let locals := locals.set 68 (.i64 alpha)
  let locals := locals.set 69 (.i64 source)
  let locals := locals.set 70 (.i64 source)
  let locals := locals.set 71 (.i64 (UInt64.ofNat n))
  let locals := locals.set 72 (.i64 trials)
  let locals := locals.set 73 (.i64 time)
  let locals := locals.set 74 (.i64 half)
  let locals := locals.set 75 (.i64 alpha)
  let locals := locals.set 76 (.i64 source)
  let locals := locals.set 77 (.i64 source)
  let locals := locals.set 78 (.i64 0)
  let locals := locals.set 0 (.i64 0)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 half, .i64 alpha, .i64 source, .i64 source]
    locals
    values := [] }

theorem retryCflRejectedFrame_empty (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source : UInt64) :
    ({ retryCflRejectedFrame frame fuel n trials time dt alpha source with values := [] } : Locals) =
      retryCflRejectedFrame frame fuel n trials time dt alpha source := rfl

theorem RetryFrameAt.rejectCfl {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done) :
    RetryFrameAt (retryCflRejectedFrame frame fuel n trials time dt alpha source)
      (fuel - 1) n trials time (IEEE64.mul 0x3FE0000000000000 dt) alpha source
        outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryCflRejectedFrame]

theorem RetryScratch.rejectCfl {frame : Locals} (h : RetryScratch frame)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source : UInt64) :
    RetryScratch (retryCflRejectedFrame frame fuel n trials time dt alpha source) := by
  unfold RetryScratch retryCflRejectedFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem retry_cfl_reject_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64)
    (done : Bool)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (hSource : source ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store
      (retryCflRejectedFrame frame fuel n trials time dt alpha source) env) :
    wp Project.EulerCertificate.«module» (retryCflRejectBody ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  have hTracker := h.tracker
  obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
  unfold retryCflRejectBody retryTrial retryLoop func179
  dsimp only
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, f64Mul,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le]
  simpa [retryCflRejectedFrame, hParams, List.set] using hNext

#print axioms retry_ratio_branches_shape
#print axioms retryCflRejectedFrame_empty
#print axioms RetryFrameAt.rejectCfl
#print axioms RetryScratch.rejectCfl
#print axioms retry_cfl_reject_spec
end Project.EulerCertificate.Execution
