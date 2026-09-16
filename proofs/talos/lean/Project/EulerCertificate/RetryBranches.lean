import Project.EulerCertificate.RetryTrialFrame

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann.Execution (boolWord)
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

def retryRejectBody : Wasm.Program :=
  match (retryStepBody[37]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryAcceptBody : Wasm.Program :=
  match (retryStepBody[37]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

theorem retry_trial_branches_shape : retryStepBody = retryStepBody.take 34 ++
    [.localGet 42, .constI64 0, .eqI64, .iff 0 0 retryRejectBody retryAcceptBody] := rfl

def retryRejectedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source : UInt64) : Locals :=
  let half := IEEE64.mul 0x3FE0000000000000 dt
  let locals := frame.locals.set 49 (.i64 (UInt64.ofNat n))
  let locals := locals.set 50 (.i64 trials)
  let locals := locals.set 51 (.i64 time)
  let locals := locals.set 52 (.i64 half)
  let locals := locals.set 53 (.i64 alpha)
  let locals := locals.set 54 (.i64 source)
  let locals := locals.set 55 (.i64 source)
  let locals := locals.set 56 (.i64 (UInt64.ofNat n))
  let locals := locals.set 57 (.i64 trials)
  let locals := locals.set 58 (.i64 time)
  let locals := locals.set 59 (.i64 half)
  let locals := locals.set 60 (.i64 alpha)
  let locals := locals.set 61 (.i64 source)
  let locals := locals.set 62 (.i64 source)
  let locals := locals.set 63 (.i64 0)
  let locals := locals.set 0 (.i64 0)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 half, .i64 alpha, .i64 source, .i64 source]
    locals
    values := [] }

theorem retryRejectedFrame_empty (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source : UInt64) :
    ({ retryRejectedFrame frame fuel n trials time dt alpha source with values := [] } : Locals) =
      retryRejectedFrame frame fuel n trials time dt alpha source := rfl

theorem RetryFrameAt.reject {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done) :
    RetryFrameAt (retryRejectedFrame frame fuel n trials time dt alpha source)
      (fuel - 1) n trials time (IEEE64.mul 0x3FE0000000000000 dt) alpha source
        outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryRejectedFrame]

theorem RetryScratch.reject {frame : Locals} (h : RetryScratch frame)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source : UInt64) :
    RetryScratch (retryRejectedFrame frame fuel n trials time dt alpha source) := by
  unfold RetryScratch retryRejectedFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem retry_reject_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64)
    (done : Bool)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (hSource : source ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store
      (retryRejectedFrame frame fuel n trials time dt alpha source) env) :
    wp Project.EulerCertificate.«module» (retryRejectBody ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  have hTracker := h.tracker
  obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
  unfold retryRejectBody retryStepBody retryTrial retryLoop func179
  dsimp only
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, f64Mul,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le]
  simpa [retryRejectedFrame, hParams, List.set] using hNext

theorem retry_accept_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel trials time dt alpha source ratio root : UInt64) (boundary : Vector)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 dt, .i64 alpha, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 121) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store
      (retryAcceptedFrame (retryTrialFrame frame n trials dt ratio source 1 root boundary) dt root boundary) env) :
    wp Project.EulerCertificate.«module» (retryAcceptBody ++ rest) Q store
      (retryTrialFrame frame n trials dt ratio source 1 root boundary) env := by
  unfold retryAcceptBody retryStepBody retryTrial retryLoop func179
  dsimp only
  wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals]
  simpa [retryAcceptedFrame, retryTrialFrame, hParams] using hNext

#print axioms retry_trial_branches_shape
#print axioms RetryFrameAt.reject
#print axioms RetryScratch.reject
#print axioms retry_reject_spec
#print axioms retry_accept_spec
end Project.EulerCertificate.Execution
