import Project.EulerCertificate.RetryCflReject

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann.Execution (boolWord)
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

def retryTrialFrame (frame : Locals) (n : Nat)
    (trials dt ratio source tag root : UInt64) (boundary : Vector) : Locals :=
  let locals := frame.locals.set 28 (.i64 (UInt64.ofNat n))
  let locals := locals.set 29 (.i64 trials)
  let locals := locals.set 30 (.i64 dt)
  let locals := locals.set 31 (.i64 ratio)
  let locals := locals.set 32 (.i64 source)
  let locals := locals.set 33 (.i64 source)
  let locals := locals.set 48 (.i64 boundary.energy.upper)
  let locals := locals.set 47 (.i64 boundary.energy.lower)
  let locals := locals.set 46 (.i64 boundary.energy.status)
  let locals := locals.set 45 (.i64 boundary.transverse.upper)
  let locals := locals.set 44 (.i64 boundary.transverse.lower)
  let locals := locals.set 43 (.i64 boundary.transverse.status)
  let locals := locals.set 42 (.i64 boundary.momentum.upper)
  let locals := locals.set 41 (.i64 boundary.momentum.lower)
  let locals := locals.set 40 (.i64 boundary.momentum.status)
  let locals := locals.set 39 (.i64 boundary.mass.upper)
  let locals := locals.set 38 (.i64 boundary.mass.lower)
  let locals := locals.set 37 (.i64 boundary.mass.status)
  let locals := locals.set 36 (.i64 root)
  let locals := locals.set 35 (.i64 root)
  let locals := locals.set 34 (.i64 tag)
  { frame with locals, values := [] }

def retryAcceptedFrame (frame : Locals) (dt root : UInt64) (boundary : Vector) : Locals :=
  let locals := frame.locals.set 1 (.i64 0)
  let locals := locals.set 2 (.i64 dt)
  let locals := locals.set 3 (.i64 root)
  let locals := locals.set 4 (.i64 root)
  let locals := locals.set 5 (.i64 boundary.mass.status)
  let locals := locals.set 6 (.i64 boundary.mass.lower)
  let locals := locals.set 7 (.i64 boundary.mass.upper)
  let locals := locals.set 8 (.i64 boundary.momentum.status)
  let locals := locals.set 9 (.i64 boundary.momentum.lower)
  let locals := locals.set 10 (.i64 boundary.momentum.upper)
  let locals := locals.set 11 (.i64 boundary.transverse.status)
  let locals := locals.set 12 (.i64 boundary.transverse.lower)
  let locals := locals.set 13 (.i64 boundary.transverse.upper)
  let locals := locals.set 14 (.i64 boundary.energy.status)
  let locals := locals.set 15 (.i64 boundary.energy.lower)
  let locals := locals.set 16 (.i64 boundary.energy.upper)
  let locals := locals.set 17 (.i64 1)
  { frame with locals, values := [] }

theorem RetryFrameAt.trial {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (ratio tag root : UInt64) (boundary : Vector) :
    RetryFrameAt (retryTrialFrame frame n trials dt ratio source tag root boundary)
      fuel n trials time dt alpha source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryTrialFrame]

theorem RetryScratch.trial {frame : Locals} (h : RetryScratch frame)
    (n : Nat) (trials dt ratio source tag root : UInt64) (boundary : Vector) :
    RetryScratch (retryTrialFrame frame n trials dt ratio source tag root boundary) := by
  unfold RetryScratch retryTrialFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem RetryFrameAt.accept {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (root : UInt64) (boundary : Vector) :
    RetryReturnedAt (retryAcceptedFrame frame dt root boundary) 0 dt root boundary := by
  constructor
  · simp [retryAcceptedFrame, h.params]
  · simp [retryAcceptedFrame, h.locals]
  · rfl
  · exact ⟨fuel, by simp [retryAcceptedFrame, h.params]⟩
  · simp [retryAcceptedFrame, h.locals]
  · simp [retryAcceptedFrame, h.locals]
  · simp [retryAcceptedFrame, h.locals]
  · simp [retryAcceptedFrame, h.locals]
  · intro i
    fin_cases i <;> simp [retryAcceptedFrame, h.locals, vectorValues, boundsValues]
  · simp [retryAcceptedFrame, h.locals]

#print axioms RetryFrameAt.trial
#print axioms RetryScratch.trial
#print axioms RetryFrameAt.accept
end Project.EulerCertificate.Execution
