import Project.ByteIO.ExecutionModel

namespace Project.ByteIO
open Wasm

def eofInitial : Store World := { echoInitial with host := {} }

def brokenHost : HostEnv World :=
  wasiEnv (fun _ cap => .ok cap)
    (fun w _ => if w.output.length < 2 then .ok 1 else .error 64)
    (fun _ _ => 0) (fun w => .ok (w.now + 1))
    (fun w _ => .ok { now := w.now + 1, ready := true })

def timeoutHost : HostEnv World :=
  wasiEnv (fun _ _ => .error 6) (fun _ cap => .ok cap)
    (fun _ _ => 0) (fun w => .ok (w.now + 1))
    (fun _ deadline => .ok { now := deadline, ready := false })

def retryHost : HostEnv World :=
  wasiEnv (fun w cap => if w.now.toNat ≤ 1 then .error 6 else .ok cap)
    (fun _ _ => .ok 1) (fun _ _ => 0) (fun w => .ok (w.now + 1))
    (fun w _ => .ok { now := w.now + 1, ready := true })

def caseCheck (status : UInt64) (input output : Bytes)
    (st : Store World) (values : List Value) : Bool :=
  decide (values = [.i64 status]) && st.host.input == input && st.host.output == output &&
    decide (st.globals.globals[2]? = some (.i64 1)) && decide (st.globals.globals[5]? = some (.i64 1))

def CasePost (status : UInt64) (input output : Bytes)
    (st : Store World) (values : List Value) : Prop :=
  values = [.i64 status] ∧ st.host.input = input ∧ st.host.output = output ∧
    st.globals.globals[2]? = some (.i64 1) ∧ st.globals.globals[5]? = some (.i64 1)

theorem caseCheck_sound (status : UInt64) (input output : Bytes)
    (st : Store World) (values : List Value) (h : caseCheck status input output st values = true) :
    CasePost status input output st values := by
  simpa [caseCheck, CasePost, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem brokenHost_satisfies : brokenHost.Satisfies Artifact.module wasiSpec :=
  wasiEnv_satisfies _ _ _ _ _ _ Artifact.imports_exact

theorem timeoutHost_satisfies : timeoutHost.Satisfies Artifact.module wasiSpec :=
  wasiEnv_satisfies _ _ _ _ _ _ Artifact.imports_exact

theorem retryHost_satisfies : retryHost.Satisfies Artifact.module wasiSpec :=
  wasiEnv_satisfies _ _ _ _ _ _ Artifact.imports_exact

end Project.ByteIO
