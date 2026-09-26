import Project.ByteIO.ArtifactModule

namespace Project.ByteIO
open Wasm

def exampleInput : Bytes := [0, 255, 13, 10]

def echoInitial : Store World :=
  { (Artifact.module.initialStore : Store World) with host := { input := exampleInput } }

/-- One read followed by four one-byte writes exercises genuine partial
output progress, including the clock check between committed prefixes. -/
def partialHost : HostEnv World :=
  wasiEnv (fun _ cap => .ok cap) (fun _ _ => .ok 1) (fun _ _ => 0)
    (fun w => .ok (w.now + 1))
    (fun w _ => .ok { now := w.now + 1, ready := true })

theorem partialHost_satisfies : partialHost.Satisfies Artifact.module wasiSpec :=
  wasiEnv_satisfies _ _ _ _ _ _ Artifact.imports_exact

def echoCheck (st : Store World) (values : List Value) : Bool :=
  decide (values = [.i64 0]) && st.host.input.isEmpty && st.host.output == exampleInput &&
    decide (st.globals.globals[2]? = st.globals.globals[5]?)

def EchoPost (st : Store World) (values : List Value) : Prop :=
  values = [.i64 0] ∧ st.host.input = [] ∧ st.host.output = exampleInput ∧
    st.globals.globals[2]? = st.globals.globals[5]?

end Project.ByteIO
