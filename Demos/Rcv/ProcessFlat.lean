import Demos.Rcv.Process
import LeanExe.Pipeline.Implements
import Verified.Source

/-! The representation of the tabulators' process state, which the Oakland process of
`Demos/Rcv/ProcessWasi.lean` and the Maine process of `Demos/Rcv/Maine/ProcessWasi.lean` share: the
`Flat` instances of the state and of a step's result that `verified_compile_wasi` reads, the
state's type `stateTy` in the compiled module, and `sourceState`, the value of that type that holds
a state. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi LeanExe.Pipeline Verified

instance : Flat State (Bytes × UInt64) :=
  ⟨fun s => (s.output, s.written)⟩

instance : Flat (ProcessStep State) (Bool × UInt64 × State) :=
  ⟨fun result => (result.running, result.status, result.state)⟩

def stateTy : Ty :=
  .pair .bytes .word

def sourceState (s : State) : stateTy.denote := (s.output, s.written)

end Demos.Rcv.Process
