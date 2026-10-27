import Demos.RunningSum.Compiled
import Demos.RunningSum.Stream
import Verified.Wasi.ReflectCommand

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi LeanExe.Pipeline

instance : Flat State (Decimal × Array UInt64 × Bytes × UInt64 × Bytes × UInt64 × Bool) :=
  ⟨fun state => (state.total, state.line, state.input, state.cursor, state.output, state.written, state.eof)⟩

instance : Flat (ProcessStep State) (Bool × UInt64 × State) :=
  ⟨fun result => (result.running, result.status, result.state)⟩

set_option Elab.async false
verified_compile_wasi io :=
  [zero, parse, magnitudeLess, combineMagnitude, add, render, initial, completeLine, consumeInput,
    remainingOutput, afterWrite, afterRead, writeStep, readStep, step, begin]

end Demos.RunningSum
