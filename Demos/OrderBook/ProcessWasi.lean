import Demos.OrderBook.Flat
import Demos.OrderBook.Process
import Verified.Wasi.ReflectCommand

/-! The order book's process compiled by the verified WASI compiler.  The list holds the program's
functions in calling order, from `emit` to `run`, and the process's functions after them.  `byteAt`
and the program's `@[inline]` functions unfold into their callers.  The reflection of `fillArrays`
takes about 270,000 heartbeats, above the default limit. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi LeanExe.Pipeline

instance : Flat State (Array UInt64 × Array UInt64 × Array UInt64 × Array UInt64 × Array UInt64 ×
    Array UInt64 × Array UInt64 × UInt64 × UInt64 × Bytes × Bytes × UInt64 × Bool) :=
  ⟨fun s => (s.oid, s.acct, s.qty, s.lvl, s.nxt, s.head, s.tail, s.nextId, s.count, s.carry,
    s.output, s.written, s.eof)⟩

instance : Flat (ProcessStep State) (Bool × UInt64 × State) :=
  ⟨fun result => (result.running, result.status, result.state)⟩

set_option Elab.async false
set_option maxHeartbeats 1000000 in
verified_compile_wasi io :=
  [Program.emit, Program.findSlot, Program.freeSlot, Program.predecessor, Program.bestPrice,
    Program.crosses, Program.fillArrays, Program.submitArrays, Program.stepArrays, Program.run,
    initial, wordsOf, eventBytes, tailBytes, runWords, remainingOutput, afterWrite, afterRead,
    writeStep, readStep, step, begin]

end Demos.OrderBook.Process
