import LeanExe.Linux.CallTable

/-!
The bytes that a trace of the Linux call layer's events moved through a descriptor: `readData fd`
concatenates, for each `read` of `fd` whose result is at most its count, the first bytes of its
output region, as many as its result, and `writeData fd` the same for the input regions of the
`write` events of `fd`.  A read or write whose result lies above its count, a negated error number
among them, contributes nothing.
-/

namespace LeanExe.Linux

/-- The bytes that the event `e` returned as a `read` of `fd`. -/
def Event.readBytes (fd : UInt64) (e : Event) : List UInt8 :=
  if e.call = readCall ∧ arg e.args 0 = fd ∧ e.ret.toNat ≤ (arg e.args 2).toNat then
    e.output.take e.ret.toNat
  else []

/-- The bytes that the event `e` took as a `write` of `fd`. -/
def Event.writeBytes (fd : UInt64) (e : Event) : List UInt8 :=
  if e.call = writeCall ∧ arg e.args 0 = fd ∧ e.ret.toNat ≤ (arg e.args 2).toNat then
    (e.inputs.headD []).take e.ret.toNat
  else []

/-- The bytes that the reads of `fd` in `tr` returned, in order. -/
def readData (fd : UInt64) (tr : List Event) : List UInt8 := tr.flatMap (Event.readBytes fd)

/-- The bytes that the writes of `fd` in `tr` took, in order. -/
def writeData (fd : UInt64) (tr : List Event) : List UInt8 := tr.flatMap (Event.writeBytes fd)

end LeanExe.Linux
