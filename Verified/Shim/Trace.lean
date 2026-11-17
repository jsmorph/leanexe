import LeanExe.Linux.Trace
import Verified.Shim.Footprint

/-!
The bytes that a trace of images moved through a descriptor.  `committedReads trace` concatenates
the bytes that the `fd_read` events of a WASI trace committed, and `committedWrites output trace`
the first `committed` bytes that its `fd_write` events to `output` offered.  For layer events that
are images of a WASI trace, the layer's `readData 0` and `writeData` of the stream's descriptor
are these byte strings: a result above the request's count, an error number among them, moves no
bytes on either side.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The bytes that the `fd_read` events of `trace` committed, in order. -/
def committedReads (trace : List Wasi.Event) : List UInt8 :=
  trace.flatMap fun
    | .read _ reply => reply.committed.data.data.toList
    | _ => []

/-- The bytes that the `fd_write` events of `trace` to `output` committed, in order: the first
`committed` bytes that each offered. -/
def committedWrites (output : Output) (trace : List Wasi.Event) : List UInt8 :=
  trace.flatMap fun
    | .write target bytes reply =>
      if target = output then bytes.data.data.toList.take reply.committed.toNat else []
    | _ => []

theorem readCall_ne_writeCall : Linux.readCall ≠ Linux.writeCall := by decide

theorem Output.fd_inj {output target : Output} (h : target.fd = output.fd) : target = output := by
  cases target <;> cases output <;> first | rfl | cases h

theorem image_readData {e : Wasi.Event} {l : List Linux.Event} (image : Image e l) :
    Linux.readData 0 l = committedReads [e] := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, args, rfl⟩ := image
    by_cases within : x.ret.toNat ≤ count.toNat
    · simp [Linux.readData, committedReads, Linux.Event.readBytes, call, args, Linux.arg,
        readReply, within, Transfer.committed, bytesOfList]
    · simp only [Linux.readData, committedReads, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Linux.Event.readBytes, call, args, Linux.arg, List.getD_cons_zero,
        List.getD_cons_succ, within, and_false, ↓reduceIte, readReply]
      split <;> rfl
  | write output bytes reply =>
    obtain ⟨x, a, rfl, call, _, _, _⟩ := image
    simp [Linux.readData, committedReads, Linux.Event.readBytes, call,
      readCall_ne_writeCall.symm]
  | exit code =>
    cases image
    rfl
  | exitTrap code message =>
    cases image
    rfl
  | sys call args reply => exact image.elim

theorem image_writeData (output : Output) {e : Wasi.Event} {l : List Linux.Event}
    (image : Image e l) : Linux.writeData output.fd l = committedWrites output [e] := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, _, _⟩ := image
    simp [Linux.writeData, committedWrites, Linux.Event.writeBytes, call, readCall_ne_writeCall]
  | write target bytes reply =>
    obtain ⟨x, a, rfl, call, args, inputs, rfl⟩ := image
    by_cases same : target = output
    · subst same
      simp only [Linux.writeData, committedWrites, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Linux.Event.writeBytes, call, args, inputs, Linux.arg,
        List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, true_and,
        ↓reduceIte, writeReply]
      by_cases within : x.ret.toNat ≤ (UInt64.ofNat bytes.data.size).toNat
      · simp only [within, ↓reduceIte, Transfer.committed]
      · simp only [within, ↓reduceIte]
        split <;> rfl
    · have apart : target.fd ≠ output.fd := fun h => same (Output.fd_inj h)
      simp [Linux.writeData, committedWrites, Linux.Event.writeBytes, args, Linux.arg, same,
        apart]
  | exit code =>
    cases image
    rfl
  | exitTrap code message =>
    cases image
    rfl
  | sys call args reply => exact image.elim

theorem committedReads_cons (e : Wasi.Event) (es : List Wasi.Event) :
    committedReads (e :: es) = committedReads [e] ++ committedReads es := by
  simp [committedReads]

theorem committedWrites_cons (output : Output) (e : Wasi.Event) (es : List Wasi.Event) :
    committedWrites output (e :: es) =
      committedWrites output [e] ++ committedWrites output es := by
  simp [committedWrites]

/-- The bytes that the reads of descriptor 0 returned in images of a WASI trace are those that its
`fd_read` events committed. -/
theorem Images.readData {trace : List Wasi.Event} {ls : List Linux.Event}
    (h : Images trace ls) : Linux.readData 0 ls = committedReads trace := by
  induction h with
  | nil => rfl
  | @cons e l es ls image _ ih =>
    rw [committedReads_cons, ← image_readData image, ← ih]
    simp [Linux.readData]

/-- The bytes that the writes of a stream's descriptor took in images of a WASI trace are those
that its `fd_write` events to the stream committed. -/
theorem Images.writeData (output : Output) {trace : List Wasi.Event} {ls : List Linux.Event}
    (h : Images trace ls) : Linux.writeData output.fd ls = committedWrites output trace := by
  induction h with
  | nil => rfl
  | @cons e l es ls image _ ih =>
    rw [committedWrites_cons, ← image_writeData output image, ← ih]
    simp [Linux.writeData]

end Verified.Shim
