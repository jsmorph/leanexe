import LeanExe.Linux.Trace
import Verified.Shim.Footprint

/-!
The bytes that a trace of images moved through a descriptor.  `committedReads fd trace`
concatenates the bytes that the reads of `fd` among the events of a WASI trace committed: those of
an `fd_read` of the stream when `fd` is 0, and those of an `fd_read` of a handle of `fd` that
returned errno 0, as many as its count.  `committedWrites fd trace` concatenates the first
`committed` bytes that each `fd_write` of the stream of `fd` offered and the bytes, as many as the
count, that each successful `fd_write` of a handle of `fd` offered.  For layer events that are
images of a WASI trace, the layer's `readData fd` and `writeData fd` are these byte strings: a
result above the request's count, an error number among them, moves no bytes on either side, and
the shim's other calls neither read nor write.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The bytes that the WASI event `e` read from `fd`. -/
def eventReads (fd : UInt64) : Wasi.Event → List UInt8
  | .read _ reply => if fd = 0 then reply.committed.data.data.toList else []
  | .sys call args (.returned errno outputs) =>
    if call = Call.fdRead ∧ errno = 0 ∧ args.head?.map Arg.value = some fd then
      (outputs.headD Bytes.empty).data.data.toList.take
        (littleEndian (outputs.getD 1 Bytes.empty)).toNat
    else []
  | _ => []

/-- The bytes that the WASI event `e` wrote to `fd`. -/
def eventWrites (fd : UInt64) : Wasi.Event → List UInt8
  | .write output bytes reply =>
    if output.fd = fd then bytes.data.data.toList.take reply.committed.toNat else []
  | .sys call args (.returned errno outputs) =>
    if call = Call.fdWrite ∧ errno = 0 ∧ args.head?.map Arg.value = some fd then
      match args with
      | [_, .bytes data] =>
        data.data.data.toList.take (littleEndian (outputs.headD Bytes.empty)).toNat
      | _ => []
    else []
  | _ => []

/-- The bytes that the events of `trace` read from `fd`, in order. -/
def committedReads (fd : UInt64) (trace : List Wasi.Event) : List UInt8 :=
  trace.flatMap (eventReads fd)

/-- The bytes that the events of `trace` wrote to `fd`, in order. -/
def committedWrites (fd : UInt64) (trace : List Wasi.Event) : List UInt8 :=
  trace.flatMap (eventWrites fd)

theorem readCall_ne_writeCall : Linux.readCall ≠ Linux.writeCall := by decide

/-- Layer events none of which is a `read` read nothing. -/
theorem readData_none {fd : UInt64} {l : List Linux.Event}
    (none : ∀ x ∈ l, x.call ≠ Linux.readCall) : Linux.readData fd l = [] := by
  simp only [Linux.readData, List.flatMap_eq_nil_iff]
  intro x member
  simp [Linux.Event.readBytes, none x member]

/-- Layer events none of which is a `write` wrote nothing. -/
theorem writeData_none {fd : UInt64} {l : List Linux.Event}
    (none : ∀ x ∈ l, x.call ≠ Linux.writeCall) : Linux.writeData fd l = [] := by
  simp only [Linux.writeData, List.flatMap_eq_nil_iff]
  intro x member
  simp [Linux.Event.writeBytes, none x member]

theorem randomCalls_calls {a : UInt64} {length : Nat} {reply : Transfer (List Bytes)} :
    ∀ {done : Nat} {filled : List UInt8} {l : List Linux.Event},
      RandomCalls a length done filled l reply → ∀ x ∈ l, x.call = Linux.getrandomCall
  | _, _, [], _ => fun _ member => nomatch member
  | _, _, _ :: _, ⟨_, _, _, _, rfl, rest⟩ => by
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · split at rest
      · exact randomCalls_calls rest x member
      · obtain ⟨rfl, _⟩ := rest
        cases member

theorem openCalls_calls {L : ShimLayout} {dir : UInt64} {path how : List UInt8}
    {reply : Transfer (List Bytes)} :
    ∀ {calls : Nat} {l : List Linux.Event},
      OpenCalls L dir path how calls l reply → ∀ x ∈ l, x.call = Linux.openat2Call
  | _, [], h => h.elim
  | _, _ :: _, ⟨_, rfl, rest⟩ => by
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · split at rest
      · exact openCalls_calls rest x member
      · obtain ⟨rfl, _⟩ := rest
        cases member

/-- The calls of an image of a flat call other than the handle forms of `fd_read` and
`fd_write`: `clock_gettime`, `getrandom`, `openat2`, and `close`. -/
theorem sysImage_calls {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {call : Call} {args : List Arg} {reply : Transfer (List Bytes)}
    {l : List Linux.Event} (image : SysImage F L I events call args reply l)
    (notRead : call ≠ Call.fdRead)
    (notWrite : call ≠ Call.fdWrite) :
    ∀ x ∈ l, x.call ≠ Linux.readCall ∧ x.call ≠ Linux.writeCall := by
  have member := sysImage_mem image
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  have distinct : ∀ x : Linux.Event, x.call ∈ [Linux.clockGettimeCall, Linux.getrandomCall,
      Linux.openat2Call, Linux.closeCall] → x.call ≠ Linux.readCall ∧ x.call ≠ Linux.writeCall := by
    intro x listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with same | same | same | same <;> rw [same] <;> decide
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sysImage_clock] at image
    unfold ClockImage at image
    split at image
    · split at image
      · obtain ⟨_, _, rfl, _⟩ := image
        intro x member
        obtain rfl := List.mem_singleton.mp member
        exact distinct _ (by simp)
      · obtain ⟨rfl, _⟩ := image
        intro x member
        cases member
    · exact image.elim
  · rw [sysImage_random] at image
    unfold RandomImage at image
    split at image
    · obtain ⟨_, image⟩ := image
      intro x member
      exact distinct x (by simp [randomCalls_calls image x member])
    · exact image.elim
  · rw [sysImage_argsSizes] at image
    obtain ⟨_, rfl, _⟩ := image
    intro x member
    cases member
  · rw [sysImage_args] at image
    obtain ⟨_, rfl, _⟩ := image
    intro x member
    cases member
  · rw [sysImage_environSizes] at image
    obtain ⟨_, rfl, _⟩ := image
    intro x member
    cases member
  · rw [sysImage_environ] at image
    obtain ⟨_, rfl, _⟩ := image
    intro x member
    cases member
  · rw [sysImage_open] at image
    unfold OpenImage at image
    split at image
    · split at image
      · intro x member
        exact distinct x (by simp [openCalls_calls image x member])
      · obtain ⟨rfl, _⟩ := image
        intro x member
        cases member
    · exact image.elim
  · rw [sysImage_close] at image
    unfold CloseImage at image
    split at image
    · split at image
      · obtain ⟨_, rfl, _⟩ := image
        intro x member
        obtain rfl := List.mem_singleton.mp member
        exact distinct _ (by simp)
      · obtain ⟨rfl, _⟩ := image
        intro x member
        cases member
    · exact image.elim
  · exact absurd rfl notRead
  · exact absurd rfl notWrite
  · rw [sysImage_prestat] at image
    unfold PrestatImage at image
    split at image
    · obtain ⟨rfl, _⟩ := image
      intro x member
      cases member
    · exact image.elim
  · rw [sysImage_dirName] at image
    unfold DirNameImage at image
    split at image
    · obtain ⟨rfl, _⟩ := image
      intro x member
      cases member
    · exact image.elim

theorem fdWrite_ne_fdRead : Call.fdWrite ≠ Call.fdRead := by decide

theorem fdRead_ne_fdWrite : Call.fdRead ≠ Call.fdWrite := by decide

/-- An accepted `fd_read` on a handle asks for fewer than `2^32` bytes. -/
theorem read_small {fd capacity : UInt64}
    (h : Call.fdRead.reject [.word fd, .space capacity] = 0) : capacity.toNat < 2 ^ 32 := by
  by_contra big
  have refused : ((61 : UInt64) = 0) = False := eq_false (by decide)
  by_cases fdSmall : fd.toNat < 2 ^ 32
  · simp only [Call.reject, Call.fdRead, rejectArgs, Param.takesArg, ↓reduceIte, Param.reject,
      Arg.value, Arg.capacity, fdSmall, big, refused] at h
  · simp only [Call.reject, Call.fdRead, rejectArgs, Param.takesArg, ↓reduceIte, Param.reject,
      Arg.value, fdSmall, refused] at h

/-- An accepted `fd_write` on a handle offers fewer than `2^32` bytes. -/
theorem write_small {fd : UInt64} {data : Bytes}
    (h : Call.fdWrite.reject [.word fd, .bytes data] = 0) : data.data.size < 2 ^ 32 := by
  by_contra big
  have refused : ((61 : UInt64) = 0) = False := eq_false (by decide)
  by_cases fdSmall : fd.toNat < 2 ^ 32
  · simp only [Call.reject, Call.fdWrite, rejectArgs, Param.takesArg, ↓reduceIte, Param.reject,
      Arg.value, Arg.length, fdSmall, big, refused] at h
  · simp only [Call.reject, Call.fdWrite, rejectArgs, Param.takesArg, ↓reduceIte, Param.reject,
      Arg.value, fdSmall, refused] at h

theorem littleEndian_count {ret : UInt64} (small : ret.toNat < 2 ^ 32) :
    (littleEndian (leBytes 4 ret.toNat)).toNat = ret.toNat := by
  rw [littleEndian_leBytes (by omega) (by omega),
    UInt64.toNat_ofNat_of_lt' (show ret.toNat < 2 ^ 64 by omega)]

theorem image_readData (fd : UInt64) {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {e : Wasi.Event} {l : List Linux.Event}
    (image : Image F L I events e l) :
    Linux.readData fd l = eventReads fd e := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, args, _, rfl⟩ := image
    by_cases zero : fd = 0
    · subst zero
      by_cases within : x.ret.toNat ≤ count.toNat
      · simp [Linux.readData, eventReads, Linux.Event.readBytes, call, args, Linux.arg,
          readReply, within, Transfer.committed, bytesOfList]
      · simp only [Linux.readData, eventReads, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, Linux.Event.readBytes, call, args, Linux.arg, List.getD_cons_zero,
          List.getD_cons_succ, within, and_false, ↓reduceIte, readReply]
        split <;> rfl
    · simp [Linux.readData, eventReads, Linux.Event.readBytes, call, args, Linux.arg, zero,
        Ne.symm zero]
  | write output bytes reply =>
    obtain ⟨x, a, rfl, call, _, _, _, _, _⟩ := image
    simp [Linux.readData, eventReads, Linux.Event.readBytes, call, readCall_ne_writeCall.symm]
  | exit code =>
    cases image
    rfl
  | exitTrap code message =>
    cases image
    rfl
  | sys call args reply =>
    obtain ⟨accepted, image⟩ := image
    by_cases isRead : call = Call.fdRead
    · subst isRead
      rw [sysImage_read] at image
      unfold HandleReadImage at image
      split at image
      · rename_i handle capacity
        split at image
        · obtain ⟨a, prior, ret, output, rfl, rfl⟩ := image
          have small := read_small accepted
          unfold handleReadReply
          by_cases within : ret.toNat ≤ capacity.toNat
          · simp only [within, ↓reduceIte]
            by_cases same : handle = fd
            · subst same
              simp [Linux.readData, eventReads, Linux.Event.readBytes, Linux.arg, Arg.value,
                within, littleEndian_count (show ret.toNat < 2 ^ 32 by omega), bytesOfList]
            · simp [Linux.readData, eventReads, Linux.Event.readBytes, Linux.arg, Arg.value, same]
          · simp only [within, ↓reduceIte]
            split <;> simp [Linux.readData, eventReads, Linux.Event.readBytes, Linux.arg, within,
              errnoOf_valid]
        · obtain ⟨rfl, rfl⟩ := image
          simp [Linux.readData, eventReads]
      · exact image.elim
    · by_cases isWrite : call = Call.fdWrite
      · subst isWrite
        rw [sysImage_write] at image
        unfold HandleWriteImage at image
        split at image
        · split at image
          · obtain ⟨a, ret, rfl, rfl⟩ := image
            cases handleWriteReply (UInt64.ofNat _) ret <;>
              simp [Linux.readData, eventReads, Linux.Event.readBytes, readCall_ne_writeCall.symm,
                fdWrite_ne_fdRead]
          · obtain ⟨rfl, rfl⟩ := image
            simp [Linux.readData, eventReads, fdWrite_ne_fdRead]
        · exact image.elim
      · rw [readData_none fun x member => (sysImage_calls image isRead isWrite x member).1]
        cases reply <;> simp [eventReads, isRead]

theorem image_writeData (fd : UInt64) {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {e : Wasi.Event} {l : List Linux.Event}
    (image : Image F L I events e l) :
    Linux.writeData fd l = eventWrites fd e := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, _, _, _⟩ := image
    simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, call, readCall_ne_writeCall]
  | write target bytes reply =>
    obtain ⟨x, a, rfl, call, args, inputs, _, _, rfl⟩ := image
    by_cases same : target.fd = fd
    · subst same
      simp only [Linux.writeData, eventWrites, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Linux.Event.writeBytes, call, args, inputs, Linux.arg,
        List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, true_and,
        ↓reduceIte, writeReply]
      by_cases within : x.ret.toNat ≤ (UInt64.ofNat bytes.data.size).toNat
      · simp only [within, ↓reduceIte, Transfer.committed]
      · simp only [within, ↓reduceIte]
        split <;> rfl
    · simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, args, Linux.arg, same]
  | exit code =>
    cases image
    rfl
  | exitTrap code message =>
    cases image
    rfl
  | sys call args reply =>
    obtain ⟨accepted, image⟩ := image
    by_cases isWrite : call = Call.fdWrite
    · subst isWrite
      rw [sysImage_write] at image
      unfold HandleWriteImage at image
      split at image
      · rename_i handle data
        split at image
        · obtain ⟨a, ret, rfl, rfl⟩ := image
          have small := write_small accepted
          have wide : (UInt64.ofNat data.data.size).toNat = data.data.size :=
            UInt64.toNat_ofNat_of_lt' (show data.data.size < 2 ^ 64 by omega)
          unfold handleWriteReply
          rw [wide]
          by_cases within : ret.toNat ≤ data.data.size
          · simp only [within, ↓reduceIte]
            by_cases same : handle = fd
            · subst same
              simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, Linux.arg, Arg.value,
                within, wide, littleEndian_count (show ret.toNat < 2 ^ 32 by omega)]
            · simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, Linux.arg, Arg.value,
                same]
          · simp only [within, ↓reduceIte]
            split <;> simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, Linux.arg,
              within, wide, errnoOf_valid]
        · obtain ⟨rfl, rfl⟩ := image
          simp [Linux.writeData, eventWrites]
      · exact image.elim
    · by_cases isRead : call = Call.fdRead
      · subst isRead
        rw [sysImage_read] at image
        unfold HandleReadImage at image
        split at image
        · split at image
          · obtain ⟨a, prior, ret, output, rfl, rfl⟩ := image
            cases handleReadReply _ ret output <;>
              simp [Linux.writeData, eventWrites, Linux.Event.writeBytes, readCall_ne_writeCall,
                fdRead_ne_fdWrite]
          · obtain ⟨rfl, rfl⟩ := image
            simp [Linux.writeData, eventWrites, fdRead_ne_fdWrite]
        · exact image.elim
      · rw [writeData_none fun x member => (sysImage_calls image isRead isWrite x member).2]
        cases reply <;> simp [eventWrites, isWrite]

/-- The bytes that the reads of `fd` returned in images of a WASI trace are those that its events
read from `fd`. -/
theorem Images.readData (fd : UInt64) {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (h : Images F L I events trace ls) : Linux.readData fd ls = committedReads fd trace := by
  induction h with
  | nil => rfl
  | @cons _ e l es ls image _ ih =>
    rw [committedReads, List.flatMap_cons, ← committedReads, ← ih, Linux.readData,
      List.flatMap_append, ← Linux.readData, image_readData fd image]
    rfl

/-- The bytes that the writes of `fd` took in images of a WASI trace are those that its events
wrote to `fd`. -/
theorem Images.writeData (fd : UInt64) {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (h : Images F L I events trace ls) : Linux.writeData fd ls = committedWrites fd trace := by
  induction h with
  | nil => rfl
  | @cons _ e l es ls image _ ih =>
    rw [committedWrites, List.flatMap_cons, ← committedWrites, ← ih, Linux.writeData,
      List.flatMap_append, ← Linux.writeData, image_writeData fd image]
    rfl

end Verified.Shim
